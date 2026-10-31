-- Prove2me | Definitions.Def_OAIQ095D004
-- name    : OAIQ095D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:02:45.758644+00:00
-- url     : https://prove2.me/theorems/f940354c-6a14-4a87-80dc-397611e7ef9c
-- title:
--   Definitions bundle OAIQ095D004 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 618 declarations of OpenAI's Lean: 402 definitions, 9 instances and 207 theorems. The definitions and types are `OAI.Ostmann.adaptivePivotCoefficients`, `OAI.Ostmann.adaptivePivotData`, `OAI.Ostmann.adaptivePivotResidueSplit`, `OAI.Ostmann.advanceNatAtomSources`, `OAI.Ostmann.allowedSummandResidues`, `OAI.Ostmann.amplificationCRT`, `OAI.Ostmann.amplificationWeight`, `OAI.Ostmann.anchorCodeEntry`, `OAI.Ostmann.anchorIncoming`, `OAI.Ostmann.appendMovingSlotLeaves`, `OAI.Ostmann.arithmeticLeafSupport`, `OAI.Ostmann.arithmeticPairSplitTest`, `OAI.Ostmann.arithmeticQuadraticCoefficient`, `OAI.Ostmann.arrangementBoundary`, `OAI.Ostmann.arrangementComponentVertexEquiv`, `OAI.Ostmann.arrangementGraphReindex`, `OAI.Ostmann.arrangementLeft`, `OAI.Ostmann.arrangementMatching`, `OAI.Ostmann.arrangementProductMap`, `OAI.Ostmann.arrangementRangeEquiv`, `OAI.Ostmann.arrangementRight`, `OAI.Ostmann.atomInterval`, `OAI.Ostmann.atomIntervalRanges`, `OAI.Ostmann.atomPairChecks`, `OAI.Ostmann.badPrimeLogCells`, `OAI.Ostmann.biasedPrimeBand`, `OAI.Ostmann.binaryMomentBound`, `OAI.Ostmann.bottomQuartet`, `OAI.Ostmann.boundAtomSources`, `OAI.Ostmann.buildMovingGiantTree`, `OAI.Ostmann.buildMovingSlotData`, `OAI.Ostmann.bulkBlockProductHom`, `OAI.Ostmann.bulkFourierFactors`, `OAI.Ostmann.bulkFullSupportPolynomials`, `OAI.Ostmann.bulkLogCutoffFactors`, `OAI.Ostmann.bulkNodeFactors`, `OAI.Ostmann.bulkPairCorrelation`, `OAI.Ostmann.bulkSlotLeaves`, `OAI.Ostmann.bulkSmoothFactors`, `OAI.Ostmann.centeredSupportEquiv` and 362 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Ostmann_Arithmetic_ArithmeticLifts`, `Ostmann_Arithmetic_ArithmeticQuadraticCoefficient`, `Ostmann_Arithmetic_ArithmeticSplitData`, `Ostmann_Arithmetic_AtomIntervalRanges`, `Ostmann_Arithmetic_BulkFourierFactors`, `Ostmann_Arithmetic_BulkFrequencyFactor`, `Ostmann_Arithmetic_BulkFullSupportPolynomials`, `Ostmann_Arithmetic_BulkKernelPairComparison`, `Ostmann_Arithmetic_BulkNodeFactors`, `Ostmann_Arithmetic_BulkSlotFieldBridge`, `Ostmann_Arithmetic_BulkSlotNodup`, `Ostmann_Arithmetic_BulkSmoothFactors`, `Ostmann_Arithmetic_BulkSpectatorNorm`, `Ostmann_Arithmetic_CompensatedPairSupport`, `Ostmann_Arithmetic_FrequencyModelAdaptiveSupport`, `Ostmann_Arithmetic_FrequencyModelCoefficients`, `Ostmann_Arithmetic_FrequencyModelModulus`, `Ostmann_Arithmetic_FrequencyModelPairSupport`, `Ostmann_Arithmetic_FrequencyModelPaths`, `Ostmann_Arithmetic_FrequencyTreeNodes`, `Ostmann_Arithmetic_FrequencyTreeSum`, `Ostmann_Arithmetic_FrozenRegularSupport`, `Ostmann_Arithmetic_FrozenSpectatorAverage`, `Ostmann_Arithmetic_GuardedHistoryCancellation`, `Ostmann_Arithmetic_HarmonicHistorySupport`, `Ostmann_Arithmetic_MovingAmplitudeHarmonicCost`, `Ostmann_Arithmetic_MovingAmplitudeIndex`, `Ostmann_Arithmetic_MovingAmplitudeSymmetrizedCost`, `Ostmann_Arithmetic_MovingAmplitudeTerms`, `Ostmann_Arithmetic_MovingArithmeticBlocks`, `Ostmann_Arithmetic_MovingAuxiliaryPeriod`, `Ostmann_Arithmetic_MovingAuxiliaryUnits`, `Ostmann_Arithmetic_MovingAveragedIntegerNode`, `Ostmann_Arithmetic_MovingBulkFrames`, `Ostmann_Arithmetic_MovingBulkLogFactors`, `Ostmann_Arithmetic_MovingBulkPairedCutoffs`, `Ostmann_Arithmetic_MovingCompensatedEquations`, `Ostmann_Arithmetic_MovingCompensationWeight`, `Ostmann_Arithmetic_MovingDiagonalOuterWeight`, `Ostmann_Arithmetic_MovingFourierFactor`, `Ostmann_Arithmetic_MovingFourierPolynomials`, `Ostmann_Arithmetic_MovingFrequencyCoefficient`, `Ostmann_Arithmetic_MovingFrequencyResidues`, `Ostmann_Arithmetic_MovingFullSupport`, `Ostmann_Arithmetic_MovingGiantPolynomial`, `Ostmann_Arithmetic_MovingGiantSamples`, `Ostmann_Arithmetic_MovingInternalLocalFactor`, `Ostmann_Arithmetic_MovingMaskedTemplateEnergy`, `Ostmann_Arithmetic_MovingModularSpectator`, `Ostmann_Arithmetic_MovingNodeCutoffFactor`, `Ostmann_Arithmetic_MovingOriginalSampleExpansion`, `Ostmann_Arithmetic_MovingOriginalStatistic`, `Ostmann_Arithmetic_MovingOuterKernel`, `Ostmann_Arithmetic_MovingPatternBulkData`, `Ostmann_Arithmetic_MovingPrimeOccurrences`, `Ostmann_Arithmetic_MovingRealResidues`, `Ostmann_Arithmetic_MovingRecursiveCompensation`, `Ostmann_Arithmetic_MovingRecursiveSupport`, `Ostmann_Arithmetic_MovingRegularTemplate`, `Ostmann_Arithmetic_MovingResidueFactorization`, `Ostmann_Arithmetic_MovingRestoredMultiplier`, `Ostmann_Arithmetic_MovingSampleCoordinateLevels`, `Ostmann_Arithmetic_MovingSampleCoordinates`, `Ostmann_Arithmetic_MovingSampleMap`, `Ostmann_Arithmetic_MovingSampleOccurrence`, `Ostmann_Arithmetic_MovingSamplePairExpansion`, `Ostmann_Arithmetic_MovingSamplePairPatterns`, `Ostmann_Arithmetic_MovingSamplePrior`, `Ostmann_Arithmetic_MovingSampleSlots`, `Ostmann_Arithmetic_MovingSampleValues`, `Ostmann_Arithmetic_MovingSampledRecursion`, `Ostmann_Arithmetic_MovingScalarWindows`, `Ostmann_Arithmetic_MovingSeparatedProduct`, `Ostmann_Arithmetic_MovingSignedUnits`, `Ostmann_Arithmetic_MovingSlotLines`, `Ostmann_Arithmetic_MovingSlotSpectator`, `Ostmann_Arithmetic_MovingSlotSystem`, `Ostmann_Arithmetic_MovingSquareLines`, `Ostmann_Arithmetic_MovingSupportCells`, `Ostmann_Arithmetic_MovingSupportWeight`, `Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel`, `Ostmann_Arithmetic_MovingSymmetrizedProductLower`, `Ostmann_Arithmetic_MovingTemplateCoefficient`, `Ostmann_Arithmetic_MovingTemplateEnumeration`, `Ostmann_Arithmetic_MovingTemplateSupport`, `Ostmann_Arithmetic_MovingTemplateWeightedSupport`, `Ostmann_Arithmetic_NodeBulkProducts`, `Ostmann_Arithmetic_RealBulkKernel`, `Ostmann_Arithmetic_RealNodeSupport`, `Ostmann_Arithmetic_RealSlotEvaluation`, `Ostmann_Arithmetic_ReconstructedPhaseWeight`, `Ostmann_Arithmetic_RecursiveFrequencySupport`, `Ostmann_Arithmetic_SequentialSupport`, `Ostmann_Arithmetic_SingleFrequencyModulus`, `Ostmann_Arithmetic_SingleFrequencyTree`, `Ostmann_Arithmetic_SingleHistorySupport`, `Ostmann_Arithmetic_SmoothPolynomialWeight`, `Ostmann_Arithmetic_SupportedPolynomialCharacterSum`, `Ostmann_Arithmetic_WeightedArithmeticSupport`, `Ostmann_Characters_AnchorGraphEvolution`, `Ostmann_Characters_AnchorPairCode`, `Ostmann_Characters_CharacterAtomIteration`, `Ostmann_Characters_CharacterCellIntervals`, `Ostmann_Characters_CharacterFullPrimeCells`, `Ostmann_Characters_CharacterHCoordinates`, `Ostmann_Characters_CharacterHigherBias`, `Ostmann_Characters_CharacterLiftCellBounds`, `Ostmann_Characters_CharacterLogDerivativeLocal`, `Ostmann_Characters_CharacterLogDerivativeRight`, `Ostmann_Characters_CharacterLogDerivativeSeparated`, `Ostmann_Characters_CharacterPrimeCells`, `Ostmann_Characters_CharacterScheduleCounts`, `Ostmann_Characters_CharacterScheduleRoles`, `Ostmann_Characters_CharacterSelectedBulk`, `Ostmann_Characters_CharacterSelectionScales`, `Ostmann_Characters_CharacterTargetCenters`, `Ostmann_Characters_CharacterTargetCode`, `Ostmann_Characters_FiniteKernelLinearMaps`, `Ostmann_Characters_HigherCharacterDecorrelation`, `Ostmann_Characters_LogCutoffPolynomial`, `Ostmann_Characters_MixedBulkSymmetrization`, `Ostmann_Characters_MixedExternalAverage`, `Ostmann_Characters_NormalizedResidueIndicator`, `Ostmann_Characters_PolynomialLineFlags`, `Ostmann_Characters_PolynomialWeightPair`, `Ostmann_Characters_QuartetCrossBound`, `Ostmann_Characters_QuartetFullCoordinates`, `Ostmann_Characters_QuartetIndexCoordinates`, `Ostmann_Characters_QuartetMovingAction`, `Ostmann_Characters_QuartetProductCoordinates`, `Ostmann_Characters_QuartetProductFibers`, `Ostmann_Characters_QuartetSamePairBound`, `Ostmann_Characters_ReciprocalPolynomialFactor`, `Ostmann_Characters_SparseAdditiveKernel`, `Ostmann_Characters_SparseKernelLocalBlocks`, `Ostmann_Characters_SparsePolydiscBlocks`, `Ostmann_Characters_SparseResidueMatrix`, `Ostmann_Characters_SparseTensorPolynomial`, `Ostmann_Characters_TreeAncestorScheme`, `Ostmann_Characters_TreeLeafIndex`, `Ostmann_Characters_TreeLeafProducts`, `Ostmann_Characters_TreeSplitCoordinates`, `Ostmann_Characters_TreeTupleProfiles`, `Ostmann_Construction_AdaptivePivotCoefficients`, `Ostmann_Construction_AdaptivePivotSupport`, `Ostmann_Construction_ArrangementBoundary`, `Ostmann_Construction_ArrangementProductImage`, `Ostmann_Construction_ArrangementProducts`, `Ostmann_Construction_ArrangementUniformLaw`, `Ostmann_Construction_AtomSourceDescent`, `Ostmann_Construction_AtomTopSupport`, `Ostmann_Construction_BadPrimeLogCells`, `Ostmann_Construction_ComplexCellMeans`, `Ostmann_Construction_ConstituentAmplitudeEnergy`, `Ostmann_Construction_ConstituentBlockProducts`, `Ostmann_Construction_ConstituentCharacterCoefficient`, `Ostmann_Construction_ConstituentCharacterCore`, `Ostmann_Construction_ConstituentCopiedWeight`, `Ostmann_Construction_ConstituentDiagonal`, `Ostmann_Construction_ConstituentDiagonalSupport`, `Ostmann_Construction_ConstituentEnergyTransport`, `Ostmann_Construction_ConstituentFamilyEnergy`, `Ostmann_Construction_ConstituentGuardedNext`, `Ostmann_Construction_ConstituentInvariantCharacter`, `Ostmann_Construction_ConstituentInvariantPairFactors`, `Ostmann_Construction_ConstituentMatchedCharacter`, `Ostmann_Construction_ConstituentMatchingExpansion`, `Ostmann_Construction_ConstituentOriginalAmplitude`, `Ostmann_Construction_ConstituentPairFactors`, `Ostmann_Construction_ConstituentPrimeGuardedAmplitude`, `Ostmann_Construction_ConstituentRootCoefficient`, `Ostmann_Construction_ConstituentTransferWeight`, `Ostmann_Construction_ConstituentUnweighted`, `Ostmann_Construction_ConstituentWords`, `Ostmann_Construction_ConstructedCharacterCells`, `Ostmann_Construction_CopiedDirectedPhase`, `Ostmann_Construction_CopiedPriorFubini`, `Ostmann_Construction_CopyScheduleSupport`, `Ostmann_Construction_CopyScheduleUnary`, `Ostmann_Construction_DyadicHarmonicBias`, `Ostmann_Construction_ExpandedOutsideWords`, `Ostmann_Construction_ExpandedPrimeReplay`, `Ostmann_Construction_ExpandedRangedWeight`, `Ostmann_Construction_ExpandedScheduleCoordinates`, `Ostmann_Construction_ExpandedScheduleRanges`, `Ostmann_Construction_ExpandedScheduleWeight`, `Ostmann_Construction_ExpandedScheduledTemplate`, `Ostmann_Construction_ExternalSquareFibers`, `Ostmann_Construction_FinalParityPaths`, `Ostmann_Construction_FinalReassignmentInteraction`, `Ostmann_Construction_FiniteCellMeans`, `Ostmann_Construction_FixedCharacterTargetCells`, `Ostmann_Construction_FixedPivotTopConditions`, `Ostmann_Construction_FixedPivotTwoCoordinates`, `Ostmann_Construction_FullAtomTransferWeight`, `Ostmann_Construction_GiantOuterFactors`, `Ostmann_Construction_GiantReciprocalFactor`, `Ostmann_Construction_GraphCopySchedule`, `Ostmann_Construction_GroupedCoprimeCoefficient`, `Ostmann_Construction_GroupedFullCoprime`, `Ostmann_Construction_GroupedScheduleCoefficient`, `Ostmann_Construction_GroupedUnitCoefficient`, `Ostmann_Construction_HalfPrimeEndpoint`, `Ostmann_Construction_HistoryGiantSources`, `Ostmann_Construction_HistoryResidueGate`, `Ostmann_Construction_InitialConstituentPoisson`, `Ostmann_Construction_InitialCutoffProduct`, `Ostmann_Construction_InitialFrozenAmplitude`, `Ostmann_Construction_InitialHalfListWeights`, `Ostmann_Construction_InitialHalfLogSlots`, `Ostmann_Construction_InitialMovingAverage`, `Ostmann_Construction_InitialMovingBulkLists`, `Ostmann_Construction_InitialMovingBulkTree`, `Ostmann_Construction_InitialMovingCutoff`, `Ostmann_Construction_InitialMovingData`, `Ostmann_Construction_InitialMovingSlots`, `Ostmann_Construction_InitialMovingSupport`, `Ostmann_Construction_InitialMovingTreeWeight`, `Ostmann_Construction_InitialWordBinIdentification`, `Ostmann_Construction_InitialWordRanges`, `Ostmann_Construction_InsertedConstituentWords`, `Ostmann_Construction_LocalSmoothGiantSelection`, `Ostmann_Construction_MaskedPhaseGiantMean`, `Ostmann_Construction_ModularAdaptiveCoefficients`, `Ostmann_Construction_ModularAdaptiveSupport`, `Ostmann_Construction_OriginalDirectedTransfer`, `Ostmann_Construction_PairedScheduledHistory`, `Ostmann_Construction_PhaseGiantTest`, `Ostmann_Construction_PrimeLogCellMeasure`, `Ostmann_Construction_RegularInitialAmplitude`, `Ostmann_Construction_ScaledWordLeaves`, `Ostmann_Construction_ScheduleAtomSystem`, `Ostmann_Construction_ScheduleWordSlots`, `Ostmann_Construction_ScheduledFinalPrimeRanges`, `Ostmann_Construction_ScheduledFourierEnergy`, `Ostmann_Construction_ScheduledFrequencyHistory`, `Ostmann_Construction_ScheduledHistoryEmbedding`, `Ostmann_Construction_ScheduledInitialPhase`, `Ostmann_Construction_ScheduledNodeSources`, `Ostmann_Construction_ScheduledPrimePhase`, `Ostmann_Construction_ScheduledRolePrior`, `Ostmann_Construction_ScheduledSamplePhase`, `Ostmann_Construction_ScheduledTransferGraph`, `Ostmann_Construction_ScheduledWordLeafCoordinates`, `Ostmann_Construction_ScheduledWordLeafProducts`, `Ostmann_Construction_SelectedAnchorMatchingCount`, `Ostmann_Construction_SignedAtomSchedule`, `Ostmann_Construction_TransferConjugations`, `Ostmann_Construction_TransferFrequencyRange`, `Ostmann_Construction_TransferredPivotSubstitution`, `Ostmann_Construction_TwoCoordinatePrior`, `Ostmann_Construction_TypicalCharacterShells`, `Ostmann_Construction_WeightedWordLeaves`, `Ostmann_Construction_WordTransferPeriods`, `Ostmann_Construction_WordTransferReplay`, `Ostmann_Preliminaries_AdditiveSieveProbability`, `Ostmann_Preliminaries_FiniteMean`, `Ostmann_Preliminaries_FullSummandResidues`, `Ostmann_QuadraticCenter_AmplificationMean`, `Ostmann_QuadraticCenter_AmplificationWeight`, `Ostmann_QuadraticCenter_ClosedQuadraticBand`, `Ostmann_QuadraticCenter_FixedQuadraticFamily`, `Ostmann_QuadraticCenter_FullQuadraticCoefficient`, `Ostmann_QuadraticCenter_OffWitnessFamily`, `Ostmann_QuadraticCenter_OuterDivisorNorm`, `Ostmann_QuadraticCenter_PositiveDivisorEnergy`, `Ostmann_Quadratic_QuadraticBiasSelection`, `Ostmann_Supply_BilinearCube`, `Ostmann_Supply_BilinearCubeSupport`, `Ostmann_Supply_CenteredCoordinateSupport`, `Ostmann_Supply_FiniteSpectralProjection`, `Ostmann_Tree_ArrangementGraph`, `Ostmann_Tree_ArrangementReindex`, `Ostmann_Tree_CrossQuartetFiber`, `Ostmann_Tree_PairedFrequencyProjection`, `Ostmann_Tree_PartitionMatching`, `Ostmann_Tree_PreorderNodePaths`, `Ostmann_Tree_SamePairFiber`, `Ostmann_Tree_TwoVertexReindex`, `Ostmann_ZeroDensity_ArithmeticRieszMean`, `Ostmann_ZeroDensity_CharacterContourZeroSet`, `Ostmann_ZeroDensity_CharacterGammaContour`, `Ostmann_ZeroDensity_CharacterGammaGrowth`, `Ostmann_ZeroDensity_CharacterGammaShift`, `Ostmann_ZeroDensity_CharacterHeightZeroCount`, `Ostmann_ZeroDensity_CharacterRieszLocalDecay`, `Ostmann_ZeroDensity_CharacterZeroMultiplicity`, `Ostmann_ZeroDensity_CharacterZeroPolynomial`, `Ostmann_ZeroDensity_CharacterZeroQuotientBound`, `Ostmann_ZeroDensity_CharacterZeroQuotientLog`, `Ostmann_ZeroDensity_CompletedCompensationPrior`, `Ostmann_ZeroDensity_ComplexLowZeroBound`, `Ostmann_ZeroDensity_DensityCRTProduct`, `Ostmann_ZeroDensity_DensityCompletedSquare`, `Ostmann_ZeroDensity_DensityCorrelation`, `Ostmann_ZeroDensity_DensityCriticalDetector`, `Ostmann_ZeroDensity_DensityCriticalMass`, `Ostmann_ZeroDensity_DensityDetectorAnalytic`, `Ostmann_ZeroDensity_DensityDetectorIntegral`, `Ostmann_ZeroDensity_DensityDetectorSeries`, `Ostmann_ZeroDensity_DensityFiniteContourShift`, `Ostmann_ZeroDensity_DensityNormalizedEquation`, `Ostmann_ZeroDensity_DensitySmoothedKernel`, `Ostmann_ZeroDensity_DensitySquareContour`, `Ostmann_ZeroDensity_DensitySquareEquation`, `Ostmann_ZeroDensity_DensitySquareGaussian`, `Ostmann_ZeroDensity_DensitySquareLimit`, `Ostmann_ZeroDensity_DensitySquareSeriesIntegral`, `Ostmann_ZeroDensity_DensitySquareTerms`, `Ostmann_ZeroDensity_GammaContourBounds`, `Ostmann_ZeroDensity_GammaGrowthStrip`, `Ostmann_ZeroDensity_GammaLogDerivativeBound`, `Ostmann_ZeroDensity_GammaRealContourBound`, `Ostmann_ZeroDensity_IntegratedThetaMain`, `Ostmann_ZeroDensity_LogDerivativeContourDisk`, `Ostmann_ZeroDensity_LogDerivativeDiskBound`, `Ostmann_ZeroDensity_PageSelection`, `Ostmann_ZeroDensity_PrincipalRieszBound`, `Ostmann_ZeroDensity_PrincipalRieszIntegral`, `Ostmann_ZeroDensity_PrincipalRieszRectangle`, `Ostmann_ZeroDensity_RectangleBoundary`, `Ostmann_ZeroDensity_ResiduePrimePowerRemoval`, `Ostmann_ZeroDensity_ResidueRieszFinite`, `Ostmann_ZeroDensity_RieszCoprimeComparison`, `Ostmann_ZeroDensity_RieszExponentialParameters`, `Ostmann_ZeroDensity_RieszFiniteSum`, `Ostmann_ZeroDensity_RieszPoleRectangle`, `Ostmann_ZeroDensity_RieszPositiveRecovery`, `Ostmann_ZeroDensity_RieszPrimeRemoval`, `Ostmann_ZeroDensity_RieszResidueError`, `Ostmann_ZeroDensity_RieszSmoothRecovery`, `Ostmann_ZeroDensity_RieszUnsmoothing`, `Ostmann_ZeroDensity_SmallDiskLogDerivative`, `Ostmann_ZeroDensity_SmoothContourResidue`, `Ostmann_ZeroDensity_SmoothDirichletIntegral`, `Ostmann_ZeroDensity_SmoothHorizontalBound`, `Ostmann_ZeroDensity_SmoothLeftContourWeight`, `Ostmann_ZeroDensity_SmoothMellinInversion`, `Ostmann_ZeroDensity_SmoothRightContour`, `Ostmann_ZeroDensity_SmoothVerticalKernel`, `Ostmann_ZeroDensity_ThetaMainTerm`, `Ostmann_ZeroDensity_TreeDensity`, `Ostmann_ZeroDensity_ZetaAbsoluteRightBound`, `Ostmann_ZeroDensity_ZetaNearZeroBound`, `Ostmann_ZeroDensity_ZetaTrigonometric`, `Ostmann_ZeroDensity_ZetaZeroFreeRegion`.
--
--   **Imports.** It imports the bundles `OAIQ095D000`, `OAIQ095D001` and `OAIQ095D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D006` and `OAIQ095D007`; the statements `OAI.Ostmann.densitySmoothedSquare_mean`, `OAI.Ostmann.density_polynomial_alternative_balanced`, `OAI.Ostmann.eventual_character_anchor_decay`, `OAI.Ostmann.eventual_large_kernel_prime_moment`, `OAI.Ostmann.eventual_original_outer_first_moment`, `OAI.Ostmann.eventual_selected_nonanchor_product_decay`, `OAI.Ostmann.eventual_uniform_character_endpoint_contradiction`, `OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient` and `OAI.Ostmann.projectedTree_mean_le`; the proofs of `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction`, `OAI.Ostmann.eventual_original_outer_first_moment`, `OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient`, `OAI.Ostmann.quadraticBandMass_isLittleO` and `OAI_Ostmann_quadratic_rough_iteration`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D000
import Definitions.Def_OAIQ095D001
import Definitions.Def_OAIQ095D002

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- A prime-square residue is a unit exactly when its reduction is nonzero. -/
theorem isUnit_square_iff {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2)) :
    IsUnit x ↔ squareReduction p x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (squareReduction p)).ne_zero
  · intro hx
    have hv : squareReduction p x = (x.val : ZMod p) := by
      have h := congrArg (squareReduction p) (ZMod.natCast_zmod_val x)
      simpa only [map_natCast] using h.symm
    have hc : x.val.Coprime p := (ZMod.isUnit_iff_coprime _ _).mp
      (isUnit_iff_ne_zero.mpr (hv ▸ hx))
    have hunit : IsUnit (x.val : ZMod (p ^ 2)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right 2)
    simpa only [ZMod.natCast_zmod_val] using hunit

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

/-- This is the actual product of the centered functions, formed by CRT
along the list of distinct prime factors. -/
noncomputable def densityCRTList (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    @DensityCRTData ps.prod ⟨(prime_list_prod_pos ps hp).ne'⟩ := by
  cases ps with
  | nil => exact DensityCRTData.one
  | cons p ps =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : Fact p.Prime := ⟨hp p List.mem_cons_self⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change DensityCRTData (p * ps.prod)
    exact DensityCRTData.mul (m := p) (n := ps.prod) (Nat.coprime_list_prod_right_iff.mpr hcp.1)
      (DensityCRTData.prime p (S p)) (densityCRTList ps hp' hcp.2 S)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-by-prime correlation bound for centered densities -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- Extend the local transform to an unrestricted prime index. The value at
zero is immaterial; all applications index positive primes. -/
noncomputable def primeDensityFourier (f : ∀ p : ℕ, ZMod p → ℂ) (p : ℕ) : ZMod p → ℂ :=
  if h : 0 < p then @densityFourier p ⟨h.ne'⟩ (f p) else fun _ => 0

noncomputable def correlationPrimeFactor (f : ∀ p : ℕ, ZMod p → ℂ)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) (p : ℕ) (x : ZMod p) : ℂ :=
  match side p with
  | .left => primeDensityFourier f p ((a p : ZMod p) * x)
  | .right => conj (primeDensityFourier f p ((b p : ZMod p) * x))
  | .both => primeDensityFourier f p ((a p : ZMod p) * x) *
      conj (primeDensityFourier f p ((b p : ZMod p) * x))

noncomputable def correlationPrimeBound (side : ℕ → CorrelationSide) (p : ℕ) : ℝ :=
  match side p with
  | .left => (Real.sqrt (p : ℝ))⁻¹
  | .right => (Real.sqrt (p : ℝ))⁻¹
  | .both => 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy of the original positive quadratic series on a dyadic segment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def primeDivisorPositive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ) : ℂ := by
  classical
  exact if hU : U ⊆ P then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))).ne'⟩
    positiveQuadraticSum (densityFourier (densityCRTList U.toList
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hP p (hU hp))) D).value)
      (a U) (θ U) Φ R v s
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OuterDivisorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The outer divisor gives the full reciprocal-divisor norm gain -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def primeDivisorMultiples (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (P : ℕ) (U : Finset ℕ) (s : ℕ) : ℂ :=
  (P : ℂ)⁻¹ * primeDivisorPositive Q hQ D a θ Φ R v U (s * P ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both divisor sums in the original quadratic coefficient -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def fullQuadraticCoefficient (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ) : ℂ :=
  divisorWeightedCoefficient Q ξ (fun V s =>
    ∑ U ∈ Q.powerset, c U *
      primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s) s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependence of the original coefficient on finite arithmetic residues -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def arithmeticQuadraticCoefficient (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (s : ℕ) : ℂ :=
  fullQuadraticCoefficient Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ) Φ R P (quadraticSymbolCoefficient M) (quadraticDivisorSymbol M) s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

noncomputable def sequentialSupport {A : Type} (test : List A → A → Prop)
    (past : List A) : (n : ℕ) → SplitSamples A n → ℝ
  | 0, _ => 1
  | n + 1, x => if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

instance treeLeafTupleFintype (U : Type*) [Fintype U] (n : ℕ) : Fintype (TreeLeafTuple U n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype U)
  | succ n ih => exact @instFintypeProd _ _ ih ih

def treeLeafFiberZeroEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 0 P ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨P, rfl⟩
  left_inv x := Subtype.ext x.property.symm
  right_inv x := by cases x; rfl

/-- Exposing the product in the left half leaves independent product fibers below it. -/
def treeLeafFiberSuccEquiv {U : Type*} [CommGroup U] (n : ℕ) (P : U) :
    TreeLeafFiber U (n + 1) P ≃
      Σ m : U, TreeLeafFiber U n m × TreeLeafFiber U n (P / m) where
  toFun x := ⟨treeLeafProduct n x.1.1, ⟨x.1.1, rfl⟩, ⟨x.1.2, by
    calc
      _ = (treeLeafProduct n x.1.1 * treeLeafProduct n x.1.2) /
          treeLeafProduct n x.1.1 := (mul_div_cancel_left _ _).symm
      _ = _ := congrArg (fun t => t / treeLeafProduct n x.1.1) x.property⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by
    change treeLeafProduct n x.2.1.1 * treeLeafProduct n x.2.2.1 = P
    rw [x.2.1.property, x.2.2.property]
    exact mul_div_cancel _ _⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨m, ⟨a, ha⟩, ⟨b, hb⟩⟩
    dsimp at ha hb ⊢
    subst m
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeSplitCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent split coordinates on each actual leaf-product fiber -/

namespace Ostmann

open scoped BigOperators Classical

def splitSamplesAppendEquiv (A : Type) : (m n : ℕ) →
    SplitSamples A (m + n) ≃ SplitSamples A m × SplitSamples A n
  | 0, n => by
      let e : SplitSamples A n ≃ Unit × SplitSamples A n :=
        { toFun := fun x => ((), x)
          invFun := Prod.snd
          left_inv := fun _ => rfl
          right_inv := fun x => by rcases x with ⟨u, x⟩; cases u; rfl }
      simpa only [Nat.zero_add, SplitSamples] using e
  | m + 1, n => by
      have e := (Equiv.prodCongr (Equiv.refl A) (splitSamplesAppendEquiv A m n)).trans
        (Equiv.prodAssoc A (SplitSamples A m) (SplitSamples A n)).symm
      simpa only [Nat.succ_add, SplitSamples] using e

/-- Preorder split products are coordinates: root split first, followed by
the left subtree and the right subtree. Each coordinate is an independent
Haar unit even after the total leaf product is fixed. -/
noncomputable def treeLeafSplitEquiv {G : Type} [CommGroup G] : (n : ℕ) → (P : G) →
    TreeLeafFiber G n P ≃ SplitSamples G (2 ^ n - 1)
  | 0, P => treeLeafFiberZeroEquiv P
  | n + 1, P => by
      let k := 2 ^ n - 1
      let e : TreeLeafFiber G (n + 1) P ≃ G × (SplitSamples G k × SplitSamples G k) :=
        (treeLeafFiberSuccEquiv n P).trans
          ((Equiv.sigmaCongrRight fun m =>
            Equiv.prodCongr (treeLeafSplitEquiv n m) (treeLeafSplitEquiv n (P / m))).trans
              (Equiv.sigmaEquivProd G (SplitSamples G k × SplitSamples G k)))
      have hcount : 2 ^ (n + 1) - 1 = k + k + 1 := by
        have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        dsimp [k]
        rw [pow_succ]
        omega
      have e' := e.trans (Equiv.prodCongr (Equiv.refl G) (splitSamplesAppendEquiv G k k).symm)
      simpa only [hcount, SplitSamples] using e'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue data at an exposed arithmetic split -/

namespace Ostmann

open scoped BigOperators Classical

/-- `none` means a preceding unit or support test failed. It has zero
weight and does not impose any condition on an unexposed split. -/
def arithmeticPairSplitTest {Q : ℕ} (d : Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) : Prop :=
  match d with
  | none => False
  | some (d, e) => d.test x ∧ e.test x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original positive periodic amplification weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def amplificationWeight (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) : ℝ :=
  ∏ p ∈ Q, (1 + (1 / 16 : ℝ) * centeredDensity (D p) (n : ZMod p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_AmplificationMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive periodic amplification has mean one -/

namespace Ostmann

open scoped BigOperators

noncomputable def amplificationCRT (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) : ZMod Q.toList.prod → ℂ :=
  primeCRTFunction Q.toList (primeSet_list_prime Q hQ) (primeSet_list_coprime Q hQ)
    (fun p x => 1 + (1 / 16 : ℂ) * (centeredDensity (D p) x : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferFrequencyRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite range of a transferred frequency -/

namespace Ostmann

open scoped BigOperators Classical

theorem mem_transferFrequencyRange (V : ℕ) (s : ℤ) :
    s ∈ transferFrequencyRange V ↔ s.natAbs ≤ V := by
  simp only [transferFrequencyRange, Finset.mem_Icc]
  rw [← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast (Iff.rfl : s.natAbs ≤ V ↔ s.natAbs ≤ V)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedDirectedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next directed phase with support derived from the original ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def copiedDirectedPhase {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : ℂ := by
  letI := transferredPrimeFact L R U
  exact directedPrimePhase (transferredLabels L R U)
    (fun i => copiedSlotCharacter χH χY i (transferredLabels L R U i))
    (fun i => t (transferredLabels L R U i))
    (copiedSlotUnary (transferredLabels L R U) χH b νL νR νYL νYR v w s)
    (transferredGraph b) s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

theorem copyPathParity_sign (t : ℕ → Bool) (j : ℕ) :
    copyPathParity t j = 1 ∨ copyPathParity t j = -1 := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    rcases ih with h | h <;> cases ht : t j <;>
      simp [copyPathParity, ht, transferCopySign, h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalParityPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two equally sized final-parity classes of actual copy paths -/

namespace Ostmann

open scoped Classical

theorem copyPathParity_congr_prefix (t u : ℕ → Bool) (n : ℕ)
    (h : ∀ j < n, t j = u j) : copyPathParity t n = copyPathParity u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copyPathParity, h n (Nat.lt_succ_self _), ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem finalCopyParity_snoc {n : ℕ} (t : Fin n → Bool) (b : Bool) :
    finalCopyParity (Fin.snoc t b) = transferCopySign b * finalCopyParity t := by
  have hbefore : copyPathParity (finiteCopyPath (Fin.snoc t b)) n =
      copyPathParity (finiteCopyPath t) n := by
    apply copyPathParity_congr_prefix
    intro j hj
    simp only [finiteCopyPath, hj, Nat.lt_succ_of_lt hj, dite_true]
    exact @Fin.snoc_castSucc n (fun _ => Bool) b t ⟨j, hj⟩
  have hlast : finiteCopyPath (Fin.snoc t b) n = b := by
    simp only [finiteCopyPath, Nat.lt_succ_self, dite_true]
    exact @Fin.snoc_last n (fun _ => Bool) b t
  change transferCopySign (finiteCopyPath (Fin.snoc t b) n) *
      copyPathParity (finiteCopyPath (Fin.snoc t b)) n = _
  rw [hlast, hbefore]
  rfl

noncomputable instance finalParityReassignmentsFintype (n m : ℕ) :
    Fintype (FinalParityReassignments n m) := by
  classical
  unfold FinalParityReassignments
  exact @Pi.instFintype (Fin m)
    (fun _ => Equiv.Perm (ParityPaths n 1) × Equiv.Perm (ParityPaths n (-1)))
    inferInstance inferInstance (fun _ => inferInstance)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignmentInteraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting the actual small-anchor interaction between two reassignments -/

namespace Ostmann

def anchorCodeEntry {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool)
    (j : Fin n) (positive : Bool) : ℤ :=
  if positive then (finiteAnchorCode α t j).1 else (finiteAnchorCode α t j).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorGraphEvolution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor coefficients through their actual creation and later copies -/

namespace Ostmann

/-- The incoming anchor edge before normalization by the bulk parity. -/
def anchorIncoming {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool)
    (j : Fin n) (b : Bool) : ℤ :=
  finalCopyParity t * anchorCodeEntry α t j b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GraphCopySchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- A fresh anchor is retained until its reserved step, copied exactly once,
and then retained at every later step. -/
noncomputable def copyScheduleAnchor {I : Type*} :
    (n : ℕ) → ℕ → Bool → I → CopyScheduleVertex I n
  | 0, _, _, i => i
  | n + 1, j, b, i =>
      if j = n then Sum.inl (b, copyScheduleOutside n i)
      else Sum.inr (copyScheduleAnchor n j b i)

theorem copyScheduleAnchor_new {I : Type*} (n : ℕ) (b : Bool) (i : I) :
    copyScheduleAnchor (n + 1) n b i = Sum.inl (b, copyScheduleOutside n i) := by
  change (if n = n then (Sum.inl (b, copyScheduleOutside n i) :
    (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n)
    else Sum.inr (copyScheduleAnchor n n b i)) = _
  exact ite_eq_left rfl

theorem copyScheduleAnchor_old {I : Type*} (n j : ℕ) (b : Bool) (i : I) (hj : j ≠ n) :
    copyScheduleAnchor (n + 1) j b i = Sum.inr (copyScheduleAnchor n j b i) := by
  change (if j = n then (Sum.inl (b, copyScheduleOutside n i) :
    (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n)
    else Sum.inr (copyScheduleAnchor n j b i)) = _
  exact ite_eq_right hj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopyScheduleSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual H/Y/pivot partition of the copied-slot schedule -/

namespace Ostmann

/-- This is a literal equivalence, not a count of an oversized ambient space. -/
def copyScheduleSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} ≃
      (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n where
  toFun i := match i with
    | ⟨.inl (b, j), h⟩ => .inl (b, ⟨j, h⟩)
    | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
  invFun i := match i with
    | .inl (b, j) => ⟨.inl (b, j.val), j.property⟩
    | .inr j => ⟨.inr j.val, j.property⟩
  left_inv i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl p => rcases p with ⟨b, j⟩; rfl
    | inr j => rfl
  right_inv i := by
    cases i with
    | inl p => rcases p with ⟨b, j⟩; rfl
    | inr j => rfl

/-- A reserved anchor really remains in Y until its designated step. -/
theorem copyScheduleSurvives_reserved {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : n ≤ k) :
    CopyScheduleSurvives role n (copyScheduleOutside n i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copyScheduleOutside n i) ∧ _
    refine ⟨ih (by omega), ?_⟩
    rw [copyScheduleRole_outside, hi]
    simp [CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt, show n ≠ k by omega]

theorem copyScheduleRole_anchor {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : k < n) (b : Bool) :
    copyScheduleRole role n (copyScheduleAnchor n k b i) = .outside := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k = n
    · subst k
      have he : copyScheduleAnchor (n + 1) n b i = .inl (b, copyScheduleOutside n i) := copyScheduleAnchor_new n b i
      rw [he]
      change (copyScheduleRole role n (copyScheduleOutside n i)).afterCopy b = _
      rw [copyScheduleRole_outside, hi]
      rfl
    · have he : copyScheduleAnchor (n + 1) k b i = .inr (copyScheduleAnchor n k b i) := copyScheduleAnchor_old n k b i hk
      rw [he]
      exact ih (by omega)

/-- Both fresh-anchor clones survive and thereafter remain outside. -/
theorem copyScheduleSurvives_anchor {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : k < n) (b : Bool) :
    CopyScheduleSurvives role n (copyScheduleAnchor n k b i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k = n
    · subst k
      have he : copyScheduleAnchor (n + 1) n b i = .inl (b, copyScheduleOutside n i) := copyScheduleAnchor_new n b i
      rw [he]
      change CopyScheduleSurvives role n (copyScheduleOutside n i) ∧ _
      refine ⟨copyScheduleSurvives_reserved role i n hi n le_rfl, ?_⟩
      rw [copyScheduleRole_outside, hi]
      simp [CopyScheduleRole.copiedAt]
    · have he : copyScheduleAnchor (n + 1) k b i = .inr (copyScheduleAnchor n k b i) := copyScheduleAnchor_old n k b i hk
      rw [he]
      change CopyScheduleSurvives role n (copyScheduleAnchor n k b i) ∧ _
      refine ⟨ih (by omega), ?_⟩
      rw [copyScheduleRole_anchor role i k hi n (by omega)]
      exact ⟨rfl, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleWordSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving word slots are precisely the full binary copy paths -/

namespace Ostmann

theorem surviving_word_is_path {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (hw : copyScheduleRole role n v = .word) :
    ∃ (t : Fin n → Bool) (i : I), role i = .word ∧ v = copySchedulePath n t i := by
  induction n with
  | zero => exact ⟨fun j => Fin.elim0 j, v, hw, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change CopyScheduleSurvives role n v ∧ _ at hv
      change (copyScheduleRole role n v).afterCopy b = .word at hw
      have hrole : copyScheduleRole role n v = .word := by
        cases hr : copyScheduleRole role n v <;>
          cases b <;> simp_all [CopyScheduleRole.afterCopy]
      obtain ⟨t, i, hi, rfl⟩ := ih v hv.1 hrole
      exact ⟨Fin.snoc t b, i, hi, (copySchedulePath_snoc t b i).symm⟩
    | inr v =>
      change CopyScheduleSurvives role n v ∧ _ ∧ _ at hv
      change copyScheduleRole role n v = .word at hw
      have hc := hv.2.1
      rw [hw] at hc
      cases hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the graph update to the actual H/Y partition -/

namespace Ostmann

/-- The input graph retains only the total pivot and the actual H/Y slots. -/
noncomputable def scheduledRetainedGraph {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) :
    Option (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      Option (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℤ :=
  let old : Option (CopyScheduleH role n ⊕ CopyScheduleY role n) → CopyScheduleVertex I n := fun i =>
    match i with
    | none => copySchedulePositive n (pivot n)
    | some (.inl h) => h.val
    | some (.inr y) => y.val
  fun i j => copyScheduleGraph g pivot n (old i) (old j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaMainTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem hasDerivAt_thetaMainTerm (φ χ β : ℝ) (hβ : β ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaMainTerm φ χ β) (thetaMainDensity φ χ β x) x := by
  have h := ((hasDerivAt_id x).sub
    (((Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.ne')).const_mul χ).div_const β)).div_const φ
  change HasDerivAt (fun y : ℝ => (y - χ * y ^ β / β) / φ)
    ((1 - χ * (β * x ^ (β - 1)) / β) / φ) x at h
  change HasDerivAt (fun y : ℝ => (y - χ * y ^ β / β) / φ)
    ((1 - χ * x ^ (β - 1)) / φ) x
  have he : (1 - χ * (β * x ^ (β - 1)) / β) / φ =
      (1 - χ * x ^ (β - 1)) / φ := by
    congr 1
    field_simp
  exact he ▸ h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPolynomialWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

noncomputable def smoothPolynomialWeight {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (x : ℝ) : ℂ := ∏ i, (F i).value x

noncomputable def smoothPolynomialBudget {n : ℕ} (F : Fin n → ClippedPolynomialFactor) : ℝ :=
  ∏ i, (2 * (F i).bound + (F i).lip * ((F i).hi - (F i).lo))

theorem smoothPolynomialWeight_norm {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    ‖smoothPolynomialWeight F x‖ ≤ smoothPolynomialBudget F := by
  rw [smoothPolynomialWeight, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  apply ((F i).norm_value x).trans
  have h := mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi)
  linarith [(F i).bound_nonneg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SupportedPolynomialCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted character bound with its actual polynomial support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def historyWeightRootCuts {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : Finset ℝ :=
  polynomialRootCuts (Sum.elim (fun i => (F i).polynomial.derivative) H)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def polynomialAmplitude {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) : ℂ :=
  (if keep (polynomialSupportCode H x) = true then 1 else 0) * smoothPolynomialWeight F x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialLineFlags
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact cleared polynomial flags for an internal line system -/

namespace Ostmann

noncomputable section

open scoped Classical

/-- The distinguished row supplies the coefficient tests; its minors with
all other rows supply the rank tests. -/
def lineTestPolynomials {σ J : Type*} (L : J → PolynomialGiantLine σ) (i : J) :
    Bool ⊕ J → MvPolynomial σ ℤ
  | .inl false => (L i).a
  | .inl true => (L i).b
  | .inr j => (L i).minor (L j)

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryResidueGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the residue gate for cleared integer history tests -/

namespace Ostmann

open scoped Classical

noncomputable def clearedHistoryResidueGate {σ I : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ)
    (a : σ → ℤ) (i : σ) (M : ℕ) [NeZero M] (z : ZMod M) : ℂ :=
  if ∀ j, smallDivisionTest
    (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i (z.val : ℤ)) (P j)) (d j) (s j)
    then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Means on the actual fibers of a finite partition -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteCellMean (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ) (h : ℕ) : ℝ :=
  (finiteCellMass P label μ h)⁻¹ * ∑ p ∈ P.filter (fun p => label p = h), μ p * f p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ComplexCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex averages on the actual prime cells -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def complexCellMean (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  (finiteCellMass P label μ h : ℂ)⁻¹ *
    ∑ p ∈ P.filter (fun p => label p = h), (μ p : ℂ) * F p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exceptional character for every modulus in a row

Only zeros in Page's common region are retained. Local exceptional zeros
outside that region will be bounded as an error, rather than identified
with a character belonging to a different modulus.
-/

namespace Ostmann

open Classical

noncomputable def pageAtModulus (q : ℕ) (z : Option PrimitiveRealZero) :
    Option PrimitiveRealZero :=
  z.bind fun e => if e.modulus ∣ q then some e else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GuardedHistoryCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided cancellation retaining all polynomial history tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def guardedHistoryAmplitude {σ I : Type*} [Fintype I] {n t : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (x : ℤ) : ℂ :=
  (if ∀ j, smallDivisionTest
    (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a i x) (N j)) (d j) (s j) then 1 else 0) *
    polynomialAmplitude F H keep (x : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing internal frequencies from the root downwards -/

namespace Ostmann

open scoped BigOperators

instance frequencyTreeFintype (A : Type) [Fintype A] (n : ℕ) :
    Fintype (FrequencyTree A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype A)
  | succ n ih => exact @instFintypeProd _ _ _ (@instFintypeProd _ _ ih ih)

noncomputable def frequencyTreeWeight {A : Type} (K : A → A → A → ℝ) (W : A → ℝ) :
    (n : ℕ) → FrequencyTree A n → ℝ
  | 0, x => W x
  | n + 1, x => K x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) *
      frequencyTreeWeight K W n x.2.1 * frequencyTreeWeight K W n x.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

def validTransferredPivot (T : Finset ℕ) (N s : ℤ) : Prop :=
  s ≠ 0 ∧ s ∣ N ∧ 0 < N / s ∧ reconstructedPivot N s ∈ T

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

/-- At a leaf, the state contains the original word whose Fourier factor
is evaluated. Internal states are never queried by the leaf list. -/
noncomputable def wordTransferLeafValue {σ : Type*} : WordTransferState σ → ℕ
  | ⟨0, .leaf word, x⟩ => (word.map x).prod
  | ⟨_ + 1, _, _⟩ => 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedWordLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal frequency and polynomial of every reconstructed Fourier leaf -/

namespace Ostmann

open scoped Classical

/-- Preserve the actual leaf frequency as well as its sign and word value. -/
noncomputable def evaluatedTransferLeaf {σ : Type*}
    (z : (WordTransferState σ × ℤ) × Bool) : Bool × ℤ × ℚ :=
  (z.2, z.1.2, (wordTransferLeafValue z.1.1 : ℚ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferPeriods
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common residue period derived from the actual branching frequencies -/

namespace Ostmann

open scoped Classical

/-- Only internal frequencies enter the denominators of reconstructed words. -/
def internalFrequencyList : (n : ℕ) → FrequencyTree ℤ n → List ℤ
  | 0, _ => []
  | n + 1, t => t.1 :: (internalFrequencyList n t.2.1 ++ internalFrequencyList n t.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopyScheduleUnary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unary factors on the copied schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def copyScheduleUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ) :
    (n : ℕ) → FrequencyTree ℤ n → CopyScheduleVertex I n → ℕ → ℂ
  | 0, t, i, p => initial i t p
  | n + 1, t, .inl (true, i), p =>
    copyScheduleUnary χ g pivot initial n t.2.1 i p *
      χ (copyScheduleOrigin n i) p (((frequencyRoot n t.2.1 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        copyScheduleGraph g pivot n i (copySchedulePositive n (pivot n))
  | n + 1, t, .inl (false, i), p =>
    conj (copyScheduleUnary χ g pivot initial n t.2.2 i p) *
      χ (copyScheduleOrigin n i) p (((-frequencyRoot n t.2.2 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        (-copyScheduleGraph g pivot n i (copySchedulePositive n (pivot n)))
  | n + 1, t, .inr i, p =>
    copyScheduleUnary χ g pivot initial n t.2.1 i p *
      conj (copyScheduleUnary χ g pivot initial n t.2.2 i p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPrimePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The directed phase on the actual surviving prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledPrimePhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (p : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ)
    [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p) : ℂ :=
  directedPrimePhase p (fun i => χ (copyScheduleOrigin n i.val) (p i))
    (fun i => center (p i)) (fun i => copyScheduleUnary χ g pivot initial n t i.val (p i))
    (fun i j => copyScheduleGraph g pivot n i.val j.val) (frequencyRoot n t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduledTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The atom schedule expanded into its actual prime constituents -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def expandedHWord {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ) : List σ :=
  (Finset.univ.toList : List (CopyScheduleH role n)).flatMap fun i =>
    current ⟨.inl (b, i.val), i.property⟩

/-- Actual atoms may have several prime constituents. An erased pivot is
replaced by its single reconstructed total; all other atoms retain their lists. -/
noncomputable def expandedScheduledTemplate {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → List Bool → (CopyScheduleAtoms role n → List σ) → WordTransferTemplate σ n
  | 0, _, current => .leaf ((Finset.univ.toList : List (CopyScheduleAtoms role 0)).flatMap current)
  | n + 1, path, current =>
      .node ⟨address n path, expandedHWord role n true current, expandedHWord role n false current,
        childBound n, pivotBound n⟩
        (expandedScheduledTemplate role address childBound pivotBound n (true :: path)
          (reverseCopyLabelMap role n true [address n path] current))
        (expandedScheduledTemplate role address childBound pivotBound n (false :: path)
          (reverseCopyLabelMap role n false [address n path] current))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduleConstituentWord {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    List (SurvivingConstituent role size n) :=
  List.ofFn (fun k : Fin (size (copyScheduleOrigin n v.val)) =>
    (survivingConstituentEquiv role size n).symm ⟨v, k⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

def expandedPivotAddress (α : Type*) (depth j : ℕ) (path : List Bool) : ExpandedScheduledVariable α depth :=
  .inr (⟨j % (depth + 1), Nat.mod_lt _ (by omega)⟩, fun i => path.getD i.val false)

noncomputable def expandedRootTemplate {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) : WordTransferTemplate (ExpandedScheduledVariable α depth) depth :=
  expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound depth []
    (fun i => (words i).map Sum.inl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleAtomSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal reverse transfer system on current atom values -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def expandedAtomValues {I σ : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) : CopyScheduleAtoms role n → ℕ :=
  fun i => ((current i).map x).prod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original atom weight is the concrete prime-word coefficient -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def scheduleAtomTotal {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨n, x⟩ => ∏ i : CopyScheduleAtoms role n, x i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TwoVertexReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isolating two selected actual vertices without changing a graph product -/

namespace Ostmann

open scoped Classical

noncomputable def twoVertexEquiv {V : Type*} (a b : V) (hab : a ≠ b) :
    (Bool ⊕ OtherVertices a b) ≃ V where
  toFun v := match v with
    | .inl true => a
    | .inl false => b
    | .inr v => v.val
  invFun v := if ha : v = a then .inl true else
    if hb : v = b then .inl false else .inr ⟨v, ha, hb⟩
  left_inv v := by
    cases v with
    | inl t => cases t <;> simp [hab.symm]
    | inr v => simp [v.property.1, v.property.2]
  right_inv v := by
    dsimp only
    split_ifs with ha hb
    · exact ha.symm
    · exact hb.symm
    · rfl

@[simp] theorem twoVertexEquiv_short {V : Type*} (a b : V) (hab : a ≠ b) :
    twoVertexEquiv a b hab (.inl true) = a := rfl

@[simp] theorem twoVertexEquiv_long {V : Type*} (a b : V) (hab : a ≠ b) :
    twoVertexEquiv a b hab (.inl false) = b := rfl

@[simp] theorem twoVertexEquiv_other {V : Type*} (a b : V) (hab : a ≠ b)
    (v : OtherVertices a b) : twoVertexEquiv a b hab (.inr v) = v := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TwoCoordinatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the selected pair inside the unchanged original product prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def twoCoordinateAssignment {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) : V → A :=
  fun v => Sum.elim (fun t => if t then q else p) outside ((twoVertexEquiv a b hab).symm v)

@[simp] theorem twoCoordinateAssignment_short {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) :
    twoCoordinateAssignment a b hab outside q p a = q := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inl true))) = q
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem twoCoordinateAssignment_long {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) :
    twoCoordinateAssignment a b hab outside q p b = p := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inl false))) = p
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem twoCoordinateAssignment_other {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) (v : OtherVertices a b) :
    twoCoordinateAssignment a b hab outside q p v = outside v := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inr v))) = outside v
  rw [Equiv.symm_apply_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top atom support as explicit original-prime tests -/

namespace Ostmann

open scoped BigOperators Classical

/-- Every prime constituent of one atom is compared to every constituent of
each different atom. Repeated coordinates are deliberately retained. -/
noncomputable def atomPairChecks {I V : Type*} [Fintype I]
    (words : I → List V) : List (TopPrimeCondition V) :=
  Finset.univ.toList.flatMap fun i => Finset.univ.toList.flatMap fun j =>
    if i = j then [] else
      (words i).flatMap fun v => (words j).map (TopPrimeCondition.distinct v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime constituents of each retained Y atom -/

namespace Ostmann

open scoped Classical

def expandedOriginalWord {V : Type*} {depth : ℕ} :
    List (ExpandedScheduledVariable V depth) → List V
  | [] => []
  | .inl v :: w => v :: expandedOriginalWord w
  | .inr _ :: w => expandedOriginalWord w

def expandedYPrimeWord {I V : Type*} (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (i : CopyScheduleY role n) : List V :=
  expandedOriginalWord (current ⟨.inr i.val, i.property⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

noncomputable def expandedScheduleRanges {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → List Bool → (CopyScheduleAtoms role n → List σ) → WordRangeDecoration σ n
  | 0, _, current => .leaf ((ranges 0).map fun r => r.toWord current)
  | n + 1, path, current => .node ((ranges (n + 1)).map fun r => r.toWord current)
      (expandedScheduleRanges role address ranges n (true :: path)
        (reverseCopyLabelMap role n true [address n path] current))
      (expandedScheduleRanges role address ranges n (false :: path)
        (reverseCopyLabelMap role n false [address n path] current))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedPrimeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Y-atom coprimalities are a finite list of original-prime checks -/

namespace Ostmann

open scoped Classical

noncomputable def expandedYPrimeCoordinates {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth)) : List V :=
  (Finset.univ.toList : List (CopyScheduleY role n)).flatMap
    (expandedYPrimeWord role depth n current)

noncomputable def expandedSchedulePrimes {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) :
    (n : ℕ) → List Bool →
      (CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth)) → WordPrimeDecoration V n
  | 0, _, _ => .leaf
  | n + 1, path, current => .node (expandedYPrimeCoordinates role depth n current)
      (expandedSchedulePrimes role depth n (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress V depth n path] current))
      (expandedSchedulePrimes role depth n (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress V depth n path] current))

noncomputable def scheduleAtomCoprimalitiesValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, _, _ => True
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ i : CopyScheduleY role n, (x ⟨.inr i.val, i.property⟩).Coprime P) ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedScheduleCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original grouped-atom amplitudes in the independent prime variables -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

def expandedPrimeNatValues {V : Type*} (n : ℕ) (x : V → ℕ) : ExpandedScheduledVariable V n → ℕ
  | .inl v => x v
  | .inr _ => 1

noncomputable def groupedScheduleFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
    (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
    (fun _ _ _ _ => 1) n ⟨n, fun i => ((words i).map x).prod⟩ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedRangedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original all-stage ranges in the concrete Fourier coefficient -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def expandedRootRanges {I V : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) :
    WordRangeDecoration (ExpandedScheduledVariable V n) n :=
  expandedScheduleRanges role (expandedPivotAddress V n) ranges n [] (fun i => (words i).map Sum.inl)

noncomputable def groupedRangedFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomRangesValid role childBound pivotBound ranges n (fun i => ((words i).map x).prod) t
    then 1 else 0) * groupedScheduleFourierWeight role n words childBound pivotBound ψ X lo hi t x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedUnitCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original all-atom frequency-units in the ranged Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def groupedUnitRangedFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedCoprimeCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reconstructed Y-coprimalities in the original grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def groupedCoprimeFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomCoprimalitiesValid role childBound pivotBound n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original complete coprimality support in the grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def groupedFullCoprimeFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomFullCoprimeValid role childBound pivotBound n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

noncomputable def fullAtomRootGuard {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (n : ℕ) (x : CopyScheduleAtoms role (n + 1) → ℕ) (P : ℕ) (s : ℤ) : Prop :=
  Pairwise (fun i j => (x i).Coprime (x j)) ∧ (∀ i, P.Coprime (x i)) ∧
    (∀ i, (x i).Coprime s.natAbs) ∧ (∀ r ∈ ranges (n + 1), r.Holds x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopiedPriorFubini
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The copied H priors and the single retained Y prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledCopiedAssignment {I A : Type*}
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} → A :=
  fun i => match copyScheduleSurvivorEquiv role n i with
    | .inl (true, h) => l h
    | .inl (false, h) => r h
    | .inr y => u y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRolePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same original marginal follows every surviving copy -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledRolePrior {I A : Type*} (role : I → CopyScheduleRole)
    (μ : I → A → ℝ) (n : ℕ)
    (i : {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}) (a : A) : ℝ :=
  μ (copyScheduleOrigin n i.val) a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructedPhaseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The forced-pivot off-diagonal is the actual next directed amplitude -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def copiedWeightedAmplitude {A H Y : Type*} [Fintype A] [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ a',
    let N := v a * (∏ h, L a' h) - v a' * (∏ h, L a h)
    let M := reconstructedPivot N s
    if validTransferredPivot T N s then
      W M a * conj (W M a') *
        copiedDirectedPhase (L a) (L a') U t χH χY b (ν a) (ν a') (νY a) (νY a') (v a) (v a') s
    else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalDirectedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An arithmetic transfer of the actual supported directed amplitude -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedDirectedAmplitude {A H Y Z : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype Z]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (Q : Fin n → Finset ℕ) (S : Finset (Fin n → P))
    (χP : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (ε : Fin n → ℤ)
    (L : A → H → ℕ) (U : Z → Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : Z → A → H → ℂ) (νY : Z → A → Y → ℂ) (v : A → ℤ)
    (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) : ℂ :=
  ∑ z, (μ z : ℂ) * ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
    ∑ a, primeTupleResidueRow P hP χP κ t (∏ y, U z y) ε x
      (primeTuplePivotKey P hP x (∏ h, L a h) (v a)) *
      retainedWeightedCoefficient L (U z) t χH χY b (ν z) (νY z) v (W z) (∏ i, (x i : ℕ)) a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSamplePhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual scheduled phase on a finite prime sample -/

namespace Ostmann

open scoped Classical

noncomputable def scheduledSamplePhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : CopyScheduleAtoms role n → P)
    (center : ∀ p : ℕ, ZMod p) : ℂ := by
  letI : ∀ i, Fact (q i : ℕ).Prime := fun i => ⟨hP _ (q i).property⟩
  exact scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (fun i => (q i : ℕ)) center

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentOriginalAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual original-prior amplitude in arithmetic-transfer coordinates -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentCurrentWeight {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ :=
  ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentBlockProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact products of all constituents in an H or Y block -/

namespace Ostmann

open scoped BigOperators Classical

theorem blockForget_injective {I : Type*} (size : I → ℕ) (n : ℕ)
    (P : CopyScheduleVertex I n → Prop) :
    Function.Injective (fun z : Σ v : {v // P v}, Fin (size (copyScheduleOrigin n v.val)) =>
      (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))) := by
  rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨b, hb⟩, j⟩ he
  change (⟨a, i⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))) = ⟨b, j⟩ at he
  cases he
  rfl

noncomputable def constituentHEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    (Σ v : CopyScheduleH role n, Fin (size (copyScheduleOrigin n v.val))) ≃
      CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun z => constituentH role size n z.1 z.2) (by
    constructor
    · intro a b he
      apply blockForget_injective size n
      have hs : (survivingConstituentEquiv role size n).symm ⟨⟨a.1.val, a.1.property.1⟩, a.2⟩ =
          (survivingConstituentEquiv role size n).symm ⟨⟨b.1.val, b.1.property.1⟩, b.2⟩ :=
        Subtype.ext (congrArg (fun q : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n => q.val) he)
      exact congrArg (fun z : Σ v : CopyScheduleAtoms role n, Fin (size (copyScheduleOrigin n v.val)) =>
        (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))))
        ((survivingConstituentEquiv role size n).symm.injective hs)
    · intro q
      let z := survivingConstituentEquiv role size n ⟨q.val, q.property.1⟩
      have hr : copyScheduleRole role n z.1.val =
          copyScheduleRole (fun i : Σ a, Fin (size a) => role i.1) n q.val := by
        change copyScheduleRole role n (copyConstituentEquiv size n q.val).1 = _
        rw [copyConstituentEquiv_atom]
        exact copyScheduleRole_map Sigma.fst role n q.val
      let v : CopyScheduleH role n := ⟨z.1.val, z.1.property, hr.symm ▸ q.property.2⟩
      refine ⟨⟨v, z.2⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun q : SurvivingConstituent role size n => q.val)
        ((survivingConstituentEquiv role size n).symm_apply_apply
        ⟨q.val, q.property.1⟩))

noncomputable def constituentYEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    (Σ v : CopyScheduleY role n, Fin (size (copyScheduleOrigin n v.val))) ≃
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun z => constituentY role size n z.1 z.2) (by
    constructor
    · intro a b he
      apply blockForget_injective size n
      have hs : (survivingConstituentEquiv role size n).symm ⟨⟨a.1.val, a.1.property.1⟩, a.2⟩ =
          (survivingConstituentEquiv role size n).symm ⟨⟨b.1.val, b.1.property.1⟩, b.2⟩ :=
        Subtype.ext (congrArg (fun q : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n => q.val) he)
      exact congrArg (fun z : Σ v : CopyScheduleAtoms role n, Fin (size (copyScheduleOrigin n v.val)) =>
        (⟨z.1.val, z.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))))
        ((survivingConstituentEquiv role size n).symm.injective hs)
    · intro q
      let z := survivingConstituentEquiv role size n ⟨q.val, q.property.1⟩
      have hr : copyScheduleRole role n z.1.val =
          copyScheduleRole (fun i : Σ a, Fin (size a) => role i.1) n q.val := by
        change copyScheduleRole role n (copyConstituentEquiv size n q.val).1 = _
        rw [copyConstituentEquiv_atom]
        exact copyScheduleRole_map Sigma.fst role n q.val
      let v : CopyScheduleY role n := ⟨z.1.val, z.1.property, hr.symm ▸ q.property.2⟩
      refine ⟨⟨v, z.2⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun q : SurvivingConstituent role size n => q.val)
        ((survivingConstituentEquiv role size n).symm_apply_apply
        ⟨q.val, q.property.1⟩))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original constituent support in the arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

/-- Pairwise prime support is retained inside each grouped atom as well as
between atoms. The reconstructed pivot remains a single integer parameter. -/
noncomputable def constituentTransferWeight {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ :=
  if Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) then
    constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product of the two arithmetic branch coefficients -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def copiedConstituentAtomValues {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    CopyScheduleAtoms role (n + 1) → ℕ :=
  scheduledCopiedAssignment role n
    (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
    (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
    (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AtomIntervalRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete inherited intervals for every original atom role -/

namespace Ostmann

open scoped Classical

noncomputable def atomInterval {I : Type*} (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) : ScheduleAtomRange role n where
  atoms := [v]
  lower := lo (copyScheduleOrigin n v.val)
  upper := hi (copyScheduleOrigin n v.val)

noncomputable def atomIntervalRanges {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) : List (ScheduleAtomRange role n) :=
  Finset.univ.toList.map (atomInterval role lo hi n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TreeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- The successive bounds are `E`, `2 E²`, `8 E⁴`, and so on. -/
def binaryMomentBound (E : ℝ) : ℕ → ℝ
  | 0 => E
  | n + 1 => 2 * binaryMomentBound E n ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

instance treeLeafIndexDecidableEq (n : ℕ) : DecidableEq (TreeLeafIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact @instDecidableEqSum _ _ ih ih

def bottomQuartet : (n : ℕ) → TreeLeafIndex (n + 2) → TreeLeafIndex n
  | 0, _ => ()
  | n + 1, .inl i => .inl (bottomQuartet n i)
  | n + 1, .inr i => .inr (bottomQuartet n i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the constant Fourier mode

Centering a finite-field function removes exactly its zero frequency.
The energy splits into the centered energy and the squared mean.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def fieldMean {p : ℕ} [NeZero p] (F : ZMod p → ℂ) : ℂ :=
  additiveFourier F 0

noncomputable def fieldCentered {p : ℕ} [NeZero p] (F : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  F x - fieldMean F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSamePairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two moving leaves in the same bottom pair of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def samePairLeftLeaves {U : Type*} [CommGroup U] (P a b r : U) :
    TreeLeafTuple U 2 := ((P / (a * r), r), (a / b, b))

noncomputable def samePairRightLeaves {U : Type*} [CommGroup U] (P a b r : U) :
    TreeLeafTuple U 2 := ((a⁻¹ / b, b), (P * a / r, r))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCrossBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient bound for every cross-pair orientation of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def crossQuartetLeaves {U : Type*} [CommGroup U]
    (left right : Bool) (P a b r : U) : TreeLeafTuple U 2 :=
  ((crossLeftLeaves left a r : U × U), (crossRightLeaves right P a b r : U × U))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossQuartetFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-fiber coordinates for the cross-pair coefficient bounds -/

namespace Ostmann

open scoped BigOperators

local instance zeroTupleCommGroup {U : Type*} [CommGroup U] :
    CommGroup (TreeLeafTuple U 0) := inferInstanceAs (CommGroup U)

def quartetOrientFiberEquiv {U : Type*} [CommGroup U] (left right : Bool) (P : U) :
    TreeLeafFiber U 2 P ≃ TreeLeafFiber U 2 P where
  toFun m := ⟨quartetOrient left right m.1, by
    change (pairOrient left m.1.1).1 * (pairOrient left m.1.1).2 *
      ((pairOrient right m.1.2).1 * (pairOrient right m.1.2).2) = P
    rw [pairOrient_product, pairOrient_product]
    exact m.property⟩
  invFun m := ⟨quartetOrient left right m.1, by
    change (pairOrient left m.1.1).1 * (pairOrient left m.1.1).2 *
      ((pairOrient right m.1.2).1 * (pairOrient right m.1.2).2) = P
    rw [pairOrient_product, pairOrient_product]
    exact m.property⟩
  left_inv m := by
    apply Subtype.ext
    cases left <;> cases right <;> rfl
  right_inv m := by
    apply Subtype.ext
    cases left <;> cases right <;> rfl

/-- The held coordinates and the inverse first free coordinate parametrize
one quartet product fiber without changing its uniform measure. -/
noncomputable def friendlyQuartetFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := (m.1.1.2, m.1.2.2, m.1.1.1⁻¹)
  invFun x := ⟨((x.2.2⁻¹, x.1), (P * x.2.2 / (x.1 * x.2.1), x.2.1)),
    quartet_friendly_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (inv_inv _) rfl
    · apply Prod.ext
      · exact fourth_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property
      · rfl
  right_inv x := by
    change (x.1, x.2.1, (x.2.2⁻¹)⁻¹) = x
    simp only [inv_inv]

noncomputable def crossQuartetFiberEquiv {U : Type*} [CommGroup U]
    (left right : Bool) (P : U) : TreeLeafFiber U 2 P ≃ U × (U × U) :=
  (quartetOrientFiberEquiv left right P).trans (friendlyQuartetFiberEquiv P)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SamePairFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-fiber laws for the two same-pair parametrizations -/

namespace Ostmann

open scoped BigOperators

local instance samePairZeroTupleCommGroup {U : Type*} [CommGroup U] :
    CommGroup (TreeLeafTuple U 0) := inferInstanceAs (CommGroup U)

noncomputable def samePairLeftFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := ((m.1.2.1 : U) * m.1.2.2, m.1.2.2, m.1.1.2)
  invFun x := ⟨samePairLeftLeaves P x.1 x.2.1 x.2.2,
    samePair_total_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (first_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property) rfl
    · exact Prod.ext (mul_div_cancel_right _ _) rfl
  right_inv x := by
    change ((x.1 / x.2.1) * x.2.1, x.2.1, x.2.2) = x
    simp only [div_mul_cancel]

noncomputable def samePairRightFiberEquiv {U : Type*} [CommGroup U] (P : U) :
    TreeLeafFiber U 2 P ≃ U × (U × U) where
  toFun m := (((m.1.1.1 : U) * m.1.1.2)⁻¹, m.1.1.2, m.1.2.2)
  invFun x := ⟨samePairRightLeaves P x.1 x.2.1 x.2.2,
    samePair_right_total_product P x.1 x.2.1 x.2.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact undo_pair_product m.1.1.1 m.1.1.2
      · rfl
    · exact Prod.ext (third_of_product m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 P m.property) rfl
  right_inv x := by
    change (((x.1⁻¹ / x.2.1) * x.2.1)⁻¹, x.2.1, x.2.2) = x
    simp only [div_mul_cancel, inv_inv]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent product fibers at the bottom quartet level -/

namespace Ostmann

open scoped BigOperators

/-- Given the bottom quartet products, their interiors are independent
uniform fibers; the maps do not depend on any tree parameters. -/
def quartetProductFiberEquiv {U : Type*} [CommGroup U] (n : ℕ) (P : TreeLeafIndex n → U) :
    QuartetProductFiber U n P ≃ ((i : TreeLeafIndex n) → TreeLeafFiber U 2 (P i)) where
  toFun m i := ⟨quartetBlockEquiv U n m.1 i, congrFun m.property i⟩
  invFun m := ⟨(quartetBlockEquiv U n).symm (fun i => (m i).1), by
    funext i
    change treeLeafProduct 2 (quartetBlockEquiv U n
      ((quartetBlockEquiv U n).symm (fun i => (m i).1)) i) = P i
    rw [Equiv.apply_symm_apply]
    exact (m i).property⟩
  left_inv m := by
    apply Subtype.ext
    exact (quartetBlockEquiv U n).symm_apply_apply m.1
  right_inv m := by
    funext i
    apply Subtype.ext
    exact congrFun ((quartetBlockEquiv U n).apply_symm_apply (fun i => (m i).1)) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetIndexCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf coordinates within a labeled bottom quartet -/

namespace Ostmann

open scoped BigOperators

def quartetLeafIndex : (n : ℕ) → TreeLeafIndex n → TreeLeafIndex 2 → TreeLeafIndex (n + 2)
  | 0, _, j => j
  | n + 1, .inl q, j => .inl (quartetLeafIndex n q j)
  | n + 1, .inr q, j => .inr (quartetLeafIndex n q j)

def quartetLeafCoordinates : (n : ℕ) → TreeLeafIndex (n + 2) → TreeLeafIndex n × TreeLeafIndex 2
  | 0, j => ((), j)
  | n + 1, .inl j => let q := quartetLeafCoordinates n j; (.inl q.1, q.2)
  | n + 1, .inr j => let q := quartetLeafCoordinates n j; (.inr q.1, q.2)

theorem quartetLeafCoordinates_index (n : ℕ) (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    quartetLeafCoordinates n (quartetLeafIndex n q j) = (q, j) := by
  induction n with
  | zero => cases q; rfl
  | succ n ih => cases q <;> simp only [quartetLeafIndex, quartetLeafCoordinates, ih]

theorem quartetLeafCoordinates_fst (n : ℕ) (j : TreeLeafIndex (n + 2)) :
    (quartetLeafCoordinates n j).1 = bottomQuartet n j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact congrArg Sum.inl (ih j)
    | inr j => exact congrArg Sum.inr (ih j)

theorem bottomQuartet_leafIndex (n : ℕ) (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    bottomQuartet n (quartetLeafIndex n q j) = q := by
  rw [← quartetLeafCoordinates_fst, quartetLeafCoordinates_index]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferConjugations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual transfer has opposite conjugations in every bottom sibling pair -/

namespace Ostmann

/-- `true` means complex conjugation, as in `rationalTreeAmplitude`. -/
def transferConjugations : (n : ℕ) → Bool → TreeLeafTuple Bool n
  | 0, b => b
  | n + 1, b => (transferConjugations n b, transferConjugations n (!b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

def multiplySmallLeaves : (n : ℕ) →
    TreeLeafTuple ℕ n → TreeLeafTuple ℕ n → TreeLeafTuple ℕ n
  | 0, x, y => (show ℕ from x) * (show ℕ from y)
  | n + 1, x, y => (multiplySmallLeaves n x.1 y.1, multiplySmallLeaves n x.2 y.2)

theorem multiplySmallLeaves_product (n : ℕ) (x y : TreeLeafTuple ℕ n) :
    treeLeafProduct n (multiplySmallLeaves n x y) = treeLeafProduct n x * treeLeafProduct n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [multiplySmallLeaves, treeLeafProduct, ih]
    ring

/-- `small` contains only the fixed regular factors at the top of this history.
Bulk values and the two moving giants do not occur in this constructor. -/
def buildMovingGiantTree : (n : ℕ) → (t : FrequencyTree ℤ n) →
    (small : TreeLeafTuple ℕ n) → MovingGiantSamples n →
      MovingGiantTree n (treeLeafProduct n small)
  | 0, t, small, .leaf => .leaf (frequencyRoot 0 t) (treeLeafProduct 0 small)
  | n + 1, t, small, .node samples left right =>
      let u := compensationLeafProducts n samples
      let L := buildMovingGiantTree n t.2.1 (multiplySmallLeaves n u small.1) left
      let R := buildMovingGiantTree n t.2.2 (multiplySmallLeaves n u small.2) right
      .node t.1 (treeLeafProduct n small.1) (treeLeafProduct n small.2) (treeLeafProduct n u)
        (L.castConstant (multiplySmallLeaves_product n u small.1))
        (R.castConstant (multiplySmallLeaves_product n u small.2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cleared line bounds for the source-ordered moving giant histories -/

namespace Ostmann

noncomputable def movingPolynomialAncestors {σ : Type*} :
    List (PolynomialReversal σ) → PolynomialGiantRows σ
  | [] => PolynomialGiantRows.identity
  | s :: steps => (movingPolynomialAncestors steps).movingReverse s.left s.v s.w s.u

noncomputable def movingHistoryLine {σ : Type*} (steps : List (PolynomialReversal σ))
    (v w : MvPolynomial σ ℤ) : PolynomialGiantLine σ :=
  (movingPolynomialAncestors steps).numeratorLine v w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous arithmetic replacement for concrete moving-giant slots -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotLine {σ : Type*} (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) : PolynomialGiantLine σ :=
  movingHistoryLine (path.map MovingSlotReversal.polynomial)
    current.polynomial.v current.polynomial.w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labelled four-slot samples and the concrete occurrence paths -/

namespace Ostmann
open scoped Classical

def appendMovingSlotLeaves {σ : Type*} : (n : ℕ) →
    TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n
  | 0, x, y => (show List σ from x) ++ (show List σ from y)
  | n + 1, x, y => (appendMovingSlotLeaves n x.1 y.1, appendMovingSlotLeaves n x.2 y.2)

theorem flattenMovingSlots_append_bound {σ : Type*} (tier : σ → ℕ) (r n : ℕ)
    (x y : TreeLeafTuple (List σ) n)
    (hx : ∀ i ∈ flattenMovingSlots n x, r ≤ tier i)
    (hy : ∀ i ∈ flattenMovingSlots n y, r ≤ tier i) :
    ∀ i ∈ flattenMovingSlots n (appendMovingSlotLeaves n x y), r ≤ tier i := by
  induction n with
  | zero =>
    intro i hi
    exact (List.mem_append.mp hi).elim (hx i) (hy i)
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ih x.1 y.1 (fun i h => hx i (List.mem_append_left _ h))
        (fun i h => hy i (List.mem_append_left _ h)) i hi
    · exact ih x.2 y.2 (fun i h => hx i (List.mem_append_right _ h))
        (fun i h => hy i (List.mem_append_right _ h)) i hi

/-- This carries the source's compensation product into both child regular
lists while retaining the per-leaf distribution of the four samples. -/
def buildMovingSlotData {σ : Type*} : (n : ℕ) → FrequencyTree ℤ n →
    TreeLeafTuple (List σ) n → TreeLeafTuple (List σ) n →
    MovingSampleSlots σ n → MovingSlotData σ n
  | 0, t, small, bulk, .leaf =>
      .leaf (frequencyRoot 0 t) (flattenMovingSlots 0 small ++ flattenMovingSlots 0 bulk)
  | n + 1, t, small, bulk, .node samples left right =>
      let u := movingCompensationSlots n samples
      .node t.1
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
        (flattenMovingSlots n u)
        (buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left)
        (buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right)

theorem buildMovingSlotData_levels {σ : Type*} (tier : σ → ℕ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tier i)
    (hsamples : samples.Levels tier) :
    (buildMovingSlotData n t small bulk samples).Levels tier := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have hsmallL : ∀ i ∈ flattenMovingSlots n small.1, n + 1 ≤ tier i :=
      fun i hi => hsmall i (List.mem_append_left _ hi)
    have hsmallR : ∀ i ∈ flattenMovingSlots n small.2, n + 1 ≤ tier i :=
      fun i hi => hsmall i (List.mem_append_right _ hi)
    have hbulkL : ∀ i ∈ flattenMovingSlots n bulk.1, n + 1 ≤ tier i :=
      fun i hi => hbulk i (List.mem_append_left _ hi)
    have hbulkR : ∀ i ∈ flattenMovingSlots n bulk.2, n + 1 ≤ tier i :=
      fun i hi => hbulk i (List.mem_append_right _ hi)
    refine ⟨?_, ?_, hsamples.1, ?_, ?_⟩
    · intro i hi
      exact (List.mem_append.mp hi).elim (hsmallL i) (hbulkL i)
    · intro i hi
      exact (List.mem_append.mp hi).elim (hsmallR i) (hbulkR i)
    · apply ihL _ _ _ _ _ hsamples.2.1
      · apply flattenMovingSlots_append_bound
        · intro i hi
          exact le_of_eq (hsamples.1 i hi).symm
        · intro i hi
          exact (Nat.le_succ n).trans (hsmallL i hi)
      · intro i hi
        exact (Nat.le_succ n).trans (hbulkL i hi)
    · apply ihR _ _ _ _ _ hsamples.2.2
      · apply flattenMovingSlots_append_bound
        · intro i hi
          exact le_of_eq (hsamples.1 i hi).symm
        · intro i hi
          exact (Nat.le_succ n).trans (hsmallR i hi)
      · intro i hi
        exact (Nat.le_succ n).trans (hbulkR i hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

def movingSlotValues {σ : Type*} (value : σ → ℕ) : (n : ℕ) →
    TreeLeafTuple (List σ) n → TreeLeafTuple ℕ n
  | 0, x => MovingSlotReversal.naturalProduct value (show List σ from x)
  | n + 1, x => (movingSlotValues value n x.1, movingSlotValues value n x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- The extra support test is literal divisibility of the composite pivot by
its sampled compensation product. All smooth and other support factors stay
in `extra`. -/
noncomputable def movingSlotCutoff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  if 0 < x.compensation value ∧
      x.compensation value ∣ historyPivot (movingSlotSystem value childBound pivotBound) x s v w
  then extra x s v w else 0

theorem buildMovingSlotData_follows {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).Follows t := by
  induction samples with
  | leaf => rfl
  | node samples left right ihL ihR => exact ⟨rfl, ihL _ _ _, ihR _ _ _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator factorization for the source moving-giant coefficient -/

namespace Ostmann
open scoped Classical

def movingSlotModulus {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ regular, XL, XR⟩ => XL * XR * MovingSlotReversal.naturalProduct value regular
  | ⟨_ + 1, .node _ CL CR _ _ _, XL, XR⟩ =>
      XL * XR * MovingSlotReversal.naturalProduct value (CL ++ CR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeTupleProfiles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed products and means at a horizontal tree level -/

namespace Ostmann

open scoped BigOperators

theorem treeLeafTupleEquiv_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple A n) (i : TreeLeafIndex n) :
    treeLeafTupleEquiv B n (treeLeafMap f n a) i = f (treeLeafTupleEquiv A n a i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih a.1 i
    | inr i => exact ih a.2 i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial smooth factors in the full moving-giant coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFourierLeaf {σ : Type*} (value : σ → ℕ)
    (ψ : ℝ → ℂ) (X : ℝ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  normalizedFourierProfile ψ s ((movingSlotModulus value x : ℝ) / X)

noncomputable def movingFourierTree {σ : Type*} (value : σ → ℕ) (ψ : ℝ → ℂ) (X : ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR =>
      normalizedFourierProfile ψ s
        ((XL * XR * MovingSlotReversal.naturalProduct value regular : ℕ) / X)
  | _, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      movingFourierTree value ψ X left p XL * star (movingFourierTree value ψ X right p XR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def movingLeafIndexEquiv (n : ℕ) : TreeLeafIndex n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (card_treeLeafIndex n)

noncomputable def movingLeafNormalizedPolynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X : ℝ) (i : TreeLeafIndex n) : Polynomial ℝ :=
  Polynomial.C X⁻¹ * T.leafPolynomials value L R i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed residue and root cells for full moving arithmetic support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingArithmeticPeriod (nodes : List MovingFormulaNode) : ℕ :=
  (nodes.map MovingFormulaNode.residuePeriod).prod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact arithmetic indicator from the recursive weight -/

namespace Ostmann
open scoped Classical

noncomputable def movingArithmeticIndicator {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : ℂ :=
  if T.ArithmeticSupport value childBound pivotBound XL XR then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

noncomputable def movingArchimedeanGate (nodes : List MovingFormulaNode) (x : Bool → ℝ) : Prop :=
  ∀ f ∈ nodes, f.guard.archimedeanAt x

noncomputable def movingArchimedeanRootCuts (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) : Finset ℝ :=
  nodes.toFinset.biUnion fun f => polynomialRootCuts (f.guard.realPolynomials a coord)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingResidueFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue factors separated from the real moving support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingArchimedeanFlag (nodes : List MovingFormulaNode) (x : Bool → ℝ) : ℂ :=
  if movingArchimedeanGate nodes x then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingScalarWindows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining original scalar and its literal terminal windows -/

namespace Ostmann
open scoped Classical

noncomputable def movingDataLeaf {σ : Type*}
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  F x.data s

noncomputable def movingDataExtra {σ : Type*}
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ := E x.data s v w

noncomputable def movingDataWeight {σ : Type*}
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℂ
  | _, T@(.leaf s _) => F T s
  | _, T@(.node s _ _ _ left right) =>
      (E T s left.frequency right.frequency : ℂ) * movingDataWeight F E left *
        star (movingDataWeight F E right)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_LogCutoffPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial factors for the actual logarithmic node cutoff -/

namespace Ostmann

/-- No large-center cost occurs in a logarithmic node cutoff's variation. -/
theorem logCutoffPolynomialFactor_budget (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    let f := logCutoffPolynomialFactor P φ G B D hB hD hφ hlip
    2 * f.bound + f.lip * (f.hi - f.lo) = 2 * B + D * (Real.exp 2 - 1) := by
  change 2 * B + (D * (Real.exp (G - 1))⁻¹) * (Real.exp (G + 1) - Real.exp (G - 1)) = _
  rw [show G + 1 = (G - 1) + 2 by ring, Real.exp_add]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeCutoffFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the original logarithmic cutoff in every moving node -/

namespace Ostmann
open scoped Classical

noncomputable def movingPhiExtra {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  extra x s v w * positiveLogCutoff φ (G x.depth)
    ((historyPivot (movingSlotSystem value childBound pivotBound) x s v w / x.compensation value : ℕ) : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realValueFourierWeight {σ : Type*} (value : σ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (L R : ℝ) : ℂ :=
  ∏ j : TreeLeafIndex n,
    let v := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies j) lo hi hlo hhi).value
      (T.realValueLeafModuli value L R j / X)
    if treeLeafTupleEquiv Bool n (transferConjugations n false) j then conj v else v

noncomputable def realValueSmoothWeight {σ : Type*} (value : σ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueFourierWeight value T ψ X lo hi hlo hhi L R * realValueNodeCutoff value φ G T L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSquareLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square exclusions for the actual moving occurrence lines -/

namespace Ostmann
open scoped BigOperators Classical

@[simp] theorem naturalReduction_square {σ : Type*} (p : ℕ) (value : σ → ℕ)
    (f : MvPolynomial σ ℤ) :
    squareReduction p (MovingSlotReversal.naturalReduction (p ^ 2) value f) =
      MovingSlotReversal.naturalReduction p value f := by
  have he : (squareReduction p).comp (MovingSlotReversal.naturalReduction (p ^ 2) value) =
      MovingSlotReversal.naturalReduction p value := by
    ext i <;> simp [MovingSlotReversal.naturalReduction]
  exact DFunLike.congr_fun he f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

/-- Tests the two giants against every subtree frequency, every current
regular slot, and the fixed outside list. Mutual coprimality of the two
current giants is deliberately separate. -/
def movingLocalGiantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct ∧
    IsCoprime XL (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∧
    IsCoprime XR (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∧
    IsCoprime XL (outside.prod : ℤ) ∧ IsCoprime XR (outside.prod : ℤ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full pairwise and subtree-frequency support, with the top giant pair separated -/

namespace Ostmann
open scoped Classical

/-- The outside list is fixed while the current regular slots change. These
small-slot tests are independent of both top giant values. -/
def movingRegularOutsidePairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, T@(.leaf _ _) => (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime
  | _, T@(.node _ _ _ _ left right) =>
      (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime ∧
        movingRegularOutsidePairwise value outside left ∧ movingRegularOutsidePairwise value outside right

/-- Literal pairwise support at every current state, including the fixed
outside list from the manuscript's recursive average. -/
def movingFullOutsidePairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime ∧
        movingFullOutsidePairwise value outside left p XL ∧ movingFullOutsidePairwise value outside right p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFourierFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped Fourier factors along an original bulk-prime coordinate -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkFourierFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : Fin (2 ^ n) → ClippedPolynomialFactor :=
  fun j =>
    let leaf := (movingLeafIndexEquiv n).symm j
    let f := fourierPolynomialFactor (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R leaf)
      ψ (T.leafFrequencies leaf) lo hi hlo hhi
    if treeLeafTupleEquiv Bool n (transferConjugations n false) leaf then f.conjugate else f

theorem bulkFourierFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) :
    smoothPolynomialBudget (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) ≤
      movingFourierVariationBudget ψ V lo hi n := by
  unfold smoothPolynomialBudget movingFourierVariationBudget
  calc
    _ ≤ ∏ _j : Fin (2 ^ n),
        (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
          (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) := by
      apply Finset.prod_le_prod
      · intro j _
        let f := bulkFourierFactors value i T L R ψ X lo hi hlo hhi j
        exact add_nonneg (mul_nonneg (by norm_num) f.bound_nonneg)
          (mul_nonneg f.lip_nonneg (sub_nonneg.mpr f.lo_le_hi))
      · intro j _
        have hv := T.leafFrequencies_bound V hV ((movingLeafIndexEquiv n).symm j)
        have hd := mul_le_mul_of_nonneg_left hv (schwartz_profile_lip_nonneg ψ)
        have he := mul_le_mul_of_nonneg_right
          (add_le_add (le_rfl : SchwartzMap.seminorm ℝ 0 0 ψ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) hd)
          (sub_nonneg.mpr hhi)
        dsimp only [bulkFourierFactors]
        split_ifs <;> exact add_le_add le_rfl he
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAuxiliaryUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating inherited regular-slot units from the recursive residue tests -/

namespace Ostmann
open scoped Classical

def movingAuxiliaryLocalUnits {σ : Type*} (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct ∧
    IsCoprime XL (outside.prod : ℤ) ∧ IsCoprime XR (outside.prod : ℤ)

def movingAuxiliaryUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => movingAuxiliaryLocalUnits outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      movingAuxiliaryLocalUnits outside T XL XR ∧
        movingAuxiliaryUnits value outside left p XL ∧ movingAuxiliaryUnits value outside right p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAuxiliaryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A residue period that omits inherited regular-slot unit tests -/

namespace Ostmann
open scoped Classical

def movingAuxiliaryUnitPeriod {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ
  | _, T@(.leaf _ _) => T.frequencyProduct * outside.prod
  | _, T@(.node s _ _ U left right) =>
      (T.frequencyProduct * outside.prod) * (s * (MovingSlotReversal.naturalProduct value U : ℤ)) *
        movingAuxiliaryUnitPeriod value outside left * movingAuxiliaryUnitPeriod value outside right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

def movingFrequencyLocalUnits {σ : Type*} {n : ℕ} (T : MovingSlotData σ n)
    (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct

def movingFrequencyGate {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), XL, XR => movingFrequencyLocalUnits T XL XR
  | n + 1, T@(.node s CL CR U left right), XL, XR =>
      let step := MovingSlotData.step s CL CR U left right false
      let p := step.frequencyPivot value R (n + 1) XL XR
      movingFrequencyLocalUnits T XL XR ∧ s ∣ step.signedNumerator value XL XR ∧
        movingFrequencyGate value R left p XL ∧ movingFrequencyGate value R right p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalPolynomialFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized counterpart ratio is an admissible smooth factor -/

namespace Ostmann

open scoped BigOperators

noncomputable def reciprocalPolynomialFactor (P : Polynomial ℝ) (hi : ℝ)
    (hhi : 1 ≤ hi) : ClippedPolynomialFactor where
  polynomial := P
  profile := fun z => Complex.ofReal (z⁻¹)
  lo := 1
  hi := hi
  bound := 1
  lip := 1
  lo_le_hi := hhi
  bound_nonneg := by norm_num
  lip_nonneg := by norm_num
  norm_le := by
    intro z hz
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_trans (by norm_num) hz.1))]
    exact inv_le_one_of_one_le₀ hz.1
  lipschitz := by
    intro x hx y hy
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact abs_inv_sub_inv_le_of_one_le x y hx.1 hy.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReciprocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal giant factor in the diagonal multiplier -/

namespace Ostmann

/-- Reuse the existing reciprocal factor after scaling the polynomial by
its lower cell endpoint. The variation budget is independent of the center. -/
noncomputable def giantReciprocalFactor (P : Polynomial ℝ) (G : ℝ) : ClippedPolynomialFactor :=
  reciprocalPolynomialFactor (Polynomial.C ((Real.exp (G - 1))⁻¹) * P) (Real.exp 2)
    (Real.one_le_exp (by norm_num))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def giantOuterFactors (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) : Fin 3 → ClippedPolynomialFactor :=
  ![logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip,
    logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip,
    if diagonal then giantReciprocalFactor R Jright else onePolynomialFactor]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-history kernel with its original outer priors and diagonal ratio -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def giantOuterWeight (φ : ℝ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool)
    (L R : ℝ) : ℂ :=
  (positiveLogCutoff φ Jleft L : ℂ) * (positiveLogCutoff φ Jright R : ℂ) *
    (if diagonal then ((Real.exp Jright / R : ℝ) : ℂ) else 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

noncomputable def movingModularSpectator {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ZMod q → ZMod q → ℂ
  | _, .leaf s regular, x, y =>
      g ((s : ZMod q) / ((D : ZMod q) * (x * y * MovingSlotReversal.naturalProduct value regular)))
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
      if p = 0 then 0 else
        movingModularSpectator value q g D left p x * star (movingModularSpectator value q g D right p y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalLocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual internal-prime factors before averaging -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- All occurrences of a fixed internal prime impose their line modulo `p`
and exclude its zero lift modulo `p²`. Repeated occurrences remain simultaneous. -/
noncomputable def movingInternalLocalSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (p : ℕ) (x y : ZMod (p ^ 2)) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, value i = p →
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let z := φ (movingSlotLine o.path o.current).a * x +
      φ (movingSlotLine o.path o.current).b * y
    squareReduction p z = 0 ∧ z ≠ 0

noncomputable def movingInternalPairFactor {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod (p ^ 2)) : ℂ :=
  if ∀ side, movingInternalLocalSupport value (T side) p x y then 1 else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product of the frequency, internal-prime and spectator factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingFrequencyPairSupport {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (nodes : Bool → List MovingFormulaNode) (R x y : ℤ) : Prop :=
  ∀ side, movingRegularOutsidePairwise value outside (T side) ∧
    (∀ f ∈ nodes side, f.guard.frequencyBounds) ∧
    movingFrequencyGate value R (T side) x y

noncomputable def movingFrequencyPairFactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (nodes : Bool → List MovingFormulaNode) (R x y : ℤ) : ℂ :=
  if movingFrequencyPairSupport value outside T nodes R x y then
    movingDataWeight (F false) (E false) (T false) *
      conj (movingDataWeight (F true) (E true) (T true)) else 0

noncomputable def movingSpectatorPairFactor {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (x y : ZMod q) : ℂ :=
  movingModularSpectator value q g (D false) (T false) x y *
    conj (movingModularSpectator value q g (D true) (T true) x y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate the nonperiodic prime coincidences from frequency support -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFrequencyCore {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R x y : ℤ) : ℂ :=
  if ∀ b, movingFrequencyGate value R (T b) x y then
    movingDataWeight (F false) (E false) (T false) *
      conj (movingDataWeight (F true) (E true) (T true)) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

noncomputable def realValueNodeSupport {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) : {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → Prop
  | _, .leaf _ _, _, _ => True
  | n + 1, .node s CL CR u left right, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let Q := step.realCompositePivot value L R
      let p := step.realValuePivot value L R
      1 ≤ Q ∧ Q ≤ pivotBound (n + 1) ∧
        ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ) ≤
          R * realSlotProduct value CR ∧
        realValueNodeSupport value childBound pivotBound left p L ∧
        realValueNodeSupport value childBound pivotBound right p R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodeFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original node cutoffs with one free bulk coordinate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkNodeFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (T.bulkNodePolynomials value i L R).length → ClippedPolynomialFactor := fun j =>
  let f := (T.bulkNodePolynomials value i L R)[j]
  logCutoffPolynomialFactor f.2 φ (G f.1) B D hB hD hφ hlip

theorem bulkNodeFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) =
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  unfold smoothPolynomialBudget
  simp only [bulkNodeFactors, logCutoffPolynomialFactor_budget, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, T.bulkNodePolynomials_length]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSmoothFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full smooth bulk-coordinate factor and its finite variation budget -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def bulkSmoothFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (2 ^ n + (T.bulkNodePolynomials value i L R).length) → ClippedPolynomialFactor :=
  Fin.append (bulkFourierFactors value i T L R ψ X lo hi hlo hhi)
    (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip)

theorem bulkSmoothFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  change smoothPolynomialBudget (Fin.append _ _) ≤ _
  simp only [smoothPolynomialBudget, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  change smoothPolynomialBudget (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) *
    smoothPolynomialBudget (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) ≤ _
  rw [bulkNodeFactors_budget]
  apply mul_le_mul_of_nonneg_right (bulkFourierFactors_budget value i T L R ψ X lo hi V hlo hhi hV)
  have hE := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realValueFullSupport {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : Prop :=
  realValueNodeSupport value childBound pivotBound T L R ∧
    ∀ j, T.realValueLeafModuli value L R j / X ∈ Set.Icc lo hi

noncomputable def realValueSupportFlag {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : ℂ :=
  if realValueFullSupport value childBound pivotBound T X lo hi L R then 1 else 0

noncomputable def realValueKernel {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueSupportFlag value childBound pivotBound T X lo hi L R *
    realValueSmoothWeight value T ψ X lo hi hlo hhi φ G L R

theorem realValueSupportFlag_norm {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : ‖realValueSupportFlag value childBound pivotBound T X lo hi L R‖ ≤ 1 := by
  unfold realValueSupportFlag
  split_ifs <;> norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFullSupportPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root cells for every original bulk support gate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkFullSupportPolynomials {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (X lo hi : ℝ) :
    Fin (T.bulkNodeSupportPolynomials value i childBound pivotBound L R).length ⊕
      (TreeLeafIndex n × Bool) → Polynomial ℝ :=
  Sum.elim (fun j => (T.bulkNodeSupportPolynomials value i childBound pivotBound L R)[j])
    (fun j => let M := Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R j.1
      if j.2 then Polynomial.C hi - M else M - Polynomial.C lo)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeasure
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact atomic measure of a harmonic prime cell -/

namespace Ostmann
open MeasureTheory Filter
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable def primeLogCellMeasure (q a : ℕ) (u v : ℝ) : Measure ℝ :=
  ∑ p ∈ primeLogCellSet q a u v, ENNReal.ofReal ((p : ℝ)⁻¹) • Measure.dirac (Real.log p)

instance finite_primeLogCellMeasure (q a : ℕ) (u v : ℝ) :
    IsFiniteMeasure (primeLogCellMeasure q a u v) := by
  unfold primeLogCellMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkKernelPairComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the full original pair, with every sharp gate -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realValueKernelPair {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueKernel value childBound pivotBound (T false) ψ X lo hi hlo hhi φ G L R *
    conj (realValueKernel value childBound pivotBound (T true) ψ X lo hi hlo hhi φ G L R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetMovingAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reciprocal leaf action in the six quartet coordinates -/

namespace Ostmann

open scoped BigOperators

def quartetMovingSign : QuartetMovingCase → TreeLeafTuple ℤ 2
  | .cross left right =>
      (((if left then (-1, 0) else (0, -1)), (if right then (1, 0) else (0, 1))) :
        (ℤ × ℤ) × (ℤ × ℤ))
  | .leftPair => (((-1, 1), (0, 0)) : (ℤ × ℤ) × (ℤ × ℤ))
  | .rightPair => (((0, 0), (-1, 1)) : (ℤ × ℤ) × (ℤ × ℤ))

noncomputable def quartetMovingFiberEquiv {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P : U) : TreeLeafFiber U 2 P ≃ U × (U × U) :=
  match choice with
  | .cross left right => crossQuartetFiberEquiv left right P
  | .leftPair => samePairLeftFiberEquiv P
  | .rightPair => samePairRightFiberEquiv P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent held and moving coordinates on a product of quartet fibers -/

namespace Ostmann

open scoped BigOperators

noncomputable def quartetProductCoordinates {I U : Type*} [CommGroup U]
    (choice : I → QuartetMovingCase) (P : I → U) :
    ((i : I) → TreeLeafFiber U 2 (P i)) ≃ (I → U × U) × (I → U) :=
  (Equiv.piCongrRight (fun i =>
    (quartetMovingFiberEquiv (choice i) (P i)).trans (Equiv.prodAssoc U U U).symm)).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => U × U) (fun _ => U))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFullCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full tree in held and moving quartet coordinates -/

namespace Ostmann

open scoped BigOperators

noncomputable def fullQuartetFiberCoordinates {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U) :
    QuartetProductFiber U n P ≃ (TreeLeafIndex n → U × U) × (TreeLeafIndex n → U) :=
  (quartetProductFiberEquiv n P).trans (quartetProductCoordinates choice P)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable instance instFintypePartitionMatching {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) : Fintype (PartitionMatching f g) :=
  inferInstanceAs (Fintype {e : A ≃ B // ∀ a, g (e a) = f a})

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bipartite overlap graph of an actual bulk permutation -/

namespace Ostmann

open scoped Classical

def arrangementLeft {L : Type*} {m : ℕ} (e : Equiv.Perm (L × Fin m))
    (l : L) : (arrangementGraph m e).ConnectedComponent :=
  (arrangementGraph m e).connectedComponentMk (.inl l)

def arrangementRight {L : Type*} {m : ℕ} (e : Equiv.Perm (L × Fin m))
    (l : L) : (arrangementGraph m e).ConnectedComponent :=
  (arrangementGraph m e).connectedComponentMk (.inr l)

theorem arrangement_components_match {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (x : L × Fin m) :
    arrangementRight e (e x).1 = arrangementLeft e x.1 := by
  apply Eq.symm
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact ⟨x.2, (e x).2, rfl⟩

def arrangementMatching {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) :
    PartitionMatching (fun x : L × Fin m => arrangementLeft e x.1)
      (fun x : L × Fin m => arrangementRight e x.1) :=
  ⟨e, arrangement_components_match e⟩

theorem arrangementLeft_surjective {L : Type*} {m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (L × Fin m)) : Function.Surjective (arrangementLeft e) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    cases v with
    | inl l => exact ⟨l, rfl⟩
    | inr l =>
      let x := e.symm (l, ⟨0, hm⟩)
      refine ⟨x.1, ?_⟩
      have h := arrangement_components_match e x
      simpa only [x, Equiv.apply_symm_apply, arrangementRight] using h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component products for the two arrangements of the same bulk variables -/

namespace Ostmann

open scoped BigOperators Classical

theorem component_block_product {L C G : Type*} [Fintype L] [CommMonoid G]
    (component : L → C) (m : ℕ) (x : L × Fin m → G) (c : C) :
    (∏ l : {l : L // component l = c}, bulkBlockProduct x l.1) =
      ∏ s : {s : L × Fin m // component s.1 = c}, x s.1 := by
  have h := (slotFiberEquiv component m c).prod_comp (fun lj => x (lj.1.1, lj.2))
  simpa only [slotFiberEquiv, Equiv.coe_fn_mk, Fintype.prod_prod_type,
    bulkBlockProduct] using h.symm

/-- Multiplying leaf products inside an actual overlap component gives
the same answer on both sides of the permutation. -/
theorem arrangement_partition_products {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (x : L × Fin m → G) :
    partitionProduct (arrangementLeft e) (bulkBlockProduct x) =
      partitionProduct (arrangementRight e) (bulkBlockProduct (x ∘ e.symm)) := by
  funext c
  change (∏ l : {l : L // arrangementLeft e l = c}, bulkBlockProduct x l.1) =
    ∏ l : {l : L // arrangementRight e l = c}, bulkBlockProduct (x ∘ e.symm) l.1
  rw [component_block_product, component_block_product]
  exact ((arrangementMatching e).restrict c).symm.prod_comp
    (fun s : {s : L × Fin m // arrangementLeft e s.1 = c} => x s.1) |>.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementBoundary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfers along the actual overlap graph

The signed vertex products form a group homomorphism. A slot transfers an
arbitrary unit between its two endpoints; connected paths compose transfers.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def arrangementBoundary {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) : (L × Fin m → G) →* (L ⊕ L → G) where
  toFun x := Sum.elim (bulkBlockProduct x) (fun l => (bulkBlockProduct (x ∘ e.symm) l)⁻¹)
  map_one' := by ext v; cases v <;> simp [bulkBlockProduct]
  map_mul' x y := by
    ext v
    cases v <;> simp [bulkBlockProduct, Pi.mul_apply, Function.comp_apply, Finset.prod_mul_distrib, mul_comm]

theorem bulkBlockProduct_mulSingle {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (s : L × Fin m) (g : G) (l : L) :
    bulkBlockProduct (Pi.mulSingle s g) l = if l = s.1 then g else 1 := by
  rcases s with ⟨a, i⟩
  by_cases h : l = a
  · subst l
    simp [bulkBlockProduct, Pi.mulSingle_apply, Prod.mk.injEq]
  · simp [bulkBlockProduct, Prod.mk.injEq, h]

theorem arrangementBoundary_mulSingle {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (s : L × Fin m) (g : G) :
    arrangementBoundary e (Pi.mulSingle s g) =
      Pi.mulSingle (Sum.inl s.1) g / Pi.mulSingle (Sum.inr (e s).1) g := by
  have he : (Pi.mulSingle s g) ∘ e.symm = Pi.mulSingle (e s) g := by
    funext t
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]
  ext v
  cases v with
  | inl l =>
    simp [arrangementBoundary, bulkBlockProduct_mulSingle, Pi.mulSingle_apply]
  | inr l =>
    simp [arrangementBoundary, he, bulkBlockProduct_mulSingle, Pi.mulSingle_apply]

theorem arrangementBoundary_transfer_adj {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (u v : L ⊕ L)
    (h : (arrangementGraph m e).Adj u v) (g : G) :
    Pi.mulSingle u g / Pi.mulSingle v g ∈ (arrangementBoundary (G := G) e).range := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact False.elim h
    | inr b =>
      obtain ⟨i, j, hij⟩ := h
      refine ⟨Pi.mulSingle (a, i) g, ?_⟩
      simp only [arrangementBoundary_mulSingle, hij]
  | inr b =>
    cases v with
    | inr a => exact False.elim h
    | inl a =>
      obtain ⟨i, j, hij⟩ := h
      have hf : Pi.mulSingle (Sum.inl a) g / Pi.mulSingle (Sum.inr b) g ∈
          (arrangementBoundary (G := G) e).range := by
        refine ⟨Pi.mulSingle (a, i) g, ?_⟩
        simp only [arrangementBoundary_mulSingle, hij]
      simpa only [inv_div] using (arrangementBoundary (G := G) e).range.inv_mem hf

theorem arrangementBoundary_transfer_reachable {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (u v : L ⊕ L)
    (h : (arrangementGraph m e).Reachable u v) (g : G) :
    Pi.mulSingle u g / Pi.mulSingle v g ∈ (arrangementBoundary (G := G) e).range := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have ha := arrangementBoundary_transfer_adj (G := G) e a b hab g
    have hm := (arrangementBoundary (G := G) e).range.mul_mem ha ih
    simpa only [div_mul_div_cancel] using hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementProductImage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every compatible pair of leaf-product vectors is realized by bulk slots -/

namespace Ostmann
open scoped Classical BigOperators

theorem arrangementBoundary_range_of_balanced {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (f : L ⊕ L → G)
    (hf : ∀ c : (arrangementGraph m e).ConnectedComponent,
      (∏ v : {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c}, f v.val) = 1) :
    f ∈ (arrangementBoundary e).range := by
  let component := (arrangementGraph m e).connectedComponentMk
  choose root hroot using arrangementLeft_surjective hm e
  let vertex : (arrangementGraph m e).ConnectedComponent → L ⊕ L := fun c => Sum.inl (root c)
  have hv (c) : component (vertex c) = c := hroot c
  have hmem (v : L ⊕ L) : Pi.mulSingle (M := fun _ : L ⊕ L => G) v (f v) / Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v) ∈
      (arrangementBoundary e).range := by
    apply arrangementBoundary_transfer_reachable
    exact SimpleGraph.ConnectedComponent.exact (hv (component v)).symm
  have hden : (∏ v : L ⊕ L, Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v)) = 1 := by
    rw [← Fintype.prod_fiberwise component (fun v => Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v))]
    apply Finset.prod_eq_one
    intro c _
    calc
      _ = (MonoidHom.mulSingle (fun _ : L ⊕ L => G) (vertex c))
          (∏ v : {v : L ⊕ L // component v = c}, f v.val) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro v _
        simp only [MonoidHom.mulSingle_apply, v.property]
      _ = 1 := by rw [hf c]; exact map_one _
  have hnum : (∏ v : L ⊕ L, Pi.mulSingle v (f v)) = f := by
    ext v
    change (Pi.evalMonoidHom (fun _ : L ⊕ L => G) v) (∏ w, Pi.mulSingle w (f w)) = _
    rw [map_prod]
    exact Fintype.prod_pi_mulSingle v f
  have hall := (arrangementBoundary (G := G) e).range.prod_mem (fun v (_ : v ∈ Finset.univ) => hmem v)
  simpa only [Finset.prod_div_distrib, hnum, hden, div_one] using hall

noncomputable def arrangementComponentVertexEquiv {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (c : (arrangementGraph m e).ConnectedComponent) :
    {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c} ≃
      ({l : L // arrangementLeft e l = c} ⊕ {l : L // arrangementRight e l = c}) where
  toFun v := match v with
    | ⟨.inl l, h⟩ => .inl ⟨l, h⟩
    | ⟨.inr l, h⟩ => .inr ⟨l, h⟩
  invFun v := match v with
    | .inl ⟨l, h⟩ => ⟨.inl l, h⟩
    | .inr ⟨l, h⟩ => ⟨.inr l, h⟩
  left_inv v := by rcases v with ⟨v, h⟩; cases v <;> rfl
  right_inv v := by cases v <;> rfl

theorem arrangement_component_signed_product {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (a b : L → G)
    (c : (arrangementGraph m e).ConnectedComponent) :
    (∏ v : {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c},
      Sum.elim a (fun l => (b l)⁻¹) v.val) =
      partitionProduct (arrangementLeft e) a c / partitionProduct (arrangementRight e) b c := by
  rw [← (arrangementComponentVertexEquiv e c).symm.prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [arrangementComponentVertexEquiv, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
    div_eq_mul_inv, ← Finset.prod_inv_distrib, partitionProduct]

theorem arrangement_leaf_products_surjective {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (a b : L → G)
    (hab : partitionProduct (arrangementLeft e) a = partitionProduct (arrangementRight e) b) :
    ∃ x : L × Fin m → G, bulkBlockProduct x = a ∧ bulkBlockProduct (x ∘ e.symm) = b := by
  have hf := arrangementBoundary_range_of_balanced hm e (Sum.elim a (fun l => (b l)⁻¹))
    (fun c => by rw [arrangement_component_signed_product, congrFun hab c]; exact div_self' _)
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, ?_, ?_⟩
  · funext l
    exact congrFun hx (.inl l)
  · funext l
    have h := congrFun hx (.inr l)
    exact inv_injective h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementUniformLaw
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact joint law of the two actual bulk leaf products -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def arrangementProductMap {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) :
    (L × Fin m → G) →* ((L → G) × (L → G)) where
  toFun x := (bulkBlockProduct x, bulkBlockProduct (x ∘ e.symm))
  map_one' := by ext <;> simp [bulkBlockProduct]
  map_mul' x y := by
    ext <;> simp [bulkBlockProduct, Function.comp_apply, Finset.prod_mul_distrib]

theorem mem_arrangementProductMap_range {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (ab : (L → G) × (L → G)) :
    ab ∈ (arrangementProductMap (G := G) e).range ↔
      partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact arrangement_partition_products e x
  · intro h
    obtain ⟨x, hx, hy⟩ := arrangement_leaf_products_surjective hm e ab.1 ab.2 h
    exact ⟨x, Prod.ext hx hy⟩

noncomputable def arrangementRangeEquiv {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    (arrangementProductMap (G := G) e).range ≃
      {ab : (L → G) × (L → G) //
        partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2} where
  toFun x := ⟨x.val, (mem_arrangementProductMap_range hm e x.val).mp x.property⟩
  invFun x := ⟨x.val, (mem_arrangementProductMap_range hm e x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def bulkPairCorrelation {L G : Type*} [Fintype L] [Fintype G] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (F H : (L → G) → ℂ) : ℂ :=
  (Fintype.card (L × Fin m → G) : ℂ)⁻¹ *
    ∑ x : L × Fin m → G, F (bulkBlockProduct x) * conj (H (bulkBlockProduct (x ∘ e.symm)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def bulkSlotLeaves {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) : TreeLeafTuple (List σ) n :=
  (treeLeafTupleEquiv (List σ) n).symm (fun j => List.ofFn (fun i => slot (j, i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenRegularSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained nonbulk coprimality support for the complete sampled tree -/

namespace Ostmann
open scoped Classical

def movingNonbulkOutsidePairwise {σ : Type*} (value : σ → ℕ) (bulk : σ → Bool)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) : Prop :=
  ∀ L ∈ T.regularLists, ((L.filter fun i => !(bulk i)).map value ++ outside).Pairwise Nat.Coprime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotNodup
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct selected bulk labels in the concrete leaf constructor -/

namespace Ostmann
open scoped Classical

theorem mem_flatten_bulkSlotLeaves {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) (i : σ) :
    i ∈ flattenMovingSlots n (bulkSlotLeaves n m slot) ↔ ∃ j, slot j = i := by
  induction n with
  | zero =>
    change i ∈ List.ofFn (fun j => slot ((), j)) ↔ ∃ j, slot j = i
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨((), j), hj⟩
    · rintro ⟨⟨u, j⟩, hj⟩; cases u; exact ⟨j, hj⟩
  | succ n ih =>
    change i ∈ (flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) ++
      flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2)))) ↔ _
    rw [List.mem_append, ih, ih]
    constructor
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨(.inl j.1, j.2), hj⟩
      · exact ⟨(.inr j.1, j.2), hj⟩
    · rintro ⟨⟨j | j, k⟩, h⟩
      · exact Or.inl ⟨(j, k), h⟩
      · exact Or.inr ⟨(j, k), h⟩

theorem bulkSlotLeaves_nodup {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) (hinj : Function.Injective slot) :
    (flattenMovingSlots n (bulkSlotLeaves n m slot)).Nodup := by
  induction n with
  | zero =>
    apply List.nodup_ofFn_ofInjective
    intro i j h
    exact congrArg Prod.snd (hinj h)
  | succ n ih =>
    change (flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) ++
      flattenMovingSlots n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2)))).Nodup
    refine List.nodup_append.mpr ⟨ih _ ?_, ih _ ?_, ?_⟩
    · intro i j h
      have h' := hinj h
      have hi : i.1 = j.1 := Sum.inl.inj
        (congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.1) h')
      have hj : i.2 = j.2 := congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.2) h'
      exact Prod.ext hi hj
    · intro i j h
      have h' := hinj h
      have hi : i.1 = j.1 := Sum.inr.inj
        (congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.1) h')
      have hj : i.2 = j.2 := congrArg (fun x : TreeLeafIndex (n + 1) × Fin m => x.2) h'
      exact Prod.ext hi hj
    · intro a ha b hb hab
      obtain ⟨j, hj⟩ := (mem_flatten_bulkSlotLeaves n m _ a).mp ha
      obtain ⟨k, hk⟩ := (mem_flatten_bulkSlotLeaves n m _ b).mp hb
      have h' := congrArg Prod.fst (hinj (hj.trans (hab.trans hk.symm)))
      cases h'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSpectatorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute bounds under the original independent bulk-slot law -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

def bulkBlockProductHom {L G : Type*} [Fintype L] [CommGroup G] (m : ℕ) :
    (L × Fin m → G) →* (L → G) where
  toFun := bulkBlockProduct
  map_one' := by ext; simp [bulkBlockProduct]
  map_mul' x y := by ext; simp [bulkBlockProduct, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

def pairedNodeFrequencies (S : Finset ℤ) (root left right : S × S) :
    NodeFrequencies × NodeFrequencies :=
  (⟨root.1, left.1, right.1⟩, ⟨root.2, left.2, right.2⟩)

def frequencySplitList (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree (S × S) n → List (NodeFrequencies × NodeFrequencies)
  | 0, _ => []
  | n + 1, x => pairedNodeFrequencies S x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) ::
      (frequencySplitList S n x.2.1 ++ frequencySplitList S n x.2.2)

noncomputable def frequencyLeafWeight {A : Type} (W : A → ℝ) :
    (n : ℕ) → FrequencyTree A n → ℝ
  | 0, x => W x
  | n + 1, x => frequencyLeafWeight W n x.2.1 * frequencyLeafWeight W n x.2.2

def emptyNodeFrequencies : NodeFrequencies := ⟨0, 0, 0⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency budget for one squared history

Unlike a pair of histories, this sum has exactly one frequency at each leaf.
This is needed before the level-zero square-weight cancellation.
-/

namespace Ostmann

open scoped BigOperators Classical

def singleFrequencySplitList (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree S n → List NodeFrequencies
  | 0, _ => []
  | n + 1, x => ⟨x.1, (frequencyRoot n x.2.1 : S), (frequencyRoot n x.2.2 : S)⟩ ::
      (singleFrequencySplitList S n x.2.1 ++ singleFrequencySplitList S n x.2.2)

theorem singleFrequencySplitList_length (S : Finset ℤ) (n : ℕ) (x : FrequencyTree S n) :
    (singleFrequencySplitList S n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [singleFrequencySplitList, List.length_cons, List.length_append, ih]
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

def singleTreeNodeFrequencies (S : Finset ℤ) (n : ℕ) (x : FrequencyTree S n)
    (j : ℕ) : NodeFrequencies :=
  (singleFrequencySplitList S n x).getD j emptyNodeFrequencies

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleHistorySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact one-history arithmetic support under independent uniform leaves -/

namespace Ostmann

open scoped BigOperators Classical

def diagonalSplitData {Q : ℕ} (d : Option (ArithmeticSplitData Q)) :
    Option (ArithmeticSplitData Q × ArithmeticSplitData Q) := d.map fun e => (e, e)

def singleArithmeticSplitTest {Q : ℕ} (d : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) : Prop := match d with
  | none => False
  | some e => e.test x

noncomputable def singleArithmeticLeafSupport {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : ℝ :=
  sequentialSupport (fun past y => singleArithmeticSplitTest (data (treeLeafProduct n x) past) y)
    [] (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_HarmonicHistorySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic support bound under the original prime priors

The residue modulus is allowed to depend on the entire fixed frequency
history. Only the prime samples are averaged, with their original priors.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def harmonicHistorySupportSum (P : Finset ℕ) (S : Finset ℤ) (V n : ℕ)
    (Q : FrequencyTree S n → ℕ) [∀ t, NeZero (Q t)]
    (T : TreeLeafIndex n → Finset ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (Q t))
    (data : (t : FrequencyTree S n) → (ZMod (Q t))ˣ →
      List (ZMod (Q t))ˣ → Option (ArithmeticSplitData (Q t))) : ℝ :=
  ∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
    (∑ x : TreeLeafIndex n → P, (∏ i, primeSubsetPrior P (T i) (x i)) *
      singleArithmeticLeafSupport n (data t)
        ((treeLeafTupleEquiv (ZMod (Q t))ˣ n).symm
          (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit t (x i)))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original leaf-frequency cutoffs in the recursive squared weights -/

namespace Ostmann

open scoped Classical

def frequencyTreeMap {A B : Type} (f : A → B) : (n : ℕ) → FrequencyTree A n → FrequencyTree B n
  | 0, x => f x
  | n + 1, x => (f x.1, frequencyTreeMap f n x.2.1, frequencyTreeMap f n x.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AdaptivePivotCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing coefficients from the already exposed product prefix -/

namespace Ostmann

open scoped Classical

/-- Choose any valid completion of the exposed prefix. The precision theorem
below proves that the required reduced coefficients do not depend on it. -/
noncomputable def adaptivePivotCoefficients (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ) : ZMod Q × ZMod Q :=
  if hj : past.length < 2 ^ n - 1 then
    if h : ∃ a : SampledPivotHistory n Q, a.valid D ∧ a.matches total past then
      let a := Classical.choose h
      (D.leftCoefficient a.pivots ⟨past.length, hj⟩,
        D.rightCoefficient a.pivots ⟨past.length, hj⟩)
    else (0, 0)
  else (0, 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AdaptivePivotSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual integral histories pass the constructed adaptive split tests -/

namespace Ostmann

open scoped Classical

noncomputable def adaptivePivotResidueSplit (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) : ArithmeticResidueSplit (R ^ (k + 2)) where
  frequencies := D.frequencies ⟨past.length, hj⟩
  frequency_ne_zero := hs _
  frequency_dvd := (hsR _).trans (dvd_pow_self R (by omega))
  leftFactor := (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).1
  rightFactor := (adaptivePivotCoefficients n (R ^ (k + 2)) D total past).2
  parentProduct := splitPrefixParent n total past

noncomputable def adaptivePivotData (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1))
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (k + 2))) :=
  if hj : past.length < 2 ^ n - 1 then
    (adaptivePivotResidueSplit n R k D hs hsR total past hj).toData
  else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The modulus attached to one fixed frequency history -/

namespace Ostmann

open scoped BigOperators Classical

/-- The product includes every internal frequency and every leaf frequency,
with multiplicity, exactly as in the residue-precision argument. -/
def historyFrequencyProduct (S : Finset ℤ) : (n : ℕ) → FrequencyTree S n → ℕ
  | 0, s => (show S from s).val.natAbs
  | n + 1, t => (t.1 : ℤ).natAbs * historyFrequencyProduct S n t.2.1 *
      historyFrequencyProduct S n t.2.2

def historyFrequencyModulus (S : Finset ℤ) (n k : ℕ) (t : FrequencyTree S n) : ℕ :=
  historyFrequencyProduct S n t ^ (k + 2)

theorem singleFrequencySplitList_root_mem (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n t) : f.root ∈ S := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact t.1.property
    · exact ih _ hf
    · exact ih _ hf

theorem singleTreeNodeFrequencies_root_mem (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (j : ℕ) (hj : j < 2 ^ n - 1) : (singleTreeNodeFrequencies S n t j).root ∈ S := by
  apply singleFrequencySplitList_root_mem S n t
  have hj' : j < (singleFrequencySplitList S n t).length := by
    simpa only [singleFrequencySplitList_length] using hj
  rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj']
  exact List.getElem_mem hj'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PreorderNodePaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit preorder indices for internal nodes and their ancestors -/

namespace Ostmann

theorem nodePathIndex_preorderNodePath (n : ℕ) (j : Fin (2 ^ n - 1)) :
    nodePathIndex n (preorderNodePath n j) = j.val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [preorderNodePath]
    split_ifs with h0 hL
    · exact h0.symm
    · simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, ih]
      omega
    · simp only [nodePathIndex, ite_true, if_true, ih]
      omega

theorem preorderNodePath_nodePathIndex (n : ℕ) (p : List Bool) (hp : p.length < n) :
    preorderNodePath n ⟨nodePathIndex n p, nodePathIndex_lt n p hp⟩ = p := by
  induction n generalizing p with
  | zero => simp at hp
  | succ n ih =>
    cases p with
    | nil => simp [nodePathIndex, preorderNodePath]
    | cons b p =>
      have hp' : p.length < n := by simpa using hp
      have hi := nodePathIndex_lt n p hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · have hzero : 1 + nodePathIndex n p ≠ 0 := by omega
        have hleft : 1 + nodePathIndex n p < 2 ^ n := by omega
        simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, preorderNodePath,
          hzero, dite_false, hleft, dite_true]
        congr 1
        simpa only [Nat.add_sub_cancel_left] using ih p hp'
      · have hzero : 2 ^ n + nodePathIndex n p ≠ 0 := by positivity
        have hleft : ¬2 ^ n + nodePathIndex n p < 2 ^ n := by omega
        simp only [nodePathIndex, ite_true, if_true, preorderNodePath, hzero, dite_false, hleft]
        congr 1
        simpa only [Nat.add_sub_cancel_left] using ih p hp'

theorem nodePathIndex_nonempty_pos (n : ℕ) (p : List Bool)
    (hp : p.length < n) (hne : p ≠ []) : 0 < nodePathIndex n p := by
  cases n with
  | zero => simp at hp
  | succ n =>
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons b p =>
      have := Nat.one_le_two_pow (n := n)
      cases b <;> simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> omega

theorem nodePathIndex_proper_prefix (n : ℕ) (p s : List Bool)
    (hps : (p ++ s).length < n) (hs : s ≠ []) :
    nodePathIndex n p < nodePathIndex n (p ++ s) := by
  induction n generalizing p with
  | zero => simp at hps
  | succ n ih =>
    cases p with
    | nil =>
      simpa only [List.nil_append, nodePathIndex] using nodePathIndex_nonempty_pos (n + 1) s hps hs
    | cons b p =>
      have hi := ih p (by simpa only [List.cons_append, List.length_cons, Nat.add_lt_add_iff_right] using hps)
      simp only [List.cons_append, nodePathIndex]
      exact Nat.add_lt_add_left hi _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeAncestorScheme
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

theorem ancestorNodeIndex_path (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) :
    preorderNodePath n (ancestorNodeIndex n j i) = (preorderNodePath n j).take i.val :=
  preorderNodePath_nodePathIndex n _ (by
    rw [List.length_take]
    exact (min_le_right _ _).trans_lt (preorderNodePath_length n j))

theorem ancestorNodeIndex_earlier (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) :
    (ancestorNodeIndex n j i).val < j.val ∧
      (preorderNodePath n (ancestorNodeIndex n j i)).length < (preorderNodePath n j).length := by
  have hsplit := List.take_append_drop i.val (preorderNodePath n j)
  have hdrop : (preorderNodePath n j).drop i.val ≠ [] := by
    intro hz
    have hl := congrArg List.length hz
    simp only [List.length_drop, List.length_nil] at hl
    omega
  constructor
  · change nodePathIndex n ((preorderNodePath n j).take i.val) < j.val
    rw [← nodePathIndex_preorderNodePath n j]
    conv_rhs => rw [← hsplit]
    apply nodePathIndex_proper_prefix n _ _ _ hdrop
    rw [hsplit]
    exact preorderNodePath_length n j
  · rw [ancestorNodeIndex_path, List.length_take, min_eq_left (Nat.le_of_lt i.isLt)]
    exact i.isLt

/-- The selected ancestors are genuine prefixes. Fixed label products and
which prefixes enter each coefficient may vary with the actual node. -/
noncomputable def treeAncestorScheme (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (CL CR : List Bool → ℤ)
    (AL AR : (p : List Bool) → Finset (Fin p.length)) : PivotDependencyScheme (2 ^ n - 1) where
  frequencies j := singleTreeNodeFrequencies S n t j.val
  depth j := (preorderNodePath n j).length
  fixedLeft j := CL (preorderNodePath n j)
  fixedRight j := CR (preorderNodePath n j)
  ancestorsLeft j := (AL (preorderNodePath n j)).image (ancestorNodeIndex n j)
  ancestorsRight j := (AR (preorderNodePath n j)).image (ancestorNodeIndex n j)
  earlierLeft j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a
  earlierRight j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryGiantSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two current giants refer only to previously reconstructed pivots -/

namespace Ostmann

open scoped Classical

def evolveGiantSources : ℕ → HistoryGiantSource × HistoryGiantSource → List Bool →
    HistoryGiantSource × HistoryGiantSource
  | _, g, [] => g
  | d, g, b :: path => evolveGiantSources (d + 1) (.ancestor d, if b then g.2 else g.1) path

theorem evolveGiantSources_known (d : ℕ) (g : HistoryGiantSource × HistoryGiantSource)
    (hg : g.1.knownBefore d ∧ g.2.knownBefore d) (path : List Bool) :
    (evolveGiantSources d g path).1.knownBefore (d + path.length) ∧
      (evolveGiantSources d g path).2.knownBefore (d + path.length) := by
  induction path generalizing d g with
  | nil => exact hg
  | cons b path ih =>
    have hs : (.ancestor d : HistoryGiantSource).knownBefore (d + 1) ∧
        (if b then g.2 else g.1).knownBefore (d + 1) := by
      constructor
      · exact Nat.lt_succ_self d
      · cases b <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
        · cases h : g.1 with
          | fixed c => trivial
          | ancestor i =>
            have hi : i < d := by simpa only [h, HistoryGiantSource.knownBefore] using hg.1
            exact hi.trans (Nat.lt_succ_self d)
        · cases h : g.2 with
          | fixed c => trivial
          | ancestor i =>
            have hi : i < d := by simpa only [h, HistoryGiantSource.knownBefore] using hg.2
            exact hi.trans (Nat.lt_succ_self d)
    simpa only [evolveGiantSources, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
      ih (d + 1) (.ancestor d, if b then g.2 else g.1) hs

def historyGiantSources (XL XR : ℤ) (path : List Bool) : HistoryGiantSource × HistoryGiantSource :=
  evolveGiantSources 0 (.fixed XL, .fixed XR) path

theorem historyGiantSources_known (XL XR : ℤ) (path : List Bool) :
    (historyGiantSources XL XR path).1.knownBefore path.length ∧
      (historyGiantSources XL XR path).2.knownBefore path.length := by
  simpa only [historyGiantSources, Nat.zero_add] using
    evolveGiantSources_known 0 (.fixed XL, .fixed XR) ⟨trivial, trivial⟩ path

noncomputable def forwardTreeAncestorScheme (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (XL XR : ℤ) (CL CR : List Bool → ℤ) : PivotDependencyScheme (2 ^ n - 1) :=
  treeAncestorScheme S n t
    (fun path => CR path * (historyGiantSources XL XR path).2.fixedFactor)
    (fun path => CL path * (historyGiantSources XL XR path).1.fixedFactor)
    (fun path => (historyGiantSources XL XR path).2.ancestorLevels path
      (historyGiantSources_known XL XR path).2)
    (fun path => (historyGiantSources XL XR path).1.ancestorLevels path
      (historyGiantSources_known XL XR path).1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomSourceDescent
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual reverse paths with freshly indexed ancestor pivot sources -/

namespace Ostmann
open scoped Classical

noncomputable def advanceNatAtomSources {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ) :
    CopyScheduleAtoms role n → B ⊕ ℕ := reverseCopyLabelMap role n b (.inr d) source

theorem advanceNatAtomSources_before {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ)
    (hs : ∀ v, AtomSourceBefore d (source v)) :
    ∀ v, AtomSourceBefore (d + 1) (advanceNatAtomSources role n d b source v) := by
  intro v
  unfold advanceNatAtomSources reverseCopyLabelMap
  split_ifs
  · exact (hs _).mono (Nat.le_succ d)
  · exact Nat.lt_succ_self d
  · exact (hs _).mono (Nat.le_succ d)

/-- The first entry of the path is the root branch. Source indices count
the previously reconstructed pivots in root-to-leaf order. -/
noncomputable def descendAtomSources {I B : Type*} (role : I → CopyScheduleRole) :
    (h n d : ℕ) → (Fin h → Bool) → (CopyScheduleAtoms role (n + h) → B ⊕ ℕ) →
      CopyScheduleAtoms role n → B ⊕ ℕ
  | 0, _, _, _, source => source
  | h + 1, n, d, path, source =>
    descendAtomSources role h n (d + 1) (Fin.tail path)
      (advanceNatAtomSources role (n + h) d (path 0) source)

theorem descendAtomSources_before {I B : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (hs : ∀ v, AtomSourceBefore d (source v)) :
    ∀ v, AtomSourceBefore (d + h) (descendAtomSources role h n d path source v) := by
  induction h generalizing d with
  | zero => exact hs
  | succ h ih =>
    have hp := ih (d + 1) (Fin.tail path) _
      (advanceNatAtomSources_before role (n + h) d (path 0) source hs)
    intro v
    exact (hp v).mono (by omega)

noncomputable def descendAtomValues {I A : Type*} (role : I → CopyScheduleRole) :
    (h n d : ℕ) → (Fin h → Bool) → (ℕ → A) → (CopyScheduleAtoms role (n + h) → A) →
      CopyScheduleAtoms role n → A
  | 0, _, _, _, _, current => current
  | h + 1, n, d, path, p, current =>
    descendAtomValues role h n (d + 1) (Fin.tail path) p
      (reverseCopyLabelMap role (n + h) (path 0) (p d) current)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ancestor-source environments at every scheduled tree node -/

namespace Ostmann
open scoped Classical

noncomputable def boundAtomSources {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (a : A) : B ⊕ Fin d :=
  match h : source a with
  | .inl b => .inl b
  | .inr j => .inr ⟨j, by simpa only [h, AtomSourceBefore] using hs a⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkFrames
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed nonbulk factors and literal bulk products at each moving node -/

namespace Ostmann
open scoped Classical

/-- These factors are computed from the fixed small and internal samples;
no bulk coordinate or giant value is used. -/
def movingFrameConstants {σ : Type*} (value : σ → ℕ) :
    (n : ℕ) → TreeLeafTuple (List σ) n → MovingSampleSlots σ n →
      List Bool → MovingFrameConstants
  | 0, _, .leaf, _ => ⟨1, 1, 1⟩
  | n + 1, small, .node a l r, path =>
      let u := movingCompensationSlots n a
      match path with
      | [] => ⟨MovingSlotReversal.naturalProduct value (flattenMovingSlots n small.1),
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n small.2),
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)⟩
      | false :: path => movingFrameConstants value n (appendMovingSlotLeaves n u small.1) l path
      | true :: path => movingFrameConstants value n (appendMovingSlotLeaves n u small.2) r path

/-- The two child bulk products in the same root-to-node order. -/
def movingBulkProducts {σ : Type*} (value : σ → ℕ) :
    (n : ℕ) → TreeLeafTuple (List σ) n → List Bool → ℕ × ℕ
  | 0, _, _ => (1, 1)
  | n + 1, bulk, [] =>
      (MovingSlotReversal.naturalProduct value (flattenMovingSlots n bulk.1),
        MovingSlotReversal.naturalProduct value (flattenMovingSlots n bulk.2))
  | n + 1, bulk, false :: path => movingBulkProducts value n bulk.1 path
  | n + 1, bulk, true :: path => movingBulkProducts value n bulk.2 path

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensatedEquations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

def movingSampleCompensation {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (j : Fin (2 ^ n - 1)) : ℤ :=
  (movingFrameConstants value n small a (preorderNodePath n j)).compensation

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original independent compensation samples

Section 7.4, equations (7.10)--(7.11), samples one compensation vector at
each node. That vector is shared by its two children; samples subsequently
made in the children are independent. These are the literal finite priors,
before any distinctness or equality-pattern restriction.
-/

namespace Ostmann
open scoped Classical BigOperators

def movingSampleNodeEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple (Fin 4 → A) n × MovingSampleSlots A n × MovingSampleSlots A n ≃
      MovingSampleSlots A (n + 1) where
  toFun x := .node x.1 x.2.1 x.2.2
  invFun x := match x with | .node a l r => (a, l, r)
  left_inv _ := rfl
  right_inv x := by cases x; rfl

def movingSampleZeroEquiv (A : Type*) : Unit ≃ MovingSampleSlots A 0 where
  toFun _ := .leaf
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := by cases x; rfl

noncomputable instance movingSampleSlotsFintype (A : Type*) [Fintype A] :
    (n : ℕ) → Fintype (MovingSampleSlots A n)
  | 0 => Fintype.ofEquiv Unit (movingSampleZeroEquiv A)
  | n + 1 => @Fintype.ofEquiv _ _
      (@instFintypeProd _ _ (treeLeafTupleFintype (Fin 4 → A) n)
        (@instFintypeProd _ _ (movingSampleSlotsFintype A n) (movingSampleSlotsFintype A n)))
      (movingSampleNodeEquiv A n)

noncomputable def movingCompensationPrior {A : Type*} (μ : A → ℝ) :
    (n : ℕ) → TreeLeafTuple (Fin 4 → A) n → ℝ
  | 0, a => ∏ i : Fin 4, μ (a i)
  | n + 1, a => movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2

noncomputable def movingSamplesPrior {A : Type*} (μ : ℕ → A → ℝ) :
    {n : ℕ} → MovingSampleSlots A n → ℝ
  | _, .leaf => 1
  | n + 1, .node a l r =>
      movingCompensationPrior (μ n) n a * movingSamplesPrior μ l * movingSamplesPrior μ r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledRecursion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

/-- Original node factors depend on the current prime lists, two giants and
complete frequency tree, not on prime samples which will be made later. -/
noncomputable def movingLocalExtra {σ : Type*}
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  E ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ s v w

/-- The finite expansion keeps every internal sample's original prior. -/
noncomputable def movingSampledWeight {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingLocalSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) : Prop :=
  (x.data.currentSlots value x.leftGiant x.rightGiant ++ outside).Pairwise Nat.Coprime ∧
    movingLocalGiantUnits value outside x.data x.leftGiant x.rightGiant

noncomputable def movingGuardedLeaf {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  if movingLocalSupport value outside x then F x s else 0

noncomputable def movingGuardedExtra {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  if movingLocalSupport value outside x then E x s v w else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedArithmeticSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining a bounded integrand in the arithmetic support sum -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def arithmeticLeafSupport {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : ℝ :=
  sequentialSupport
    (fun past y => arithmeticPairSplitTest (data (treeLeafProduct n x) past) y) []
    (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CompensatedPairSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired adaptive support on the same original bulk variables -/

namespace Ostmann
open scoped Classical

def pairArithmeticData {Q : ℕ} (d e : Option (ArithmeticSplitData Q)) :
    Option (ArithmeticSplitData Q × ArithmeticSplitData Q) :=
  match d, e with
  | some d, some e => some (d, e)
  | _, _ => none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularAdaptiveCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive coefficients for the frequency-only arithmetic model -/

namespace Ostmann

open scoped Classical

/-- Choose any valid completion of the exposed prefix. The precision theorem
below proves that the required reduced coefficients do not depend on it. -/
noncomputable def modularAdaptiveCoefficients (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ) : ZMod (R ^ (k + 2)) × ZMod (R ^ (k + 2)) :=
  if hj : past.length < 2 ^ n - 1 then
    if h : ∃ a : SampledPivotHistory n (R ^ (k + 2)), a.modularValid D R k U ∧ a.matches total past then
      let a := Classical.choose h
      (D.leftCoefficient a.pivots ⟨past.length, hj⟩,
        D.rightCoefficient a.pivots ⟨past.length, hj⟩)
    else (0, 0)
  else (0, 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularAdaptiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-congruence histories pass the adaptive split tests -/

namespace Ostmann

open scoped Classical

noncomputable def modularAdaptiveResidueSplit (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) : ArithmeticResidueSplit (R ^ (k + 2)) where
  frequencies := D.frequencies ⟨past.length, hj⟩
  frequency_ne_zero := hs _
  frequency_dvd := (hsR _).trans (dvd_pow_self R (by omega))
  leftFactor := (modularAdaptiveCoefficients n R k D U total past).1
  rightFactor := (modularAdaptiveCoefficients n R k D U total past).2
  parentProduct := splitPrefixParent n total past

noncomputable def modularAdaptiveData (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (k + 2))) :=
  if hj : past.length < 2 ^ n - 1 then
    (modularAdaptiveResidueSplit n R k D U hs hsR total past hj).toData
  else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

def frequencyModelAtPath {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    (n : ℕ) → MovingSlotData σ n → ℤ → ℤ → List Bool → FrequencyModelState σ
  | 0, T, x, y, _ => ⟨0, T, x, y⟩
  | n + 1, T@(.node s CL CR U l r), x, y, path =>
      match path with
      | [] => ⟨n + 1, T, x, y⟩
      | b :: path =>
          let p := (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y
          if b then frequencyModelAtPath value R n r p y path
          else frequencyModelAtPath value R n l p x path

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed factors and ancestor coefficients of the frequency model -/

namespace Ostmann
open scoped Classical

def frequencyModelPivots {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (j : Fin (2 ^ n - 1)) : ℤ :=
  (frequencyModelAtPath value R n T x y (preorderNodePath n j)).pivot value R

noncomputable def frequencyModelAncestorScheme {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ) :
    PivotDependencyScheme (2 ^ n - 1) :=
  forwardTreeAncestorScheme S n t x y
    (fun path => (movingFrameConstants value n small a path).leftSmall)
    (fun path => (movingFrameConstants value n small a path).rightSmall)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelAdaptiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed split support for the arithmetic frequency gate -/

namespace Ostmann
open scoped Classical

noncomputable def frequencyModelHistory {σ : Type*} (value : σ → ℕ)
    (R : ℕ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z) :
    SampledPivotHistory n (R ^ (n - 1 + 2)) where
  bulk := treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)
  residue := z
  pivots := frequencyModelPivots value R n (buildMovingSlotData n t small bulk a) x y
  compatible := hz

noncomputable def frequencyModelAdaptiveData {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ) :
    (ZMod (R ^ (n - 1 + 2)))ˣ → List (ZMod (R ^ (n - 1 + 2)))ˣ →
      Option (ArithmeticSplitData (R ^ (n - 1 + 2))) :=
  modularAdaptiveData n R (n - 1)
    (frequencyModelAncestorScheme value S n t small a x y)
    (movingSampleCompensation value n small a)
    (fun i => hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt))
    hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairedFrequencyProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual frequency histories inside a paired tree -/

namespace Ostmann
open scoped Classical

def frequencyPairProjection (S : Finset ℤ) (n : ℕ) (b : Bool)
    (t : FrequencyTree (S × S) n) : FrequencyTree S n :=
  frequencyTreeMap (fun p => if b then p.2 else p.1) n t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelPairSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired support for the two actual arithmetic frequency gates -/

namespace Ostmann
open scoped Classical

noncomputable def frequencyModelPairData {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (n - 1 + 2)) × ArithmeticSplitData (R ^ (n - 1 + 2))) :=
  pairArithmeticData
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n false t)
      hS (hR false) (small false) (a false) x y total past)
    (frequencyModelAdaptiveData value S n R (frequencyPairProjection S n true t)
      hS (hR true) (small true) (a true) x y total past)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeOccurrences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous occurrences of one actual internal prime in both histories -/

namespace Ostmann
open scoped Classical BigOperators

def movingPrimeOccurrence {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (j : MovingPrimeOccurrences value T p) : MovingSlotOccurrence σ :=
  (T j.1).occurrences.get j.2.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

def movingSampleCoordinates (A : Type*) : (n : ℕ) →
    MovingSampleSlots A n ≃ (MovingSampleIndex n → A)
  | 0 =>
      { toFun := fun _ i => Empty.elim i
        invFun := fun _ => .leaf
        left_inv := fun a => by cases a; rfl
        right_inv := fun a => by funext i; exact Empty.elim i }
  | n + 1 =>
      { toFun := fun a => match a with
          | .node u l r => fun i => match i with
              | .inl (t, j) => treeLeafTupleEquiv (Fin 4 → A) n u t j
              | .inr (true, i) => movingSampleCoordinates A n l i
              | .inr (false, i) => movingSampleCoordinates A n r i
        invFun := fun a => .node
          ((treeLeafTupleEquiv (Fin 4 → A) n).symm (fun t j => a (.inl (t, j))))
          ((movingSampleCoordinates A n).symm (fun i => a (.inr (true, i))))
          ((movingSampleCoordinates A n).symm (fun i => a (.inr (false, i))))
        left_inv := by
          intro a
          cases a with
          | node u l r =>
              simp only [Equiv.symm_apply_apply]
        right_inv := by
          intro a
          funext i
          rcases i with ⟨t, j⟩ | ⟨b, i⟩
          · exact congrFun (congrFun ((treeLeafTupleEquiv (Fin 4 → A) n).apply_symm_apply
                (fun t j => a (.inl (t, j)))) t) j
          · cases b <;> exact congrFun ((movingSampleCoordinates A n).apply_symm_apply _) i }

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact compensation factors in the original history weight

Every sampled prime occurs once in the factor `u` at the node where it is
sampled. Its subsequent appearances in descendants do not add factors of `u`.
-/

namespace Ostmann
open scoped Classical BigOperators

def movingSampleProduct {A : Type*} (value : A → ℕ) :
    {n : ℕ} → MovingSampleSlots A n → ℕ
  | _, .leaf => 1
  | n + 1, .node u l r =>
      MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n u)) *
        movingSampleProduct value l * movingSampleProduct value r

noncomputable def movingCompensationExtra {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ
  | _, .leaf _ _, _, _, _ => 1
  | _, .node _ _ _ u _ _, _, _, _ => MovingSlotReversal.naturalProduct value u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality patterns of the two actual internal sample trees -/

namespace Ostmann
open scoped Classical BigOperators

def movingSamplePairCoordinates (A : Type*) (n : ℕ) :
    (MovingSampleSlots A n × MovingSampleSlots A n) ≃ (Bool × MovingSampleIndex n → A) where
  toFun a i := if i.1 then movingSampleCoordinates A n a.2 i.2
    else movingSampleCoordinates A n a.1 i.2
  invFun x := ((movingSampleCoordinates A n).symm (fun i => x (false, i)),
    (movingSampleCoordinates A n).symm (fun i => x (true, i)))
  left_inv a := by
    rcases a with ⟨l, r⟩
    simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    rcases i with ⟨b, i⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Equiv.apply_symm_apply]

@[simp] theorem movingSamplePairCoordinates_left {A : Type*} (n : ℕ)
    (x : Bool × MovingSampleIndex n → A) (i : MovingSampleIndex n) :
    movingSampleCoordinates A n ((movingSamplePairCoordinates A n).symm x).1 i = x (false, i) := by
  exact congrFun ((movingSampleCoordinates A n).apply_symm_apply (fun i => x (false, i))) i

@[simp] theorem movingSamplePairCoordinates_right {A : Type*} (n : ℕ)
    (x : Bool × MovingSampleIndex n → A) (i : MovingSampleIndex n) :
    movingSampleCoordinates A n ((movingSamplePairCoordinates A n).symm x).2 i = x (true, i) := by
  exact congrFun ((movingSampleCoordinates A n).apply_symm_apply (fun i => x (true, i))) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinateLevels
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tier separation for the original indexed sample tree -/

namespace Ostmann
open scoped Classical

theorem movingCompensationSlots_forall {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (P : A → Prop)
    (h : ∀ t j, P (treeLeafTupleEquiv (Fin 4 → A) n a t j)) :
    ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n a), P i := by
  induction n with
  | zero =>
      intro i hi
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact h () j
  | succ n ih =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact ih a.1 (fun t j => h (.inl t) j) i hi
      · exact ih a.2 (fun t j => h (.inr t) j) i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleMap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem flattenMovingSlots_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple (List A) n) :
    flattenMovingSlots n (treeLeafMap (List.map f) n a) = (flattenMovingSlots n a).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [treeLeafMap, flattenMovingSlots, List.map_append, ih]

theorem appendMovingSlotLeaves_map {A B : Type*} (f : A → B) (n : ℕ)
    (a b : TreeLeafTuple (List A) n) :
    treeLeafMap (List.map f) n (appendMovingSlotLeaves n a b) =
      appendMovingSlotLeaves n (treeLeafMap (List.map f) n a) (treeLeafMap (List.map f) n b) := by
  induction n with
  | zero => exact List.map_append
  | succ n ih => exact Prod.ext (ih a.1 b.1) (ih a.2 b.2)

theorem movingCompensationSlots_map {A B : Type*} (f : A → B) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationSlots n (treeLeafMap (fun a : Fin 4 → A => f ∘ a) n a) =
      treeLeafMap (List.map f) n (movingCompensationSlots n a) := by
  induction n with
  | zero => exact List.map_ofFn.symm
  | succ n ih => exact Prod.ext (ih a.1) (ih a.2)

theorem buildMovingSlotData_map {A B : Type*} (f : A → B) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List A) n) (a : MovingSampleSlots A n) :
    (buildMovingSlotData n t small bulk a).map f =
      buildMovingSlotData n t (treeLeafMap (List.map f) n small)
        (treeLeafMap (List.map f) n bulk) (a.map f) := by
  induction a with
  | leaf => exact congrArg (MovingSlotData.leaf t) List.map_append
  | node u l r hl hr =>
      simp only [buildMovingSlotData, MovingSlotData.map, MovingSampleSlots.map,
        treeLeafMap, movingCompensationSlots_map, flattenMovingSlots_map,
        List.map_append, hl, hr, appendMovingSlotLeaves_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleOccurrence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual occurrence for every internal sample class -/

namespace Ostmann
open scoped Classical

theorem movingCompensationSlots_mem {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (t : TreeLeafIndex n) (j : Fin 4) :
    treeLeafTupleEquiv (Fin 4 → A) n a t j ∈
      flattenMovingSlots n (movingCompensationSlots n a) := by
  induction n with
  | zero => exact List.mem_ofFn.mpr ⟨j, rfl⟩
  | succ n ih =>
    cases t with
    | inl t => exact List.mem_append_left _ (ih a.1 t)
    | inr t => exact List.mem_append_right _ (ih a.2 t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern pair in selected bulk coordinates -/

namespace Ostmann
open scoped Classical

theorem bulkSlotLeaves_map {A B : Type*} (f : A → B) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    treeLeafMap (List.map f) n (bulkSlotLeaves n m slot) =
      bulkSlotLeaves n m (f ∘ slot) := by
  apply (treeLeafTupleEquiv (List B) n).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn, Function.comp_def]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A modulus using only the frequencies of the two fixed histories -/

namespace Ostmann
open scoped Classical

def frequencyModelBase (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n) : ℕ :=
  historyFrequencyProduct S n (frequencyPairProjection S n false t) *
    historyFrequencyProduct S n (frequencyPairProjection S n true t)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def residueVariance {p : ℕ} (S : Finset (ZMod p)) : ℝ :=
  residueDensity S * (1 - residueDensity S)

noncomputable def normalizedResidueIndicator {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  ((centeredDensity S x / Real.sqrt (residueVariance S) : ℝ) : ℂ)

noncomputable def normalizedResidueTransform {p : ℕ} [NeZero p] (S : Finset (ZMod p)) : ZMod p → ℂ :=
  densityFourier (normalizedResidueIndicator S)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExternalSquareFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disintegration into the two giant prime-square lift fibers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def externalSquareFiberEquiv (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) :
    {w : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ //
      externalResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)) w = z} ≃
      SquareLiftPairs p z.1 (z.2 : ZMod p) where
  toFun w :=
    (⟨w.1.1, congrArg Prod.fst w.2⟩,
      ⟨w.1.2, congrArg (fun t : ZMod p × (ZMod p)ˣ => (t.2 : ZMod p)) w.2⟩)
  invFun v := by
    have hred : squareReduction p (v.2 : ZMod (p ^ 2)) ≠ 0 := by
      rw [v.2.property]
      exact Units.ne_zero z.2
    let hu := (isUnit_square_iff (v.2 : ZMod (p ^ 2))).mpr hred
    refine ⟨(v.1, hu.unit), ?_⟩
    apply Prod.ext
    · exact v.1.property
    · apply Units.ext
      change squareReduction p (hu.unit : ZMod (p ^ 2)) = (z.2 : ZMod p)
      rw [IsUnit.unit_spec]
      exact v.2.property
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Units.ext
      exact IsUnit.unit_spec _
  right_inv v := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp only
      exact IsUnit.unit_spec _

noncomputable def externalSquareDecompose (p : ℕ) [Fact p.Prime] :
    (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) ≃
      Σ z : ZMod p × (ZMod p)ˣ, SquareLiftPairs p z.1 (z.2 : ZMod p) :=
  (Equiv.sigmaFiberEquiv (externalResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)))).symm.trans
    (Equiv.sigmaCongrRight (externalSquareFiberEquiv p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

/-- One frequency block, one square for each distinct internal prime, and
one field for each spectator. -/
def movingArithmeticModuli {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) : MovingArithmeticBlocks P S → ℕ
  | .inl _ => r
  | .inr (.inl p) => p.val ^ 2
  | .inr (.inr i) => q i.val

noncomputable def movingArithmeticLocalFactor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) (P : Finset ℕ) (S : Finset I) :
    (b : MovingArithmeticBlocks P S) →
      ZMod (movingArithmeticModuli r q P S b) × (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ
  | .inl _, z => movingFrequencyPairFactor value outside F E T nodes R
      z.1.val (show (ZMod r)ˣ from z.2).val.val
  | .inr (.inl p), z => movingInternalPairFactor value T p.val z.1 (show (ZMod (p.val ^ 2))ˣ from z.2).val
  | .inr (.inr i), z => movingSpectatorPairFactor value (q i.val) (g i.val)
      (fun side => D side i.val) T z.1 (show (ZMod (q i.val))ˣ from z.2).val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spectator Haar factor as a fixed function of the bulk residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {σ : Type*} {q : ℕ} [Fact q.Prime]
  (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
  (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))

noncomputable def frozenBulkSpectatorPair (g : ZMod q → ℂ)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℂ :=
  movingFieldGiantAmplitude g (D false)
    (buildMovingGiantTree n (t false) (movingSlotValues base n (small false))
      ((samples false).values base)) a.1 a.2
    ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)) *
  conj (movingFieldGiantAmplitude g (D true)
    (buildMovingGiantTree n (t true) (movingSlotValues base n (small true))
      ((samples true).values base)) a.1 a.2
    ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct (z ∘ e.symm))))

noncomputable def frozenBulkSpectatorHaar (g : ZMod q → ℂ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℂ :=
  ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
    ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ a, frozenBulkSpectatorPair base n m t small samples D e g a z)

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPrimeGuardedAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-prior expectation with every constituent-prime guard -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentPrimeGuardedAmplitude {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) : ℂ :=
  ∑ q : SurvivingConstituent role size n → P,
    ((∏ i, scheduledRolePrior (fun i : Σ a, Fin (size a) => role i.1)
      (fun j => primeSubsetPrior P (Q j)) n i (q i) : ℝ) : ℂ) *
    ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
      (hist d) * (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
        scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
          χ κ pivot n (hist d) P hP q center else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentGuardedNext
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The guarded next expectation is the actual arithmetic off-diagonal -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def copiedConstituentHistory {D : Type*} {n : ℕ}
    (hist : D → FrequencyTree ℤ n) (V : ℕ) :
    (transferFrequencyRange V) × (D × D) → FrequencyTree ℤ (n + 1) :=
  fun a => (a.1.val, hist a.2.1, hist a.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite frequency histories with the actual cutoff at every level -/

namespace Ostmann

open scoped Classical

noncomputable instance scheduledFrequencyIndexFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (ScheduledFrequencyIndex V n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (transferFrequencyRange (V 0)))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((transferFrequencyRange (V (n + 1))) ×
      (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

def frequencyTreeInFinset (S : Finset ℤ) : (n : ℕ) → (t : FrequencyTree ℤ n) →
    (∀ s ∈ allFrequencyList n t, s ∈ S) → FrequencyTree S n
  | 0, t, h => ⟨t, h t (by simp [allFrequencyList])⟩
  | n + 1, t, h =>
    (⟨t.1, h t.1 (List.mem_cons_self ..)⟩,
      frequencyTreeInFinset S n t.2.1
        (fun s hs => h s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))),
      frequencyTreeInFinset S n t.2.2
        (fun s hs => h s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))))

theorem frequencyTreeInFinset_map (S : Finset ℤ) (n : ℕ) (t : FrequencyTree ℤ n)
    (h : ∀ s ∈ allFrequencyList n t, s ∈ S) :
    frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n t h) = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with ⟨s, l, r⟩
    change (s, frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n l _),
      frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n r _)) = (s, l, r)
    exact congrArg₂ (fun l r => (s, l, r)) (ih _ _) (ih _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PairedScheduledHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original scheduled histories as one paired frequency tree -/

namespace Ostmann
open scoped Classical BigOperators

def pairFrequencyTrees (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree S n → FrequencyTree S n → FrequencyTree (S × S) n
  | 0, a, b => (a, b)
  | n + 1, a, b => ((a.1, b.1), pairFrequencyTrees S n a.2.1 b.2.1,
      pairFrequencyTrees S n a.2.2 b.2.2)

theorem frequencyPairProjection_pair (S : Finset ℤ) (n : ℕ)
    (a b : FrequencyTree S n) (side : Bool) :
    frequencyPairProjection S n side (pairFrequencyTrees S n a b) = if side then b else a := by
  induction n with
  | zero => cases side <;> rfl
  | succ n ih =>
    change ((if side then b.1 else a.1),
      frequencyPairProjection S n side (pairFrequencyTrees S n a.2.1 b.2.1),
      frequencyPairProjection S n side (pairFrequencyTrees S n a.2.2 b.2.2)) = _
    rw [ih, ih]
    cases side <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingCompensatedExtra {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ :=
  (x.compensation value : ℝ) * E x s v w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingCompensatedAverage {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H : MovingSampleSlots A n → ℂ) : ℂ :=
  ∑ a, (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) * H a

noncomputable def movingSupportedSampledWeight {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) : ℂ :=
  movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
    (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
    n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalSampleExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalNode {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    MovingSlotState σ → ℤ → ℤ → ℤ → ℝ :=
  movingPhiExtra value childBound pivotBound (fun _ _ _ _ => 1) φ G

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable instance movingDescendantFrequencyIndexFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (MovingDescendantFrequencyIndex V n) := by
  cases n <;> dsimp only [MovingDescendantFrequencyIndex] <;> infer_instance

noncomputable def movingRootedFrequencyTree (V : ℕ → ℕ) :
    (n : ℕ) → ℤ → MovingDescendantFrequencyIndex V n → FrequencyTree ℤ n
  | 0, s, _ => s
  | n + 1, s, t => (s, scheduledFrequencyHistory V n t.1, scheduledFrequencyHistory V n t.2)

/-- This is the current coefficient after the original internal prime samples
and all descendant frequencies have been summed. Root guards remain in each
term and are never turned into a conditioned probability law. -/
noncomputable def movingFrequencyCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) : ℂ :=
  ∑ t : MovingDescendantFrequencyIndex V n,
    movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n
      (movingRootedFrequencyTree V n s t) small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original root, prime and integer average as one finite positive law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def mixedExternalPrior {B A : Type*} [Fintype B]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (x : MixedExternalPoint B A N u v r w) : ℝ :=
  (∏ b, ν b (x.2.1 b)) *
    (if (x.2.2.1.val).Prime then (x.2.2.1.val : ℝ)⁻¹ else 0) *
      integerResidueAtom 1 0 center x.2.2.2.val

noncomputable def mixedExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z =>
      complexIntegerInterval 1 0 u v center (fun x => F s.val y x z))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting actual overlap graphs along a leaf enumeration -/

namespace Ostmann

noncomputable def arrangementGraphReindex {L L' : Type*} (f : L ≃ L') {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) :
    arrangementGraph m e ≃g arrangementGraph m (reindexArrangement f e) where
  toEquiv := f.sumCongr f
  map_rel_iff' := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b => rfl
      | inr b =>
        change (∃ i j, reindexArrangement f e (f a, i) = (f b, j)) ↔
          ∃ i j, e (a, i) = (b, j)
        simp only [reindexArrangement_eq_iff]
    | inr b =>
      cases y with
      | inl a =>
        change (∃ i j, reindexArrangement f e (f a, i) = (f b, j)) ↔
          ∃ i j, e (a, i) = (b, j)
        simp only [reindexArrangement_eq_iff]
      | inr a => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedBulkSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetrization of the original mixed law, with bad pairs paid by energy -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def mixedBulkSymmetrize {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (s : ℤ) (y : B → A) (x z : ℝ) : ℂ :=
  finiteFamilyAverage (fun e : Equiv.Perm (TreeLeafIndex n × Fin m) =>
    fun _ : Unit => F s (selectedBulkSample slot e⁻¹ y) x z) ()

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original mixed arithmetic statistic and its symmetrized upper bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingExternalRegularFactor {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (y : B → σ) (x z : ℝ) : ℂ :=
  primeProductTransform greg (outside.prod * ⌊Real.exp x⌋₊ * ⌊Real.exp z⌋₊)
    (MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk)) s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def densityFourierInverse {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (x : ZMod p) : ℂ := densityFourier g (-x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateSmall (n r m : ℕ) : TreeLeafTuple (List (MovingRegularSlot n r m)) n :=
  bulkSlotLeaves n r (fun j => (j.1, .inl j.2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInitialPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial Poisson phase is the initial phase of the actual schedule -/

namespace Ostmann

open scoped Classical

def initialSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) :
    I ≃ {i : CopyScheduleVertex I 0 // CopyScheduleSurvives role 0 i} where
  toFun i := ⟨i, trivial⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem initialSurvivorPrimeFact {I : Type*} (role : I → CopyScheduleRole)
    (p : I → ℕ) [hp : ∀ i, Fact (p i).Prime] :
    ∀ i : {j : CopyScheduleVertex I 0 // CopyScheduleSurvives role 0 j}, Fact (p i.val).Prime :=
  fun i => hp i.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialConstituentPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fully guarded initial constituent coefficient is the Poisson sum -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def scheduleFourierLeaf {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) :
    ScheduleAtomState role → ℤ → ℂ :=
  fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
    normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentAmplitudeEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A direct finite-frequency energy bound for the actual final amplitude -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def constituentPrimeCoefficient {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (q : SurvivingConstituent role size n → P) : ℂ :=
  ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
    (hist d) * (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
        χ κ pivot n (hist d) P hP q center else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One original word-prime coordinate at each arithmetic tree leaf -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafSlot_left {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (wordLeafSlot role i hi (n + 1) (.inl t)).val =
      .inl (true, (wordLeafSlot role i hi n t).val) := by
  exact copySchedulePath_snoc _ _ _

theorem wordLeafSlot_right {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (wordLeafSlot role i hi (n + 1) (.inr t)).val =
      .inl (false, (wordLeafSlot role i hi n t).val) := by
  exact copySchedulePath_snoc _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected prime products in the two actual H branches -/

namespace Ostmann
open scoped BigOperators Classical

/-- Every other H coordinate is among the primes held fixed in the
conditional leaf expectation, including the currently sampled pivot groups. -/
noncomputable def copiedWordLeafOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (h : WordLeafHOutside role i hi n) : WordLeafOutside role i hi (n + 1) :=
  ⟨⟨.inl (b, h.val.val), h.val.property⟩, by
    rintro ⟨t, ht⟩
    apply h.property
    cases t with
    | inl t =>
      have he : Sum.inl (true, (wordLeafSlot role i hi n t).val) =
          (Sum.inl (b, h.val.val) : CopyScheduleVertex I (n + 1)) :=
        (wordLeafSlot_left role i hi n t).symm.trans (congrArg Subtype.val ht)
      exact ⟨t, Subtype.ext (congrArg Prod.snd (Sum.inl.inj he))⟩
    | inr t =>
      have he : Sum.inl (false, (wordLeafSlot role i hi n t).val) =
          (Sum.inl (b, h.val.val) : CopyScheduleVertex I (n + 1)) :=
        (wordLeafSlot_right role i hi n t).symm.trans (congrArg Subtype.val ht)
      exact ⟨t, Subtype.ext (congrArg Prod.snd (Sum.inl.inj he))⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScaledWordLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected prime factors through every actual ancestor substitution -/

namespace Ostmann
open scoped BigOperators Classical

def descendLeafValues {A : Type*} : (h n : ℕ) → (Fin h → Bool) →
    (TreeLeafIndex (n + h) → A) → TreeLeafIndex n → A
  | 0, _, _, x => x
  | h + 1, n, path, x => descendLeafValues h n (Fin.tail path)
      (fun t => x (if path 0 then .inl t else .inr t))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NodeBulkProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

def childProductsAtPath {G : Type*} [CommMonoid G] :
    (n : ℕ) → TreeLeafTuple G n → List Bool → G × G
  | 0, _, _ => (1, 1)
  | n + 1, x, [] => (treeLeafProduct n x.1, treeLeafProduct n x.2)
  | n + 1, x, b :: path =>
      if b then childProductsAtPath n x.2 path else childProductsAtPath n x.1 path

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original coefficient on the complete regular-slot template -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) : ℂ :=
  movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
    (treeLeafMap (List.map y) n (movingTemplateSmall n r m))
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal regular template and its full Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateSlotList (n r m : ℕ) : List (MovingRegularSlot n r m) :=
  flattenMovingSlots n (movingTemplateSmall n r m) ++
    flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))

theorem mem_movingTemplateSlotList (n r m : ℕ) (i : MovingRegularSlot n r m) :
    i ∈ movingTemplateSlotList n r m := by
  rcases i with ⟨j, i | i⟩
  · apply List.mem_append_left
    exact (mem_flatten_bulkSlotLeaves n r _ _).mpr ⟨(j, i), rfl⟩
  · apply List.mem_append_right
    exact (mem_flatten_bulkSlotLeaves n m _ _).mpr ⟨(j, i), rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAveragedIntegerNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the forced integer node under the surviving regular law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateIntegerFourierTerm {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (I : Finset ℕ)
    (XL XR : ℕ) (s : ℤ) (left right : MovingRegularSlot n r m → σ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (u : TreeLeafIndex n × Fin 4 → σ) (v w : ℤ) : ℂ :=
  let LH := XL * ∏ i, value (left i)
  let RH := XR * ∏ i, value (right i)
  let p := reconstructedPivot (v * RH - w * LH) (s * ∏ i, value (u i))
  if validTransferredPivot I (v * RH - w * LH) (s * ∏ i, value (u i)) then
    (φ (Real.log p - G (n + 1)) : ℂ) *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v
        (movingRestoreSample n r m u left) p XL *
      star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR) *
      movingTaggedTransform
        (Sum.elim (movingOneGiantModuli XL (value ∘ left))
          (movingOneGiantModuli XR (value ∘ right)))
        (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
          (Sum.elim (fun _ : Unit => true) (fun _ => false)))
        greg ggiant favorable outside.prod s
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateWeightedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original external weight multiplying a restored coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateTransferWeight {σ A : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (v : A → ℤ) (α : A → ℂ) (X : A → ℕ)
    (y : A → MovingRegularSlot n r m → σ)
    (u : TreeLeafIndex n × Fin 4 → σ) (p : ℕ) (a : A) : ℂ :=
  α a * movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m
    (v a) (movingRestoreSample n r m u (y a)) p (X a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving giant, regular tuple and frequency as one transfer index -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingAmplitudePrior {σ : Type} (Pg : Finset ℕ) (n r m : ℕ)
    (V : ℕ → ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (a : MovingAmplitudeIndex σ Pg n r m V) : ℝ :=
  ρ a.1 * ∏ i, ν i (a.2.1 i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual diagonal and integer off-diagonal of a prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingAmplitudeDiagonal {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℝ :=
  let A := MovingAmplitudeIndex σ Pg n r m V
  let X := fun a : A => (a.1 : ℕ)
  let y := fun a : A => a.2.1
  let v := fun a : A => a.2.2.val
  let α := fun a : A => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ)
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
    n r m v α X y
  ∑ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) *
    ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      (pivotDiagonal (fun a => X a * ∏ i, value (y a i)) v
        (fun a => W u p a * movingTaggedTransform (movingOneGiantModuli (X a) (value ∘ y a))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable
          (p * (∏ i, value (u i)) * outside.prod) (v a))).re

noncomputable def movingAmplitudeOffDiagonal {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℂ :=
  ∑ u : TreeLeafIndex n × Fin 4 → σ,
    (((∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) : ℝ) : ℂ) *
      ∑ s : transferFrequencyRange (V (n + 1)),
        ∑ a : MovingAmplitudeIndex σ Pg n r m V,
          ∑ b : MovingAmplitudeIndex σ Pg n r m V,
            (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) *
              (movingAmplitudePrior Pg n r m V ρ ν b : ℂ) *
                movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G
                  n r m I a.1 b.1 s.val a.2.1 b.2.1 greg ggiant favorable u a.2.2.val b.2.2.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularInitialAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original initial Fourier amplitude and repeated-prime error -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def primeTupleFourierCoefficient {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : Fin n → P) : ℂ :=
  ∑ v ∈ transferFrequencyRange N,
    normalizedFourierProfile (fun t => 𝓕 ψ t) v ((∏ i, (x i : ℕ)) / X) *
      movingRegularTransform (fun i => (x i : ℕ)) (fun i => densityFourier (F i (x i))) 1 v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfListWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialLogSumWeight {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) : ℝ :=
  logCellProfile ((∑ i, Real.log (value (x i) : ℝ)) - c)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeHarmonicCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform counterpart cost for the complete original-prior diagonal -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingAmplitudeRegularEnergy
    (P Pg I : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) : ℝ :=
  let ρ := smoothGiantPrior Pg φ (G (n + 1))
  let ν := fun i => primeSubsetPrior P (Q i)
  ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
    ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      ∑ a : MovingAmplitudeIndex P Pg n r m V,
        movingAmplitudePrior Pg n r m V ρ ν a *
          ‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
            n (4 + r) m a.2.2.val (movingRestoreSample n r m u a.2.1) p a.1 *
            primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
              (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedProductLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full harmonic denominator survives bulk symmetrization -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSymmetrizedTemplateCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (y : MovingRegularSlot n r m → σ)
    (XL XR : ℕ) : ℂ :=
  mixedBulkSymmetrize n m (movingTemplateBulk n r m)
    (fun _ z _ _ => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u z) XL XR) 0 y 0 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeSymmetrizedCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal with the full symmetrized harmonic cost -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingAmplitudeSymmetrizedRegularEnergy
    (P Pg I : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) : ℝ :=
  let ρ := smoothGiantPrior Pg φ (G (n + 1))
  let ν := fun i => primeSubsetPrior P (Q i)
  ∑ u : TreeLeafIndex n × Fin 4 → P, (∏ i, μ n (u i)) * (∏ i, (u i : ℕ) : ℕ) *
    ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      ∑ a : MovingAmplitudeIndex P Pg n r m V,
        movingAmplitudePrior Pg n r m V ρ ν a *
          ‖movingSymmetrizedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
            n r m a.2.2.val u a.2.1 p a.1 *
            primeProductTransform greg (p * (∏ i, (u i : ℕ)) * outside.prod * (a.1 : ℕ))
              (∏ i, (a.2.1 i : ℕ)) a.2.2.val‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkLogFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained bulk logarithmic cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkLogCutoffFactors {σ : Type*} {t : ℕ}
    (value : σ → ℝ) (i : σ) (cb D : ℝ) (hD : 0 ≤ D)
    (hlip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y|)
    (slots : Fin t → List σ) : Fin t → ClippedPolynomialFactor := fun j =>
  logCutoffPolynomialFactor (bulkSlotProduct value i (slots j)) logCellProfile cb 1 D
    zero_le_one hD (fun x => by
      rw [abs_of_nonneg (logCellProfile_nonneg x)]
      exact logCellProfile_le_one x) hlip

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkPairedCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bulk leaf lists and their retained logarithmic cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingBulkPairedCutoffSlots {B : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) : Fin (2 ^ n + 2 ^ n) → List B :=
  Fin.append (fun i => treeLeafTupleEquiv (List B) n (bulk false) ((treeLeafEnumeration n).symm i))
    (fun i => treeLeafTupleEquiv (List B) n (bulk true) ((treeLeafEnumeration n).symm i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalOuterWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingDiagonalOuterWeight {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) : ℂ :=
  (giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v) *
    (inactiveRegularDensity prime reg active x : ℂ)) /
      (diagonalOuterMajorant B D diagonal : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRestoredMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving Fourier factors in the restored compensation coordinates -/

namespace Ostmann
open scoped Classical BigOperators

/-- The extracted compensation primes retain their places in every cofactor,
but the Cauchy step leaves no Fourier factor at those places. -/
def movingRestoredActive (n r m : ℕ) : MovingRegularSlot n (4 + r) m → Bool :=
  Sum.elim (fun _ => false) (fun _ => true) ∘ (movingReverseTemplate n r m).symm

@[simp] theorem movingRestoredActive_compensation (n r m : ℕ)
    (i : TreeLeafIndex n × Fin 4) :
    movingRestoredActive n r m (movingReverseTemplate n r m (.inl i)) = false := by
  simp only [movingRestoredActive, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredActive_surviving (n r m : ℕ)
    (i : MovingRegularSlot n r m) :
    movingRestoredActive n r m (movingReverseTemplate n r m (.inr i)) = true := by
  simp only [movingRestoredActive, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

/-- In particular every protected bulk coordinate remains active. -/
@[simp] theorem movingRestoredActive_bulk (n r m : ℕ) (i : TreeLeafIndex n × Fin m) :
    movingRestoredActive n r m (movingTemplateBulk n (4 + r) m i) = true := by
  rw [← movingReverseTemplate_bulk, movingRestoredActive_surviving]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMaskedTemplateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-branch energy with its actual compensation mask -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRestoredCompensationProduct {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (x : MovingRegularSlot n (4 + r) m → A) : ℕ :=
  ∏ i : TreeLeafIndex n × Fin 4, value (x (movingReverseTemplate n r m (.inl i)))

@[simp] theorem movingRestoredCompensationProduct_restore {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    movingRestoredCompensationProduct value n r m (movingRestoreSample n r m u y) =
      ∏ i, value (u i) := by
  simp only [movingRestoredCompensationProduct, movingRestoreSample,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSymmetrizedMaskedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored multiplier of the actual bulk-averaged coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingBulkAveragedTemplateCoefficient {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (x : MovingRegularSlot n r m → A) (XL XR : ℕ) : ℂ :=
  mixedBulkSymmetrize n m (movingTemplateBulk n r m)
    (fun _ y _ _ => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y XL XR) 0 x 0 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical full list contains every template coordinate once -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateSlotList_nodup (n r m : ℕ) :
    (movingTemplateSlotList n r m).Nodup := by
  unfold movingTemplateSlotList movingTemplateSmall
  apply List.nodup_append.mpr
  refine ⟨bulkSlotLeaves_nodup n r _ ?_,
    bulkSlotLeaves_nodup n m _ (movingTemplateBulk n r m).injective, ?_⟩
  · intro i j h
    exact Prod.ext (congrArg (fun z : MovingRegularSlot n r m => z.1) h)
      (Sum.inl.inj (congrArg (fun z : MovingRegularSlot n r m => z.2) h))
  · intro a ha b hb hab
    obtain ⟨i, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ a).mp ha
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ b).mp hb
    have hh : (Sum.inl i.2 : Fin r ⊕ Fin m) = Sum.inr j.2 :=
      congrArg (fun z : MovingRegularSlot n r m => z.2) hab
    cases hh

noncomputable def movingTemplateListEquiv (n r m : ℕ) :
    Fin (movingTemplateSlotList n r m).length ≃ MovingRegularSlot n r m :=
  List.Nodup.getEquivOfForallMemList (movingTemplateSlotList n r m)
    (movingTemplateSlotList_nodup n r m) (mem_movingTemplateSlotList n r m)

@[simp] theorem movingTemplateListEquiv_apply (n r m : ℕ)
    (i : Fin (movingTemplateSlotList n r m).length) :
    movingTemplateListEquiv n r m i = (movingTemplateSlotList n r m).get i := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual diagonal of the constituent-prime arithmetic step -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentRetainedCoefficient {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a *
    retainedPrimePhase (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M (frequencyRoot n (hist a.2))

noncomputable def constituentPivotDiagonal {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ) : ℂ :=
  pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => frequencyRoot n (hist a.2))
    (constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCharacterCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the common additive factor from the actual diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def constituentCharacterCoefficient {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a *
    retainedCharacterBranch (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUnweighted
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original H prior from the supported Fourier weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentUnweightedTransferWeight {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ :=
  if Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) then
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2)
  else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCharacterCore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original priors in each matched character correlation -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def constituentCharacterCore {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M a *
    retainedCharacterBranch (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchedCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual supported character core in a matched diagonal pair -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledRetainedUnary {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (n : ℕ) (t : FrequencyTree ℤ n) : CopyScheduleH role n ⊕ CopyScheduleY role n → ℕ → ℂ :=
  Sum.elim
    (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val)
    (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInvariantCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual original character signs survive every matching -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledRetainedCharacters {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ) :
    CopyScheduleH role n ⊕ CopyScheduleY role n → ∀ p : ℕ, DirichletCharacter ℂ p :=
  Sum.elim (fun h => χ (copyScheduleOrigin n h.val))
    (fun y => χ (copyScheduleOrigin n y.val))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SignedAtomSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive and conjugate atom copies retain their original characters -/

namespace Ostmann

/-- The first squared-amplitude branch supplies the copied roles. The other
branch is retained outside throughout the transfer schedule. -/
def signedAtomRole {I : Type*} (role : I → CopyScheduleRole) :
    Bool × I → CopyScheduleRole := fun i => if i.1 then role i.2 else .outside

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact closed integer ranges for the original logarithmic word bins -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def initialWordBinRange {C : Type*} (role : Bool × Option C → CopyScheduleRole)
    (b : Bool) (j : ℕ) : ScheduleAtomRange role 0 where
  atoms := [⟨(b, none), trivial⟩]
  lower := ⌈Real.exp (j : ℝ)⌉₊
  upper := (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 : ℕ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialWordBinIdentification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual depth-zero atom ranges are exactly the two word-bin events -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialWordBinRanges {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ) :
    List (ScheduleAtomRange role 0) :=
  [initialWordBinRange role true j, initialWordBinRange role false j]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleRoles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

def characterPositiveRole (k : ℕ) : Option (CharacterCell k) → CopyScheduleRole
  | none => .word
  | some (.inl j) => .pivot j.val
  | some (.inr (.inl (j, _))) => .anchor j.val
  | some (.inr (.inr _)) => .outside

def characterRole (k : ℕ) : CharacterRole k → CopyScheduleRole :=
  signedAtomRole (characterPositiveRole k)

def characterCellSize {k : ℕ} (r : Fin k → ℕ) (f : ℕ) : CharacterCell k → ℕ
  | .inl j => r j
  | .inr (.inl _) => 1
  | .inr (.inr _) => f

def characterSize {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) : CharacterRole k → ℕ :=
  fun v => initialWordSize (m + 1) (characterCellSize r f) v.2

def characterPivotAtom {k : ℕ} (j : Fin k) : CharacterRole k :=
  (true, some (.inl j))

def characterAnchorAtom {k : ℕ} (j : Fin k) (b : Bool) : CharacterRole k :=
  (true, some (.inr (.inl (j, b))))

@[simp] theorem characterRole_word (k : ℕ) : characterRole k (true, none) = .word := rfl
@[simp] theorem characterRole_pivot {k : ℕ} (j : Fin k) :
    characterRole k (characterPivotAtom j) = .pivot j.val := rfl
@[simp] theorem characterRole_anchor {k : ℕ} (j : Fin k) (b : Bool) :
    characterRole k (characterAnchorAtom j b) = .anchor j.val := rfl

@[simp] theorem characterSize_word {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    characterSize m r f (true, none) = m + 1 := rfl
@[simp] theorem characterSize_pivot {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) (j : Fin k) :
    characterSize m r f (characterPivotAtom j) = r j := rfl
@[simp] theorem characterSize_anchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : characterSize m r f (characterAnchorAtom j b) = 1 := rfl

/-- The actual positive word, including its one top label. -/
noncomputable def characterWordEquiv {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fin (m + 1) ≃ {i : Σ v, Fin (characterSize m r f v) // characterRole k i.1 = .word} :=
  Equiv.ofBijective (fun t => ⟨⟨(true, none), t⟩, rfl⟩) (by
    constructor
    · intro a b h
      have hs : (⟨(true, none), a⟩ : Σ v, Fin (characterSize m r f v)) = ⟨(true, none), b⟩ :=
        congrArg Subtype.val h
      cases hs
      rfl
    · rintro ⟨⟨⟨b, c⟩, t⟩, ht⟩
      cases b with
      | false => simp [characterRole, signedAtomRole] at ht
      | true =>
        cases c with
        | none => exact ⟨t, rfl⟩
        | some c =>
          rcases c with j | a | u <;>
            simp [characterRole, signedAtomRole, characterPositiveRole] at ht)

/-- Extend the finitely many real pivots by an arbitrary existing word slot.
All transfer theorems use only the genuine prefix. -/
noncomputable def characterPivot {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (j : ℕ) : Σ v, Fin (characterSize m r f v) :=
  if h : j < k then ⟨characterPivotAtom ⟨j, h⟩, ⟨0, hr ⟨j, h⟩⟩⟩
  else ⟨(true, none), ⟨0, Nat.succ_pos m⟩⟩

@[simp] theorem characterPivot_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (j : ℕ) (hj : j < k) :
    characterRole k (characterPivot m r f hr j).1 = .pivot j := by
  simp [characterPivot, hj]

def characterAnchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : Σ v, Fin (characterSize m r f v) :=
  ⟨characterAnchorAtom j b, ⟨0, Nat.zero_lt_one⟩⟩

@[simp] theorem characterAnchor_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : characterRole k (characterAnchor m r f j b).1 = .anchor j.val := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word coordinates for the fixed integer pivot and the retained primes -/

namespace Ostmann

open scoped BigOperators Classical

def insertedConstituentValues {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    InsertedConstituentVariable role size n → ℕ
  | none => M
  | some (.inl h) => l h
  | some (.inr y) => u y

noncomputable def insertedConstituentWord {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    List (InsertedConstituentVariable role size n) :=
  match (scheduledPartitionEquiv role n).symm v with
  | .inl _ => [none]
  | .inr (.inl h) => List.ofFn (fun k => some (.inl (constituentH role size n h k)))
  | .inr (.inr y) => List.ofFn (fun k => some (.inr (constituentY role size n y k)))

def insertedConstituentPerm {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    Equiv.Perm (InsertedConstituentVariable role size n) :=
  Equiv.optionCongr (Equiv.sumCongr e (Equiv.refl _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTopConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prime tests for a top atom pair containing a fixed pivot -/

namespace Ostmann

open scoped Classical

noncomputable def fixedPivotCheckAt {V : Type*} (M : ℕ)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (i : Fin tests.length) : TopPrimeCondition V :=
  (tests[i.val]).fixPivot M (h _ (List.getElem_mem i.isLt))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPairFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact prime guard and counterpart mask in the actual matched pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

noncomputable def constituentPrimePairChecks (K : Type*) [Fintype K] :
    List (TopPrimeCondition (Option K)) := atomPairChecks (fun i : K => [some i])

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ)
local notation "ρ" => (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
local notation "H" => CopyScheduleH ρ n
local notation "Y" => CopyScheduleY ρ n
local notation "K" => H ⊕ Y

noncomputable def constituentMatchedGraph (e : Equiv.Perm H) : K → K → ℤ :=
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  graphDifference (retainedInternalGraph g)
    (transportGraph (Equiv.sumCongr e (Equiv.refl Y)) (retainedInternalGraph g))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFinalPrimeRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final one-sided pair retains its actual anchor and word origins -/
namespace Ostmann
open scoped Classical

@[simp] theorem copyScheduleOrigin_outside {I : Type*} (n : ℕ) (i : I) :
    copyScheduleOrigin n (copyScheduleOutside n i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem copyScheduleOrigin_anchor {I : Type*} (n j : ℕ) (b : Bool) (i : I) :
    copyScheduleOrigin n (copyScheduleAnchor n j b i) = i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hj : j = n
    · subst j
      rw [copyScheduleAnchor_new]
      exact copyScheduleOrigin_outside n i
    · rw [copyScheduleAnchor_old n j b i hj]
      exact ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact whole-atom coordinates of the character argument's copied block -/
namespace Ostmann
open scoped Classical BigOperators

theorem surviving_anchor_is_reserved {I : Type*} (role : I → CopyScheduleRole)
    (n k : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (ha : copyScheduleRole role n v = .anchor k) :
    n ≤ k ∧ ∃ i, role i = .anchor k ∧ v = copyScheduleOutside n i := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, v, ha, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change (copyScheduleRole role n v).afterCopy b = .anchor k at ha
      cases h : copyScheduleRole role n v <;> cases b <;>
        simp [h, CopyScheduleRole.afterCopy] at ha
    | inr v =>
      change copyScheduleRole role n v = .anchor k at ha
      obtain ⟨hn, i, hi, he⟩ := ih v hv.1 ha
      have hne : n ≠ k := by
        have hh := hv.2.1
        change (copyScheduleRole role n v).copiedAt n = false at hh
        rw [ha] at hh
        change decide (n = k) = false at hh
        exact of_decide_eq_false hh
      exact ⟨by omega, i, hi, congrArg Sum.inr he⟩

theorem characterRole_word_unique {k : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .word) : i = (true, none) := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => rfl
    | some c =>
      rcases c with j | ⟨j, b⟩ | u <;>
        simp [characterRole, signedAtomRole, characterPositiveRole] at hi

theorem characterRole_pivot_exists {k j : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .pivot j) : ∃ t : Fin k, t.val = j ∧ i = characterPivotAtom t := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hi
    | some c =>
      rcases c with t | ⟨t, b⟩ | u
      · exact ⟨t, CopyScheduleRole.pivot.inj hi, rfl⟩
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi

theorem characterRole_anchor_exists {k j : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .anchor j) :
    ∃ t : Fin k, ∃ b : Bool, t.val = j ∧ i = characterAnchorAtom t b := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hi
    | some c =>
      rcases c with t | ⟨t, b⟩ | u
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi
      · exact ⟨t, b, CopyScheduleRole.anchor.inj hi, rfl⟩
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi

noncomputable def characterHCoordinate {k n : ℕ} (hn : n < k) :
    CharacterHIndex k n → CopyScheduleH (characterRole k) n
  | .inl t => scheduledWordH (characterRole k) n t ⟨(true, none), rfl⟩
  | .inr (.inl j) => ⟨copySchedulePositive n (characterPivotAtom j.val),
      copyScheduleSurvives_positive _ _ j.val.val (characterRole_pivot _) n j.property.le,
      by rw [copyScheduleRole_positive _ _ j.val.val (characterRole_pivot _)];
         simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using j.property⟩
  | .inr (.inr b) => ⟨copyScheduleOutside n (characterAnchorAtom ⟨n, hn⟩ b),
      copyScheduleSurvives_reserved _ _ n (characterRole_anchor _ _) n le_rfl,
      by rw [copyScheduleRole_outside, characterRole_anchor];
         simp only [CopyScheduleRole.copiedAt, decide_true]⟩

@[simp] theorem characterHCoordinate_role {k n : ℕ} (hn : n < k) (x : CharacterHIndex k n) :
    copyScheduleRole (characterRole k) n (characterHCoordinate hn x).val =
      match x with
      | .inl _ => .word
      | .inr (.inl j) => .pivot j.val.val
      | .inr (.inr _) => .anchor n := by
  rcases x with t | (j | b)
  · exact copyScheduleRole_path _ _ rfl n t
  · exact copyScheduleRole_positive _ _ j.val.val (characterRole_pivot _) n
  · exact copyScheduleRole_outside _ n _

@[simp] theorem characterHCoordinate_origin {k n : ℕ} (hn : n < k) (x : CharacterHIndex k n) :
    copyScheduleOrigin n (characterHCoordinate hn x).val =
      match x with
      | .inl _ => (true, none)
      | .inr (.inl j) => characterPivotAtom j.val
      | .inr (.inr b) => characterAnchorAtom ⟨n, hn⟩ b := by
  rcases x with t | (j | b)
  · exact copyScheduleOrigin_path n t _
  · exact copyScheduleOrigin_positive n _
  · exact copyScheduleOrigin_outside n _

theorem characterHCoordinate_injective {k n : ℕ} (hn : n < k) :
    Function.Injective (characterHCoordinate hn) := by
  intro x y h
  have hr := congrArg (fun h : CopyScheduleH (characterRole k) n =>
    copyScheduleRole (characterRole k) n h.val) h
  simp only [characterHCoordinate_role] at hr
  rcases x with t | (j | b) <;> rcases y with u | (l | c)
  · have ht := @copySchedulePath_injective (CharacterRole k) n (t, (true, none))
      (u, (true, none)) (congrArg Subtype.val h)
    exact congrArg Sum.inl (congrArg Prod.fst ht)
  · cases hr
  · cases hr
  · cases hr
  · have he : j = l := Subtype.ext (Fin.ext (CopyScheduleRole.pivot.inj hr))
    exact congrArg (fun j => Sum.inr (Sum.inl j)) he
  · cases hr
  · cases hr
  · cases hr
  · have ho := congrArg (fun h : CopyScheduleH (characterRole k) n =>
      copyScheduleOrigin n h.val) h
    simp only [characterHCoordinate_origin, characterAnchorAtom, Prod.mk.injEq,
      Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq, true_and] at ho
    exact congrArg (fun b => Sum.inr (Sum.inr b)) ho

theorem characterHCoordinate_surjective {k n : ℕ} (hn : n < k) :
    Function.Surjective (characterHCoordinate hn) := by
  intro h
  cases hr : copyScheduleRole (characterRole k) n h.val with
  | word =>
    obtain ⟨t, i, hi, he⟩ := surviving_word_is_path _ n h.val h.property.1 hr
    have hi' := characterRole_word_unique i hi
    subst i
    exact ⟨.inl t, Subtype.ext he.symm⟩
  | pivot j =>
    obtain ⟨_, i, hi, he⟩ := surviving_pivot_is_positive _ n j h.val h.property.1 hr
    obtain ⟨t, ht, rfl⟩ := characterRole_pivot_exists i hi
    have hnj : n < j := by
      have hh := h.property.2
      rw [hr] at hh
      simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using hh
    refine ⟨.inr (.inl ⟨t, by omega⟩), Subtype.ext he.symm⟩
  | anchor j =>
    obtain ⟨_, i, hi, he⟩ := surviving_anchor_is_reserved _ n j h.val h.property.1 hr
    obtain ⟨t, b, ht, rfl⟩ := characterRole_anchor_exists i hi
    have hnj : n = j := by
      have hh := h.property.2
      rw [hr] at hh
      simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using hh
    have ht' : t = ⟨n, hn⟩ := Fin.ext (ht.trans hnj.symm)
    subst t
    exact ⟨.inr (.inr b), Subtype.ext he.symm⟩
  | outside =>
    have hh := h.property.2
    rw [hr] at hh
    cases hh

noncomputable def characterHEquiv {k n : ℕ} (hn : n < k) :
    CharacterHIndex k n ≃ CopyScheduleH (characterRole k) n :=
  Equiv.ofBijective (characterHCoordinate hn)
    ⟨characterHCoordinate_injective hn, characterHCoordinate_surjective hn⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCenters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual backwards targets give the copied block's exact center -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterLogCenter {k : ℕ} (J : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) (F : ℝ) (v : CharacterRole k) : ℝ :=
  match v.2 with
  | none => J
  | some (.inl j) => T j
  | some (.inr (.inl (j, b))) => a j b
  | some (.inr (.inr _)) => F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAtomIteration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iteration with the selected word bin and actual character cell products -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def characterPivotRole (k n : ℕ) : CharacterRole k :=
  if h : n < k then characterPivotAtom ⟨n, h⟩ else (true, none)

@[simp] theorem characterPivotRole_eq {k n : ℕ} (hn : n < k) :
    characterPivotRole k n = characterPivotAtom ⟨n, hn⟩ := by
  simp only [characterPivotRole, dite_eq_left hn]

@[simp] theorem characterPivotCap_eq {k n : ℕ} (hn : n < k) (T : Fin k → ℝ) (C : ℝ) :
    characterPivotCap T C n = naturalProductCap (T ⟨n, hn⟩ + C) := by
  simp only [characterPivotCap, dite_eq_left hn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCellIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The pivot lists, two anchors and filler give the actual character cells -/
namespace Ostmann
open scoped Classical BigOperators

/-- A selected ordered list is used once in each signed copy. -/
def characterCellIndex {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) :
    (v : CharacterCell k) → Fin (characterCellSize (fun j => (w j).length) u.length v) → ℕ
  | .inl j, i => (w j).get i
  | .inr (.inl (j, b)), _ => a j b
  | .inr (.inr _), i => u.get i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact active nonbulk count in the finite character schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterActiveSlotEquiv {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    ((Σ j : Fin k, Fin (r j)) ⊕ (Fin k × Bool)) ≃
      {i : Σ v, Fin (characterSize m r f v) //
        characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} := by
  let toSlot : ((Σ j : Fin k, Fin (r j)) ⊕ (Fin k × Bool)) →
      {i : Σ v, Fin (characterSize m r f v) //
        characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} := fun x =>
    match x with
    | .inl ⟨j, t⟩ => ⟨⟨characterPivotAtom j, t⟩, by simp⟩
    | .inr (j, b) => ⟨characterAnchor m r f j b, by simp⟩
  refine Equiv.ofBijective toSlot ⟨?_, ?_⟩
  · rintro (⟨i, t⟩ | ⟨i, b⟩) (⟨j, u⟩ | ⟨j, c⟩) h
    · have hp := congrArg (fun x => x.val.1) h
      have hij : i = j := by simpa [toSlot, characterPivotAtom] using hp
      subst j
      have ht : t = u := by
        have hh := congrArg Subtype.val h
        exact eq_of_heq (Sigma.mk.inj hh).2
      subst u
      rfl
    · have hp := congrArg (fun x => x.val.1) h
      simp [toSlot, characterPivotAtom, characterAnchor, characterAnchorAtom] at hp
    · have hp := congrArg (fun x => x.val.1) h
      simp [toSlot, characterPivotAtom, characterAnchor, characterAnchorAtom] at hp
    · have hp := congrArg (fun x => x.val.1) h
      have hij : i = j ∧ b = c := by
        simpa [toSlot, characterAnchor, characterAnchorAtom] using hp
      rcases hij with ⟨rfl, rfl⟩
      rfl
  · rintro ⟨⟨⟨b, c⟩, t⟩, hw, ho⟩
    cases b with
    | false => simp [characterRole, signedAtomRole] at ho
    | true =>
      cases c with
      | none => simp at hw
      | some c =>
        rcases c with j | ⟨j, b⟩ | u
        · exact ⟨.inl ⟨j, t⟩, rfl⟩
        · refine ⟨.inr (j, b), ?_⟩
          have ht : t = (⟨0, Nat.zero_lt_one⟩ : Fin 1) := by
            apply Fin.ext
            have hlt : t.val < 1 := t.isLt
            change t.val = 0
            omega
          subst t
          rfl
        · simp [characterRole, signedAtomRole, characterPositiveRole] at ho

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectedBulk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original m bulk primes exclude the one top prime of each word -/
namespace Ostmann
open scoped Classical BigOperators

/-- The top prime is position zero; the bulk positions are its successors. -/
def characterBulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fin m ↪ (Σ v, Fin (characterSize m r f v)) where
  toFun i := ⟨(true, none), i.succ⟩
  inj' := by
    intro i j h
    have ht : i.succ = j.succ := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.succ_injective m ht

def characterTop {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Σ v, Fin (characterSize m r f v) := ⟨(true, none), ⟨0, Nat.succ_pos m⟩⟩

@[simp] theorem characterBulk_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (i : Fin m) : characterRole k (characterBulk m r f i).1 = .word := rfl

@[simp] theorem characterTop_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    characterRole k (characterTop m r f).1 = .word := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFullPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original signed product law from its word and nonword prime cells -/
namespace Ostmann
open scoped Classical BigOperators

/-- Both signs use the same marginal. Signs change the characters, never the
original positive harmonic measure. -/
noncomputable def characterFullPrimeCells {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) :
    (Σ v, Fin (characterSize m r f v)) → Finset ℕ
  | ⟨(_, none), i⟩ => Q i
  | ⟨(_, some v), i⟩ => R v i

@[simp] theorem characterFullPrimeCells_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) (i : Fin m) :
    characterFullPrimeCells m r f Q R (characterBulk m r f i) = Q i.succ := rfl

@[simp] theorem characterFullPrimeCells_top {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ) :
    characterFullPrimeCells m r f Q R (characterTop m r f) = Q 0 := rfl

@[simp] theorem characterFullPrimeCells_anchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (Q : Fin (m + 1) → Finset ℕ)
    (R : (v : CharacterCell k) → Fin (characterCellSize r f v) → Finset ℕ)
    (j : Fin k) (b : Bool) :
    characterFullPrimeCells m r f Q R (characterAnchor m r f j b) =
      R (.inr (.inl (j, b))) ⟨0, by change 0 < 1; omega⟩ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the actual target shells and their ordered cell lists -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterTargetCodeGroups {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) : List (List ℕ) :=
  List.ofFn (fun i : Fin (k + 1) => (w (finSuccEquiv k i)).code)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedCharacterTargetCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed target-cell priors after the endpoint pigeonhole -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def fixedTargetCells {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (i : Σ j, Fin (w j).indices.length) : Finset ℕ :=
  (w i.1).cell ((w i.1).indices.get i.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pivot, anchor and filler marginals on the common prime set -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterPrimeCells {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (A : Fin k × Bool → Finset ℕ) :
    (v : CharacterCell k) →
      Fin (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v) → Finset ℕ
  | .inl j, i => fixedTargetCells w ⟨some j, i⟩
  | .inr (.inl j), _ => A j
  | .inr (.inr _), i => fixedTargetCells w ⟨none, i⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedCharacterCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected pivot, filler and anchor cells form actual probability laws -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterAnchorCells {P : Finset ℕ} {F : ℕ → ℂ} {c δ : ℝ}
    {k : ℕ} {u : Fin k × Bool → ℝ}
    (a : ∀ j, CharacterAnchorCell P F c δ (u j)) : Fin k × Bool → Finset ℕ :=
  fun j => (a j).cell

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentRootCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-frequency fibres of the actual guarded prime coefficient -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ)
variable (center : ∀ p : ℕ, ZMod p)

noncomputable def constituentPrimeTerm (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P) : ℂ :=
  fullAtomTransferWeight role childBound pivotBound ranges leaf n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t *
    (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
        χ κ pivot n t P hP q center else 0)

noncomputable def constituentPrimeRootCoefficient (hist : D → FrequencyTree ℤ n)
    (root : D → R) (s : R) (q : SurvivingConstituent role size n → P) : ℂ :=
  rootFibreSum root s (fun d => constituentPrimeTerm role size χ κ pivot n P hP
    childBound pivotBound ranges leaf center (hist d) q)

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentDiagonalSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bad/good splitting of the original-prior pivot diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D K : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

noncomputable def constituentMatchingFamily
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (M : ℕ) : ℂ :=
  ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
    ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
    ∑ e ∈ S, primeMatchingContribution P (fun d => frequencyRoot n (hist d))
      (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M) e

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorMatchingCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the selected bulk, excluding the top slot -/
namespace Ostmann
open scoped Classical

noncomputable def selectedAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  Finset.univ.image (fun e : {e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
    (selectedBulkLabel role n m bulk hbulk) // PreservesSelectedAnchorCode role n m bulk hbulk e} => e.val.val)

@[simp] theorem mem_selectedAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : Equiv.Perm (CopyScheduleH role n)) :
    e ∈ selectedAnchorMatchingSet role n m bulk hbulk ↔
      ∃ h : ∀ x, selectedBulkLabel role n m bulk hbulk (e x) = selectedBulkLabel role n m bulk hbulk x,
        PreservesSelectedAnchorCode role n m bulk hbulk ⟨e, h⟩ := by
  simp only [selectedAnchorMatchingSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨f, hf⟩, hc⟩, rfl⟩
    exact ⟨hf, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨⟨e, h⟩, hc⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLiftCellBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lift actual nonword intervals to both signed copies -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterLiftCellBound {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f d : ℕ)
    (bound : (Σ v, Fin (characterCellSize r f v)) → ℕ) :
    (Σ v, Fin (characterSize m r f v)) → ℕ
  | ⟨(_, none), _⟩ => d
  | ⟨(_, some v), i⟩ => bound ⟨v, i⟩

@[simp] theorem characterLiftCellBound_nonword {k : ℕ} (m : ℕ) (r : Fin k → ℕ)
    (f d : ℕ) (bound : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (sgn : Bool) (v : CharacterCell k) (i : Fin (characterCellSize r f v)) :
    characterLiftCellBound m r f d bound ⟨(sgn, some v), i⟩ = bound ⟨v, i⟩ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentEnergyTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the selected-prime energy under every original constituent prior -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def constituentWordLeafBase {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ) :
    CopyScheduleAtoms role n → ℕ :=
  fun a => ((scheduleConstituentWord role size n a).map
    (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFourierEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Fourier energy with the original bottom-frequency cutoff -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

noncomputable def clippedFullAtomFourierWeight {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (S : Finset ℤ) (V n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n) : ℂ :=
  if frequencyLeafWeight (singleFrequencyLeaf S V) n t = 1 then
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n x (frequencyTreeMap Subtype.val n t) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFamilyEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior matching energy after the external pivot is summed -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

noncomputable def constituentHistoryEnergy (M : ℕ) : ℝ :=
  ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
    (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
    ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
      (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTwoCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed integer outside the two selected original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotOutside {V : Type*} (a b : V) (M : ℕ)
    (outside : OtherVertices a b → ℕ) : OtherVertices (some a) (some b) → ℕ :=
  fun i => match h : i.val with
  | none => M
  | some v => outside ⟨v, fun hv => i.property.1 (h.trans (congrArg some hv)),
      fun hv => i.property.2 (h.trans (congrArg some hv))⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchingExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal matching sum under its original H and Y priors -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

/-- The pair is integrated before the external-pivot sum. The second H prior
is kept explicitly, with the inverse of the matching in the diagonal. -/
noncomputable def constituentOriginalMatchedPair
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (M : ℕ) : ℂ :=
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let Qr : CopyScheduleH ρ n ⊕ CopyScheduleY ρ n → Finset ℕ := Sum.elim
    (fun h => Q (copyScheduleOrigin n h.val)) (fun y => Q (copyScheduleOrigin n y.val))
  let core := fun x : CopyScheduleH ρ n ⊕ CopyScheduleY ρ n → P =>
    constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
      (fun y => x (.inr y)) M
  ∑ x, ((∏ i, primeSubsetPrior P (Qr i) (x i) : ℝ) : ℂ) *
    ((∏ h, primeSubsetPrior P (Qr (.inl h)) (x (.inl (e.symm h))) : ℝ) : ℂ) *
    (core x ((fun h => x (.inl h)), d) * conj (core x ((fun h => x (.inl (e.symm h))), d')))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInvariantPairFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original conjugate-role characters in the exact masked pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform
section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ)

noncomputable def constituentInvariantUnary (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
    (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ) (t t' : FrequencyTree ℤ n) : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → ℕ → ℂ :=
  let g := scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t
  let ω := scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t'
  let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
  fun i p => constituentCounterpartMask Q e i p *
    (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) g ν M i p *
      conj (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) g ω M (σ.symm i) p))

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionScales
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rates for the actual tail count and top-word bin count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

@[simp] theorem characterEndpointExtension_of_mem (E : Finset ℕ) (x₀ : ℕ)
    (G : ℕ → ℕ → ℂ) {x : ℕ} (hx : x ∈ E) (p : ℕ) :
    characterEndpointExtension E x₀ G x p = G x p := ite_eq_left hx

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalCharacterShells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite test family covers precisely the needed character shells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def characterShellTests (k : ℕ) (P Ubulk T₀ : Finset ℕ)
    (Ulate T c : ℝ) (u : Fin k × Bool → ℝ) : CharacterShellTestIndex k → Finset ℕ
  | .inl j => if c ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ ∧
      (∀ p ∈ loglogShell P (Ulate + j), Real.log (p : ℝ) ≤ T / 4)
      then loglogShell P (Ulate + j) else Ubulk
  | .inr (.inl j) => loglogShell P (u j)
  | .inr (.inr false) => Ubulk
  | .inr (.inr true) => T₀

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHigherBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform translated higher-order character bias of the actual residue supports -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def translatedResidueCharacterMean (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) : ℂ :=
  (∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)) / ((tailSupport A N p).card : ℂ)

noncomputable def higherCharacterBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ χ : DirichletCharacter ℂ p, χ ^ 2 ≠ 1 ∧
    ∃ t : ZMod p, r = ‖translatedResidueCharacterMean A N p χ t‖})

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroMultiplicity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual analytic multiplicities of character zeros

The divisor on the whole plane is used consistently, so local disk counts
and later sums over finitely many zeros count the same multiplicities.
-/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

theorem characterZeroOrder_nonneg (χ : PrimitiveComplexCharacter) (z : ℂ) :
    0 ≤ characterZeroOrder χ z :=
  (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z).divisor_nonneg z

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothMellinInversion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mellin inversion for the concrete prime-mean test -/

namespace Ostmann

open MeasureTheory Set Filter
open scoped Topology

noncomputable def complexPrimeMeanTest (t : ℝ) : ℂ := primeMeanTest t

theorem complexPrimeMeanTest_continuous : Continuous complexPrimeMeanTest :=
  Complex.continuous_ofReal.comp (primeMeanTest_contDiff (n := 0)).continuous

theorem primeMeanMellin_eq_mellin : primeMeanMellin = mellin complexPrimeMeanTest := by
  funext s
  unfold primeMeanMellin mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (primeMeanTest t : ℂ) * Complex.exp ((s - 1) * (Real.log t : ℂ)) =
    (t : ℂ) ^ (s - 1) * complexPrimeMeanTest t
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt ht),
    ← Complex.ofReal_log (le_of_lt ht)]
  simp only [complexPrimeMeanTest, mul_comm]

theorem complexPrimeMeanTest_bigO_atTop (a : ℝ) :
    complexPrimeMeanTest =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hz := primeMeanTest_zero_outside t (by intro h; linarith [h.2])
  simp [complexPrimeMeanTest, hz]

theorem complexPrimeMeanTest_bigO_zero (b : ℝ) :
    complexPrimeMeanTest =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hz := primeMeanTest_zero_outside t (by intro h; linarith [h.1])
  simp [complexPrimeMeanTest, hz]

theorem primeMeanMellin_differentiable : Differentiable ℂ primeMeanMellin := by
  rw [primeMeanMellin_eq_mellin]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (complexPrimeMeanTest_continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (complexPrimeMeanTest_bigO_atTop (s.re + 1)) (by linarith)
    (complexPrimeMeanTest_bigO_zero (s.re - 1)) (by linarith)

theorem complexPrimeMeanTest_mellinConvergent (s : ℂ) :
    MellinConvergent complexPrimeMeanTest s :=
  mellinConvergent_of_isBigO_rpow
    (complexPrimeMeanTest_continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (complexPrimeMeanTest_bigO_atTop (s.re + 1)) (by linarith)
    (complexPrimeMeanTest_bigO_zero (s.re - 1)) (by linarith)

theorem primeMeanMellin_verticalIntegrable : Complex.VerticalIntegrable primeMeanMellin 2 := by
  obtain ⟨C, hC, hbound⟩ := primeMeanMellin_decay
  have hmajor : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-(8 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 8)).const_mul C
  apply hmajor.mono'
    (primeMeanMellin_differentiable.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with y
  have hh := hbound ((2 : ℂ) + (y : ℂ) * Complex.I) (by norm_num) (by norm_num)
  simpa [Real.norm_eq_abs, Real.rpow_def_of_pos (show 0 < 1 + |y| by positivity),
    mul_comm] using hh

/-- Inversion on Re(s)=2, used before shifting the explicit-formula contour. -/
theorem primeMeanTest_mellin_inversion (x : ℝ) (hx : 0 < x) :
    mellinInv 2 primeMeanMellin x = (primeMeanTest x : ℂ) := by
  rw [primeMeanMellin_eq_mellin]
  exact mellinInv_mellin_eq 2 complexPrimeMeanTest hx
    (complexPrimeMeanTest_mellinConvergent 2)
    (by rw [← primeMeanMellin_eq_mellin]; exact primeMeanMellin_verticalIntegrable)
    complexPrimeMeanTest_continuous.continuousAt

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothVerticalKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent vertical kernel before contour shifting -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def primeVerticalWeight (X t : ℝ) : ℂ :=
  (X : ℂ) ^ primeMellinLine t * primeMeanMellin (primeMellinLine t)

theorem primeVerticalWeight_continuous (X : ℝ) (hX : 0 < X) :
    Continuous (primeVerticalWeight X) := by
  apply Continuous.mul
  · exact (show Continuous primeMellinLine by fun_prop).const_cpow
      (.inl (by exact_mod_cast hX.ne'))
  · exact primeMeanMellin_differentiable.continuous.comp (by fun_prop)

theorem primeVerticalWeight_norm (X t : ℝ) (hX : 0 < X) :
    ‖primeVerticalWeight X t‖ = X ^ 2 * ‖primeMeanMellin (primeMellinLine t)‖ := by
  rw [primeVerticalWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [primeMellinLine_re, Real.rpow_two]

theorem primeVerticalWeight_integrable (X : ℝ) (hX : 0 < X) :
    Integrable (primeVerticalWeight X) := by
  have hm : Integrable (fun t => primeMeanMellin (primeMellinLine t)) :=
    primeMeanMellin_verticalIntegrable
  apply (hm.norm.const_mul (X ^ 2)).mono'
    (primeVerticalWeight_continuous X hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (primeVerticalWeight_norm X t hX).le)

theorem characterMangoldtCoefficient_summable (χ : PrimitiveComplexCharacter) :
    LSeriesSummable (characterMangoldtCoefficient χ) 2 :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by norm_num)

theorem characterMangoldt_term_norm (χ : PrimitiveComplexCharacter) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖ := by
  simp [LSeries.norm_term_eq, primeMellinLine_re]

theorem characterMangoldt_term_continuous (χ : PrimitiveComplexCharacter) (n : ℕ) :
    Continuous (fun t => LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((show Continuous primeMellinLine by fun_prop).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

/-- Termwise inversion, including the zero coefficient at n=0. -/
theorem characterMangoldt_term_inversion (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n *
        primeVerticalWeight X t) =
      characterMangoldtCoefficient χ n * (primeMeanTest (n / X) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [characterMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) :
      LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n *
        primeVerticalWeight X t = characterMangoldtCoefficient χ n *
          (((n : ℝ) / X : ℝ) : ℂ) ^ (-primeMellinLine t) * primeMeanMellin (primeMellinLine t) := by
    rw [LSeries.term_of_ne_zero hn, primeVerticalWeight, Complex.cpow_neg,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := primeMeanTest_mellin_inversion ((n : ℝ) / X) (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-primeMellinLine t) * primeMeanMellin (primeMellinLine t)) = _ at hinv
  rw [← hinv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothDirichletIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial vertical-line formula for the smooth Mangoldt sum -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def characterVerticalTerm (χ : PrimitiveComplexCharacter) (X : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n * primeVerticalWeight X t

theorem characterVerticalTerm_norm (χ : PrimitiveComplexCharacter) (X : ℝ) (n : ℕ) (t : ℝ) :
    ‖characterVerticalTerm χ X n t‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖ * ‖primeVerticalWeight X t‖ := by
  rw [characterVerticalTerm, norm_mul, characterMangoldt_term_norm]

theorem characterVerticalTerm_integrable (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (n : ℕ) : Integrable (characterVerticalTerm χ X n) := by
  apply ((primeVerticalWeight_integrable X hX).norm.const_mul
    ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖).mono'
  · exact ((characterMangoldt_term_continuous χ n).mul
      (primeVerticalWeight_continuous X hX)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (characterVerticalTerm_norm χ X n t).le)

theorem characterVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter)
    (X : ℝ) :
    Summable (fun n => ∫ t : ℝ, ‖characterVerticalTerm χ X n t‖) := by
  have hs := (characterMangoldtCoefficient_summable χ).norm.mul_right
    (∫ t : ℝ, ‖primeVerticalWeight X t‖)
  apply hs.congr
  intro n
  simp only [characterVerticalTerm_norm, integral_const_mul]

theorem smoothMangoldtMean_eq_vertical_LSeries (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean χ.modulus χ.character X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        LSeries (characterMangoldtCoefficient χ) (primeMellinLine t) * primeVerticalWeight X t := by
  calc
    _ = ∑' n : ℕ, characterMangoldtCoefficient χ n * (primeMeanTest (n / X) : ℂ) := by
      apply tsum_congr
      intro n
      simp only [characterMangoldtCoefficient]
      ring
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, characterVerticalTerm χ X n t :=
      tsum_congr (fun n => (characterMangoldt_term_inversion χ X hX n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, characterVerticalTerm χ X n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, characterVerticalTerm χ X n t := by
      rw [integral_tsum_of_summable_integral_norm
        (characterVerticalTerm_integrable χ X hX) (characterVerticalTerm_summable_norm χ X)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact tsum_mul_right

/-- The exact starting contour for the published explicit formula. -/
theorem smoothMangoldtMean_eq_vertical_logDerivative (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean χ.modulus χ.character X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)) *
          primeVerticalWeight X t := by
  rw [smoothMangoldtMean_eq_vertical_LSeries χ X hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [χ.mangoldt_LSeries_eq (primeMellinLine t) (by simp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativeRight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent logarithmic derivative on Re(s)=3/2 -/

namespace Ostmann

open scoped BigOperators

theorem character_logDeriv_right_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = 3 / 2 → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (3 / 2 : ℂ) n‖
  have hsum : LSeriesSummable f (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (3 / 2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    rw [show (3 / 2 : ℂ).re = (3 / 2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by rw [hs]; norm_num), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeDiskBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic-derivative estimate from the actual modulus on a disk -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem logDeriv_norm_le_of_disk (g : ℂ → ℂ) (R A : ℝ) (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A) :
    ‖logDeriv g 0‖ ≤ 4 * A / R := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hhalf : 0 < R / 2 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall 0 (R / 2)) : z ∈ ball 0 R := by
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hdc : DiffContOnCl ℂ F (ball 0 (R / 2)) := by
    refine ⟨hd.mono (ball_subset_ball (by linarith)), ?_⟩
    rw [closure_ball 0 hhalf.ne']
    exact fun z hz => (hF z (hsmall z hz)).continuousAt.continuousWithinAt
  have hb : ∀ z ∈ sphere 0 (R / 2), ‖F z‖ ≤ 2 * A := by
    intro z hz
    have hn : ‖z‖ = R / 2 := by simpa using hz
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR
      (hsmall z (sphere_subset_closedBall hz)) hF0
    rw [hn] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hdc hb
  rw [(hF 0 (mem_ball_self hR)).deriv] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaLogDerivativeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the Gamma logarithmic derivative

Only the compact real strip [1/4,3/4] is needed. The proof combines the
Euler-integral upper bound, the reflection lower bound, and the disk estimate.
-/

namespace Ostmann

open Complex Metric Set

/-- Linear growth is enough after multiplication by the eighth-order Mellin decay. -/
theorem gamma_logDeriv_strip_bound : ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
    (1 / 4 : ℝ) ≤ z.re → z.re ≤ 3 / 4 →
      ‖logDeriv Complex.Gamma z‖ ≤ B * (1 + |z.im|) := by
  obtain ⟨C, hC, hbound⟩ := gamma_positive_strip_bound (1 / 8) (7 / 8) (by norm_num)
  let K : ℝ := 2 * |Real.log C| + |Real.log Real.pi| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨32 * (K + Real.pi), by positivity, ?_⟩
  intro z hz hz'
  let g : ℂ → ℂ := fun w => Complex.Gamma (z + w)
  have hre (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) :
      (1 / 8 : ℝ) ≤ (z + w).re ∧ (z + w).re ≤ 7 / 8 := by
    have hn : ‖w‖ < 1 / 8 := by simpa using hw
    have ha := abs_re_le_norm w
    have hl := neg_le_abs w.re
    have hu := le_abs_self w.re
    simp only [add_re]
    constructor <;> linarith
  have hgpos (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : 0 < (z + w).re := by
    linarith [(hre w hw).1]
  have hgd (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : DifferentiableAt ℂ Complex.Gamma (z + w) := by
    apply Complex.differentiableAt_Gamma
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp := hgpos w hw
    simp only [add_re] at hp
    linarith
  have hg : AnalyticOnNhd ℂ g (ball 0 (1 / 8 : ℝ)) := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ball.eventually_mem hw] with u hu
    exact (hgd u hu).comp u (differentiableAt_id.const_add z)
  have hne (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : g w ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (hgpos w hw)
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hi : ‖(Complex.Gamma z)⁻¹‖ ≤ (C / Real.pi) * Real.exp (Real.pi * |z.im|) :=
    gamma_inv_norm_bound C hC.le z (by linarith)
      (hbound (1 - z) (by simp; linarith) (by simp; linarith))
  have hlogInv : -Real.log ‖Complex.Gamma z‖ ≤
      Real.log C - Real.log Real.pi + Real.pi * |z.im| := by
    calc
      _ = Real.log ‖(Complex.Gamma z)⁻¹‖ := by rw [norm_inv, Real.log_inv]
      _ ≤ Real.log ((C / Real.pi) * Real.exp (Real.pi * |z.im|)) :=
        Real.log_le_log (norm_pos_iff.mpr (inv_ne_zero hgz)) hi
      _ = _ := by rw [Real.log_mul (div_ne_zero hC.ne' Real.pi_ne_zero) (Real.exp_ne_zero _),
                      Real.log_div hC.ne' Real.pi_ne_zero, Real.log_exp]
  have hlog (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ K + Real.pi * |z.im| := by
    have hu : Real.log ‖g w‖ ≤ Real.log C :=
      Real.log_le_log (norm_pos_iff.mpr (hne w hw)) (hbound (z + w) (hre w hw).1 (hre w hw).2)
    simp only [g, add_zero] at *
    dsimp only [K]
    linarith [le_abs_self (Real.log C), neg_le_abs (Real.log Real.pi)]
  have hestimate := logDeriv_norm_le_of_disk g (1 / 8) (K + Real.pi * |z.im|)
    (by norm_num) (by positivity) hg hne hlog
  have hdg : HasDerivAt g (deriv Complex.Gamma z) 0 := by
    convert! (hgd 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8))).hasDerivAt.comp 0
      ((hasDerivAt_id (0 : ℂ)).const_add z) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have he : logDeriv g 0 = logDeriv Complex.Gamma z := by
    simp only [logDeriv_apply, hdg.deriv, g, add_zero]
  rw [he] at hestimate
  calc
    _ ≤ 32 * (K + Real.pi * |z.im|) := by convert hestimate using 1; ring
    _ ≤ 32 * (K + Real.pi) * (1 + |z.im|) := by
      nlinarith [abs_nonneg z.im, Real.pi_pos]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaContourBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma logarithmic derivatives on the four contour lines -/

namespace Ostmann

open Complex

theorem gamma_logDeriv_contour_bound : ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
    (z.re = -(1 / 4 : ℝ) ∨ z.re = 1 / 4 ∨ z.re = 3 / 4 ∨ z.re = 5 / 4) →
      ‖logDeriv Complex.Gamma z‖ ≤ B * (1 + |z.im|) := by
  obtain ⟨B, hB, hbound⟩ := gamma_logDeriv_strip_bound
  refine ⟨B + 4, by linarith, ?_⟩
  intro z hz
  rcases hz with hz | hz | hz | hz
  · have hp := gamma_not_pole_of_re z (by linarith) (by rw [hz]; norm_num)
    have hrec := Complex.digamma_apply_add_one z hp
    have hb := hbound (z + 1) (by simp; linarith) (by simp; linarith)
    have hi := norm_inv_le_four_of_quarter_re z (by rw [hz]; norm_num)
    have he : logDeriv Complex.Gamma z = logDeriv Complex.Gamma (z + 1) - z⁻¹ := by
      simp only [← Complex.digamma_def]
      rw [hrec]
      ring
    rw [he]
    have hh := (norm_sub_le (logDeriv Complex.Gamma (z + 1)) z⁻¹).trans (add_le_add hb hi)
    simp only [add_im, one_im, add_zero] at hh
    nlinarith [abs_nonneg z.im]
  · have hb := hbound z (by linarith) (by linarith)
    nlinarith [abs_nonneg z.im]
  · have hb := hbound z (by linarith) (by linarith)
    nlinarith [abs_nonneg z.im]
  · have hp := gamma_not_pole_of_re (z - 1) (by simp; linarith) (by simp; linarith)
    have hrec := Complex.digamma_apply_add_one (z - 1) hp
    have hb := hbound (z - 1) (by simp; linarith) (by simp; linarith)
    have hi := norm_inv_le_four_of_quarter_re (z - 1) (by simp; rw [hz]; norm_num)
    have he : logDeriv Complex.Gamma z = logDeriv Complex.Gamma (z - 1) + (z - 1)⁻¹ := by
      simpa only [sub_add_cancel, Complex.digamma_def] using hrec
    rw [he]
    have hh := (norm_add_le (logDeriv Complex.Gamma (z - 1)) (z - 1)⁻¹).trans (add_le_add hb hi)
    simp only [sub_im, one_im, sub_zero] at hh
    nlinarith [abs_nonneg z.im]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaRealContourBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the real-place Gamma factor on the shifted contour -/

namespace Ostmann

open Complex

theorem gammaReal_contour_logDeriv_bound : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
    (s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2) →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := gamma_logDeriv_contour_bound
  refine ⟨B + |Real.log Real.pi| + 1, by positivity, ?_⟩
  intro s hs
  have hhalf : (s / 2).re = -(1 / 4 : ℝ) ∨ (s / 2).re = 1 / 4 ∨
      (s / 2).re = 3 / 4 ∨ (s / 2).re = 5 / 4 := by
    simp only [div_ofNat_re]
    rcases hs with h | h | h | h
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; linarith
  have hb := hbound (s / 2) hhalf
  change ‖Complex.digamma (s / 2)‖ ≤ _ at hb
  have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
  have hnorm : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [gammaReal_logDeriv s (gammaReal_contour_regular s hs), norm_div, norm_ofNat]
  have hh := (norm_sub_le (Complex.digamma (s / 2)) (Complex.log (Real.pi : ℂ))).trans
    (add_le_add hb (le_refl ‖Complex.log (Real.pi : ℂ)‖))
  rw [him, hnorm] at hh
  change ‖Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)‖ / 2 ≤ _
  nlinarith [abs_nonneg s.im, abs_nonneg (Real.log Real.pi)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character Gamma factors on both vertical contour lines -/

namespace Ostmann

open Complex
open scoped Classical

theorem characterGamma_contour_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ),
      (s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := gammaReal_contour_logDeriv_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact hbound s (contourLine_expanded s hs)
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_differentiableAt (s + 1) (gammaReal_contour_regular _ (contourLine_shift s hs)))
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hbound (s + 1) (contourLine_shift s hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaGrowthStrip
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma-factor growth in the narrow strip around the contour

The upper bounds use only Euler's integral and reflection. They are needed
for the horizontal-edge logarithmic-derivative estimate.
-/

namespace Ostmann

open Complex

theorem gammaReal_growth_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 11 / 4 → ‖Complex.Gammaℝ s‖ ≤ C) ∧
    (∀ s : ℂ, -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|)) := by
  obtain ⟨C, hC, hΓ⟩ := gamma_positive_strip_bound (1 / 4) (11 / 8) (by norm_num)
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs hs'
    have hg := hΓ (s / 2) (by simp; linarith) (by simp; linarith)
    have hp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
      simp
      linarith
    rw [Complex.Gammaℝ_def, norm_mul]
    exact (mul_le_mul hp hg (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  · intro s hs hs'
    have hg := hΓ (1 - s / 2) (by simp; linarith) (by simp; linarith)
    have hi := gamma_inv_norm_bound C hC.le (s / 2) (by simp; linarith) hg
    have hp : ‖(Real.pi : ℂ) ^ (s / 2)‖ ≤ Real.pi := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      calc
        _ ≤ Real.pi ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) (by simp; linarith)
        _ = _ := Real.rpow_one _
    have him : |(s / 2).im| ≤ |s.im| := by
      simp only [div_ofNat_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg s.im]
    rw [gammaReal_inverse_eq, norm_mul]
    calc
      _ ≤ Real.pi * ((C / Real.pi) * Real.exp (Real.pi * |(s / 2).im|)) :=
        mul_le_mul hp hi (norm_nonneg _) Real.pi_pos.le
      _ = C * Real.exp (Real.pi * |(s / 2).im|) := by field_simp
      _ ≤ C * Real.exp (Real.pi * |s.im|) := by gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Gamma factors for the horizontal-contour growth estimate -/

namespace Ostmann

open Complex
open scoped Classical

theorem characterGamma_growth_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ (χ : PrimitiveComplexCharacter) (s : ℂ), (1 / 2 : ℝ) ≤ s.re → s.re ≤ 7 / 4 →
      ‖DirichletCharacter.gammaFactor χ.character s‖ ≤ C) ∧
    (∀ (χ : PrimitiveComplexCharacter) (s : ℂ), -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖χ.gammaInverse s‖ ≤ C * Real.exp (Real.pi * |s.im|)) := by
  obtain ⟨C, hC, hp, hi⟩ := gammaReal_growth_bounds
  refine ⟨C, hC, ?_, ?_⟩
  · intro χ s hs hs'
    by_cases hc : χ.character.Even
    · simpa only [DirichletCharacter.gammaFactor, hc, ↓reduceIte] using hp s hs (by linarith)
    · simpa only [DirichletCharacter.gammaFactor, hc, ↓reduceIte] using
        hp (s + 1) (by simp; linarith) (by simp; linarith)
  · intro χ s hs hs'
    by_cases hc : χ.character.Even
    · simpa only [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hc, ↓reduceIte]
        using hi s hs (by linarith)
    · simpa only [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hc, ↓reduceIte,
        add_im, one_im, add_zero] using hi (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual finite zero factors of an entire character L-function -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

noncomputable def characterZeroPolynomial (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ z ∈ S, (s - z) ^ analyticOrderNatAt χ.L z

theorem characterZeroPolynomial_analytic (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) : AnalyticAt ℂ (characterZeroPolynomial χ S) s := by
  exact S.analyticAt_fun_prod fun z _ => (analyticAt_id.sub analyticAt_const).pow _

theorem characterZeroPolynomial_ne_zero (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) (hs : s ∉ S) : characterZeroPolynomial χ S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))

theorem characterZeroPolynomial_insert (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (z s : ℂ) (hz : z ∈ S) :
    characterZeroPolynomial χ S s =
      (s - z) ^ analyticOrderNatAt χ.L z * characterZeroPolynomial χ (S.erase z) s := by
  exact (Finset.mul_prod_erase S _ hz).symm

/-- The quotient by any finite collection of complete zero factors extends
analytically to the whole plane. It is nonzero at each removed zero. -/
theorem character_remove_finite_zeros (χ : PrimitiveComplexCharacter) (S : Finset ℂ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, χ.L s = characterZeroPolynomial χ S s * g s) ∧
      (∀ s ∈ S, g s ≠ 0) := by
  choose R hR hRne heR using fun z =>
    (χ.L_analytic z).analyticOrderAt_ne_top.mp (χ.L_order_ne_top z)
  let g : ℂ → ℂ := fun z => if z ∈ S then
    R z z / characterZeroPolynomial χ (S.erase z) z
    else χ.L z / characterZeroPolynomial χ S z
  have hlocal (z : ℂ) (hz : z ∈ S) :
      g =ᶠ[𝓝 z] fun s => R z s / characterZeroPolynomial χ (S.erase z) s := by
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hav, heR z] with s hs he
    by_cases hsz : s = z
    · subst s
      simp only [g, ite_eq_left hz]
    · have hsS : s ∉ S := fun h => hs (Finset.mem_erase.mpr ⟨hsz, h⟩)
      simp only [g, ite_eq_right hsS]
      rw [characterZeroPolynomial_insert χ S z s hz, he]
      simp only [smul_eq_mul]
      exact mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hsz))
  have ha : ∀ s, AnalyticAt ℂ g s := by
    intro s
    by_cases hs : s ∈ S
    · exact ((hR s).div (characterZeroPolynomial_analytic χ (S.erase s) s)
        (characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp))).congr
          (hlocal s hs).symm
    · apply ((χ.L_analytic s).div (characterZeroPolynomial_analytic χ S s)
        (characterZeroPolynomial_ne_zero χ S s hs)).congr
      have hav : ∀ᶠ z in 𝓝 s, z ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
      filter_upwards [hav] with z hz
      simp only [g, ite_eq_right hz, Pi.div_apply]
  refine ⟨g, ha, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ S
    · rw [(hlocal s hs).self_of_nhds, characterZeroPolynomial_insert χ S s s hs]
      have he := (heR s).self_of_nhds
      simp only [smul_eq_mul] at he
      rw [he]
      field_simp [characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp)]
    · simp only [g, ite_eq_right hs]
      exact (mul_div_cancel₀ _ (characterZeroPolynomial_ne_zero χ S s hs)).symm
  · intro s hs
    simp only [g, ite_eq_left hs]
    exact div_ne_zero (hRne s) (characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourZeroSet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite zero set removed around a horizontal contour edge -/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

noncomputable def characterContourDivisor (χ : PrimitiveComplexCharacter) (t : ℝ) :=
  divisor χ.L (closedBall (characterZeroCenter t) (21 / 8 : ℝ))

noncomputable def characterContourZeros (χ : PrimitiveComplexCharacter) (t : ℝ) : Finset ℂ :=
  ((characterContourDivisor χ t).finiteSupport
    (isCompact_closedBall (characterZeroCenter t) (21 / 8 : ℝ))).toFinset

theorem characterContourDivisor_eq (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ)) :
    characterContourDivisor χ t z = (analyticOrderNatAt χ.L z : ℤ) := by
  rw [← characterZeroOrder_eq_nat]
  unfold characterContourDivisor characterZeroOrder
  rw [AnalyticOnNhd.divisor_apply (fun z _ => χ.L_analytic z) hz,
    AnalyticOnNhd.divisor_apply (fun z _ => χ.L_analytic z) (mem_univ z)]

theorem mem_characterContourZeros (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ) :
    z ∈ characterContourZeros χ t ↔
      z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) ∧ χ.L z = 0 := by
  change z ∈ ((characterContourDivisor χ t).finiteSupport (isCompact_closedBall _ _)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change characterContourDivisor χ t z ≠ 0 ↔ _
  constructor
  · intro hn
    have hz : z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) :=
      (characterContourDivisor χ t).supportWithinDomain hn
    refine ⟨hz, ?_⟩
    rw [characterContourDivisor_eq χ t z hz, ← characterZeroOrder_eq_nat] at hn
    exact (characterZeroOrder_pos_iff χ z).mp
      (lt_of_le_of_ne (characterZeroOrder_nonneg χ z) (Ne.symm hn))
  · rintro ⟨hz, he⟩
    rw [characterContourDivisor_eq χ t z hz, ← characterZeroOrder_eq_nat]
    exact ne_of_gt ((characterZeroOrder_pos_iff χ z).mpr he)

theorem characterContourZeros_mass_eq (χ : PrimitiveComplexCharacter) (t : ℝ) :
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) =
      ((∑ᶠ z, characterContourDivisor χ t z : ℤ) : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := characterContourZeros χ t) _ (by
    intro z hz
    exact ((characterContourDivisor χ t).finiteSupport
      (isCompact_closedBall _ _)).mem_toFinset.mpr hz), Int.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [characterContourDivisor_eq χ t z ((mem_characterContourZeros χ t z).mp hz).1]
  simp

theorem characterContourZeros_mass_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M) :
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) ≤
      Real.log (3 * M) / Real.log (22 / 21 : ℝ) := by
  have ha : AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) |(11 / 4 : ℝ)|) :=
    fun z _ => χ.L_analytic z
  have hlo := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hne : χ.L (characterZeroCenter t) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hlo
    linarith
  have hj := ha.sum_divisor_le (r := (21 / 8 : ℝ)) (R := (11 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz => hbound z (by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 11 / 4)] using
        sphere_subset_closedBall hz))
  have hn : 0 < ‖χ.L (characterZeroCenter t)‖ := by linarith
  have hr : M / ‖χ.L (characterZeroCenter t)‖ ≤ 3 * M := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  rw [characterContourZeros_mass_eq]
  change ((∑ᶠ z, divisor χ.L (closedBall (characterZeroCenter t) (21 / 8)) z : ℤ) : ℝ) ≤ _
  rw [show |(21 / 8 : ℝ)| = 21 / 8 by norm_num,
    show (11 / 4 : ℝ) / (21 / 8) = 22 / 21 by norm_num] at hj
  apply hj.trans
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (div_pos (by linarith) hn) hr)
    (Real.log_pos (by norm_num)).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroQuotientBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Modulus bounds after removing the finite zero factors -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem characterZeroPolynomial_norm_le (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (_hr : 0 ≤ r) (hS : ∀ w ∈ S, ‖z - w‖ ≤ r) :
    ‖characterZeroPolynomial χ S z‖ ≤ r ^ (∑ w ∈ S, analyticOrderNatAt χ.L w) := by
  simp only [characterZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hS w hw) _)

theorem characterZeroPolynomial_norm_ge (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ w ∈ S, r ≤ ‖z - w‖) :
    r ^ (∑ w ∈ S, analyticOrderNatAt χ.L w) ≤ ‖characterZeroPolynomial χ S z‖ := by
  simp only [characterZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => pow_nonneg hr _)
    (fun w hw => pow_le_pow_left₀ hr (hS w hw) _)

/-- The removed quotient is nonvanishing on the whole smaller disk. -/
theorem character_contour_quotient_exists (χ : PrimitiveComplexCharacter) (t : ℝ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s) ∧
      (∀ s ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ), g s ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := character_remove_finite_zeros χ (characterContourZeros χ t)
  refine ⟨g, hg, he, ?_⟩
  intro s hs
  by_cases hz : s ∈ characterContourZeros χ t
  · exact hne s hz
  · intro hh
    have hf : χ.L s = 0 := by rw [he, hh, mul_zero]
    exact hz ((mem_characterContourZeros χ t s).mpr ⟨hs, hf⟩)

/-- A fixed annular reserve bounds the analytic quotient throughout the outer
 disk, even when the original L-function vanishes inside it. -/
theorem character_contour_quotient_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (_hM : 0 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (g : ℂ → ℂ) (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s) :
    ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ),
      ‖g z‖ ≤ M * 8 ^ (∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w) := by
  let N := ∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w
  have hb : ∀ z ∈ sphere (characterZeroCenter t) (11 / 4 : ℝ), ‖g z‖ ≤ M * 8 ^ N := by
    intro z hz
    have hdist : ‖z - characterZeroCenter t‖ = 11 / 4 := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have hlower : (1 / 8 : ℝ) ^ N ≤ ‖characterZeroPolynomial χ (characterContourZeros χ t) z‖ := by
      apply characterZeroPolynomial_norm_ge χ _ z (1 / 8) (by norm_num)
      intro w hw
      have hw' := ((mem_characterContourZeros χ t w).mp hw).1
      have hdw : ‖w - characterZeroCenter t‖ ≤ 21 / 8 := by
        simpa only [mem_closedBall, dist_eq_norm] using hw'
      have hh := norm_sub_le (z - w) (characterZeroCenter t - w)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (characterZeroCenter t)] at hh
      linarith
    have hnorm := hbound z (sphere_subset_closedBall hz)
    rw [he z, norm_mul] at hnorm
    have hprod : (1 / 8 : ℝ) ^ N * ‖g z‖ ≤ M :=
      (mul_le_mul_of_nonneg_right hlower (norm_nonneg _)).trans hnorm
    have hh := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 1 / 8) N)).mpr (by simpa only [mul_comm] using hprod)
    simpa only [one_div, inv_pow, div_inv_eq_mul] using hh
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (characterZeroCenter t) (11 / 4)) isBounded_ball (f := g)
  · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
      (fun w _ => (hg w).continuousAt.continuousWithinAt)
  · rw [frontier_ball (characterZeroCenter t) (by norm_num : (11 / 4 : ℝ) ≠ 0)]
    exact hb
  · rwa [closure_ball (characterZeroCenter t) (by norm_num : (11 / 4 : ℝ) ≠ 0)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeContourDisk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zero-free logarithmic-derivative bound up to the contour's left edge -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem logDeriv_norm_le_contour_disk (g : ℂ → ℂ) (A : ℝ) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 (21 / 8)))
    (hne : ∀ z ∈ ball 0 (21 / 8), g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 (21 / 8), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ 5 / 2) : ‖logDeriv g w‖ ≤ 1312 * A := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g (21 / 8)
    (by norm_num) hg hne
  have hd : DifferentiableOn ℂ F (ball 0 (21 / 8)) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 (21 / 8)) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self (by norm_num))) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (1 / 16)) : ‖v‖ ≤ 41 / 16 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ 1 / 16 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (1 / 16)) : v ∈ ball 0 (21 / 8) := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (1 / 16)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (1 / 16), ‖F v‖ ≤ 82 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < 21 / 8 - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal (by norm_num)
      (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 16) hdc hbound
  have hwball : w ∈ ball 0 (21 / 8) := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroQuotientLog
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized logarithm of the quotient by all nearby zeros -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem character_contour_quotient_log_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (g : ℂ → ℂ) (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, χ.L s = characterZeroPolynomial χ (characterContourZeros χ t) s * g s)
    (hne : ∀ s ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ), g s ≠ 0) :
    ∀ z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ),
      Real.log ‖g z‖ - Real.log ‖g (characterZeroCenter t)‖ ≤
        Real.log (3 * M) +
          (∑ w ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L w : ℝ)) * Real.log 21 := by
  let N := ∑ w ∈ characterContourZeros χ t, analyticOrderNatAt χ.L w
  have hc : characterZeroCenter t ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) :=
    mem_closedBall_self (by norm_num)
  have hgc : 0 < ‖g (characterZeroCenter t)‖ := norm_pos_iff.mpr (hne _ hc)
  have hp : ‖characterZeroPolynomial χ (characterContourZeros χ t) (characterZeroCenter t)‖ ≤
      (21 / 8 : ℝ) ^ N := by
    apply characterZeroPolynomial_norm_le χ _ _ _ (by norm_num)
    intro w hw
    rw [norm_sub_rev]
    exact (mem_closedBall_iff_norm.mp ((mem_characterContourZeros χ t w).mp hw).1)
  have hlo : (1 / 3 : ℝ) ≤ (21 / 8 : ℝ) ^ N * ‖g (characterZeroCenter t)‖ := by
    have hh := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
    rw [he, norm_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hpow : (8 : ℝ) ^ N * (21 / 8 : ℝ) ^ N = 21 ^ N := by
    rw [← mul_pow]
    norm_num
  have hm : M * 8 ^ N ≤ 3 * M * 21 ^ N * ‖g (characterZeroCenter t)‖ := by
    calc
      _ = (3 * M * 8 ^ N) * (1 / 3) := by ring
      _ ≤ (3 * M * 8 ^ N) * ((21 / 8) ^ N * ‖g (characterZeroCenter t)‖) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = 3 * M * (8 ^ N * (21 / 8) ^ N) * ‖g (characterZeroCenter t)‖ := by ring
      _ = _ := by rw [hpow]
  intro z hz
  have hzouter : z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num) hz
  have hupper := character_contour_quotient_bound χ t M (by linarith) hbound g hg he z hzouter
  have hratio : ‖g z‖ / ‖g (characterZeroCenter t)‖ ≤ 3 * M * 21 ^ N :=
    (div_le_iff₀ hgc).mpr (hupper.trans hm)
  have hnz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
  rw [← Real.log_div hnz.ne' hgc.ne']
  apply (Real.log_le_log (div_pos hnz hgc) hratio).trans_eq
  rw [Real.log_mul (by positivity : 3 * M ≠ 0) (by positivity : (21 : ℝ) ^ N ≠ 0),
    Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativeLocal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A local logarithmic-derivative expansion with its actual zero multiplicities -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem characterZeroPolynomial_logDeriv (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (s : ℂ) (hs : s ∉ S) :
    logDeriv (characterZeroPolynomial χ S) s =
      ∑ z ∈ S, (analyticOrderNatAt χ.L z : ℂ) / (s - z) := by
  change logDeriv (fun w => ∏ z ∈ S, (w - z) ^ analyticOrderNatAt χ.L z) s = _
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro z hz
    have hp := logDeriv_fun_pow (f := fun w : ℂ => w - z) (x := s)
      (differentiableAt_id.sub_const z) (analyticOrderNatAt χ.L z)
    rw [hp]
    simp [logDeriv_apply, div_eq_mul_inv]
  · intro z hz
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))
  · intro z _
    exact (differentiableAt_id.sub_const z).pow _

/-- Away from the actual nearby zeros, L'/L differs from their partial fractions
by a controlled analytic term. No zero-separation assumption enters this term. -/
theorem character_logDeriv_local_error (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (s : ℂ) (hs : ‖s - characterZeroCenter t‖ ≤ 5 / 2)
    (hszero : s ∉ characterContourZeros χ t) :
    ‖logDeriv χ.L s -
      ∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z)‖ ≤
      1312 * (Real.log (3 * M) +
        (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1) := by
  obtain ⟨g, hg, he, hgne⟩ := character_contour_quotient_exists χ t
  let c := characterZeroCenter t
  let A := Real.log (3 * M) +
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1
  have hA : 0 < A := by
    have hlog : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have h21 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
    dsimp [A]
    positivity
  have hball (w : ℂ) (hw : w ∈ ball 0 (21 / 8 : ℝ)) :
      w + c ∈ closedBall c (21 / 8 : ℝ) := by
    simpa only [mem_closedBall, mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_right, sub_zero]
      using (mem_ball_iff_norm.mp hw).le
  have hq := logDeriv_norm_le_contour_disk (fun w => g (w + c)) A hA
    (fun w _ => (hg (w + c)).comp (f := fun u : ℂ => u + c) (x := w) (by fun_prop))
    (fun w hw => hgne _ (hball w hw)) (fun w hw => ?_) (s - c) hs
  · have hsball : s ∈ closedBall c (21 / 8 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      linarith
    have hshift : logDeriv (fun w => g (w + c)) (s - c) = logDeriv g s := by
      change logDeriv (g ∘ (fun w => w + c)) (s - c) = _
      have hh := logDeriv_comp (f := g) (g := fun w : ℂ => w + c) (x := s - c)
        ((hg _).differentiableAt) (differentiableAt_id.add_const c)
      simpa using hh
    rw [hshift] at hq
    have hf : χ.L = fun w => characterZeroPolynomial χ (characterContourZeros χ t) w * g w :=
      funext he
    have hsplit : logDeriv χ.L s = logDeriv (characterZeroPolynomial χ (characterContourZeros χ t)) s + logDeriv g s := by
      rw [hf]
      exact logDeriv_mul s
        (characterZeroPolynomial_ne_zero χ _ s hszero) (hgne s hsball)
        ((characterZeroPolynomial_analytic χ _ s).differentiableAt) ((hg s).differentiableAt)
    rw [hsplit, characterZeroPolynomial_logDeriv χ _ s hszero]
    simpa only [A, add_sub_cancel_left] using hq
  · have hh := character_contour_quotient_log_bound χ t M hM hbound g hg he hgne
      (w + c) (hball w hw)
    simpa only [zero_add, A, c] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativeSeparated
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual logarithmic-derivative control away from the nearby zeros -/

namespace Ostmann

open Complex Metric
open scoped BigOperators

theorem character_logDeriv_separated_bound (χ : PrimitiveComplexCharacter) (t M δ : ℝ)
    (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (s : ℂ) (hs : ‖s - characterZeroCenter t‖ ≤ 5 / 2)
    (hsep : ∀ z ∈ characterContourZeros χ t, δ ≤ ‖s - z‖) :
    ‖logDeriv χ.L s‖ ≤
      1312 * (Real.log (3 * M) +
        (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1) +
      (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) / δ := by
  have hsnot : s ∉ characterContourZeros χ t := by
    intro h
    have hh := hsep s h
    simp only [sub_self, norm_zero] at hh
    linarith
  have he := character_logDeriv_local_error χ t M hM hbound s hs hsnot
  have hsum : ‖∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z)‖ ≤
      (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) / δ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep z hz)
  have ht := norm_le_norm_sub_add (logDeriv χ.L s)
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z))
  exact ht.trans (add_le_add he hsum)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteSpectralProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete finite additive spectral projections for Section 5 -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finiteSpectralProjection {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (f : ZMod p → ℂ) : ZMod p → ℂ :=
  densityFourierInverse (fun b => if b ∈ E then densityFourier f b else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseAdditiveKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual additive kernel of the sparse spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseAdditiveKernel {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (x : ZMod p) : ℂ :=
  (t : ℂ) * additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelLocalBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual local blocks of `(1+b)^2` at the fixed parameter `17/20` -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def localSparseKernel {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) : ZMod p → ℂ := sparseAdditiveKernel E (17 / 20)

noncomputable def localSparseSquare {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (x : ZMod p) : ℂ := localSparseKernel E x * localSparseKernel E x

noncomputable def localSparseScalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) : ℂ :=
  1 + 2 * residueKernelScalar S (localSparseKernel E) + residueKernelScalar S (localSparseSquare E)

noncomputable def localSparseSide {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  2 * residueKernelSide S T (localSparseKernel E) x + residueKernelSide S T (localSparseSquare E) x

noncomputable def localSparseLower {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (f : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  2 * residueKernelLower S T (localSparseKernel E) f x +
    residueKernelLower S T (localSparseSquare E) f x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePolydiscBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform side and lower bounds on the complex parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def polydiscSparseScalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (c d : ℂ) : ℂ :=
  1 + c * residueKernelScalar S (localSparseKernel E) +
    d * residueKernelScalar S (localSparseSquare E)

noncomputable def polydiscSparseSide {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (x : ZMod p) : ℂ :=
  c * residueKernelSide S T (localSparseKernel E) x +
    d * residueKernelSide S T (localSparseSquare E) x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelLinearMaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps for the concrete finite kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def polydiscLowerLinearMap {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  c • residueLowerLinearMap S T (localSparseKernel E) +
    d • residueLowerLinearMap S T (localSparseSquare E)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HigherCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proposition 4.1: maximal translated higher-order bias has harmonic mass o(L) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

noncomputable def higherCharacterBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ closedLogLogPrimeBand α β L, (p : ℝ)⁻¹ * higherCharacterBias A N p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseResidueMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix form of the concrete local sparse kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseResidueMatrix {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (u v : ℂ) : Option (ZMod p) → Option (ZMod p) → ℂ :=
  finiteBlockMatrix (polydiscSparseScalar S E (u + v) (u * v))
    (polydiscSparseSide (Finset.univ \ S) S E (conj (u + v)) (conj (u * v)))
    (polydiscSparseSide S (Finset.univ \ S) E (u + v) (u * v))
    (polydiscLowerLinearMap S (Finset.univ \ S) E (u + v) (u * v))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCube
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a finite product of bilinear factors -/

namespace Ostmann
open scoped Classical BigOperators

def cubeDegree {n : ℕ} (t : BilinearCube n) (b : Bool) : ℕ :=
  ∑ i, if (if b then (t i).2 else (t i).1) then 1 else 0

noncomputable def cubeCoefficient {n : ℕ} {E : Type*} [AddCommMonoid E]
    (A : BilinearCube n → E) (i j : ℕ) : E :=
  ∑ t ∈ Finset.univ.filter (fun t => (cubeDegree t false, cubeDegree t true) = (i, j)), A t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTensorPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete coefficients of the sparse tensor polynomial -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def localSparseCoefficient {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (b : Bool × Bool) (x y : Option (ZMod p)) : ℂ :=
  match b with
  | (false, false) => sparseResidueMatrix S E 0 0 x y
  | (true, false) => sparseResidueMatrix S E 1 0 x y - sparseResidueMatrix S E 0 0 x y
  | (false, true) => sparseResidueMatrix S E 0 1 x y - sparseResidueMatrix S E 0 0 x y
  | (true, true) => sparseResidueMatrix S E 1 1 x y - sparseResidueMatrix S E 1 0 x y -
      sparseResidueMatrix S E 0 1 x y + sparseResidueMatrix S E 0 0 x y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BadPrimeLogCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic imbalance budget excludes only linearly many cells -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- `badPrimes` is the set removed by the balance or test-error threshold. -/
noncomputable def badPrimeLogCells (I badPrimes : Finset ℕ) : Finset ℕ :=
  I.filter (fun h => 1 ≤ h ∧ 1 / (8 * ((h : ℝ) + 1)) ≤
    finiteCellMass badPrimes primeLogIndex (fun p => (p : ℝ)⁻¹) h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBiasSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting a fixed quadratic bias from a large weighted mean -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def biasedPrimeBand (A : Set ℕ) (N : ℕ) (T δ : ℝ) (t : ℕ → ℤ) : Finset ℕ :=
  (logPrimeBand T).filter fun p => δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedQuadraticFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def fixedQuadraticCoefficient (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (s : ℕ) : ℂ :=
  arithmeticQuadraticCoefficient Q hQ D Φ
    (quadraticGridScale (Real.exp (-200 * T)) i.2.2.2) i.2.2.1 i.1 i.2.1
    (quadraticGridPhase (Real.exp (-200 * T)) i.2.2.2) s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed subfamily in which all small-kernel witnesses fail -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def fixedPrimeDivisorTerm (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (V U : Finset ℕ) (s : ℕ) : ℂ :=
  primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue i.1) V)
    (fun _ => (i.2.1 : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) i.2.2.2)
    Φ (quadraticGridScale (Real.exp (-200 * T)) i.2.2.2) V.toList.prod U s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ClosedQuadraticBand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed prime band used in the manuscript's quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def closedQuadraticBandMass (A : Set ℕ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ closedLogPrimeBand T, (Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicHarmonicBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring quadratic smallness to harmonic prime intervals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def harmonicQuadraticBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  maximalQuadraticBias (tailSupport A N p) p / p

noncomputable def harmonicQuadraticBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ iteratedLogPrimeBand α β L, harmonicQuadraticBias A N p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HalfPrimeEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common endpoint scalar in the Section 7 half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def endpointResidueValue {p : ℕ} (S : Finset (ZMod p)) : ℝ :=
  (1 - residueDensity S) / Real.sqrt (residueVariance S)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCutoffProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two cutoff weights control the full sampled product -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfCutoffWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (x : Fin (b + (d + r)) → P) : ℝ :=
  initialLogSumWeight value cb (fun i => x (i.castAdd (d + r))) *
    initialLogSumWeight value cd (fun i => x ((i.castAdd r).natAdd b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCubeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree bounds the number of centered coordinates -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def cubeSupport {n : ℕ} (t : BilinearCube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (t i).1 = true ∨ (t i).2 = true)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredCoordinateSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decomposing the actual tensor coordinates by their centered support -/

namespace Ostmann
open scoped Classical BigOperators

theorem supportedCoordinates_reconstruct {n : ℕ} (p : Fin n → ℕ)
    (x : ∀ i, Option (ZMod (p i))) :
    supportedCoordinates p (centeredCoordinateSupport x) (fun i => (x i).get
      (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp i.property).2)) = x := by
  funext i
  by_cases hi : x i = none
  · simp [supportedCoordinates, centeredCoordinateSupport, hi]
  · have hmem : i ∈ centeredCoordinateSupport x := by
      simp [centeredCoordinateSupport, hi]
    simp only [supportedCoordinates, dite_eq_left hmem]
    exact Option.some_get _

noncomputable def centeredSupportEquiv {n : ℕ} (p : Fin n → ℕ) :
    (∀ i, Option (ZMod (p i))) ≃ Σ T : Finset (Fin n), (∀ i : T, ZMod (p i)) where
  toFun x := ⟨centeredCoordinateSupport x, fun i => (x i).get
    (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp i.property).2)⟩
  invFun z := supportedCoordinates p z.1 z.2
  left_inv := supportedCoordinates_reconstruct p
  right_inv z := by
    apply supportedCoordinates_injective p
    exact supportedCoordinates_reconstruct p _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The additive large sieve for a uniform measure on an actual interval subset -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def intervalSetExponentialSum {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q h : ℕ) : ℂ :=
  ∑ n ∈ A, sieveAdditivePhase q h (J + (n.val : ℤ))

noncomputable def intervalSetReducedEnergy {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q : ℕ) : ℝ :=
  ∑ h ∈ reducedNumerators q,
    ‖(A.card : ℂ)⁻¹ * intervalSetExponentialSum A J q h‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialFrozenAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Fourier amplitude with both spectator lists fixed -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def initialFrozenAmplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) : ℂ :=
  let νr := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
  ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
    ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
      let x := Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)
      w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two half-lists in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators

/-- The left giant is `true`; fixed cells precede bulk in the moving template. -/
def initialRetainedIndexEquiv (b r : ℕ) :
    InitialRetainedSlot b r ⊕ InitialRetainedSlot b r ≃
      Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) where
  toFun
    | .inl (.inl _) => .inl true
    | .inr (.inl _) => .inl false
    | .inl (.inr (.inl i)) => .inr ((), .inr (i.castAdd b))
    | .inr (.inr (.inl i)) => .inr ((), .inr (Fin.natAdd b i))
    | .inl (.inr (.inr i)) => .inr ((), .inl (i.castAdd r))
    | .inr (.inr (.inr i)) => .inr ((), .inl (Fin.natAdd r i))
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr (_, .inl i) => Fin.addCases (fun j => .inl (.inr (.inr j)))
        (fun j => .inr (.inr (.inr j))) i
    | .inr (_, .inr i) => Fin.addCases (fun j => .inl (.inr (.inl j)))
        (fun j => .inr (.inr (.inl j))) i
  left_inv := by
    rintro ((u | (i | i)) | (u | (i | i))) <;>
      simp only [Fin.addCases_left, Fin.addCases_right]
  right_inv := by
    rintro (a | ⟨u, i | i⟩)
    · cases a <;> rfl
    · cases u
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right]
    · cases u
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right]

/-- Separate all fixed spectators, then the two giants and the moving slots. -/
def initialCompleteIndexEquiv (b d r : ℕ) :
    Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b)) ≃
      Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) :=
  (Equiv.sumCongr finSumFinEquiv.symm (initialRetainedIndexEquiv b r).symm).trans
    ((Equiv.sumSumSumComm (Fin d) (Fin d) (InitialRetainedSlot b r)
      (InitialRetainedSlot b r)).trans
      ((Equiv.sumCongr (initialSpectatorSlotEquiv b d r)
        (initialSpectatorSlotEquiv b d r)).trans finSumFinEquiv))

noncomputable def initialMovingTuple {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P :=
  Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y) ∘
    (initialCompleteIndexEquiv b d r).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preserving the original retained prior in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def initialMovingRegularPrior {P : Type*} (b r : ℕ)
    (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ) :
    MovingRegularSlot 0 (r + r) (b + b) → P → ℝ :=
  fun i => Sum.elim (Fin.append μc μc) (Fin.append μb μb) i.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original logarithmic cutoffs depend only on retained bulk data -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialMovingCutoffWeight {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) : ℂ :=
  ((initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
    initialLogSumWeight value cd sl : ℝ) : ℂ) *
  ((initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
    initialLogSumWeight value cd sr : ℝ) : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original distinct-prime test as the moving leaf's pairwise guard -/
namespace Ostmann
open scoped Classical

noncomputable def initialMovingSlotList (r m d : ℕ) :
    List (Fin d ⊕ (Bool ⊕ MovingRegularSlot 0 r m)) :=
  ([Sum.inr (.inl true), Sum.inr (.inl false)] ++
    (movingTemplateSlotList 0 r m).map (fun j => Sum.inr (.inr j))) ++
    (List.finRange d).map Sum.inl

noncomputable def initialMovingState (P : Finset ℕ) (b r : ℕ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    MovingSlotState P :=
  ⟨0, .leaf s ((movingTemplateSlotList 0 (r + r) (b + b)).map y), XL, XR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def initialRegularFromList {P : Type*} (b r : ℕ) (fallback : P)
    (L : List P) : MovingRegularSlot 0 (r + r) (b + b) → P :=
  fun i => L.getD ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).val fallback

/-- Internal states use the same total function, while only terminal data
are evaluated as leaves. The fallback is never used on a genuine template. -/
noncomputable def initialMovingDataCutoff {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) :
    {n : ℕ} → MovingSlotData P n → ℤ → ℂ :=
  fun {_n} T s => if s = 0 then 0 else
    initialMovingCutoffWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback T.regularSlots)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTreeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialMovingRealWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) : ℝ :=
  (initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
    initialLogSumWeight value cd sl) *
  (initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
    initialLogSumWeight value cd sr)

noncomputable def initialMovingTreeWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) :
    {n : ℕ} → MovingSlotData P n → ℝ
  | _, T@(.leaf _ _) => initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback T.regularSlots)
  | _, .node _ _ _ _ left right =>
      initialMovingTreeWeight value b d r cb cd sl sr fallback left *
        initialMovingTreeWeight value b d r cb cd sl sr fallback right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfBulkWeight {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (bulk : Fin (b + b) → P) : ℝ :=
  (initialLogSumWeight value cb (fun i : Fin b => bulk (i.castAdd b)) *
    initialLogSumWeight value cd sl) *
  (initialLogSumWeight value cb (fun i : Fin b => bulk (Fin.natAdd b i)) *
    initialLogSumWeight value cd sr)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfBulkProduct {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) :
    (n : ℕ) → (TreeLeafIndex n × Fin (b + b) → P) → ℝ
  | 0, slot => initialHalfBulkWeight value b d cb cd sl sr (fun i => slot ((), i))
  | n + 1, slot =>
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inl j.1, j.2)) *
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inr j.1, j.2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfLogSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two half-bulk cutoffs as a finite family of log weights -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfBulkLeaves {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (side : Bool) : TreeLeafTuple (List B) n :=
  bulkSlotLeaves n b (fun j => slot (j.1, if side then Fin.natAdd b j.2 else j.2.castAdd b))

noncomputable def initialHalfLogSlots {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) : Fin (2 ^ n + 2 ^ n) → List B :=
  movingBulkPairedCutoffSlots n (initialHalfBulkLeaves n b slot)

noncomputable def initialPairedHalfLogSlots {B : Type*} (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B) :
    Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n)) → List B :=
  Fin.append (initialHalfLogSlots n b (slot false)) (initialHalfLogSlots n b (slot true))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LocalSmoothGiantSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a complete giant cell inside a prescribed finite window

The averaging family may cover boundary primes several times. Its exact
partition weight is retained, so selecting a cell never clips its prime law.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def logCellFamilyWeight (C : Finset ℤ) (p : ℕ) : ℝ :=
  ∑ n ∈ C, logCellProfile (Real.log p - n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MaskedPhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The favorable-prime mask in the initial giant

Nonfavorable primes remain in the prior. Their physical test is exactly zero.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def favorablePhaseTransform {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (i : I) : ZMod (p i) → ℂ :=
  if i ∈ F then normalizedResidueTransform (S i) else fun _ => 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FullSummandResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full forbidden residue sets in the summand-size argument -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def negativeOccupiedResidues (B : Set ℕ) (p : ℕ) : Finset (ZMod p) :=
  (occupiedResidues B p).image fun r : ℕ => -(r : ZMod p)

noncomputable def allowedSummandResidues (B : Set ℕ) (p : ℕ) [NeZero p] :
    Finset (ZMod p) := Finset.univ \ negativeOccupiedResidues B p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothContourResidue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact local zero contributions in the smooth contour integral -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def smoothContourWeight (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * primeMeanMellin s

theorem smoothContourWeight_differentiable (X : ℝ) (hX : 0 < X) :
    Differentiable ℂ (smoothContourWeight X) :=
  (differentiable_id.const_cpow (.inl (by exact_mod_cast hX.ne'))).mul
    primeMeanMellin_differentiable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothLeftContourWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable majorant for the left vertical contour -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology

noncomputable def leftContourIntegrand (χ : PrimitiveComplexCharacter) (X t : ℝ) : ℂ :=
  (-deriv χ.L (leftContourLine t) / χ.L (leftContourLine t)) *
    smoothContourWeight X (leftContourLine t)

theorem leftContourWeight_norm (X t : ℝ) (hX : 0 < X) :
    ‖smoothContourWeight X (leftContourLine t)‖ =
      ‖primeMeanMellin (leftContourLine t)‖ / Real.sqrt X := by
  rw [smoothContourWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    leftContourLine_re, Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothRightContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of the starting vertical line in the contour shift -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology BigOperators

noncomputable def rightContourIntegrand (χ : PrimitiveComplexCharacter) (X t : ℝ) : ℂ :=
  (-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)) * primeVerticalWeight X t

theorem character_logDeriv_re_two_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = 2 → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (2 : ℂ) n‖
  have hsum : LSeriesSummable f (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    rw [show (2 : ℂ).re = (2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by rw [hs]; norm_num), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

theorem rightContourIntegrand_integrable (χ : PrimitiveComplexCharacter) (X : ℝ)
    (hX : 0 < X) : Integrable (rightContourIntegrand χ X) := by
  obtain ⟨C, hC, hbound⟩ := character_logDeriv_re_two_bound
  have hcn : Continuous (rightContourIntegrand χ X) := by
    have hL : Continuous χ.L := continuous_iff_continuousAt.mpr
      (fun z => (χ.L_analytic z).continuousAt)
    have hL' : Continuous (deriv χ.L) := continuous_iff_continuousAt.mpr
      (fun z => (χ.L_analytic z).deriv.continuousAt)
    have hn (t : ℝ) : χ.L (primeMellinLine t) ≠ 0 :=
      χ.L_ne_zero_one_le_re _ (by simp)
    exact ((hL'.comp primeMellinLine_continuous).neg.div
      (hL.comp primeMellinLine_continuous) hn).mul (primeVerticalWeight_continuous X hX)
  apply ((primeVerticalWeight_integrable X hX).norm.const_mul C).mono' hcn.aestronglyMeasurable
  filter_upwards with t
  rw [rightContourIntegrand, norm_mul]
  have hn : ‖-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)‖ =
      ‖logDeriv χ.L (primeMellinLine t)‖ := by simp [logDeriv_apply, neg_div]
  rw [hn]
  exact mul_le_mul_of_nonneg_right (hbound χ _ (by simp)) (norm_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleBoundary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval BigOperators

theorem rectangleBoundaryIntegral_sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    {a b c d : ℝ} (h : ∀ i ∈ S, RectangleIntegrable (f i) a b c d) :
    rectangleBoundaryIntegral (fun z => ∑ i ∈ S, f i z) a b c d =
      ∑ i ∈ S, rectangleBoundaryIntegral (f i) a b c d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectangleBoundaryIntegral]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [rectangleBoundaryIntegral_add (h i (Finset.mem_insert_self _ _))
      (RectangleIntegrable.sum S (fun j hj => h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmallDiskLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed small-disk logarithmic-derivative estimate -/

namespace Ostmann

open Complex Metric Set

theorem logDeriv_norm_le_five_quarters_disk (g : ℂ → ℂ) (A : ℝ) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 (3 / 2)))
    (hne : ∀ z ∈ ball 0 (3 / 2), g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 (3 / 2), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ 5 / 4) : ‖logDeriv g w‖ ≤ 352 * A := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g (3 / 2)
    (by norm_num) hg hne
  have hd : DifferentiableOn ℂ F (ball 0 (3 / 2)) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 (3 / 2)) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self (by norm_num))) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (1 / 16)) : ‖v‖ ≤ 21 / 16 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ 1 / 16 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (1 / 16)) : v ∈ ball 0 (3 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (1 / 16)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (1 / 16), ‖F v‖ ≤ 22 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < 3 / 2 - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal (by norm_num)
      (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 16) hdc hbound
  have hwball : w ∈ ball 0 (3 / 2) := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszPoleRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact contribution of a real pole to the Riesz rectangle -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem riesz_pole_rectangle (X : ℝ) (hX : 0 < X) (β a b c d : ℝ)
    (ha : 0 < a) (hab : a < β) (hβb : β < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (fun s => rieszContourWeight X s / (s - (β : ℂ))) a b c d =
      (2 * (Real.pi : ℂ) * I) * rieszContourWeight X (β : ℂ) := by
  let W := rieszContourWeight X
  let g := dslope W (β : ℂ)
  have hg : ∀ s ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g s := by
    intro s hs
    apply rieszWeight_dslope_analytic X hX (β : ℂ) (by simpa using ha.trans hab) s
    exact ha.trans_le ((uIcc_of_le (hab.trans hβb).le) ▸ hs.1).1
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ (β : ℂ) :=
    contourBoundary_ne_interior ⟨hab, hβb, hc, hd⟩ hs
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun s hs => (hg s ⟨hs.1, hs.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable (fun s => W (β : ℂ) * (s - (β : ℂ))⁻¹) a b c d :=
    (rectangleIntegrable_sub_inv ⟨hab, hβb, hc, hd⟩).const_mul _
  have heq : rectangleBoundaryIntegral (fun s => W s / (s - (β : ℂ))) a b c d =
      rectangleBoundaryIntegral (fun s => g s + W (β : ℂ) * (s - (β : ℂ))⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    dsimp [g]
    rw [dslope_of_ne _ (hnot s hs)]
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    ring
  rw [heq, rectangleBoundaryIntegral_add hgI hpI,
    rectangleBoundaryIntegral_eq_zero hg, zero_add, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_sub_inv (β : ℂ) a b c d hab hβb hc hd]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszExponentialParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
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

theorem riesz_exponential_error (c A B E : ℝ) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    ∀ᶠ y : ℝ in atTop, ∀ H : ℝ, 0 < H → H ≤ 3 * y →
      A * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 - c / H) +
        B * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 +
        2 * (1 / ((1 + 1 / y ^ 2) - 1) + E) *
          (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
        3 * Real.exp (y ^ 2 - (c / 6) * y) := by
  let d := c / 6
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 2 * d ≤ 1 := by dsimp [d]; linarith
  have hp1 := riesz_polynomial_absorption (9 * A) d hd
  have hp2 := riesz_polynomial_absorption (9 * B * Real.exp 1) d hd
  have hp3 := riesz_polynomial_absorption (2 * (1 + E) * Real.exp 1) d hd
  filter_upwards [hp1, hp2, hp3, eventually_ge_atTop (1 : ℝ)] with y hyA hyB hyE hy1
  intro H hH hHy
  have hy0 : 0 < y := by linarith
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0.ne'
  have hH2 : H ^ 2 ≤ 9 * y ^ 2 := by nlinarith
  have h1 : A * H ^ 2 ≤ Real.exp (d * y) := by
    apply le_trans _ hyA
    nlinarith [mul_le_mul_of_nonneg_left hH2 hA]
  have h2 : B * H ^ 2 * Real.exp 1 ≤ Real.exp (d * y) := by
    apply le_trans _ hyB
    have he := Real.exp_pos (1 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hH2 (mul_nonneg hB he.le)]
  have h3 : 2 * (y ^ 2 + E) * Real.exp 1 ≤ Real.exp (d * y) := by
    apply le_trans _ hyE
    have he := Real.exp_pos (1 : ℝ)
    nlinarith [mul_nonneg hE (sq_nonneg y),
      mul_nonneg (mul_nonneg hE (sq_nonneg y)) he.le]
  have hrpow (r : ℝ) : (Real.exp (y ^ 2)) ^ r = Real.exp (y ^ 2 * r) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hr : (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) =
      Real.exp (y ^ 2) * Real.exp 1 := by
    rw [hrpow, show y ^ 2 * (1 + 1 / y ^ 2) = y ^ 2 + 1 by field_simp,
      Real.exp_add]
  have hgap : y ^ 2 * (1 - c / H) ≤ y ^ 2 - 2 * d * y := by
    have hh : c * y / 3 ≤ c / H * y ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hHy (show 0 ≤ c * y by positivity)
      rw [show c / H * y ^ 2 = c * y ^ 2 / H by ring]
      apply (le_div_iff₀ hH).mpr
      nlinarith
    dsimp [d]
    nlinarith
  have ht1 : A * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 - c / H) ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hrpow]
    calc
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - 2 * d * y) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr hgap) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht2 : B * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hr, ← Real.exp_nat_mul]
    calc
      _ = (B * H ^ 2 * Real.exp 1) * Real.exp (y ^ 2 - 2 * y) := by
        rw [Real.exp_sub]; ring_nf
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - 2 * y) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have ht3 : 2 * (1 / ((1 + 1 / y ^ 2) - 1) + E) *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hr, show 1 / ((1 + 1 / y ^ 2) - 1) = y ^ 2 by field_simp; ring]
    calc
      _ = (2 * (y ^ 2 + E) * Real.exp 1) * Real.exp (y ^ 2 - y) := by
        rw [Real.exp_sub]; ring
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - y) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  dsimp [d] at ht1 ht2 ht3
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszLocalDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay with the actual local exceptional-zero contribution -/

namespace Ostmann

open Filter

theorem character_riesz_height_log_bound (χ : PrimitiveComplexCharacter) (y : ℝ)
    (hy : 5 ≤ y) (hχ : (χ.modulus : ℝ) ≤ Real.exp y) :
    0 < Real.log χ.modulus + Real.log (Real.exp y + 4) + 1 ∧
      Real.log χ.modulus + Real.log (Real.exp y + 4) + 1 ≤ 3 * y := by
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (Real.exp y + 4) := Real.log_nonneg (by linarith [Real.exp_pos y])
  refine ⟨by linarith, ?_⟩
  have hqy : Real.log χ.modulus ≤ y := by
    simpa only [Real.log_exp] using Real.log_le_log (by exact_mod_cast χ.positive) hχ
  have he : 4 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hty : Real.log (Real.exp y + 4) ≤ Real.log 2 + y := by
    calc
      _ ≤ Real.log (2 * Real.exp y) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact starting contour for the principal Riesz mean -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

theorem principalRieszVerticalTerm_integrable
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    Integrable (principalRieszVerticalTerm X σ n) := by
  apply ((rieszVerticalWeight_integrable X σ hX hσ).norm.const_mul
    ‖LSeries.term (principalMangoldtCoefficient) (σ : ℂ) n‖).mono'
  · exact ((principalMangoldt_riesz_term_continuous σ n).mul
      (rieszVerticalWeight_continuous X σ hX (by linarith))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (principalRieszVerticalTerm_norm X σ n t).le)

theorem principalRieszVerticalTerm_summable_norm
    (X σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ∫ t : ℝ, ‖principalRieszVerticalTerm X σ n t‖) := by
  have hsum : LSeriesSummable (principalMangoldtCoefficient) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hs := hsum.norm.mul_right (∫ t : ℝ, ‖rieszVerticalWeight X σ t‖)
  apply hs.congr
  intro n
  simp only [principalRieszVerticalTerm_norm, integral_const_mul]

theorem principalRieszMean_eq_vertical_logDerivative
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    principalRieszMean X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-logDeriv riemannZeta (rieszMellinLine σ t)) * rieszVerticalWeight X σ t := by
  unfold principalRieszMean
  calc
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, principalRieszVerticalTerm X σ n t :=
      tsum_congr (fun n => (principalMangoldt_riesz_term_inversion X σ hX hσ.le n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, principalRieszVerticalTerm X σ n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, principalRieszVerticalTerm X σ n t := by
      rw [integral_tsum_of_summable_integral_norm
        (principalRieszVerticalTerm_integrable X σ hX hσ.le)
        (principalRieszVerticalTerm_summable_norm X σ hσ)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [show (∑' n : ℕ, principalRieszVerticalTerm X σ n t) =
        LSeries (principalMangoldtCoefficient) (rieszMellinLine σ t) * rieszVerticalWeight X σ t from tsum_mul_right]
      have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := rieszMellinLine σ t) (by simpa using hσ)
      have he' : LSeries principalMangoldtCoefficient (rieszMellinLine σ t) =
          -logDeriv riemannZeta (rieszMellinLine σ t) := by
        change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _
        simpa only [logDeriv_apply, neg_div] using he
      rw [he']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ArithmeticRieszMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite Riesz sums and character orthogonality -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszPrimeTest_norm_le_one (u : ℝ) (hu : 0 ≤ u) : ‖rieszPrimeTest u‖ ≤ 1 := by
  rw [rieszPrimeTest, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) zero_le_one

theorem rieszTwistMean_eq_principal (X : ℝ) (hX : 0 < X) :
    rieszTwistMean (fun _ => 1) X = principalRieszMean X := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      principalMangoldtCoefficient n * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp [principalMangoldtCoefficient]
    · have hnlarge : ⌊X⌋₊ < n := by simp only [Finset.mem_Ioc] at hn; omega
      have hlarge : X < n := Nat.lt_of_floor_lt hnlarge
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [principalRieszMean, tsum_eq_sum hs]
  simp only [rieszTwistMean, principalMangoldtCoefficient, mul_one]

theorem rieszResidueMean_orthogonality (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) :
    (q.totient : ℂ) * rieszResidueMean q a X =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * rieszTwistMean (fun n => χ (n : ZMod q)) X := by
  classical
  simp only [rieszResidueMean, rieszTwistMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have ho := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  calc
    _ = (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (n : ZMod q)) *
        (ArithmeticFunction.vonMangoldt n : ℂ) * rieszPrimeTest (n / X) := by
      rw [ho]
      by_cases hn : (n : ZMod q) = a
      · rw [ite_eq_left hn, ite_eq_left hn.symm]
        ring
      · rw [ite_eq_right hn, ite_eq_right (Ne.symm hn)]
        ring
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform shifted Gamma factors for actual primitive characters -/

namespace Ostmann

open Complex
open scoped Classical

noncomputable def densityCompletedSquareWeight (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ w *
    (DirichletCharacter.gammaFactor χ.character (s + w) /
      DirichletCharacter.gammaFactor χ.character s) ^ 2 * Complex.exp (w ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterHeightZeroCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the finite set of forbidden contour ordinates -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem criticalZerosUpTo_card_bound (χ : PrimitiveComplexCharacter) (T : ℝ) (hT : 0 ≤ T) :
    ((criticalZerosUpTo χ T).card : ℝ) ≤
      (32 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  calc
    _ = ∑ _z ∈ criticalZerosUpTo χ T, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ criticalZerosUpTo χ T, (characterZeroOrder χ z : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      have he := (mem_criticalZerosUpTo.mp hz).1.2.2
      have ho := (characterZeroOrder_pos_iff χ z).mpr he
      have hi : (1 : ℤ) ≤ characterZeroOrder χ z := ho
      exact_mod_cast hi
    _ ≤ _ := χ.full_zero_sum_rate T hT _ (by
      intro z hz
      obtain ⟨hz, hi⟩ := mem_criticalZerosUpTo.mp hz
      exact ⟨hz.1, hz.2.1, hi⟩)

theorem criticalZerosUpTo_card_polynomial (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      ((criticalZerosUpTo χ (T + 4)).card : ℝ) ≤ C * (T + 5) ^ 2 := by
  let A := 32 / Real.log (14 / 13 : ℝ)
  have hA : 0 < A := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hq : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  refine ⟨2 * A * χ.modulus, by positivity, ?_⟩
  intro T hT
  have hh := criticalZerosUpTo_card_bound χ (T + 4) (by linarith)
  have hl : Real.log ((χ.modulus : ℝ) * (T + 4 + 2)) ≤
      (χ.modulus : ℝ) * (T + 4 + 2) := by
    have he := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (χ.modulus : ℝ) * (T + 4 + 2))
    linarith
  have hx : T + 4 + 2 ≤ 2 * (T + 5) := by linarith
  calc
    _ ≤ A * (T + 4 + 1) * Real.log ((χ.modulus : ℝ) * (T + 4 + 2)) := hh
    _ ≤ A * (T + 4 + 1) * ((χ.modulus : ℝ) * (2 * (T + 5))) := by
      exact mul_le_mul_of_nonneg_left
        (hl.trans (mul_le_mul_of_nonneg_left hx hq.le)) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedCompensationPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A total prior extending precisely the used compensation cells

Unused indices reuse the selected top cell. The pivot exponent retains its
original zero default beyond the finite list; no extra transfer is performed.
-/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def completedCompensationSets (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) : Finset ℕ :=
  selectedTailCellPrimes A B N X hi D (completedCompensationCell top cs n)

noncomputable def completedCompensationPrior (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) : P → ℝ :=
  primeSubsetPrior P (completedCompensationSets A B N X hi D top cs n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexLowZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The low-zero Laplace estimate from the published density theorem -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def lowZeroIndices (Z : ∀ χ, ComplexZeroEnumeration χ)
    (F : Finset PrimitiveComplexCharacter) (T : ℝ) : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ) :=
  F.sigma fun χ => ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCompletedSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire completed square and its exact reflection -/

namespace Ostmann

open Complex

noncomputable def densityCompletedSquare (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ s * χ.completed s ^ 2

noncomputable def densitySquareNormalizer (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ s * (DirichletCharacter.gammaFactor χ.character s) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true truncated Mobius series in the zero detector -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityDetectorCharacterCoefficient (χ : PrimitiveComplexCharacter)
    (X n : ℕ) : ℂ := χ.character (n : ZMod χ.modulus) * densityDetectorCoefficient X n

noncomputable def densityDetectorMean (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
    densityDetectorWeight (n / Y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareGaussian
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gaussian contour for the actual completed square -/

namespace Ostmann

open Complex

noncomputable def densitySquareGaussian (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densityCompletedSquare χ (s + w) * Complex.exp (w ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The convergent vertical lines and vanishing horizontal edges -/

namespace Ostmann

open Complex Filter MeasureTheory Set
open scoped Topology Interval

noncomputable def densitySquareContour (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densitySquareGaussian χ s w / w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Gaussian functional equation for the completed square -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology Interval

noncomputable def densitySquareIntegral (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ, densitySquareContour χ s (1 + u * I)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityNormalizedEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized square functional equation on the critical line -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

noncomputable def densitySmoothedSquare (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  densitySquareIntegral χ s / densitySquareNormalizer χ s

noncomputable def densitySquareRootFactor (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
    densitySquareNormalizer χ.inverse (1 - s) / densitySquareNormalizer χ s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySmoothedKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized right-hand kernel in the square functional equation -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densitySquareKernel (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densityCompletedSquareWeight χ s w / w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFiniteContourShift
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifting the actual finite Dirichlet polynomial to a short positive line -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable def densityFiniteKernel (χ : PrimitiveComplexCharacter) (s : ℂ)
    (S : Finset ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  densitySquareKernel χ s w * densityFiniteMellin S a w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolutely integrable Dirichlet terms on the initial right line -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densitySquareCoefficient (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  χ.character (n : ZMod χ.modulus) * (n.divisors.card : ℂ)

noncomputable def densitySquareSeriesTerm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (n : ℕ) (u : ℝ) : ℂ :=
  densitySquareKernel χ s (1 + u * I) *
    LSeries.term (densitySquareCoefficient χ) (s + (1 + u * I)) n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareSeriesIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exchanging the actual divisor series and the Gaussian contour integral -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densitySquareIntegralTerm (χ : PrimitiveComplexCharacter) (s : ℂ) (n : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ, densitySquareSeriesTerm χ s n u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact initial contour of the compact Mobius zero detector -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators Classical

noncomputable def densityDetectorVerticalTerm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (densityDetectorCharacterCoefficient χ X) (s + (2 + (t : ℂ) * I)) n *
    (Y : ℂ) ^ (2 + (t : ℂ) * I) * densityDetectorKernel (2 + (t : ℂ) * I)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityDetectorAnalytic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the detector contour pole at an actual L-function zero -/

namespace Ostmann

open Complex Set
open scoped BigOperators

noncomputable def densityDetectorFactor (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  χ.L (s + w) * densityMollifier X χ.character (s + w) * (Y : ℂ) ^ w /
    ((w + 1) * (w + 2))

noncomputable def densityDetectorIntegrand (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  χ.L (s + w) * densityMollifier X χ.character (s + w) * (Y : ℂ) ^ w *
    densityDetectorKernel w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCriticalDetector
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The detector in the height convention of the proved moments -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densityCriticalProduct (χ : PrimitiveComplexCharacter) (X : ℕ)
    (t u : ℝ) : ℂ :=
  χ.L (densityVerticalPoint (1 / 2) (t + u)) *
    densityMollifier X χ.character (densityVerticalPoint (1 / 2) (t + u))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensitySquareLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of the growing original square sums -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped BigOperators Topology Classical

 @[simp] theorem densitySquareIntegralTerm_zero (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareIntegralTerm χ s 0 = 0 := by
  simp [densitySquareIntegralTerm, densitySquareSeriesTerm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCriticalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal critical-line mass controlling the integral alternative -/

namespace Ostmann

open MeasureTheory

noncomputable def densityCriticalMass (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) : ℝ :=
  ∫ v, densityCubicWeight (v - t) * ‖χ.L (densityVerticalPoint (1 / 2) v)‖ *
    ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) v)‖

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszUnsmoothing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering sharp positive counts from the integrated count -/

namespace Ostmann

open scoped BigOperators

theorem finiteRieszSum_step (S : Finset ℕ) (w : ℕ → ℝ) (x h : ℝ)
    (hh : 0 ≤ h) (hw : ∀ n ∈ S, 0 ≤ w n) :
    h * (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) ≤
        finiteRieszSum S w (x + h) - finiteRieszSum S w x ∧
      finiteRieszSum S w (x + h) - finiteRieszSum S w x ≤
        h * (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x + h), w n) := by
  have hdiff : finiteRieszSum S w (x + h) - finiteRieszSum S w x =
      ∑ n ∈ S, w n * (max (x + h - n) 0 - max (x - n) 0) := by
    simp only [finiteRieszSum, mul_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  constructor
  · have hb := Finset.sum_le_sum (s := S) (fun n hn =>
      mul_le_mul_of_nonneg_left (positivePart_step_lower x n h hh) (hw n hn))
    simpa only [mul_ite, mul_zero, Finset.sum_filter, Finset.mul_sum, mul_comm] using hb
  · have hb := Finset.sum_le_sum (s := S) (fun n hn =>
      mul_le_mul_of_nonneg_left (positivePart_step_upper x n h hh) (hw n hn))
    simpa only [mul_ite, mul_zero, Finset.sum_filter, Finset.mul_sum, mul_comm] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszPositiveRecovery
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite differences recover the sharp arithmetic count -/

namespace Ostmann

open scoped BigOperators

theorem finiteRieszSum_recover (S : Finset ℕ) (w : ℕ → ℝ) (x h m D : ℝ)
    (hh : 0 < h) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hplus : finiteRieszSum S w (x + h) - finiteRieszSum S w x ≤ h * m + D)
    (hminus : h * m - D ≤ finiteRieszSum S w x - finiteRieszSum S w (x - h)) :
    |(∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m| ≤ D / h := by
  have hupper := (finiteRieszSum_step S w x h hh.le hw).1
  have hlower := (finiteRieszSum_step S w (x - h) h hh.le hw).2
  rw [sub_add_cancel] at hlower
  have habs : |h * ((∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m)| ≤ D := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hh] at habs
  exact (le_div_iff₀ hh).mpr (by nlinarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszSmoothRecovery
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive unsmoothing with a twice differentiable main term -/

namespace Ostmann

open Set
open scoped BigOperators

theorem finiteRieszSum_smooth_recovery (S : Finset ℕ) (w : ℕ → ℝ)
    (F : ℝ → ℝ) (x h m E : ℝ) (hh : 0 < h) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hzero : |finiteRieszSum S w x - F x| ≤ E)
    (hplus : |finiteRieszSum S w (x + h) - F (x + h)| ≤ E)
    (hminus : |finiteRieszSum S w (x - h) - F (x - h)| ≤ E)
    (hFplus : |F (x + h) - F x - h * m| ≤ 2 * h ^ 2)
    (hFminus : |F x - F (x - h) - h * m| ≤ 2 * h ^ 2) :
    |(∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) - m| ≤ 2 * h + 2 * E / h := by
  have hb := finiteRieszSum_recover S w x h m (2 * h ^ 2 + 2 * E) hh hw
    (by have ha := (abs_le.mp hplus).2; have hc := (abs_le.mp hzero).1
        have hf := (abs_le.mp hFplus).2; linarith)
    (by have ha := (abs_le.mp hminus).2; have hc := (abs_le.mp hzero).1
        have hf := (abs_le.mp hFminus).1; linarith)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntegratedThetaMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated principal and exceptional main term for positive unsmoothing -/

namespace Ostmann

theorem hasDerivAt_integratedThetaMain (φ χ β : ℝ) (hβ : 0 < β)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (integratedThetaMain φ χ β) (thetaMainTerm φ χ β x) x := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).sub
    (((Real.hasDerivAt_rpow_const (p := β + 1) (.inl hx.ne')).const_mul χ).div_const (β * (β + 1)))
  have h := h.div_const φ
  norm_num only [Nat.reduceSub, pow_one, mul_one, id_eq] at h
  change HasDerivAt (integratedThetaMain φ χ β)
    ((2 * x / 2 - χ * ((β + 1) * x ^ (β + 1 - 1)) / (β * (β + 1))) / φ) x at h
  have he : (2 * x / 2 - χ * ((β + 1) * x ^ (β + 1 - 1)) / (β * (β + 1))) / φ =
      thetaMainTerm φ χ β x := by
    rw [show β + 1 - 1 = β by ring]
    unfold thetaMainTerm
    congr 1
    field_simp
  exact he ▸ h

theorem thetaMainDensity_abs_le_two (φ χ β x : ℝ)
    (hφ : 1 ≤ φ) (hχ : |χ| ≤ 1) (hβ : β ≤ 1) (hx : 1 ≤ x) :
    |thetaMainDensity φ χ β x| ≤ 2 := by
  have hφp : 0 < φ := by linarith
  have hp : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg (by linarith) _
  have hpow : x ^ (β - 1) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx (show β - 1 ≤ 0 by linarith)
    simpa using hh
  have hmul : |χ * x ^ (β - 1)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp]
    exact (mul_le_mul hχ hpow hp zero_le_one).trans_eq (one_mul 1)
  have hnum : |1 - χ * x ^ (β - 1)| ≤ 2 := by
    have hh := abs_sub (1 : ℝ) (χ * x ^ (β - 1))
    norm_num only [abs_one] at hh
    linarith
  rw [thetaMainDensity, abs_div, abs_of_pos hφp]
  apply (div_le_iff₀ hφp).mpr
  linarith

theorem integratedThetaMain_remainder_pair (φ χ β x h : ℝ)
    (hφ : 1 ≤ φ) (hχ : |χ| ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hx : 1 ≤ x - h) :
    |integratedThetaMain φ χ β (x + h) - integratedThetaMain φ χ β x -
        h * thetaMainTerm φ χ β x| ≤ 2 * h ^ 2 ∧
      |integratedThetaMain φ χ β x - integratedThetaMain φ χ β (x - h) -
        h * thetaMainTerm φ χ β x| ≤ 2 * h ^ 2 := by
  apply smooth_main_remainder_pair (integratedThetaMain φ χ β) (thetaMainTerm φ χ β)
    (thetaMainDensity φ χ β) x h hh
  · intro t ht
    exact hasDerivAt_integratedThetaMain φ χ β hβ (by have := ht.1; linarith)
  · intro t ht
    exact hasDerivAt_thetaMainTerm φ χ β hβ.ne' (by have := ht.1; linarith)
  · intro t ht
    exact thetaMainDensity_abs_le_two φ χ β t hφ hχ hβ1 (hx.trans ht.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal Riesz rectangle, including zeta's actual pole -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem principalRieszContour_rectangle (X : ℝ) (hX : 0 < X) (a b c d : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hne : ∀ s ∈ uIcc a b ×ℂ uIcc c d, regularizedZeta s ≠ 0) :
    rectangleBoundaryIntegral (principalRieszContour X) a b c d =
      (2 * (Real.pi : ℂ) * I) * (X / 2 : ℝ) := by
  let g : ℂ → ℂ := fun s => -logDeriv regularizedZeta s * rieszContourWeight X s
  let p : ℂ → ℂ := fun s => rieszContourWeight X s / (s - 1)
  have hspos (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc c d) : 0 < s.re :=
    ha.trans_le ((uIcc_of_le (ha1.trans hb).le) ▸ hs.1).1
  have hg : ∀ s ∈ uIcc a b ×ℂ uIcc c d, AnalyticAt ℂ g s := by
    intro s hs
    exact (((regularizedZeta_analytic s).deriv.div (regularizedZeta_analytic s)
      (hne s hs)).neg).mul (rieszContourWeight_analyticAt X hX s (hspos s hs))
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ 1 :=
    contourBoundary_ne_interior ⟨ha1, hb, hc, hd⟩ hs
  have hgI : RectangleIntegrable g a b c d := rectangleIntegrable_of_continuousOn
    (fun s hs => (hg s ⟨hs.1, hs.2.1⟩).continuousAt.continuousWithinAt)
  have hpI : RectangleIntegrable p a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro s hs
    exact ((rieszContourWeight_analyticAt X hX s (hspos s ⟨hs.1, hs.2.1⟩)).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (hnot s hs))).continuousAt.continuousWithinAt
  have heq : rectangleBoundaryIntegral (principalRieszContour X) a b c d =
      rectangleBoundaryIntegral (fun s => g s + p s) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    have hz : riemannZeta s ≠ 0 := by
      intro he
      apply hne s ⟨hs.1, hs.2.1⟩
      rw [regularizedZeta_eq s (hnot s hs), he, mul_zero]
    have hh := regularizedZeta_logDeriv_off_one s (hnot s hs) hz
    dsimp [principalRieszContour, g, p]
    rw [hh]
    ring
  rw [heq, rectangleBoundaryIntegral_add hgI hpI, rectangleBoundaryIntegral_eq_zero hg, zero_add]
  have hp := riesz_pole_rectangle X hX 1 a b c d ha ha1 hb hc hd
  change rectangleBoundaryIntegral (fun s => rieszContourWeight X s / (s - 1)) a b c d = _ at hp
  have hweight : rieszContourWeight X (1 : ℂ) = (X / 2 : ℝ) := by
    simp [rieszContourWeight, rieszMellinKernel]
    ring
  simpa only [p, Complex.ofReal_one, hweight] using hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaAbsoluteRightBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute zeta logarithmic-derivative control on right vertical lines -/

namespace Ostmann

open Complex LSeries
open scoped ComplexOrder

theorem zeta_logDeriv_right_pole_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → ‖logDeriv riemannZeta s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C, hC, hb⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha : LSeriesSummable a (s.re : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have ht : LSeriesSummable a s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hn (n : ℕ) : ‖LSeries.term a s n‖ = ‖LSeries.term a (s.re : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  have hr (n : ℕ) : ‖LSeries.term a (s.re : ℂ) n‖ = (LSeries.term a (s.re : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s.re))
    simpa only [Complex.ofReal_re] using hh.symm
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries a s = _ at he
  calc
    _ = ‖LSeries a s‖ := by rw [he, logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm ht.norm
    _ = ∑' n, ‖LSeries.term a (s.re : ℂ) n‖ := tsum_congr hn
    _ = (LSeries a (s.re : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s.re : ℂ)‖ := Complex.re_le_norm _
    _ ≤ _ := hb s.re hs hs2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal Riesz error from the regularized zeta rectangle -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem zeta_logDeriv_from_regularized (s : ℂ) (hs : s ≠ 1)
    (hz : regularizedZeta s ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ ‖s - 1‖) :
    ‖logDeriv riemannZeta s‖ ≤ ‖logDeriv regularizedZeta s‖ + 1 / δ := by
  have hzne : riemannZeta s ≠ 0 := by
    intro he
    apply hz
    rw [regularizedZeta_eq s hs, he, mul_zero]
  have he : logDeriv riemannZeta s = logDeriv regularizedZeta s - (s - 1)⁻¹ := by
    rw [regularizedZeta_logDeriv_off_one s hs hzne]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_inv, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hδ hd

theorem zeta_logDeriv_right_continuous (b : ℝ) (hb : 1 < b) :
    Continuous (fun t : ℝ => -logDeriv riemannZeta (rieszMellinLine b t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : rieszMellinLine b t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [rieszMellinLine_re, Complex.one_re] at hh
    linarith
  have ha := analyticOn_riemannZeta (rieszMellinLine b t) hs
  have hn := riemannZeta_ne_zero_of_one_le_re (by simpa using hb.le : 1 ≤ (rieszMellinLine b t).re)
  exact (((ha.deriv.div ha hn).neg).continuousAt).comp (rieszMellinLine_continuous b).continuousAt

theorem principalRieszMean_rectangle_bound : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ X a b T M : ℝ, 1 ≤ X → 1 / 2 ≤ a → a < 1 → 1 < b → b ≤ 2 → 0 < T → 0 ≤ M →
      (∀ s ∈ uIcc a b ×ℂ uIcc (-T) T, regularizedZeta s ≠ 0) →
      (∀ s ∈ uIcc a b ×ℂ uIcc (-T) T, ‖logDeriv regularizedZeta s‖ ≤ M) →
      ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
        K * (M + 1 / (1 - a)) * X ^ a +
        2 * ((M + 1 / T) * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨K, hK, hleft⟩ := weightedRiesz_left_segment_bound
  obtain ⟨C, hC, hright⟩ := zeta_logDeriv_right_pole_bound
  refine ⟨K, C, hK, hC, ?_⟩
  intro X a b T M hX ha ha1 hb hb2 hT hM hne hbound
  have hXp : 0 < X := by linarith
  have hab : a ≤ b := by linarith
  have hmem (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
      (σ : ℂ) + (t : ℂ) * I ∈ uIcc a b ×ℂ uIcc (-T) T := by
    constructor
    · simpa [uIcc_of_le hab] using hσ
    · simpa [uIcc_of_le (show -T ≤ T by linarith)] using ht
  have hlow (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖-logDeriv riemannZeta (rieszMellinLine a t)‖ ≤ M + 1 / (1 - a) := by
    have hs : rieszMellinLine a t ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [rieszMellinLine_re, Complex.one_re] at hh
      linarith
    have hd : 1 - a ≤ ‖rieszMellinLine a t - 1‖ := by
      have hh := Complex.abs_re_le_norm (rieszMellinLine a t - 1)
      simpa [abs_of_neg (show a - 1 < 0 by linarith)] using hh
    have hm := hmem a t ⟨le_rfl, hab⟩ ht
    simpa only [norm_neg] using (zeta_logDeriv_from_regularized _ hs (hne _ hm)
      (1 - a) (by linarith) hd).trans (add_le_add (hbound _ hm) le_rfl)
  have hedge (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t| = T) :
      ‖-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M + 1 / T := by
    have hi : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by simp
    have hd : T ≤ ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ := by
      have hh := Complex.abs_im_le_norm (((σ : ℂ) + (t : ℂ) * I) - 1)
      rwa [hi, ht] at hh
    have hs : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro he
      rw [he, sub_self, norm_zero] at hd
      linarith
    have hm := hmem σ t hσ (abs_le.mp (le_of_eq ht))
    simpa only [norm_neg] using (zeta_logDeriv_from_regularized _ hs (hne _ hm)
      T hT hd).trans (add_le_add (hbound _ hm) le_rfl)
  have hl := hleft (fun s => -logDeriv riemannZeta s) X a T (M + 1 / (1 - a))
    hXp ha (by positivity) hlow
  have hl' : ‖∫ t in -T..T, principalRieszContour X ((a : ℂ) + (t : ℂ) * I)‖ ≤
      K * (M + 1 / (1 - a)) * X ^ a := by
    simpa only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
      integral_Icc_eq_integral_Ioc, principalRieszContour, rieszContourWeight,
      rieszVerticalWeight, rieszMellinLine] using hl
  have hu := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv riemannZeta s)
    X a b T (M + 1 / T) hX hab (by simpa [abs_of_pos hT]) (by positivity)
    (fun σ hσ => hedge σ T hσ (abs_of_pos hT))
  have hd := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv riemannZeta s)
    X a b (-T) (M + 1 / T) hX hab (by simpa [abs_neg, abs_of_pos hT]) (by positivity)
    (fun σ hσ => hedge σ (-T) hσ (by rw [abs_neg, abs_of_pos hT]))
  rw [neg_sq] at hd
  have hr := principalRieszContour_rectangle X hXp a b (-T) T (by linarith) ha1 hb
    (by linarith) hT hne
  have hr' : rectangleBoundaryIntegral (principalRieszContour X) a b (-T) T =
      I * (((2 * Real.pi : ℝ) : ℂ) * (X / 2 : ℝ)) := by
    rw [hr]
    push_cast
    ring
  have hv := rectangle_vertical_shift_residue_norm_bound _ a b (-T) T _ hr'
  have hrightBound (t : ℝ) : ‖-logDeriv riemannZeta (rieszMellinLine b t)‖ ≤ 1 / (b - 1) + C := by
    simpa only [norm_neg, rieszMellinLine_re] using hright (rieszMellinLine b t) (by simpa using hb) (by simpa using hb2)
  have ht := riesz_residue_truncation (fun s => -logDeriv riemannZeta s) X b
    (1 / (b - 1) + C) T (X / 2 : ℝ) hXp hb.le (by positivity) hT
    (zeta_logDeriv_right_continuous b hb) hrightBound
  rw [← principalRieszMean_eq_vertical_logDerivative X b hXp hb] at ht
  change ‖(∫ t in -T..T, principalRieszContour X ((b : ℂ) + (t : ℂ) * I)) - _‖ ≤ _ at hv
  change ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
    ‖(∫ t in -T..T, principalRieszContour X ((b : ℂ) + (t : ℂ) * I)) -
      ((2 * Real.pi : ℝ) : ℂ) * (X / 2 : ℝ)‖ + _ at ht
  change ‖∫ σ in a..b, principalRieszContour X ((σ : ℂ) + (T : ℂ) * I)‖ ≤ _ at hu
  change ‖∫ σ in a..b, principalRieszContour X ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ _ at hd
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszFiniteSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the Riesz contour with the finite arithmetic sum -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszPrimeTest_scale (X y : ℝ) (hX : 0 < X) :
    rieszPrimeTest (y / X) = ((max (X - y) 0 / X : ℝ) : ℂ) := by
  by_cases hy : y ≤ X
  · have hdiv : y / X ≤ 1 := (div_le_one hX).mpr hy
    rw [rieszPrimeTest, max_eq_left (by linarith : 0 ≤ 1 - y / X),
      max_eq_left (sub_nonneg.mpr hy)]
    push_cast
    field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']
  · have hdiv : 1 < y / X := (one_lt_div hX).mpr (lt_of_not_ge hy)
    rw [rieszPrimeTest, max_eq_right (by linarith : 1 - y / X ≤ 0),
      max_eq_right (by linarith : X - y ≤ 0)]
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszPrimeRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Higher prime powers in the literal Riesz mean -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def rieszPrimeMean (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    (Real.log n : ℂ) * g n * rieszPrimeTest (n / X)

theorem rieszTwistMean_sub (g h : ℕ → ℂ) (X : ℝ) :
    rieszTwistMean g X - rieszTwistMean h X = rieszTwistMean (fun n => g n - h n) X := by
  simp only [rieszTwistMean, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem rieszTwistMean_sub_prime (g : ℕ → ℂ) (X : ℝ) :
    rieszTwistMean g X - rieszPrimeMean g X =
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X) := by
  have hh := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) Nat.Prime
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X))
  have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)) = rieszPrimeMean g X := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  rw [hp] at hh
  change rieszPrimeMean g X + _ = rieszTwistMean g X at hh
  linear_combination -hh

theorem rieszTwistMean_prime_error (g : ℕ → ℂ) (X B : ℝ)
    (hX : 1 ≤ X) (hB : 0 ≤ B) (hg : ∀ n, ‖g n‖ ≤ B) :
    ‖rieszTwistMean g X - rieszPrimeMean g X‖ ≤ B * (2 * Real.sqrt X * Real.log X) := by
  rw [rieszTwistMean_sub_prime]
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        B * ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hw := rieszPrimeTest_norm_le_one (n / X) (by positivity)
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n * B) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg n) ArithmeticFunction.vonMangoldt_nonneg)
            hw (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = B * (Chebyshev.psi X - Chebyshev.theta X) := by
      rw [← Finset.mul_sum, nonprime_mangoldt_sum]
    _ ≤ B * (2 * Real.sqrt X * Real.log X) := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)) hB

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszCoprimeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Riesz cost of changing coefficients only at primes dividing the modulus -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszPrimeMean_norm_le_of_coprime_zero (g : ℕ → ℂ) (q : ℕ) (X B : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n, ‖g n‖ ≤ B) (hz : ∀ n, n.Coprime q → g n = 0) :
    ‖rieszPrimeMean g X‖ ≤ B * q * Real.log X := by
  classical
  let S := (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime
  let D := S.filter (fun n => ¬n.Coprime q)
  have hsub : D ⊆ Finset.Ioc 0 q := by
    intro n hn
    obtain ⟨hnS, hnq⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hnp⟩ := Finset.mem_filter.mp hnS
    have hd : n ∣ q := by
      by_contra hd
      exact hnq (hnp.coprime_iff_not_dvd.mpr hd)
    exact Finset.mem_Ioc.mpr ⟨hnp.pos, Nat.le_of_dvd hq hd⟩
  have hcard : D.card ≤ q := by
    simpa using Finset.card_le_card hsub
  have heq : rieszPrimeMean g X = ∑ n ∈ D,
      (Real.log n : ℂ) * g n * rieszPrimeTest (n / X) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnd
    have hnq : n.Coprime q := by
      by_contra hh
      exact hnd (Finset.mem_filter.mpr ⟨hn, hh⟩)
    rw [hz n hnq, mul_zero, zero_mul]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb (n : ℕ) (hn : n ∈ D) :
      ‖(Real.log n : ℂ) * g n * rieszPrimeTest (n / X)‖ ≤ B * Real.log X := by
    obtain ⟨hnS, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hnS
    obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hnI
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mp hnX
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
    have hlogle : Real.log n ≤ Real.log X := Real.log_le_log hnR hnX'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
    calc
      _ ≤ (Real.log n * B) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hg n) hlogn)
        (rieszPrimeTest_norm_le_one (n / X) (by positivity)) (norm_nonneg _) (by positivity)
      _ ≤ B * Real.log X := by nlinarith
  rw [heq]
  calc
    _ ≤ ∑ n ∈ D, ‖(Real.log n : ℂ) * g n * rieszPrimeTest (n / X)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ D, B * Real.log X := Finset.sum_le_sum hb
    _ = (D.card : ℝ) * (B * Real.log X) := by simp
    _ ≤ B * q * Real.log X := by
      have hc : (D.card : ℝ) ≤ q := by exact_mod_cast hcard
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hB hlog)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

theorem rieszTwistMean_norm_le_of_coprime_zero (g : ℕ → ℂ) (q : ℕ) (X B : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n, ‖g n‖ ≤ B) (hz : ∀ n, n.Coprime q → g n = 0) :
    ‖rieszTwistMean g X‖ ≤ B * q * Real.log X + B * (2 * Real.sqrt X * Real.log X) := by
  have hp := rieszPrimeMean_norm_le_of_coprime_zero g q X B hq hX hB hg hz
  have he := rieszTwistMean_prime_error g X B hX hB hg
  have ht := norm_le_norm_sub_add (rieszTwistMean g X) (rieszPrimeMean g X)
  linarith

theorem rieszTwistMean_coprime_comparison (g h : ℕ → ℂ) (q : ℕ) (X : ℝ)
    (hq : 0 < q) (hX : 1 ≤ X) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1)
    (he : ∀ n, n.Coprime q → g n = h n) :
    ‖rieszTwistMean g X - rieszTwistMean h X‖ ≤
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X := by
  rw [rieszTwistMean_sub]
  have hb (n : ℕ) : ‖g n - h n‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hg n, hh n])
  have hz (n : ℕ) (hn : n.Coprime q) : g n - h n = 0 := by rw [he n hn, sub_self]
  have ht := rieszTwistMean_norm_le_of_coprime_zero (fun n => g n - h n) q X 2
    hq hX (by norm_num) hb hz
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaNearZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A near-one zeta zero contributes its full reciprocal gap -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem regularizedZeta_zero_re_lt_one (ρ : ℂ) (hρ : regularizedZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact regularizedZeta_ne_zero_right ρ (le_of_not_gt h) hρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaTrigonometric
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zeta 3-4-1 inequality and the reciprocal-gap bound -/

namespace Ostmann

open Complex

theorem zeta_trigonometric_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have hprincipal (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact map_one _
  simpa only [one_pow, hprincipal, one_mul] using
    complex_character_trigonometric_sum_nonneg (1 : DirichletCharacter ℂ 1) σ t hσ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaZeroFreeRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic zero-free region for the regularized zeta function -/

namespace Ostmann

open Complex Filter Metric
open scoped Topology

theorem regularizedZeta_small_height_gap : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ∀ ρ : ℂ, regularizedZeta ρ = 0 → 1 - r ≤ ρ.re → r ≤ |ρ.im| := by
  have hn := (regularizedZeta_analytic 1).continuousAt.eventually_ne
    (show regularizedZeta 1 ≠ 0 by simp)
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hn
  let r := min (R / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrR : r ≤ R / 4 := min_le_left _ _
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro ρ hρ hnear
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  by_contra hnot
  have hi : |ρ.im| < r := lt_of_not_ge hnot
  have hdist : dist ρ 1 < R := by
    rw [dist_eq_norm]
    have hb := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, abs_of_neg (show ρ.re - 1 < 0 by linarith)] at hb
    linarith
  exact hball hdist hρ

theorem realZeroKernel_away_bound (r δ t : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (ht : r ≤ |t|) : realZeroKernel δ t ≤ 1 / r ^ 2 := by
  have ht2 : r ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold realZeroKernel
  calc
    δ / (δ ^ 2 + t ^ 2) ≤ 1 / (δ ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_right hδ1 (by positivity)
    _ ≤ 1 / r ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszResidueError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing uniform character errors to a single residue class -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem rieszResidueMean_error_bound (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X E : ℝ) (_hE : 0 ≤ E) (M : DirichletCharacter ℂ q → ℂ)
    (herror : ∀ χ, ‖rieszTwistMean (fun n => χ (n : ZMod q)) X - M χ‖ ≤ E) :
    ‖(q.totient : ℂ) * rieszResidueMean q a X - ∑ χ, χ a⁻¹ * M χ‖ ≤ (q.totient : ℝ) * E := by
  rw [rieszResidueMean_orthogonality q a ha X, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        ‖χ a⁻¹ * rieszTwistMean (fun n => χ (n : ZMod q)) X - χ a⁻¹ * M χ‖ := norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, E := by
      apply Finset.sum_le_sum
      intro χ _
      rw [← mul_sub, norm_mul]
      exact (mul_le_mul (χ.norm_le_one _) (herror χ) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
    _ = (q.totient : ℝ) * E := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

theorem rieszResidueMean_average_error_bound (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X E : ℝ) (hE : 0 ≤ E) (M : DirichletCharacter ℂ q → ℂ)
    (herror : ∀ χ, ‖rieszTwistMean (fun n => χ (n : ZMod q)) X - M χ‖ ≤ E) :
    ‖rieszResidueMean q a X - (q.totient : ℂ)⁻¹ * ∑ χ, χ a⁻¹ * M χ‖ ≤ E := by
  have ht := rieszResidueMean_error_bound q a ha X E hE M herror
  have hpos : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have heq : (q.totient : ℂ) * (rieszResidueMean q a X -
      (q.totient : ℂ)⁻¹ * ∑ χ, χ a⁻¹ * M χ) =
      (q.totient : ℂ) * rieszResidueMean q a X - ∑ χ, χ a⁻¹ * M χ := by
    field_simp
  rw [← heq, norm_mul, Complex.norm_natCast] at ht
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using ht)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResidueRieszFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact real finite sums underlying the residue-class contour -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszResidueMean_eq_tsum (q a : ℕ) (X : ℝ) (hX : 0 < X) :
    rieszResidueMean q (a : ZMod q) X =
      ∑' n : ℕ, (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp
    · have hlarge : X < n := Nat.lt_of_floor_lt (by simp only [Finset.mem_Ioc] at hn; omega)
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hs]
  unfold rieszResidueMean rieszTwistMean
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : (n : ZMod q) = (a : ZMod q)
  · simp only [residueMangoldtWeight, hn, ite_true, if_true, mul_one]
  · simp only [residueMangoldtWeight, hn, ite_false, if_false, mul_zero, Complex.ofReal_zero, zero_mul]

theorem rieszResidueMean_finite (q a N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    (X : ℂ) * rieszResidueMean q (a : ZMod q) X =
      (finiteRieszSum (Finset.range (N + 1)) (residueMangoldtWeight q a) X : ℝ) := by
  have hs (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
      (residueMangoldtWeight q a n : ℂ) * rieszPrimeTest (n / X) = 0 := by
    have hNn : N < n := by simpa using hn
    have hxn : X < n := hXN.trans_lt (by exact_mod_cast hNn)
    rw [rieszPrimeTest_scale X n hX, max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]
    simp
  rw [rieszResidueMean_eq_tsum q a X hX, tsum_eq_sum hs, Finset.mul_sum]
  unfold finiteRieszSum
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [rieszPrimeTest_scale X n hX]
  push_cast
  field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']

theorem rieszContourWeight_real (X β : ℝ) (hX : 0 < X) :
    rieszContourWeight X (β : ℂ) = (X ^ β / (β * (β + 1)) : ℝ) := by
  rw [rieszContourWeight, ← Complex.ofReal_cpow hX.le]
  unfold rieszMellinKernel
  push_cast
  ring

theorem riesz_residue_main_scale (φ χ β X : ℝ) (hX : 0 < X) :
    (X : ℂ) * ((φ : ℂ)⁻¹ * ((X / 2 : ℝ) - (χ : ℂ) * rieszContourWeight X (β : ℂ))) =
      (integratedThetaMain φ χ β X : ℝ) := by
  rw [rieszContourWeight_real X β hX]
  unfold integratedThetaMain
  rw [Real.rpow_add hX, Real.rpow_one]
  push_cast
  ring

theorem residue_finite_count (q a N : ℕ) (X : ℝ) (hX : 0 ≤ X) (hXN : X ≤ N) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X), residueMangoldtWeight q a n) =
      residuePsi q a X := by
  unfold residuePsi
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro hn
    exact ⟨Nat.zero_le _, (Nat.le_floor_iff hX).mpr hn.2⟩
  · intro hn
    have hnx := (Nat.le_floor_iff hX).mp hn.2
    have hnN : n ≤ N := by exact_mod_cast (hnx.trans hXN)
    exact ⟨by omega, hnx⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResiduePrimePowerRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from sharp residue sums -/

namespace Ostmann

open scoped BigOperators

theorem residue_mangoldt_prime_difference (q a n : ℕ) :
    |residueMangoldtWeight q a n - primeProgressionLog q a n| ≤
      if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
  have he : ((n : ZMod q) = (a : ZMod q)) ↔ Nat.ModEq q n a := by
    rw [ZMod.natCast_eq_natCast_iff]
  by_cases hp : n.Prime
  · rw [residueMangoldtWeight, primeProgressionLog, ArithmeticFunction.vonMangoldt_apply_prime hp]
    by_cases hn : Nat.ModEq q n a
    · simp [hp, hn, he.mpr hn]
    · simp [hp, hn, mt he.mp hn]
  · rw [residueMangoldtWeight, primeProgressionLog]
    simp only [hp, false_and, ↓reduceIte, sub_zero, not_false_eq_true]
    split_ifs <;> simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      ArithmeticFunction.vonMangoldt_nonneg]

theorem residuePsi_prime_error (q a : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    |residuePsi q a X - primeProgressionTheta q a X| ≤
      2 * Real.sqrt X * Real.log X := by
  have hzero : (if ¬Nat.Prime 0 then ArithmeticFunction.vonMangoldt 0 else 0) = (0 : ℝ) := by simp
  calc
    _ = |∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      (residueMangoldtWeight q a n - primeProgressionLog q a n)| := by
        rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      |residueMangoldtWeight q a n - primeProgressionLog q a n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 :=
        Finset.sum_le_sum (fun n _ => residue_mangoldt_prime_difference q a n)
    _ = ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬n.Prime),
      ArithmeticFunction.vonMangoldt n := by
        rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), hzero, zero_add,
          Finset.sum_filter]
    _ = Chebyshev.psi X - Chebyshev.theta X := nonprime_mangoldt_sum X
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothHorizontalBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fifth-order decay of the actual horizontal contour integrals -/

namespace Ostmann

open Complex Set MeasureTheory
open scoped Interval

noncomputable def smoothHorizontalIntegral (χ : PrimitiveComplexCharacter)
    (X y : ℝ) : ℂ :=
  ∫ σ in (-(1 / 2 : ℝ))..2,
    (-deriv χ.L ((σ : ℂ) + y * I) / χ.L ((σ : ℂ) + y * I)) *
      smoothContourWeight X ((σ : ℂ) + y * I)

theorem primeMeanMellin_decay_pow : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C / (1 + |s.im|) ^ 8 := by
  obtain ⟨C, hC, hbound⟩ := primeMeanMellin_decay
  refine ⟨C, hC, ?_⟩
  intro s hs hs'
  have he : Real.exp (-8 * Real.log (1 + |s.im|)) = ((1 + |s.im|) ^ 8)⁻¹ := by
    rw [show -(8 : ℝ) * Real.log (1 + |s.im|) =
      -((8 : ℕ) * Real.log (1 + |s.im|)) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 1 + |s.im|)]
  simpa only [he, div_eq_mul_inv] using hbound s hs hs'

end Ostmann

end OAI
end


