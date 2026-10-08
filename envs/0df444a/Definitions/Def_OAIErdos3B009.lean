-- Prove2me | Definitions.Def_OAIErdos3B009
-- name    : OAIErdos3B009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:21:55.662243+00:00
-- url     : https://prove2.me/theorems/0f7bce54-72b9-4e5e-b1e9-50fb93f65bcb
-- title:
--   OpenAI Erdős-3 split, definitions bundle 10 of 88
-- statement:
--   Definitions bundle 10 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B008`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 10 available.
--
--   Modules: `Finset.sum_le_sum_of_injOn`, `OAI.Erdos3.BooleanCubeKernel.canonicalJointFrameWindowConstant`, `OAI.Erdos3.BooleanCubeKernel.comparableScalarParameterRadius`, `OAI.Erdos3.BooleanCubeKernel.jointFrameSourceHi`, `OAI.Erdos3.BooleanCubeKernel.jointFrameSourceLo`, `OAI.Erdos3.BoxProgressionPartition.card_cell`, `OAI.Erdos3.CellRefinement.bilinearIntegral`, `OAI.Erdos3.CellRefinement.replacementPotential`, `OAI.Erdos3.CoordinateDecisionTree`, `OAI.Erdos3.CoordinateDecisionTree.Valid`, `OAI.Erdos3.CoordinateDecisionTree.Valid.weaken`, `OAI.Erdos3.CoordinateDecisionTree.trace`, `OAI.Erdos3.CoordinateDecisionTree.trace_agrees`, `OAI.Erdos3.CoordinateDecisionTree.trace_contains`, `OAI.Erdos3.FixedDensity.bundleRankwiseDensityFloor`, `OAI.Erdos3.FixedDensity.bundleRankwiseDensityFloor_succ`, `OAI.Erdos3.FixedDensity.bundleRankwiseDensityFloor_zero`, `OAI.Erdos3.FixedDensity.bundleRankwiseEnvelopeError`, `OAI.Erdos3.FixedDensity.bundleRankwiseEnvelopeError_succ_order`, `OAI.Erdos3.FixedDensity.bundleRankwiseEnvelopeError_zero_card`, `OAI.Erdos3.FixedDensity.bundleRankwiseEnvelopeError_zero_order`, `OAI.Erdos3.FixedDensity.bundleRankwiseEnvelopeError_zero_parameters`, `OAI.Erdos3.FixedDensity.bundleRankwiseNextRow`, `OAI.Erdos3.FixedDensity.bundleRankwiseNextRow_succ`, `OAI.Erdos3.FixedDensity.bundleRankwiseNextRow_zero`, `OAI.Erdos3.FixedDensity.bundleRankwiseNextRow_zero_parameters`, `OAI.Erdos3.FixedDensity.bundleRankwiseScaledDefect`, `OAI.Erdos3.FixedDensity.bundleRankwiseScaledDefect_zero`, `OAI.Erdos3.FixedDensity.bundleRankwiseScaledUniformity`, `OAI.Erdos3.FixedDensity.bundleRankwiseScaledUniformity_zero`, `OAI.Erdos3.FixedDensity.bundleRankwiseStepIncrement`, `OAI.Erdos3.FixedDensity.bundleReverseDoublingHorizon`, `OAI.Erdos3.FixedDensity.cyclicAPVal`, `OAI.Erdos3.FixedDensity.cyclicAPVal_cast`, `OAI.Erdos3.HasBoundedScalarPeriod`, `OAI.Erdos3.IntegerBasisReduction.Mahler.IntegralPoint`, `OAI.Erdos3.IntegerBasisReduction.Mahler.integralEmbed`, `OAI.Erdos3.IntegerBasisReduction.Mahler.integralEmbed_add`, `OAI.Erdos3.IntegerBasisReduction.Mahler.integralEmbed_zero`, `OAI.Erdos3.IntegerBasisReduction.Mahler.integralEmbed_zsmul`, `OAI.Erdos3.IntegerBasisReduction.Mahler.mahlerFactor`, `OAI.Erdos3.IntegerBasisReduction.Mahler.mahlerFactor_zero`, `OAI.Erdos3.LowDensityThreshold`, `OAI.Erdos3.Peeling.Chain`, `OAI.Erdos3.Peeling.positiveSupport`, `OAI.Erdos3.Peeling.remainder`, `OAI.Erdos3.Peeling.slice`, `OAI.Erdos3.Peeling.translatedCellFamily`, `OAI.Erdos3.RationalPolynomialHeightLE.C`, `OAI.Erdos3.VectorPolynomial.actualForecastDataModelRequired`, `OAI.Erdos3.VectorPolynomial.affineAmbientMassLog`, `OAI.Erdos3.VectorPolynomial.affineAmbientPrimitiveBudget`, `OAI.Erdos3.VectorPolynomial.allocatedIdealLipEnvelope`, `OAI.Erdos3.VectorPolynomial.canonicalSublevelCutoff`, `OAI.Erdos3.VectorPolynomial.canonicalSublevelCutoffLip`, `OAI.Erdos3.VectorPolynomial.canonicalTransitionLip`, `OAI.Erdos3.VectorPolynomial.copiedLayerMatrix`, `OAI.Erdos3.VectorPolynomial.copiedLayerPolynomial`, `OAI.Erdos3.VectorPolynomial.copiedLayerRows`, `OAI.Erdos3.VectorPolynomial.copiedLayerSpace`, `OAI.Erdos3.VectorPolynomial.copiedLayerSpaceEquiv`, `OAI.Erdos3.VectorPolynomial.copyLeft`, `OAI.Erdos3.VectorPolynomial.copyRight`, `OAI.Erdos3.VectorPolynomial.fixedSourceFinDecidableEq`, `OAI.Erdos3.VectorPolynomial.fullTaggedBufferedCoordinates`, `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeScaleLog`, `OAI.Erdos3.VectorPolynomial.preparedUniformDegreeTolerance`, `OAI.Erdos3.VectorPolynomial.productiveFixedSourceFinDecidableEq`, `OAI.Erdos3.WeightedSifting.sampleWeight`, `OAI.Erdos3.abs_div_sub_div_bound`, `OAI.Erdos3.affineCoefficientCommonBudget`, `OAI.Erdos3.affineComparisonAccuracy`, `OAI.Erdos3.affineComparisonAccuracyLog`, `OAI.Erdos3.affineCubeCoordinates`, `OAI.Erdos3.affineIntegerCubeCoordinates`, `OAI.Erdos3.affinePairDensity`, `OAI.Erdos3.affinePairShift`, `OAI.Erdos3.affinePairWidth`, `OAI.Erdos3.affineProfileLogBound`, `OAI.Erdos3.affineProfileLogBound_nonneg`, `OAI.Erdos3.allocatedUniformPMFCanonical`, `OAI.Erdos3.amplificationSourceLogCoefficient`, `OAI.Erdos3.approxMomentEnvelope`, `OAI.Erdos3.binomialPolynomial`, `OAI.Erdos3.binomialPolynomial_natDegree`, `OAI.Erdos3.binomialPolynomial_zero`, `OAI.Erdos3.blockCubeDomain`, `OAI.Erdos3.blockJetScaleBound`, `OAI.Erdos3.blockJetScaleBound_nonneg`, `OAI.Erdos3.booleanConstantJet`, `OAI.Erdos3.booleanJetMassBudget`, `OAI.Erdos3.boxTestAverage`, `OAI.Erdos3.boxTestLipschitz`, `OAI.Erdos3.canonicalZeroSpatialKernelEmbedding`, `OAI.Erdos3.canonicalZeroSpatialKernelEmbedding_apply`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput_inl`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput_inr`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput_none`, `OAI.Erdos3.cappedDistanceTest`, `OAI.Erdos3.circle_character_mul_star`, `OAI.Erdos3.coefficientArraySampler`, `OAI.Erdos3.configurationFourierWeight`, `OAI.Erdos3.coordinateCopySum`, `OAI.Erdos3.coordinateCopySum_apply`, `OAI.Erdos3.coordinateDivergence`, `OAI.Erdos3.coordinateInjection`, `OAI.Erdos3.coordinateResamplingEquiv`, `OAI.Erdos3.coordinateZeroProjection`, `OAI.Erdos3.countingBernoulli`, `OAI.Erdos3.countingFeature`, `OAI.Erdos3.countingFeatureProduct`, `OAI.Erdos3.countingKernel`, `OAI.Erdos3.countingKernelProductAverage`, `OAI.Erdos3.crtInput`, `OAI.Erdos3.crtIntegerCoefficient`, `OAI.Erdos3.crtIntegerRepresentative`, `OAI.Erdos3.crtRepresentativePolynomial`, `OAI.Erdos3.crtRepresentativePolynomial_degree`, `OAI.Erdos3.denseResidueMeshCap`, `OAI.Erdos3.denseResidueMeshStep`, `OAI.Erdos3.designatedVectorComponent`, `OAI.Erdos3.dilatedIntegerMatrix`, `OAI.Erdos3.euclideanCharacter`, `OAI.Erdos3.euclideanCharacter_add`, `OAI.Erdos3.euclideanCharacter_neg`, `OAI.Erdos3.euclideanCharacter_zero`, `OAI.Erdos3.externalNetIndex`, `OAI.Erdos3.externalNetIndex_approx`, `OAI.Erdos3.factorial_le_exp_square`, `OAI.Erdos3.finiteFixedTagSet`, `OAI.Erdos3.finiteMixedLpBound`, `OAI.Erdos3.finiteMixedLpCore`, `OAI.Erdos3.finitePatternRepresentative`, `OAI.Erdos3.finiteProductCharacter`, `OAI.Erdos3.finiteProductCharacterCoordinate`, `OAI.Erdos3.fixedNonprincipalExponents`, `OAI.Erdos3.fixedPathAmbientPrecision`, `OAI.Erdos3.fixedPathComparisonPrecision`, `OAI.Erdos3.fixedPathForecastTolerance`, `OAI.Erdos3.fixedPathPerturbationLog`, `OAI.Erdos3.fixedPathPerturbationLog_nonneg`, `OAI.Erdos3.fixedPathSlicedSourceError`, `OAI.Erdos3.fixedSpatialEmptyCoordinates`, `OAI.Erdos3.fixedSpatialEmptyDensity`, `OAI.Erdos3.fixedSpatialEmptyIndex`, `OAI.Erdos3.flatComparisonDelta`, `OAI.Erdos3.forecastComparisonFloorPolynomial`, `OAI.Erdos3.forecastComparisonMeshPolynomial`, `OAI.Erdos3.forecastJointGridCutoff`, `OAI.Erdos3.forecastJointGridError`, `OAI.Erdos3.forecastJointGridMesh`, `OAI.Erdos3.forecastJointGridMeshLog`, `OAI.Erdos3.fourSparse12Equiv`, `OAI.Erdos3.fractionalPartBin`, `OAI.Erdos3.frequencyGridInterval`, `OAI.Erdos3.gridDensityTest`, `OAI.Erdos3.integerBoxCubeProductEquiv`, `OAI.Erdos3.integerBoxGcdCutoff`, `OAI.Erdos3.integerBoxNearRatio`, `OAI.Erdos3.integerBoxPairScale`, `OAI.Erdos3.integerBoxRetainedGap`, `OAI.Erdos3.integerLongPolynomialOutput`, `OAI.Erdos3.integerMatrixImagePMF`, `OAI.Erdos3.integerProgressionSupport`, `OAI.Erdos3.integerStrideHom`, `OAI.Erdos3.integerSupportTorusFactor`, `OAI.Erdos3.jetOutputRadiusLog`, `OAI.Erdos3.joinedCoefficientProfile`, `OAI.Erdos3.jointBooleanPerturbedPolynomial`, `OAI.Erdos3.jointBooleanPolynomial`, `OAI.Erdos3.jointCoefficientTail`, `OAI.Erdos3.jointKernelCutoff`, `OAI.Erdos3.kernelJetEntryAllowance`, `OAI.Erdos3.kernelJetInterpolationAllowance`, `OAI.Erdos3.kernelJetInverseAllowance`, `OAI.Erdos3.kernelJetMinorThreshold`, `OAI.Erdos3.l1SourceAccuracy`, `OAI.Erdos3.latticeGaussianTail`, `OAI.Erdos3.layerDegree_le_tailDegree`, `OAI.Erdos3.layerRankPotential`, `OAI.Erdos3.layerTailDegree`, `OAI.Erdos3.le_layerTailDegree`, `OAI.Erdos3.linearRestrictionHeight`, `OAI.Erdos3.localizedAverageScale`, `OAI.Erdos3.maskedNormalized`, `OAI.Erdos3.mem_drop_finRange_iff`, `OAI.Erdos3.mem_integerProgressionSupport_iff`, `OAI.Erdos3.mixedArrayEmbedding`, `OAI.Erdos3.mixedArrayEmbedding_inl`, `OAI.Erdos3.mixedArrayEmbedding_inr`, `OAI.Erdos3.mixedArrayIntegerImage`, `OAI.Erdos3.mixedResidueArrayEquiv`, `OAI.Erdos3.modularForecastRankConstant`, `OAI.Erdos3.modularTagWeight`, `OAI.Erdos3.monomialCharacterMean`, `OAI.Erdos3.monomialCharacterMean_zero`, `OAI.Erdos3.natCeil_le_exp_succ`, `OAI.Erdos3.nestedTupleResidueReduction`, `OAI.Erdos3.nonprincipalSupport`, `OAI.Erdos3.norm_euclideanCharacter`, `OAI.Erdos3.normalizedCutoffs`, `OAI.Erdos3.normalizedFiberErrorConstant`, `OAI.Erdos3.normalizedIntegerFiberOutputMass`, `OAI.Erdos3.normalizedSpatialShare`, `OAI.Erdos3.operatorPrecompose`, `OAI.Erdos3.orderedBasisProduct`, `OAI.Erdos3.orderedBasisTailProduct`, `OAI.Erdos3.ordinaryShiftBranch`, `OAI.Erdos3.originalMonomialJetMap`, `OAI.Erdos3.outputAxisReindexAddEquiv`, `OAI.Erdos3.outputAxisReindexAddEquiv_apply`, `OAI.Erdos3.padicStepQuotientUnit`, `OAI.Erdos3.padicStepQuotientUnit_coe`, `OAI.Erdos3.padicStepQuotient_coprime`, `OAI.Erdos3.permanentExponent`, `OAI.Erdos3.permanentPolynomial`, `OAI.Erdos3.pivotIterationBound`, `OAI.Erdos3.pmf_bind_toReal`, `OAI.Erdos3.polynomialC2BoxBudget`, `OAI.Erdos3.polynomialCharacterRow`, `OAI.Erdos3.polynomialPerturbationScale`, `OAI.Erdos3.polynomialSublevelThreshold`, `OAI.Erdos3.polynomialSublevelThreshold_pos`, `OAI.Erdos3.polynomialSublevelThreshold_root_bound`, `OAI.Erdos3.polynomialSublevelThreshold_total_bound`, `OAI.Erdos3.positiveCountingKernel`, `OAI.Erdos3.positiveKernelGram`, `OAI.Erdos3.preparedRoundedRank`, `OAI.Erdos3.prependPolynomialVariable`, `OAI.Erdos3.prescribedCRTArbitraryStepEquiv`, `OAI.Erdos3.principalSamplingGapRatio`, `OAI.Erdos3.principalSamplingGapRatio_one_le`, `OAI.Erdos3.principalSamplingGapRatio_width`, `OAI.Erdos3.principalTupleFlatten`, `OAI.Erdos3.probabilityIntegralThresholdPoint`, `OAI.Erdos3.productMatrixApply`, `OAI.Erdos3.productPairCoordinates`, `OAI.Erdos3.progressionPrincipalResidue`, `OAI.Erdos3.quotientCoordinateRadius`, `OAI.Erdos3.rationalCharacterIndividualModulus`, `OAI.Erdos3.rationalCharacterIndividualModulus_dvd`, `OAI.Erdos3.rationalCharacterIndividualModulus_neZero`, `OAI.Erdos3.rationalCharacterIndividualModulus_order_dvd`, `OAI.Erdos3.rationalCharacterIndividualModulus_pos`, `OAI.Erdos3.rationalCharacterIndividualReduction`, `OAI.Erdos3.rationalHeightLE_ceil_exp_of_entries`, `OAI.Erdos3.realAxisAffinePolynomial`, `OAI.Erdos3.realAxisAffinePullback`, `OAI.Erdos3.reciprocalTerm_zero`, `OAI.Erdos3.recoveredKernelScalarBudget`, `OAI.Erdos3.reducedLatticeColumn`, `OAI.Erdos3.reducedTriangularMatrix`, `OAI.Erdos3.relativeBoxInput`, `OAI.Erdos3.relativeBoxInput_eq`, `OAI.Erdos3.relativeScalarPassageSlack`, `OAI.Erdos3.retainedPatchCutoff`, `OAI.Erdos3.retainedPatchRelativeError`, `OAI.Erdos3.rootDifferenceMatrix`, `OAI.Erdos3.rootDifferenceMatrix_det`, `OAI.Erdos3.rowPolynomial_diagonal`, `OAI.Erdos3.rowPolynomial_map`, `OAI.Erdos3.scalarMeshLog`, `OAI.Erdos3.scalarPiOneEquiv`, `OAI.Erdos3.scalarTupleHom`, `OAI.Erdos3.scalePerturbedPolynomial`, `OAI.Erdos3.secondaryBoundaryMargin`, `OAI.Erdos3.secondaryMeshDelta`, `OAI.Erdos3.secondaryMovementBudget`, `OAI.Erdos3.selectedProductExtension`, `OAI.Erdos3.shiftCorrelation`, `OAI.Erdos3.sigmaProductKernel`, `OAI.Erdos3.siteExponentialOutputLog`, `OAI.Erdos3.siteExponentialOutputLog_nonneg`, `OAI.Erdos3.smallRatioCenterPotential`, `OAI.Erdos3.spatialKernelErrorConstant`, `OAI.Erdos3.splitFreeCoordinates`, `OAI.Erdos3.splitPhysicalSpatialInputScale`, `OAI.Erdos3.standardLatticeClosedQuarterBox`, `OAI.Erdos3.subspaceArrayFunctional`, `OAI.Erdos3.symmetricInterval_card`, `OAI.Erdos3.synchronize_splitting_projection`, `OAI.Erdos3.taggedIntegerResidue`, `OAI.Erdos3.taggedOutputCRTEquiv`, `OAI.Erdos3.translatedGridMass`, `OAI.Erdos3.triangularReductionMatrix`, `OAI.Erdos3.tupleColumnMatrix`, `OAI.Erdos3.tupleResidueReduction`, `OAI.Erdos3.twoSlopeAddHom`, `OAI.Erdos3.unconditionedScalarPrimeRatio`, `OAI.Erdos3.uniformProductAccuracyLog`, `OAI.Erdos3.uniformProductAccuracyLog_nonneg`, `OAI.Erdos3.unitBoxFace`, `OAI.Erdos3.unitBoxInteriorCutoff`, `OAI.Erdos3.unitCoefficientSource`, `OAI.Erdos3.unitCoefficientSource_probability`, `OAI.Erdos3.weylBudget`, `OAI.Erdos3.weylBudgetPolynomial`, `OAI.Erdos3.weylNextBudget`, `OAI.Erdos3.weylShiftDenom`, `OAI.Erdos3.weylShiftDensity`, `OAI.Erdos3.weylShiftError`, `_private.Fourier.RationalCharacterIndividualModulus.0.OAI.Erdos3.exists_rationalCharacterIndividualReduction`, `_private.Lattices.AllocatedSupportedAffineAccurateSource.0.OAI.Erdos3.VectorPolynomial.affineSourceSum`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B005

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localizedAverageScale (rank : ℕ) (R epsilon : ℝ) : ℝ≥0 :=
  (min ((1 : ℝ) / (200 * (max rank 1 : ℕ)))
    (epsilon / (400 * (max rank 1 : ℕ) * (R + 1)))).toNNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCutoffs
namespace OAI

section

namespace Erdos3

theorem abs_div_sub_div_bound {a b u v r D M E : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (hv : r ≤ v) (hD : 0 ≤ D) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hab : |a - b| ≤ D) (hb : |b| ≤ M) (huv : |u - v| ≤ E) :
    |a / u - b / v| ≤ D / r + M * E / (r * r) := by
  have hu0 : 0 < u := hr.trans_le hu
  have hv0 : 0 < v := hr.trans_le hv
  have heq : a / u - b / v = (a - b) / u + b * (v - u) / (u * v) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a - b) / u| + |b * (v - u) / (u * v)| := abs_add_le _ _
    _ = |a - b| / u + |b| * |u - v| / (u * v) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hu0, abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
    _ ≤ D / r + M * E / (r * r) :=
      add_le_add (div_le_div₀ hD hab hr hu)
        (div_le_div₀ (mul_nonneg hM hE) (mul_le_mul hb huv (abs_nonneg _) hM)
          (mul_pos hr hr) (mul_le_mul hu hv hr.le hu0.le))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal Manifold ContDiff

variable {ι X : Type*} [Fintype ι]

noncomputable def normalizedCutoffs (f : ι → X → ℝ) (i : ι) (x : X) : ℝ :=
  f i x / ∑ j, f j x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

theorem card_cell (a : ∀ i, (P i).Label) :
    (partitionCell (cell P) a).card = ∏ i, (P i).length (a i) := by
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using
    (Fintype.card_congr (pointEquiv P a)).symm

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

namespace BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

end BoxProgressionPartition
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace RationalPolynomialHeightLE

variable {σ : Type*} {p : MvPolynomial σ ℚ} {H K : ℕ}

theorem C {q : ℚ} (hq : RationalHeightLE q H) :
    RationalPolynomialHeightLE (MvPolynomial.C q : MvPolynomial σ ℚ) H := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hq
  · exact rationalHeightLE_zero
      ((Nat.one_le_iff_ne_zero.mpr q.den_ne_zero).trans hq.2)

end RationalPolynomialHeightLE

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {ι σ : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxTestSmoothing
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxTestAverage (δ : ℝ) (φ : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  kernelAverage volume (boxProbabilityWindow (fun _ => δ)) φ

noncomputable def boxTestLipschitz (δ : ℝ) (hδ : 0 < δ) : ℝ≥0 :=
  boxWindowTranslationBound (fun _ : ι => δ) (fun _ => hδ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DivergenceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateDivergence (Q : ι → (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, fderiv ℝ (Q i) x (Pi.single i 1)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateInjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateInjection {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : κ => ℝ) (f i)).comp (ContinuousLinearMap.proj i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

noncomputable def operatorPrecompose (J : E →L[ℝ] X) :
    (X →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Y) :=
  (ContinuousLinearMap.compL ℝ E X Y).flip J

end Erdos3

end

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

def unitBoxFace (j : Bool × ι) (x : ι → ℝ) : ℝ :=
  if j.1 then 1 - x j.2 else x j.2

noncomputable def unitBoxInteriorCutoff (r : ℝ) : (ι → ℝ) → ℝ :=
  inequalityBoundaryCutoff (fun _ : Bool × ι => r) unitBoxFace

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RandomAffinePair
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {T : Type*} [MeasurableSpace T]

noncomputable def affinePairWidth (a b : T → ℝ) (p : T × ℝ) : ℝ := max |a p.1| |b p.1|

noncomputable def affinePairShift (a b c : T → ℝ) (p : T × ℝ) : ℝ :=
  c p.1 + min 0 (a p.1) + min 0 (b p.1) + min |a p.1| |b p.1| * p.2

noncomputable def affinePairDensity (μ : Measure T) (a b c : T → ℝ) : ℝ → ℝ :=
  randomIntervalDensity (μ.prod unitScalarMeasure) (affinePairWidth a b) (affinePairShift a b c)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

end Erdos3

end

section

namespace Erdos3

noncomputable def scalePerturbedPolynomial {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  MvPolynomial.rename (fun i => some (Sum.inr i)) p + MvPolynomial.X none * r

end Erdos3

end

section

namespace Erdos3

noncomputable def polynomialC2BoxBudget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * (d + 1 : ℝ) ^ N * C

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    MvPolynomial (JointBlockParameter B h α) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1)
    (booleanSamplerPolynomial (F := Fin (h o.1)) (c o.1) (sets o.1 o.2))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α Z : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPerturbedPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (o : Σ d, O d) : MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  scalePerturbedPolynomial (jointBooleanPolynomial h c sets o) (r o)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BooleanJetMassBudget
namespace OAI

section

namespace Erdos3

noncomputable def booleanJetMassBudget (q h : ℕ) (W : ℝ) : ℝ :=
  (2 : ℝ) ^ q * (W * ((q : ℝ) + 1) ^ h)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTailScaling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O T : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointCoefficientTail (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (o : Σ d, O d) :
    MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  normalizedCoefficientTail (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1)
    inputIndex (sets o.1 o.2)

noncomputable def coefficientArraySampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (T d))
    (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) : ℝ :=
  jointBooleanSampler h c sets x o + t * normalizedCoefficientTailValue
    (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1) inputIndex z x (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RawProductArrayNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O L : D → Type*} [∀ d, Fintype (B d)]

def booleanConstantJet (sets : ∀ d, O d → Finset α) (constant : D → ℝ) (o : Σ d, O d) : ℝ :=
  if sets o.1 o.2 = ∅ then constant o.1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def nonprincipalSupport {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact p.support \ insert 0 (Finset.univ.image principal)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricIntervalDilation
namespace OAI

section

namespace Erdos3

theorem symmetricInterval_card (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TaggedZModOrderBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def taggedIntegerResidue {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    ((Sigma J) → ℤ) →+ (∀ h : Tag, J h → ZMod N) where
  toFun x h j := (x ⟨h, j⟩ : ZMod N)
  map_zero' := by ext h j; simp
  map_add' := by intro x y; ext h j; simp

variable {Tag X : Type*} [Fintype Tag] [Fintype X]
  (J : Tag → Type*) [∀ h, Fintype (J h)] (N : ℕ) [NeZero N]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

noncomputable def polynomialCharacterRow (row : I → R) (F : I → MvPolynomial V R) :
    MvPolynomial V R := ∑ i, C (row i) * F i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularTagGap
namespace OAI

section

namespace Erdos3

def modularTagWeight (h : ℕ) : ℕ := 2 ^ h * h.factorial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductImageDecay
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, AddCommGroup (H j)]

def finiteProductCharacter : (∀ j, AddChar (H j) ℂ) →* AddChar (∀ j, H j) ℂ where
  toFun χ := {
    toFun := fun y => ∏ j, χ j (y j)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by intro x y; simp only [Pi.add_apply, AddChar.map_add_eq_mul,
      Finset.prod_mul_distrib] }
  map_one' := by ext y; simp
  map_mul' χ ψ := by ext y; simp [Finset.prod_mul_distrib]

def finiteProductCharacterCoordinate (χ : AddChar (∀ j, H j) ℂ) (j : J) :
    AddChar (H j) ℂ where
  toFun x := χ (Pi.single j x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [Pi.single_add, χ.map_add_eq_mul]

variable [∀ j, Fintype (H j)] {X : J → Type*} [∀ j, Fintype (X j)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteAffineClassAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K]

def scalarTupleHom {I R : Type*} [CommRing R] (c : R) : (I → R) →+ (I → R) where
  toFun x i := c * x i
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp [mul_add]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

noncomputable def taggedOutputCRTEquiv (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ h : Tag, J h → ZMod (∏ l, q l)) ≃+
      (∀ l : L, ∀ h : Tag, J h → ZMod (q l)) where
  toFun y l h j := ZMod.prodEquivPi q hq (y h j) l
  invFun y h j := (ZMod.prodEquivPi q hq).symm (fun l => y l h j)
  left_inv y := by
    funext h j
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (y h j)
  right_inv y := by
    funext l h j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l h j)) l
  map_add' x y := by
    funext l h j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x h j) (y h j)) l

noncomputable def crtInput (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (v : V) : ZMod (∏ l, q l) :=
  (ZMod.prodEquivPi q hq).symm (fun l => x l v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RootDifferenceMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rootDifferenceMatrix {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) : Matrix (Unit ⊕ I) (Unit ⊕ J) R :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j)) (0 : Matrix I Unit R) D

theorem rootDifferenceMatrix_det {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (root : I → R) (A : Matrix I I R) : (rootDifferenceMatrix root A).det = A.det := by
  change (Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j))
    (0 : Matrix I Unit R) A).det = A.det
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def principalTupleFlatten {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α] :
    (PrincipalTupleIndex B h → Option α → ℝ) ≃L[ℝ] (JointBlockParameter B h α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2
      invFun := fun a j r => a ⟨j.1, j.2.1, j.2.2, r⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget
namespace OAI

namespace Erdos3

noncomputable def polynomialSublevelThreshold (n m : ℕ) (C scale η : ℝ) : ℝ :=
  (2 * (1 + scale) * (1 + 2 * C * (m + 1 : ℝ) / η) ^ n)⁻¹

theorem polynomialSublevelThreshold_pos (n m : ℕ) {C scale η : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    0 < polynomialSublevelThreshold n m C scale η := by
  unfold polynomialSublevelThreshold
  positivity

theorem polynomialSublevelThreshold_root_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      (1 + 2 * C * (m + 1 : ℝ) / η)⁻¹ := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have hscale : 0 < 1 + scale := by linarith
  have he : 2 * polynomialSublevelThreshold n m C scale η * scale =
      (scale / (1 + scale)) * (L ^ n)⁻¹ := by
    unfold polynomialSublevelThreshold
    dsimp only [L]
    field_simp
  have hfrac : scale / (1 + scale) ≤ 1 := (div_le_one hscale).mpr (by linarith)
  have hsmall : 2 * polynomialSublevelThreshold n m C scale η * scale ≤ (L ^ n)⁻¹ := by
    rw [he]
    exact mul_le_of_le_one_left (by positivity) hfrac
  have hnonneg : 0 ≤ 2 * polynomialSublevelThreshold n m C scale η * scale :=
    mul_nonneg (mul_nonneg (by norm_num) (polynomialSublevelThreshold_pos n m hC hs hη).le) hs
  calc
    _ ≤ ((L ^ n)⁻¹) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hnonneg hsmall (by positivity)
    _ = L⁻¹ := by
      rw [Real.inv_rpow (pow_nonneg hL.le n), Real.pow_rpow_inv_natCast hL.le hn.ne']

theorem polynomialSublevelThreshold_total_bound {n m : ℕ} (hn : 0 < n)
    {C scale η : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η) :
    (m : ℝ) * C * (2 * polynomialSublevelThreshold n m C scale η * scale) ^ ((n : ℝ)⁻¹) ≤
      η / 2 := by
  let L := 1 + 2 * C * (m + 1 : ℝ) / η
  have hL : 0 < L := by dsimp [L]; positivity
  have he : (η / 2) * L = η / 2 + C * (m + 1 : ℝ) := by
    dsimp only [L]
    field_simp
  calc
    _ ≤ (m : ℝ) * C * L⁻¹ := mul_le_mul_of_nonneg_left
      (polynomialSublevelThreshold_root_bound hn hC hs hη) (by positivity)
    _ ≤ η / 2 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hL).mpr
      rw [he]
      nlinarith

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeCokernelCutoff
namespace OAI

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

def HasBoundedScalarPeriod {I : Type*} [Fintype I] (L : Submodule ℤ (I → ℤ)) (B : ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ integerScalarLattice I (a : ℤ) ≤ L

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI

namespace Erdos3

noncomputable def jointKernelCutoff (n b : ℕ) (K T ε κ : ℝ) : ℕ :=
  ⌈1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε⌉₊

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerImageProbabilityLaw
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def normalizedIntegerFiberOutputMass {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S P : I → ℝ) (T : J → ℝ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  scaledIntegerFiberOutputMass A B S P T f v / scaledInputMass f S T

noncomputable def normalizedFiberErrorConstant (j d : ℕ) (G U V R H : ℝ) (K : ℝ≥0) : ℝ :=
  2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2 * R) ^ d) * ((2 * R + 2) ^ (j + d) * K)

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

def remainder (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then 0 else f x

def slice (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then f x else 0

noncomputable def positiveSupport (f : G → ℝ) : Finset G := Finset.univ.filter (fun x => 0 < f x)

end Erdos3.Peeling

namespace Erdos3

open scoped BigOperators

namespace Peeling

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

noncomputable def bilinearIntegral (A B : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * a (x + y)

variable [Fintype G] [DecidableEq G]

end CellRefinement
end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

inductive Chain (B : Finset G) (Admissible : Finset G → Prop) (K kappa : ℝ) :
    (G → ℝ) → (G → ℝ) → List (Finset G) → Prop
  | nil (f : G → ℝ) : Chain B Admissible K kappa f f []
  | step {f g : G → ℝ} {cs : List (Finset G)} (C : Finset G)
      (active : kappa ≤ 𝔼 x ∈ B, f x)
      (admissible : Admissible C)
      (concentrated : K * (𝔼 x ∈ B, f x) < 𝔼 x ∈ C, f x)
      (tail : Chain B Admissible K kappa (remainder C f) g cs) :
      Chain B Admissible K kappa f g (C :: cs)

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

end Chain
end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def spatialKernelErrorConstant (j d : ℕ) (U R : ℝ) (K : ℝ≥0) : ℝ :=
  (j.factorial * U ^ j) * (2 * R) ^ d * K * U

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

noncomputable def kernelJetInterpolationAllowance (q h : ℕ) (κ : ℝ) : ℝ :=
  (1 + (q : ℝ) * (2 * (q.factorial / κ))) ^ h

def kernelJetEntryAllowance (q h : ℕ) : ℝ := 2 ^ q * ((q : ℝ) + 1) ^ h

noncomputable def kernelJetMinorThreshold (q n j h : ℕ) (κ : ℝ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ h * kernelJetInterpolationAllowance q h κ) ^ j

noncomputable def kernelJetInverseAllowance (q n j h : ℕ) (κ : ℝ) : ℝ :=
  (j : ℝ) * ((j.factorial * (kernelJetEntryAllowance q h) ^ (j - 1)) /
    kernelJetMinorThreshold q n j h κ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def nestedTupleResidueReduction {I : Type*} (n : ℕ)
    {M N : ℕ} (hMN : M ∣ N) :
    (Fin n → I → ZMod N) →+ (Fin n → I → ZMod M) where
  toFun x a i := ZMod.castHom hMN (ZMod M) (x a i)
  map_zero' := by ext a i; simp
  map_add' := by
    intro x y
    ext a i
    exact map_add (ZMod.castHom hMN (ZMod M)) (x a i) (y a i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrderedBasisCoordinates
namespace OAI

section

namespace Erdos3

open Module

theorem mem_drop_finRange_iff {d i : ℕ} {j : Fin d} :
    j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hval : i + k = j.val := by simpa using congrArg Fin.val heq
    omega
  · intro hij
    refine ⟨j.val - i, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · apply Fin.ext
      simp only [List.getElem_finRange, Fin.val_cast]
      omega

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def orderedBasisTailProduct (i : ℕ) (t : Fin d → ℚ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def orderedBasisProduct (t : Fin d → ℚ) : NilpotentLieBCHGroup L s hnil :=
  orderedBasisTailProduct e hnil 0 t

namespace IsCentralLieBasis

variable {e}

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {d s : ℕ}
  {e : Basis (Fin d) ℚ L}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientCoordinateRadius
namespace OAI

section

namespace Erdos3

noncomputable def quotientCoordinateRadius (δ K : ℝ) (d : ℕ) : ℝ :=
  δ / (δ + 4 * K ^ 2 * (d + 1))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Compat
/-!
Backports of Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to Mathlib 0df444a, with
the same names and statements and Mathlib's own proofs (Apache-2.0).
-/

namespace Nat

end Nat

namespace Finset

/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BinomialPolynomial
namespace OAI

section

namespace Erdos3

open Polynomial

noncomputable def binomialPolynomial (n : ℕ) : Polynomial ℚ :=
  (n.factorial : ℚ)⁻¹ • descPochhammer ℚ n

@[simp] theorem binomialPolynomial_zero : binomialPolynomial 0 = 1 := by
  simp [binomialPolynomial]

theorem binomialPolynomial_natDegree (n : ℕ) : (binomialPolynomial n).natDegree = n := by
  rw [binomialPolynomial, natDegree_smul]
  · exact descPochhammer_natDegree ℚ n
  · exact inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PMFPointMassMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_bind_toReal {X Y : Type*} (p : PMF X) (q : X → PMF Y) (y : Y) :
    ((p.bind q) y).toReal = ∑' x, (p x).toReal * (q x y).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ArrayFunctionalSection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def subspaceArrayFunctional {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℝ) : (I → U) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, ∑ a, frequency i a * (x i).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FullAffineCoefficientBound
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

noncomputable def realAxisAffinePolynomial {σ : Type*} (h r : σ → ℝ) (i : σ) : MvPolynomial σ ℝ :=
  C (h i) + C (r i) * X i

noncomputable def realAxisAffinePullback {σ : Type*} (h r : σ → ℝ) :
    MvPolynomial σ ℝ →+* MvPolynomial σ ℝ :=
  eval₂Hom C (realAxisAffinePolynomial h r)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

noncomputable def frequencyGridInterval (M : ℕ) (center radius : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun k => |(k.val : ℝ) - center| ≤ radius)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerStrideHom (m : ℤ) : ℤ →+ ℤ where
  toFun x := m * x
  map_zero' := mul_zero m
  map_add' := mul_add m

noncomputable def integerProgressionSupport (c m : ℤ) (L : ℕ) : Finset ℤ :=
  translateSupport c ((Finset.Ico (0 : ℤ) (L : ℤ)).image (integerStrideHom m))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff (c : ℤ) (m H : ℕ) (hm : 0 < m) (x : ℤ) :
    x ∈ integerProgressionSupport c (m : ℤ) H ↔
      c ≤ x ∧ x < c + (m * H : ℕ) ∧ (x : ZMod m) = (c : ZMod m) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' := Finset.mem_Ico.mp hy
    change (m : ℤ) * y = x - c at he
    have hx : x = c + (m : ℤ) * y := by omega
    constructor
    · nlinarith
    constructor
    · push_cast
      nlinarith
    · rw [hx]
      simp
  · rintro ⟨hlo, hhi, hr⟩
    have hz : ((x - c : ℤ) : ZMod m) = 0 := by simp [hr]
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - c) m).mp hz
    have hy0 : 0 ≤ y := by nlinarith
    have hyH : y < H := by push_cast at hhi; nlinarith
    exact ⟨y, Finset.mem_Ico.mpr ⟨hy0, hyH⟩, hy.symm⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MahlerBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

abbrev IntegralPoint (n : ℕ) := Fin n → ℤ

def integralEmbed {n : ℕ} (x : IntegralPoint n) : Fin n → ℝ :=
  fun i ↦ (x i : ℝ)

@[simp]
theorem integralEmbed_zero {n : ℕ} :
    integralEmbed (0 : IntegralPoint n) = 0 := by
  ext i
  simp [integralEmbed]

@[simp]
theorem integralEmbed_add {n : ℕ} (x y : IntegralPoint n) :
    integralEmbed (x + y) = integralEmbed x + integralEmbed y := by
  ext i
  simp [integralEmbed]

@[simp]
theorem integralEmbed_zsmul {n : ℕ} (a : ℤ) (x : IntegralPoint n) :
    integralEmbed (a • x) = (a : ℝ) • integralEmbed x := by
  ext i
  simp [integralEmbed]

noncomputable def mahlerFactor {n : ℕ} (i : Fin n) : ℝ :=
  if i.val = 0 then 1 else (i.val + 1 : ℝ) / 2

@[simp]
theorem mahlerFactor_zero {n : ℕ} (i : Fin n) (hi : i.val = 0) :
    mahlerFactor i = 1 := by
  simp [mahlerFactor, hi]

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousDirichlet
namespace OAI

section

namespace Erdos3

noncomputable def fractionalPartBin (Q : ℕ) (hQ : 0 < Q) (x : ℝ) : Fin Q :=
  ⟨⌊(Q : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt' hQ.ne').mpr
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hQR⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSupportRawArray
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedNonprincipalExponents {K J : Type*} [Fintype J]
    (S : Finset (K →₀ ℕ)) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact S \ insert 0 (Finset.univ.image principal)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrincipalSamplingScale
namespace OAI

section

namespace Erdos3

noncomputable def principalSamplingGapRatio (γ : ℝ) : ℕ :=
  ⌈max 1 (16 * (probabilityProfileLipschitz : ℝ) / γ)⌉₊

theorem principalSamplingGapRatio_one_le (γ : ℝ) : 1 ≤ principalSamplingGapRatio γ := by
  have h : (1 : ℝ) ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem principalSamplingGapRatio_width {γ : ℝ} (hγ : 0 < γ) :
    16 * (probabilityProfileLipschitz : ℝ) ≤ γ * principalSamplingGapRatio γ := by
  have h : 16 * (probabilityProfileLipschitz : ℝ) / γ ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hb := (div_le_iff₀ hγ).mp h
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RowPolynomialCombination
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem rowPolynomial_map {K R S : Type*} [Fintype K] [CommRing R] [CommRing S]
    (f : R →+* S) (a : K → R) :
    map f (rowPolynomial a) = rowPolynomial (fun k => f (a k)) := by
  simp only [rowPolynomial, map_sum, map_mul, map_C, map_X]

theorem rowPolynomial_diagonal {K H R : Type*} [Fintype K] [Fintype H] [CommRing R]
    (a : H → K → R) (x : H → R) (w : R) :
    rowPolynomial (fun k => ∑ i, a i k * (x i * w)) =
      C w * ∑ i, x i • rowPolynomial (a i) := by
  simp only [rowPolynomial, map_sum, map_mul, smul_eq_C_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LowDensityAmplification
namespace OAI

section

namespace Erdos3

open Filter

def LowDensityThreshold (H a : ℝ) : Prop := 0 < a ∧ H ^ 2 * a ≤ 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def tupleResidueReduction {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    (A → ZMod N) →+ (A → ZMod q) where
  toFun x a := ZMod.castHom hq (ZMod q) (x a)
  map_zero' := by ext a; simp
  map_add' := by
    intro x y
    ext a
    exact map_add (ZMod.castHom hq (ZMod q)) (x a) (y a)

noncomputable def integerLongPolynomialOutput {A I J : Type*} (poly : J → MvPolynomial (A ⊕ I) ℤ)
    (inactive : I → ℤ) (N : ℕ) (t : A → ZMod N) : J → ℤ :=
  fun j => MvPolynomial.eval (Sum.elim (fun a => ((t a).val : ℤ)) inactive) (poly j)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastJointGridCutoff (P E : ℝ) : ℕ :=
  ⌈Real.exp (P + E + 4)⌉₊

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

def modularForecastRankConstant (s D : ℕ) : ℕ :=
  (D + 2) * (2 ^ s * s.factorial) * 2 ^ s

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastJointGridError
    (dout dj dc cutoff : ℕ) (D L C K δ : ℝ) : ℝ :=
  (((cutoff : ℝ) ^ (dout + 1) * (2 * (8 : ℝ) ^ dj * (L + C * K) * δ) +
    (D / cutoff) * ((8 : ℝ) ^ dj * L * δ)) * (6 : ℝ) ^ dc) + 2 * (D / cutoff)

noncomputable def forecastJointGridMeshLog (d : ℕ) (P E : ℝ) : ℝ :=
  ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + E + 8

noncomputable def forecastJointGridMesh (d : ℕ) (P E : ℝ) : ℝ :=
  Real.exp (-forecastJointGridMeshLog d P E)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrependPolynomialVariable
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def prependPolynomialVariable {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n+1)) ℝ := MvPolynomial.X 0 * MvPolynomial.rename Fin.succ P

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeCoordinates
namespace OAI

section

namespace Erdos3

def affineCubeCoordinates {I : Type*} (u : Option I → ℝ) (v : Option I → ℕ)
    (x : Option I → ℝ) : Option I → ℝ := fun i => u i + (v i : ℝ) * x i

def affineIntegerCubeCoordinates {I : Type*} (u : Option I → ℤ) (v : Option I → ℕ)
    (x : Option I → ℤ) : Option I → ℤ := fun i => u i + (v i : ℤ) * x i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

noncomputable def integerSupportTorusFactor (H : ℝ) : ℕ := 2 * ⌈H⌉₊ + 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockJetScaleBound (q h b : ℕ) (A : ℝ) : ℝ :=
  b * 2 ^ h * ((q + 1 : ℕ) : ℝ) ^ h * A

theorem blockJetScaleBound_nonneg (q h b : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ blockJetScaleBound q h b A := by unfold blockJetScaleBound; positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget
namespace OAI

section

namespace Erdos3

theorem natCeil_le_exp_succ {x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P)
    (h : x ≤ Real.exp P) : (⌈x⌉₊ : ℝ) ≤ Real.exp (P+1) := by
  apply (Nat.ceil_lt_add_one hx).le.trans
  simpa only [add_comm x 1] using one_add_le_exp_succ hP h

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LayerTailDegree
namespace OAI

section

namespace Erdos3

def layerTailDegree (m : ℕ) : ℕ := m * (2^(m+1)+1)

theorem le_layerTailDegree (m : ℕ) : m ≤ layerTailDegree m := by
  unfold layerTailDegree
  nlinarith [Nat.zero_le (2^(m+1))]

theorem layerDegree_le_tailDegree {m : ℕ} (j : Fin m) : j.val+1 ≤ layerTailDegree m :=
  (Nat.succ_le_of_lt j.isLt).trans (le_layerTailDegree m)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayIntegerImage (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) : (I → O → ℝ) × (Z → O → ℤ) :=
  (fun i => (A.map (Int.cast : ℤ → ℝ)) *ᵥ x.1 i, fun z => A *ᵥ x.2 z)

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaProductPeriodization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A : Type*} [Fintype A] {D : A → Type*}

noncomputable def sigmaProductKernel (H : ∀ a, (D a → ℝ) → ℝ)
    (x : (Σ a, D a) → ℝ) : ℝ :=
  ∏ a, H a (fun i => x ⟨a, i⟩)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def affineProfileLogBound (n : ℕ) (t : ℝ) : ℝ :=
  n + (probabilityProfileLipschitz : ℝ) + (n + 1) * t

theorem affineProfileLogBound_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ affineProfileLogBound n t := by
  unfold affineProfileLogBound
  positivity

noncomputable def affineCoefficientCommonBudget (n d : ℕ) (b t : ℝ) : ℝ :=
  b + d + affineProfileLogBound n t

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BlockCubeDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

def blockCubeDomain (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] :
    Set (BlockParameter B F α → ℝ) :=
  (blockCubeFlatten B F α).symm ⁻¹' scalarCubeProductDomain (B × F) α

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def unitCoefficientSource (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  realDensityMeasure volume (smoothProductProfile I)

instance unitCoefficientSource_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (unitCoefficientSource I) :=
  realDensityMeasure_probability volume _
    ((smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact I))
    (fun r => (smoothProductProfile_range I r).1) (smoothProductProfile_integral I)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedOutputGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def gridDensityTest {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (a S : J → ℝ) (s : Finset (J → ℤ))
    (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ) : ℂ :=
  (∑ k ∈ s, ((mask k*f (rectangularLatticePoint a S k) : ℝ) : ℂ)*φ k) / ((∏ j, S j : ℝ) : ℂ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {Q : Type*} [Fintype Q] (I : Q → Type*) [∀ q, Fintype (I q)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

noncomputable def polynomialPerturbationScale (K M Q τ : ℝ) (m : ℕ) : ℝ :=
  min 1 (min (1 / (2 * (1 + K) * (1 + M)))
    (τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M))))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def jetOutputRadiusLog (q n d : ℕ) (P : ℝ) : ℝ := 4*P+n+q+(d : ℝ)*q+2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JoinedCoefficientProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def joinedCoefficientProfile {J N : Type*}
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : J ⊕ N → ℝ) : ℝ :=
  f (fun j => x (.inl j)) * g (fun n => x (.inr n))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SplitFreeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def splitFreeCoordinates (I J N : Type*) [Fintype I] [Fintype J] [Fintype N] :
    ((J ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (((J → ℝ) × (I → ℝ)) × (N → ℝ)) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).prodCongr
    (MeasurableEquiv.refl (I → ℝ))).trans
    (MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl (J → ℝ)).prodCongr MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FinitePhaseCancellation
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem circle_character_mul_star (θ : CircleFourier.Circle) :
    character θ * star (character θ) = 1 := by
  rw [← character_neg, ← character_add, add_neg_cancel, character_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ExternalNetMaskedScores
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def externalNetIndex {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) : X → I :=
  fun x => Classical.choose (hnet x)

theorem externalNetIndex_approx {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) (x : X) (y : Y) :
    ‖F x y - centers (externalNetIndex F centers hnet x) y‖ ≤ ε :=
  Classical.choose_spec (hnet x) y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProbabilityIntegralThresholdPoint
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {Λ : Type*} [MeasurableSpace Λ]

theorem probabilityIntegralThresholdPoint (μ : Measure Λ) [IsProbabilityMeasure μ]
    {m : Λ → ℝ} (hm : Integrable m μ) {c : ℝ} (hc : c ≤ ∫ l, m l ∂μ) :
    ∃ l, c ≤ m l := by
  obtain ⟨l, hl⟩ := exists_integral_le hm
  exact ⟨l, hc.trans hl⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TupleResidueConditioning
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tupleColumnMatrix {I J : Type*} {Ω : J → Type*}
    (c : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  Matrix.of (fun i j => c j (x j) i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {I Z O J : Type*} [Fintype I] [Fintype Z]
variable [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

noncomputable def integerMatrixImagePMF (p : J → PMF ℤ) : PMF (O → ℤ) :=
  (independentProductPMF p).map (fun z => A *ᵥ z)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {I Q : Type*} [Fintype I] [Fintype Q] {Y : I → Type*} {X : Q → Type*}
variable [∀ i, MeasurableSpace (Y i)] [∀ q, Countable (X q)]
variable [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical Matrix

namespace VectorPolynomial
variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O O' B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] [∀ j, Fintype (B j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O I : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]
variable [∀ j, DecidableEq (O j)]
variable {n : Fin m → ℕ} (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m : ℕ}
variable {I O : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
variable [∀ j, DecidableEq (O j)] {n : Fin m → ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def integerBoxCubeProductEquiv {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ) (q : ℕ) :
    SupportedCube q (integerBox N : Set (I → ℤ)) ≃
      (∀ i, SupportedCube q (Set.Ico (0 : ℤ) (N i : ℤ))) where
  toFun c i := ⟨(fun j => c.val.1 j i, c.val.2 i), by
    intro ω
    have h := (mem_integerBox N _).mp (c.property ω) i
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  invFun c := ⟨(fun j i => (c i).val.1 j, fun i => (c i).val.2), by
    intro ω
    apply (mem_integerBox N _).mpr
    intro i
    have h := (c i).property ω
    simpa only [Set.mem_Ico, Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply] using h⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by funext i; apply Subtype.ext; rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawAffinePolynomialJet
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def originalMonomialJetMap {C Z X K α O : Type*}
    [Fintype C] [Fintype α] [DecidableEq α]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (c w : C → ℝ) (x : X → ℝ) (r : C → ℝ) (o : O) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input z x t)
    (monomialArrayPolynomial e (fun j => c j + w j * r j))) (rows o)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedNarrowSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

noncomputable def splitPhysicalSpatialInputScale (G N : Type*)
    (H T : ℝ) (Q : N → ℝ) : Option (G ⊕ N) → ℝ
  | none => H
  | some (.inl _) => T
  | some (.inr j) => Q j

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α]

variable [DecidableEq α] [DecidableEq G]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedWindowIndicator
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {X Y : Type*} [Countable X] [DecidableEq X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {X : A → Type*}
variable (selected : A → Prop) [DecidablePred selected]

noncomputable def selectedProductExtension (p : ∀ a, X a → ℝ)
    (g : (∀ a : {a // selected a}, X a.val) → ℂ) (N : ℝ) (z : ∀ a, X a) : ℂ :=
  g (fun a => z a.val) / (N : ℂ) * ((∏ a : {a // ¬selected a}, p a.val (z a.val) : ℝ) : ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtIntegerCoefficient (j : J) : ℤ :=
  ((ZMod.prodEquivPi N hN).symm (Pi.single j (1 : ZMod (N j)))).val

noncomputable def crtIntegerRepresentative (u : J → ℤ) : ℤ :=
  ∑ j, crtIntegerCoefficient N hN j * u j

noncomputable def crtRepresentativePolynomial : MvPolynomial J ℝ :=
  ∑ j, ((crtIntegerCoefficient N hN j : ℝ) / (∏ i, N i : ℕ)) • X j

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_degree :
    crtRepresentativePolynomial N hN ∈ weightedSupportLE (fun _ => 1) 1 := by
  apply Submodule.sum_mem
  intro j _
  exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SynchronizeSplittingProjection
namespace OAI

section

namespace Erdos3

variable {G Q : Type*} [Group G] [Group Q]

theorem synchronize_splitting_projection (q : G →* Q) (H : Subgroup G)
    (E P R a d : G) (A D : Q) (hP : P ∈ H) (ha : a ∈ H) (hd : d ∈ H)
    (haq : q a = A⁻¹ * q E) (hdq : q d = q R * D⁻¹) :
    (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ H ∧ q (E * a⁻¹) = A ∧ q (d⁻¹ * R) = D ∧
      q (a * P * d) = A⁻¹ * q (E * P * R) * D⁻¹ := by
  refine ⟨?_, H.mul_mem (H.mul_mem ha hP) hd, ?_, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, haq]
    group
  · rw [map_mul, map_inv, hdq]
    group
  · simp only [map_mul, haq, hdq]
    group

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

def standardLatticeClosedQuarterBox (J : Type*) [Fintype J] : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| ≤ 1 / 4}

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativeBoxInput {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (x : X → ℤ) : ℝ :=
  if x ∈ integerBox N then f x else 0

@[simp] theorem relativeBoxInput_eq {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {x : X → ℤ} (hx : x ∈ integerBox N) :
    relativeBoxInput N f x = f x := by
  simp only [relativeBoxInput, if_pos hx]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeature (b t : ℝ) (sigma : Bool) (u : ℝ) : ℝ :=
  1 + (b + if sigma then t else -t) * (u - 1)

noncomputable def countingKernel (b u v : ℝ) : ℝ :=
  1 + b * (u + v - 2) + (2 * b ^ 2 - b) * (u - 1) * (v - 1)

noncomputable def positiveCountingKernel (b u v : ℝ) : ℝ := 1 - b + b * u * v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeatureProduct {I X : Type*} [Fintype I] [DecidableEq I]
    (b t : ℝ) (f : I → X → ℝ) (sigma : I → Bool) (x : X) : ℝ :=
  ∏ i, countingFeature b t (sigma i) (f i x)

noncomputable def countingKernelProductAverage {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, ∏ i, countingKernel b (f i x) (g i y)

noncomputable def positiveKernelGram {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (b : ℝ) (f : I → X → ℝ) : ℝ := 𝔼 x, 𝔼 y, ∏ i, positiveCountingKernel b (f i x) (f i y)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingBernoulli {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FiniteProbabilityWeights Bool where
  weight sigma := if sigma then b else 1 - b
  nonneg sigma := by cases sigma <;> simp <;> linarith
  total := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CappedDistanceReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def cappedDistanceTest {X : Type*} [PseudoMetricSpace X] (a x : X) : ℂ :=
  (min 1 (dist a x) : ℝ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.QuotientDetectorHeightBudget
namespace OAI

section

namespace Erdos3

theorem rationalHeightLE_ceil_exp_of_entries {q : ℚ} {r : ℝ}
    (hq : (q.num.natAbs : ℝ) ≤ Real.exp r ∧ (q.den : ℝ) ≤ Real.exp r) :
    RationalHeightLE q ⌈Real.exp r⌉₊ :=
  ⟨Nat.cast_le.mp (hq.1.trans (Nat.le_ceil _)),
    Nat.cast_le.mp (hq.2.trans (Nat.le_ceil _))⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFourPointAnchors
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable (G : Type*) [AddCommGroup G]

def fourSparse12Equiv : (G × G × G) ≃ (G × G) × G where
  toFun t := ((t.2.2, t.2.1), t.2.1 - t.1)
  invFun u := (u.1.2 - u.2, u.1.2, u.1.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; simp

variable {G} [Fintype G]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightedSifting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*}

noncomputable def sampleWeight (P : Ω → ι → ℝ) {q : ℕ} (t : Fin q → Ω) (a : ι) : ℝ :=
  ∏ i, P (t i) a

variable [Fintype Ω]

end Erdos3.WeightedSifting

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*} [Fintype Ω] [Nonempty Ω]

end Erdos3.WeightedSifting

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicOrdinaryShiftBranches
namespace OAI

section

namespace Erdos3

def ordinaryShiftBranch {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) : ℤ :=
  (if N - h.val ≤ x.val then 1 else 0) - b.val

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementPotential (D Q C : Finset G) (f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, ((𝔼 x ∈ D, f x) * cellAverage C g z) ^ (1 / 4 : ℝ)

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

noncomputable def flatComparisonDelta (epsilon : ℝ) : ℝ := epsilon / (4 * (2 + epsilon))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.LocalConvolution

end Erdos3.LocalConvolution

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCellCaps
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def translatedCellFamily (Shape : Finset G → Prop) (A : Finset G) : Prop :=
  ∃ C, Shape C ∧ ∃ z : G, A = C.image (fun t => z + t)

end Erdos3.Peeling

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SmallRatioPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def smallRatioCenterPotential (L : Finset G) (f g : G → ℝ)
    (u v c₀ : ℝ) (x y : G) : ℝ := by
  classical
  exact if cellAverage L f x < c₀ * u ∨ cellAverage L g y < c₀ * v then
    (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ) else 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OneDimensionalBox
namespace OAI

section

namespace Erdos3

def scalarPiOneEquiv (A : Type*) [AddCommGroup A] : A ≃+ (Fin 1 → A) where
  toFun a _ := a
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    exact congrArg f (Subsingleton.elim _ _)
  map_add' _ _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotNativeIteration
namespace OAI

section

namespace Erdos3

noncomputable def pivotIterationBound (q r m : ℕ) (p B : ℝ) : ℝ :=
  Real.exp ((r : ℝ) * p * m / q) * B ^ ((r + 2) * m)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

def maskedNormalized {X : Type*} (mu phi : X → ℝ) (x : X) : ℝ :=
  1 + phi x * (mu x - 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ConfigurationCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def twoSlopeAddHom {R : Type*} [CommRing R] (a b : R) : (R × R) →+ (R × R) where
  toFun z := (z.1 + a * z.2, z.1 + b * z.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FourierWeightedCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def configurationFourierWeight {R J : Type*} [AddMonoid R] [Fintype J]
    (c : J → ℂ) (Psi : J → AddChar (R × R) ℂ) (z : R × R) : ℂ :=
  ∑ j, c j * Psi j z

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedIdealGridEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedIdealLipEnvelope (D p e : A) : A :=
  D * p + 2 * D + (D + 1) * e + p

end Envelopes

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D p : ℝ}
  (hp : 0 ≤ p)

include hp

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialChoiceBudget
namespace OAI

section

namespace Erdos3

noncomputable def normalizedSpatialShare (E : ℝ) : ℝ := Real.exp (-(E + 2))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoordinateZeroProjection
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]

def coordinateZeroProjection (v : D → ℝ) : D → ℝ := fun d => if P d then 0 else v d

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracyLogBounds
namespace OAI

section

namespace Erdos3

def uniformProductAccuracyLog {A : Type*} [Semiring A] (D T E : A) : A :=
  D + D * (T + 4) + E

theorem uniformProductAccuracyLog_nonneg {D T E : ℝ}
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ uniformProductAccuracyLog D T E := by unfold uniformProductAccuracyLog; positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedActiveBudgetedSite
namespace OAI

section

namespace Erdos3

def siteExponentialOutputLog {A : Type*} [Semiring A] (s : ℕ) (Q : A) : A :=
  s * (4 * Q + 8) + 8 * Q + 18

theorem siteExponentialOutputLog_nonneg (s : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ siteExponentialOutputLog s Q := by unfold siteExponentialOutputLog; positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

variable {D : ℝ}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

namespace VectorPolynomial

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def fixedPathPerturbationLog (D P E : ℝ) (m : ℕ) : ℝ :=
  let Q := D + P + E + m + 2
  48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47

theorem fixedPathPerturbationLog_nonneg {D P E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathPerturbationLog D P E m := by
  unfold fixedPathPerturbationLog
  positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAmbientUniformPrecision
namespace OAI

section

namespace Erdos3

def fixedPathComparisonPrecision (E : ℝ) : ℝ := E + 4

noncomputable def fixedPathForecastTolerance (E : ℝ) : ℝ :=
  Real.exp (-(E + 8))

def fixedPathAmbientPrecision (Q E : ℝ) : ℝ := Q + E + 8

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AmplificationSourceResourceBudget
namespace OAI

section

namespace Erdos3

noncomputable def amplificationSourceLogCoefficient (D E : ℕ) : ℝ :=
  (E : ℝ) * ((D : ℝ) + 3)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedPathSlicedSourceErrorScalar
namespace OAI

section

namespace Erdos3

def fixedPathSlicedSourceError (rP rG C K Kφ ε η ξ : ℝ) : ℝ :=
  rP + (2 * ((2 * C + 2 * K) * rP + K * ε) + 2 * η) +
    (1 + 4 * C + 3 * Kφ) * rG + Kφ * ξ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped Classical

noncomputable def jointFrameSourceLo {K I : Type*} (width : Option K × I → ℝ) :
    Option K × I → ℤ :=
  fun t => match t.1 with
    | none => 0
    | some _ => -⌈width t⌉

noncomputable def jointFrameSourceHi {K I : Type*} (N : I → ℕ)
    (width : Option K × I → ℝ) : Option K × I → ℤ :=
  fun t => match t.1 with
    | none => N t.2
    | some _ => ⌈width t⌉ + 1

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def canonicalJointFrameWindowConstant (d : ℕ) (τ : ℝ) : ℝ :=
  16 * (2 * (d : ℝ) + 1) / τ

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndexedComparableScalarParameterBox
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def comparableScalarParameterRadius (r L : ℝ) : ℕ := ⌈r * L⌉₊

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteMixedLpCore (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0 ^ (2 / p 0)
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (2 / p (n + 1) - 2 / p n)

noncomputable def finiteMixedLpBound (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (1 - 2 / p n)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X] [Nonempty X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3

universe u v

inductive CoordinateDecisionTree (ι : Type u) (Value : ι → Type v) : Type (max u v)
  | leaf : CoordinateDecisionTree ι Value
  | split (i : ι) (children : Value i → CoordinateDecisionTree ι Value) : CoordinateDecisionTree ι Value

namespace CoordinateDecisionTree

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

inductive Valid (Good : Finset ι → (∀ i, Value i) → Prop) :
    Finset ι → (∀ i, Value i) → CoordinateDecisionTree ι Value → ℕ → Prop
  | leaf {I : Finset ι} {x : ∀ i, Value i} {d : ℕ} (good : Good I x) : Valid Good I x .leaf d
  | split {I : Finset ι} {x : ∀ i, Value i} {i : ι}
      {children : Value i → CoordinateDecisionTree ι Value} {d : ℕ}
      (fresh : i ∉ I)
      (branches : ∀ value, Valid Good (insert i I) (Function.update x i value) (children value) d) :
      Valid Good I x (.split i children) (d + 1)

theorem Valid.weaken {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (extra : ℕ) : Valid Good I x tree (d + extra) := by
  induction h with
  | leaf good => exact .leaf good
  | @split I x i children d fresh branches ih =>
    have hsum : d + 1 + extra = d + extra + 1 := by omega
    rw [hsum]
    exact .split fresh ih

end CoordinateDecisionTree

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def trace : CoordinateDecisionTree ι Value → Finset ι → (∀ i, Value i) → (∀ i, Value i) →
    Finset ι × (∀ i, Value i)
  | .leaf, I, x, _ => (I, x)
  | .split i children, I, x, input =>
    trace (children (input i)) (insert i I) (Function.update x i (input i)) input

theorem trace_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) : I ⊆ (trace tree I x input).1 := by
  induction tree generalizing I x with
  | leaf => exact Finset.Subset.refl I
  | split i children ih =>
    exact (Finset.subset_insert i I).trans (ih (input i) (insert i I) (Function.update x i (input i)))

theorem trace_agrees (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (x input : ∀ i, Value i) (hagree : ∀ i ∈ I, x i = input i) :
    ∀ i ∈ (trace tree I x input).1, (trace tree I x input).2 i = input i := by
  induction tree generalizing I x with
  | leaf => exact hagree
  | split i children ih =>
    apply ih (input i) (insert i I) (Function.update x i (input i))
    intro j hj
    by_cases hji : j = i
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hji]
      exact hagree j (Finset.mem_of_mem_insert_of_ne hj hji)

end Erdos3.CoordinateDecisionTree

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductKernelPairing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

noncomputable def productMatrixApply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ y, (∏ i, A i (x i) (y i)) * f y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productPairCoordinates {ι : Type*} (X Y : ι → Type*) :
    (∀ i, X i × Y i) ≃ (∀ i, X i) × (∀ i, Y i) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentEnvelope
namespace OAI

section

namespace Erdos3

def approxMomentEnvelope (N r : ℕ) (M : ℝ) : ℝ :=
  (2 : ℝ) ^ (r + 1) * (2 + (N : ℝ)) ^ r * (2 + M)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEqualityPatternCard
namespace OAI

section

namespace Erdos3

variable {N : ℕ}

noncomputable def finitePatternRepresentative (r : Setoid (Fin N)) (i : Fin N) : Fin N := by
  classical
  exact (Finset.univ.filter (fun j => r i j)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, r.refl' i⟩⟩

end Erdos3

end

section

namespace Erdos3

variable {S : Type*} [Fintype S]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorSectionPointwise
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def finiteFixedTagSet (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X) : Finset I :=
  Finset.univ.image (fun i : {i : Fin n // s i = true} => (z i).1)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [LinearOrder I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonAccuracyLog (b : ℕ) (P L T : ℝ) : ℝ :=
  (P + 3) ^ 3 + 2 * (b : ℝ) * (P + 2) + L + T + 4

noncomputable def affineComparisonAccuracy (b : ℕ) (P L T : ℝ) : ℝ :=
  Real.exp (-affineComparisonAccuracyLog b P L T)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

noncomputable def integerBoxGcdCutoff (d : ℕ) (C epsilon : ℝ) : ℕ :=
  ⌈2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon⌉₊ + 1

noncomputable def integerBoxNearRatio (d : ℕ) (epsilon : ℝ) : ℝ :=
  replacementAccuracy (2 * (3 : ℝ) ^ d) epsilon

noncomputable def integerBoxPairScale (d : ℕ) (C epsilon : ℝ) : ℝ :=
  max (integerBoxGcdCutoff d C epsilon : ℝ) (1 / integerBoxNearRatio d epsilon)

noncomputable def integerBoxRetainedGap (d D : ℕ) (c epsilon : ℝ) : ℝ :=
  (D : ℝ) * integerBoxNearRatio d epsilon * c

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

noncomputable def scalarMeshLog (gridLog inputLog accuracyLog : ℝ) : ℝ :=
  gridLog + 3 * inputLog + accuracyLog + 50

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

def copiedLayerSpace {J K : Type*} (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    Submodule ℝ (J ⊕ K → ℝ) where
  carrier := {x | (fun j => x (.inl j)) ∈ W ∧ (fun k => x (.inr k)) ∈ V}
  zero_mem' := ⟨W.zero_mem, V.zero_mem⟩
  add_mem' hx hy := ⟨W.add_mem hx.1 hy.1, V.add_mem hx.2 hy.2⟩
  smul_mem' r _ hx := ⟨W.smul_mem r hx.1, V.smul_mem r hx.2⟩

noncomputable def copiedLayerSpaceEquiv {J K : Type*}
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    copiedLayerSpace W V ≃ₗ[ℝ] W × V where
  toFun x := (⟨fun j => x.val (.inl j), x.property.1⟩, ⟨fun k => x.val (.inr k), x.property.2⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val, x.1.property, x.2.property⟩
  left_inv x := by ext j; cases j <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def copiedLayerMatrix {J K C : Type*} (B : Matrix J C ℚ) (e : K → ℚ) :
    Matrix (J ⊕ K) (Option C) ℚ :=
  Matrix.of (fun j c => match j, c with
    | .inl j, .some c => B j c
    | .inr k, .none => e k
    | _, _ => 0)

def copiedLayerRows {J K V : Type*} (A : Matrix V J ℚ) : Matrix V (J ⊕ K) ℚ :=
  Matrix.of (fun r j => Sum.elim (A r) (fun _ => 0) j)

def copyLeft {J K : Type*} : (J → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim v 0
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

def copyRight {J K : Type*} : (K → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim 0 v
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

noncomputable def copiedLayerPolynomial {I J K : Type*}
    (p : VectorPolynomial I ℝ (J → ℝ)) (q : VectorPolynomial I ℝ (K → ℝ)) :
    VectorPolynomial I ℝ (J ⊕ K → ℝ) := map copyLeft p + map copyRight q

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedArrayRefresh
namespace OAI

section

namespace Erdos3

variable {A B J K C V S T U W : Type*}

def mixedArrayEmbedding (e : A ↪ J) (d : B ↪ K) : A ⊕ B ↪ J ⊕ (K ⊕ C) where
  toFun := Sum.elim (fun a => Sum.inl (e a)) (fun b => Sum.inr (Sum.inl (d b)))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (d.injective (Sum.inl.inj (Sum.inr.inj h)))

@[simp] theorem mixedArrayEmbedding_inl (e : A ↪ J) (d : B ↪ K) (a : A) :
    mixedArrayEmbedding (C := C) e d (Sum.inl a) = Sum.inl (e a) := rfl

@[simp] theorem mixedArrayEmbedding_inr (e : A ↪ J) (d : B ↪ K) (b : B) :
    mixedArrayEmbedding (C := C) e d (Sum.inr b) = Sum.inr (Sum.inl (d b)) := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

def affineAmbientMassLog {A : Type*} [Semiring A] (P : A) : A :=
  4 * P ^ 3 + 9 * P ^ 2 + 5 * P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

noncomputable def affineAmbientPrimitiveBudget {A : Type*} [Semiring A] (base Q : A) : A :=
  let P₂ := 9 * (9 * (base + Q) + 13) + 5
  2 * affineAmbientMassLog P₂ + 7 * P₂ + 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitializedEarlyCanonicalSliceScales
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

noncomputable def canonicalSublevelCutoffLip : ℝ≥0 :=
  Classical.choose exists_smooth_sublevel_cutoff

noncomputable def canonicalSublevelCutoff : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec exists_smooth_sublevel_cutoff).2

noncomputable def canonicalTransitionLip : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearRestrictionHeight
namespace OAI

section

namespace Erdos3

def linearRestrictionHeight (n m d H K : ℕ) : ℕ :=
  (((n + 1) ^ d * K) * (m * H + 1) ^ d) *
    (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularVectorCoefficientDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {A B I R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [CommRing R]

noncomputable def designatedVectorComponent (S : B → A → Finset I)
    (Q : B → MvPolynomial I R) (c : B → A → R) (b : B) : MvPolynomial I R :=
  Q b + ∑ a, c b a • ∏ i ∈ S b a, X i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalL1SourceAccuracy
namespace OAI

section

namespace Erdos3

noncomputable def l1SourceAccuracy (target spatialCap spatialVolume : ℝ) : ℝ :=
  Real.exp (-(target + spatialCap + spatialVolume + 8))

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X G T : Type*} [Fintype X] [Fintype G] [DecidableEq G] [Fintype T]
variable (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ) (W L : ℝ)
variable (e : (Option G × X) ↪ T)

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

def canonicalZeroSpatialKernelEmbedding (G N X : Type*) :
    Option G × X ↪ Option (G ⊕ N) × X where
  toFun := fun p => (Option.map Sum.inl p.1, p.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    cases a <;> cases b <;> simp_all

@[simp] theorem canonicalZeroSpatialKernelEmbedding_apply (G N X : Type*)
    (p : Option G × X) :
    canonicalZeroSpatialKernelEmbedding G N X p = (Option.map Sum.inl p.1, p.2) := rfl

def canonicalZeroSpatialNarrowInput {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) : Option (G ⊕ N) × X → ℝ :=
  fun a => match a.1 with
    | some (.inr _) => ξ * u a
    | _ => u a

@[simp] theorem canonicalZeroSpatialNarrowInput_none {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (none, x) = u (none, x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inl {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (g : G) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inl g), x) = u (some (.inl g), x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inr {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (n : N) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inr n), x) = ξ * u (some (.inr n), x) := rfl

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {X G : Type*} [Fintype X] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

variable (s : Empty ↪ G)
variable (τ ξ : ℝ) (box : X → ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

def mixedResidueArrayEquiv (J D R : Type*) : ((J → R) × (D → R)) ≃ ((J ⊕ D) → R) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun j => f (.inl j), fun d => f (.inr d))
  left_inv _ := rfl
  right_inv f := by funext t; cases t <;> rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem padicStepQuotient_coprime {p step : ℕ} (hp : p.Prime)
    (hstep : step ≠ 0) (A : ℕ) :
    (step / p ^ padicValNat p step).Coprime (p ^ A) := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.Coprime.pow_right A
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have hm := Nat.mul_dvd_mul_left (p ^ padicValNat p step) h
  rw [← pow_succ, Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))] at hm
  exact pow_succ_padicValNat_not_dvd hstep hm

def padicStepQuotientUnit (p A step : ℕ) (hp : p.Prime) (hstep : step ≠ 0) :
    (ZMod (p ^ A))ˣ :=
  ZMod.unitOfCoprime (step / p ^ padicValNat p step)
    (padicStepQuotient_coprime hp hstep A)

@[simp] theorem padicStepQuotientUnit_coe (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (padicStepQuotientUnit p A step hp hstep : ZMod (p ^ A)) =
      (step / p ^ padicValNat p step : ℕ) := rfl

variable {L V : Type*} [Fintype L]

def prescribedCRTArbitraryStepEquiv (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0) :
    (∀ l, V → ZMod (p l ^ A l)) ≃+ (∀ l, V → ZMod (p l ^ A l)) where
  toFun x l v := padicStepQuotientUnit (p l) (A l) step (hp l) hstep * x l v
  invFun x l v := ↑(padicStepQuotientUnit (p l) (A l) step (hp l) hstep)⁻¹ * x l v
  left_inv x := by
    funext l v
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext l v
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    funext l v
    exact mul_add _ _ _

variable [Fintype V]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalCharacterIndividualModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {O : Type*} {N : ℕ}

noncomputable def rationalCharacterIndividualModulus (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) : ℕ := Nat.lcm qW (orderOf χ)

theorem rationalCharacterIndividualModulus_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) (hW : qW ∣ N) :
    rationalCharacterIndividualModulus qW χ ∣ N :=
  Nat.lcm_dvd hW (zmod_character_order_dvd χ)

theorem rationalCharacterIndividualModulus_order_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) :
    orderOf χ ∣ rationalCharacterIndividualModulus qW χ := Nat.dvd_lcm_right _ _

variable [NeZero N] (qW : ℕ) [NeZero qW] (χ : AddChar (O → ZMod N) ℂ)

theorem rationalCharacterIndividualModulus_pos :
    0 < rationalCharacterIndividualModulus qW χ :=
  Nat.lcm_pos (NeZero.pos qW) (zmod_character_order_pos χ)

noncomputable instance rationalCharacterIndividualModulus_neZero :
    NeZero (rationalCharacterIndividualModulus qW χ) :=
  ⟨(rationalCharacterIndividualModulus_pos qW χ).ne'⟩

variable (hW : qW ∣ N)

omit [NeZero qW] in
theorem exists_rationalCharacterIndividualReduction [NeZero qW] :
    ∃ ψ : AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ,
      characterPullback (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)) ψ = χ ∧
        orderOf ψ = orderOf χ := by
  apply exists_zmodPiReduction_character (rationalCharacterIndividualModulus_dvd qW χ hW) χ
  exact orderOf_dvd_iff_pow_eq_one.mp (rationalCharacterIndividualModulus_order_dvd qW χ)

noncomputable def rationalCharacterIndividualReduction :
    AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ :=
  (exists_rationalCharacterIndividualReduction qW χ hW).choose

variable [Fintype O]

section Partial

variable {Aux D : Type*} [Fintype D]
variable (χ' : AddChar ((Aux ⊕ D) → ZMod N) ℂ)

end Partial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

noncomputable def translatedGridMass (g : (J → ℝ) → ℝ) (center T : J → ℝ) : ℝ :=
  (∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / T j)) / (∏ j, T j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {Aux J : Type*} [Fintype Aux] [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J : Type*} [Fintype Ω] [Fintype Aux] [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ContainedProgressionForecastDisintegration
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

def progressionPrincipalResidue (q : ℕ)
    (r : PrincipalTupleIndex B h → Option α → ZMod q) :
    PrincipalTupleIndex B h → Option α → ZMod q :=
  fun j a => (if a = none then (c j : ZMod q) else 0) + (step j : ZMod q) * r j a

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateCopySum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateCopySum {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) : (C → R) →ₗ[R] (J → R) where
  toFun x j := ∑ c, if label c = j then x c else 0
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp

@[simp] theorem coordinateCopySum_apply {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) (x : C → R) (j : J) :
    coordinateCopySum label x j = ∑ c, if label c = j then x c else 0 := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def layerRankPotential {s : ℕ} (d : Fin s → ℕ) : ℕ :=
  ∑ i, (i.val + 1) * d i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMaskedCoefficientHaarLaw
namespace OAI

section

namespace Erdos3

noncomputable def allocatedUniformPMFCanonical (α : Type*) [Finite α] [Nonempty α] : PMF α :=
  @PMF.uniformOfFintype α (Fintype.ofFinite α) inferInstance

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (C V : Fin m → ℝ≥0)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUniformCoordinateRefresh
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J X : Type*}

noncomputable def coordinateResamplingEquiv (f : J → I) (hf : Function.Injective f) :
    ((I → X) × (J → X)) ≃ ((I → X) × (J → X)) where
  toFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  invFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

noncomputable def permanentPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.permanent (fun i j => X (i, j))

noncomputable def permanentExponent (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin n × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i, i) 1

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

def fixedSpatialEmptyIndex : (Σ _ : X, Unit ⊕ Empty) ≃ X where
  toFun a := a.1
  invFun x := ⟨x, .inl ()⟩
  left_inv a := by
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  right_inv _ := rfl

variable [Fintype X]

noncomputable def fixedSpatialEmptyCoordinates :
    (X → ℝ) ≃ₗᵢ[ℝ] ((Σ _ : X, Unit ⊕ Empty) → ℝ) where
  toFun u a := u a.1
  invFun v x := v ⟨x, .inl ()⟩
  left_inv _ := rfl
  right_inv v := by
    funext a
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
      intro a
      exact norm_le_pi_norm u a.1
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun a : Σ _ : X, Unit ⊕ Empty => u a.1))).mpr
      intro x
      exact norm_le_pi_norm (fun a : Σ _ : X, Unit ⊕ Empty => u a.1) ⟨x, .inl ()⟩

noncomputable def fixedSpatialEmptyDensity (f : (X → ℝ) → ℝ)
    (v : (Σ _ : X, Unit ⊕ Empty) → ℝ) : ℝ :=
  f (fixedSpatialEmptyCoordinates.symm v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalOutputAxisReindex
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def outputAxisReindexAddEquiv {A B : Type*} (e : A ≃ B)
    (H : Type*) [AddCommGroup H] : (A → H) ≃+ (B → H) where
  toFun x b := x (e.symm b)
  invFun y a := y (e a)
  left_inv x := by funext a; simp
  right_inv y := by funext b; simp
  map_add' _ _ := rfl

@[simp] theorem outputAxisReindexAddEquiv_apply {A B H : Type*} [AddCommGroup H]
    (e : A ≃ B) (x : A → H) (b : B) :
    outputAxisReindexAddEquiv e H x b = x (e.symm b) := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastComparisonFloorPolynomialBudget
namespace OAI

section

namespace Erdos3

def forecastComparisonMeshPolynomial (t grid : ℝ) : ℝ :=
  (2 * t + 1) * (grid + t + 9) + 12 * t + 2 * grid + t + 12

def forecastComparisonFloorPolynomial (t source grid : ℝ) : ℝ :=
  (5 * t + 2 * source + 32) +
    (4 * t + grid + forecastComparisonMeshPolynomial t grid + 12)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TriangularAffineReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

noncomputable def reducedLatticeColumn (T : Matrix (Fin d) (Fin d) ℝ)
    (j i : Fin d) : ℤ :=
  if i < j then 0 else if i = j then 1 else
    -round (∑ k : Fin i.val,
      T i (earlierSlot i k) * (reducedLatticeColumn T j (earlierSlot i k) : ℝ))
termination_by i.val
decreasing_by exact k.isLt

noncomputable def triangularReductionMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℤ := fun i j => reducedLatticeColumn T j i

noncomputable def reducedTriangularMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  T * (triangularReductionMatrix T).map (Int.castRingHom ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {d : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MonomialCharacterMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanCharacter (ξ x : E) : ℂ :=
  CircleFourier.character ((inner ℝ ξ x : ℝ) : CircleFourier.Circle)

@[simp]
theorem euclideanCharacter_zero (ξ : E) : euclideanCharacter ξ 0 = 1 := by
  simp [euclideanCharacter]

@[simp]
theorem euclideanCharacter_add (ξ x y : E) :
    euclideanCharacter ξ (x + y) = euclideanCharacter ξ x * euclideanCharacter ξ y := by
  simp [euclideanCharacter, inner_add_right]

@[simp]
theorem euclideanCharacter_neg (ξ x : E) :
    euclideanCharacter ξ (-x) = star (euclideanCharacter ξ x) := by
  simp [euclideanCharacter]

@[simp]
theorem norm_euclideanCharacter (ξ x : E) : ‖euclideanCharacter ξ x‖ = 1 := by
  simp [euclideanCharacter]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Real
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def monomialCharacterMean (k : ℕ) (α : E) (N : ℕ) (ξ : E) : ℂ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), euclideanCharacter ξ ((n : ℝ) ^ k • α)) /
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℂ)

@[simp]
theorem monomialCharacterMean_zero (k : ℕ) (α : E) (N : ℕ) :
    monomialCharacterMean k α N 0 = 1 := by
  have hne : (Finset.Icc (-(N : ℤ)) (N : ℤ)).Nonempty := ⟨0, by simp⟩
  have hc : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℂ) ≠ 0 := by
    exact_mod_cast hne.card_ne_zero
  simp only [monomialCharacterMean, euclideanCharacter, inner_zero_left,
    AddCircle.coe_zero, CircleFourier.character_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one, div_self hc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.GaussianLatticeDistance
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeGaussianTail (t R : ℝ) : ℝ :=
  ∑' m : Λ, if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftDifferenceCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def shiftCorrelation (Q : Finset G) (f : G → ℂ) (h : G) : ℂ :=
  ∑ x ∈ Q, f x * star (f (x + h))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeylStepScales
namespace OAI

section

namespace Erdos3

def weylNextBudget (k B K : ℕ) : ℕ :=
  2 * K + 32 * B ^ 2 + 128 * B ^ 2 * K +
    65536 * 2 ^ k * B ^ 4 * K ^ 3 +
    128 * (k + 1) * B ^ 2 * K ^ 2 + 98304 * 2 ^ k * B ^ 4 * K ^ 3

def weylBudget : ℕ → ℕ → ℕ
  | 0, B => B
  | j + 1, B => weylNextBudget (j + 1) B (weylBudget j (8 * B ^ 2))

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def weylBudgetPolynomial : ℕ → Polynomial ℕ
  | 0 => X
  | j + 1 =>
    let R := (weylBudgetPolynomial j).comp (C 8 * X ^ 2)
    C 2 * R + C 32 * X ^ 2 + C 128 * X ^ 2 * R +
      C (65536 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3 +
      C (128 * (j + 2)) * X ^ 2 * R ^ 2 + C (98304 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3

end Erdos3

end

section

namespace Erdos3

def weylShiftDenom (B K : ℕ) : ℕ := 128 * B ^ 2 * K

noncomputable def weylShiftDensity (B K : ℕ) : ℝ := 1 / (32 * (B : ℝ) ^ 2 * K)

noncomputable def weylShiftError (k N K : ℕ) : ℝ := (2 : ℝ) ^ k * K / (N : ℝ) ^ k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FixedSpatialDensityBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem factorial_le_exp_square (n : ℕ) {P : ℝ} (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) :
    (n.factorial : ℝ) ≤ Real.exp (P ^ 2) := by
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hbase : (n : ℝ) ≤ Real.exp P := hn.trans (le_trans (by linarith) (Real.add_one_le_exp P))
  calc
    _ ≤ (n : ℝ) ^ n := hfac
    _ ≤ (Real.exp P) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp (P * n) := by simpa only [mul_comm] using (Real.exp_nat_mul P n).symm
    _ ≤ Real.exp (P ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m d : ℕ} {X : Type*} {J : Fin m → Type*}

noncomputable def fullTaggedBufferedCoordinates (e : Fin d ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : Fin d → ℝ :=
  fun i => eval (fun a => (x a : ℝ)) (poly (e i).1) (e i).2 - c (e i).1 (e i).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ}
  {G X : Type*}
  [Fintype G]
  [Fintype X]
  {I E J : Fin m → Type*}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}

namespace AllocatedExternalLocalChart

variable {cost : ℝ}

variable (hσ1 : ∀ j, σ j ≤ 1)
  (H : Fin m → ℝ)
  (hH : ∀ j, 0 ≤ H j)
  (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
  (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hsmall hp

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {L M : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  [LieRing M]
  [LieAlgebra ℚ M]
  {r d t : ℕ}
  {Fmark : NilpotentLieFiltration M t}
  {φ : L →ₗ⁅ℚ⁆ M}
  {weight : (X → ℤ) → ℂ}
  {cost massThreshold scoreThreshold : ℝ}
  {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (hσ1 : ∀ j, σ j ≤ 1)
  (H : Fin m → ℝ)
  (hH : ∀ j, 0 ≤ H j)
  (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
  (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hsmall hp

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeTolerance
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def preparedUniformDegreeTolerance (t : ι → ℝ) (Qσ : ℝ) : ℝ :=
  min (∏ i, t i) (Real.exp (-Qσ))

noncomputable def preparedUniformDegreeScaleLog (pRadius : ℝ) (Ptail : ι → ℝ)
    (Qσ : ℝ) : ℝ :=
  pRadius + ∑ i, Ptail i + Qσ

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable {M : ℝ} (hM : 1 ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable {M : ℝ} (hM : 1 ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable {M : ℝ} (hM : 1 ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {dim : ℕ}


variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {dim : ℕ}


variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators Classical NNReal

noncomputable def affineSourceSum {ι : Type*} [Finite ι] (f : ι → ℝ) : ℝ :=
  @Finset.sum ι ℝ _ (@Finset.univ ι (Fintype.ofFinite ι)) f

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {dim : ℕ}


variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)

variable (ρ : ℝ≥0)

variable (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RecoveredKernelScalarBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def recoveredKernelScalarBudget (B : ℝ) : ℝ := 8 * (B + 1) ^ 2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedRoundedRank
namespace OAI

section

namespace Erdos3

noncomputable def preparedRoundedRank (p : ℝ) (e : ℕ) : ℕ :=
  ⌈Real.exp ((p + 2)^e)⌉₊

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ}
  {G X : Type}
  [Fintype G]
  [Fintype X]
  {I E J : Fin m → Type}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}

namespace AllocatedExternalCandidateProblem

variable {L M : Type}
  [LieRing L]
  [LieAlgebra ℚ L]
  [LieRing M]
  [LieAlgebra ℚ M]
  {r d t : ℕ}
  {Fmark : NilpotentLieFiltration M t}
  {φ : L →ₗ⁅ℚ⁆ M}
  {weight : (X → ℤ) → ℂ}
  {cost massThreshold scoreThreshold : ℝ}
  {outputCost outputMass outputScore : ℝ}

namespace Conclusion

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ}
  {G X : Type}
  [Fintype G]
  [Fintype X]
  {I E J : Fin m → Type}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}

namespace AllocatedExternalCandidateProblem.Conclusion

variable {Y M : Type}
  [LieRing M]
  [LieAlgebra ℚ M]
  {s d t : ℕ}
  (patch : PolynomialPatch Y s d)
  {Fmark : NilpotentLieFiltration M t}
  (f : (X → ℤ) → ℝ)
  (lam : ℝ)
  {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {R σ : Fin m → ℝ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

def actualForecastDataModelRequired (budget Pnative massLog u p : ℝ) : ℝ :=
  u + 2 * p + max (max budget (3 * Pnative + 3))
    (2 * u + 4 * p + max 0 massLog + 20) + 32

section AtLaw

variable [DecidableEq G]
variable {nX : ℕ} (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)

end AtLaw
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {R σ : Fin m → ℝ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {hmem : ∀ j d, coefficients (poly j) d ∈ U j}
variable {stride : X → ℕ}

namespace AllocatedExternalCandidateProblem.Conclusion
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d)
variable {Fmark : NilpotentLieFiltration M t}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {δbase PpresBase : ℝ}
variable (hkernel : Nonempty G)

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueMeshExponentialBudget
namespace OAI

section

namespace Erdos3

noncomputable def denseResidueMeshCap (n : ℕ) (δ ε C : ℝ) : ℕ :=
  ⌈16 * ((n : ℝ) + 1) * C / (ε * δ)⌉₊ + 1

noncomputable def denseResidueMeshStep (n : ℕ) (δ ε L : ℝ) : ℕ :=
  ⌊ε * δ * L / (8 * ((n : ℝ) + 1))⌋₊

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeScalarPassageDiscount
namespace OAI

section

namespace Erdos3

noncomputable def relativeScalarPassageSlack (τ : ℝ) : ℝ := τ / (2 * (1 - τ))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SecondaryMeshGeometry
namespace OAI

section

namespace Erdos3

noncomputable def secondaryBoundaryMargin (boundary beta : ℝ) : ℝ := replacementAccuracy boundary beta

noncomputable def secondaryMeshDelta (boundary movement beta : ℝ) : ℝ :=
  replacementAccuracy movement (secondaryBoundaryMargin boundary beta)

end Erdos3

end

section

namespace Erdos3

noncomputable def secondaryMovementBudget (movement sourceRatio parameterRatio : ℝ) : ℝ :=
  movement + sourceRatio + parameterRatio

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ}
noncomputable local instance fixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _
variable {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
  {I₀ J₀ : Fin 0 → Type}
  [∀ j, Fintype (I₀ j)]
  [∀ j, Fintype (J₀ j)]
  {n₀ : Fin 0 → ℕ}
  {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
  {R₀ σ₀ : Fin 0 → ℝ}
  {hR₀ : ∀ j, 0 < R₀ j}
  {hσ₀ : ∀ j, 0 < σ₀ j}
  {N : Fin nX → ℕ}
  {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
  {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
  {τ ξ₀ : ℝ}

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {nX : ℕ} (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)

variable (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
noncomputable local instance productiveFixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {Stage : Type} (degree : Stage → ℕ)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedPatchCutoffChoice
namespace OAI

section

namespace Erdos3

noncomputable def retainedPatchCutoff (ε : ℝ) : ℕ := ⌈16 / ε⌉₊

noncomputable def retainedPatchRelativeError (ε : ℝ) : ℝ := ε / 4

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.RankwiseBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open Filter Topology

def bundleRankwiseDensityFloor (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bundleRankwiseDensityFloor α d) (α (d + 1))

@[simp]
theorem bundleRankwiseDensityFloor_zero (α : ℕ → ℝ) :
    bundleRankwiseDensityFloor α 0 = α 0 :=
  rfl

@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl

noncomputable def bundleRankwiseStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

noncomputable def bundleRankwiseNextRow
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n)

noncomputable def bundleRankwiseEnvelopeError
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d)

@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl

@[simp]
theorem bundleRankwiseNextRow_succ
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n) :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_card
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, bundleRankwiseEnvelopeError α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp

@[simp]
theorem bundleRankwiseNextRow_zero_parameters
    (α μ : ℕ → ℝ) (d : ℕ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n,
      bundleRankwiseNextRow α (fun _ => 0) μ 0 d lower n = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ, ih]
      simp [bundleRankwiseStepIncrement, hlower]

@[simp]
theorem bundleRankwiseEnvelopeError_zero_parameters
    (α μ : ℕ → ℝ) :
    ∀ d n,
      bundleRankwiseEnvelopeError α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_zero_parameters α μ d _ ih n

noncomputable def bundleRankwiseScaledDefect
    (α : ℕ → ℝ) (power : ℕ → ℕ) (t : ℝ) (d : ℕ) : ℝ :=
  (t * (α d) ^ (power d)) ^ 2

noncomputable def bundleRankwiseScaledUniformity
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) (t : ℝ) : ℝ :=
  (t *
      (bundleRankwiseDensityFloor α rankBound) ^ uniformPower) ^ 2

@[simp]
theorem bundleRankwiseScaledDefect_zero
    (α : ℕ → ℝ) (power : ℕ → ℕ) (d : ℕ) :
    bundleRankwiseScaledDefect α power 0 d = 0 := by
  simp [bundleRankwiseScaledDefect]

@[simp]
theorem bundleRankwiseScaledUniformity_zero
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) :
    bundleRankwiseScaledUniformity α rankBound uniformPower 0 = 0 := by
  simp [bundleRankwiseScaledUniformity]

def bundleReverseDoublingHorizon
    (rankBound edgeBound d : ℕ) : ℕ :=
  (edgeBound + 1) * 2 ^ (rankBound - d)

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ShortInterval
namespace OAI

section

namespace Erdos3.FixedDensity

def cyclicAPVal {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val

@[simp]
theorem cyclicAPVal_cast {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (cyclicAPVal a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DeterminingMatrixDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d m : ℕ}

def dilatedIntegerMatrix (q : ℕ) (M : Fin m → Fin d → ℤ) : Fin m → Fin d → ℤ :=
  fun i j => (q : ℤ) * M i j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

noncomputable def unconditionedScalarPrimeRatio (n : ℕ) : ℕ :=
  ⌈Real.exp ((n : ℝ) + 2)⌉₊ + 2

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Reciprocal
namespace OAI

section

open scoped BigOperators

namespace Erdos3

@[simp] theorem reciprocalTerm_zero (A : Set ℕ) : reciprocalTerm A 0 = 0 := by
  classical
  simp [reciprocalTerm]

end Erdos3

end

end OAI

end


