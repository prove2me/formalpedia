-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_02
-- name    : InfoLossLAR_NativeBundle_02
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T10:58:32.956229+00:00
-- url     : https://prove2.me/theorems/722eceb7-124d-4154-affd-b9e8935ef0dc
-- title:
--   Affine charts, tensor channels, and binary control data
-- statement:
--   This package defines finite marked charts, source and pool indices, tensor channels, affine data, and the binary arithmetic and control structures used by their numerical implementations. It also supplies the stored polynomial and rejection interfaces needed by the later current-parameter construction.
--
--   A legal affine pair over a module $V$ consists of an invertible linear map $Q:V\to V$ and an offset $b\in V$, with evaluator
--   $$x\longmapsto Qx+b.$$
--   The same finite data interfaces distinguish a source law, a public control record, and the channel applied after that record is fixed.
--
--   These objects let subsequent theorems state exact algebraic and probabilistic semantics for concrete public samplers. Any recorded operation charges are native accounting fields, rather than TM2 running-time certificates.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/AFT/ActualBasePrimaryProgram.lean, lean/AFT/BetaCountedProgram.lean, lean/AFT/V7Charge.lean, lean/AFT/ReferenceChargeConditioning.lean, lean/AFT/ActualAnchorProgram.lean, lean/AFT/BoundaryCalibration.lean, lean/AFT/BoundarySpike.lean, lean/AFT/BoundaryChartParameters.lean, lean/AFT/RationalCommonDenominator.lean, lean/AFT/RationalLinearIteration.lean, lean/AFT/IntegerLinearIteration.lean, lean/AFT/ChartProjectionProgram.lean, lean/AFT/RationalPositiveNormalize.lean, lean/AFT/MarkedChartProgram.lean, lean/AFT/FiniteAffineFeatures.lean, lean/AFT/FiniteMarkedChart.lean, lean/AFT/ActualChartProgram.lean, lean/AFT/ConditionalPairOutput.lean, lean/AFT/ActualConditionalPairProgram.lean, lean/AFT/TensorChannel.lean, lean/AFT/ChannelCentering.lean, lean/AFT/MixtureTail.lean, lean/AFT/TaggedBlockTail.lean, lean/AFT/LocalCoefficientLinear.lean, lean/AFT/JointFock.lean, lean/AFT/TensorChannelFormula.lean, lean/AFT/JointPhysicalChannel.lean, lean/AFT/PackedFock.lean, lean/AFT/PackedFockEvaluation.lean, lean/AFT/JointPhysicalFock.lean, lean/AFT/PublicChartGaussian.lean, lean/AFT/ResponseEnergy.lean, lean/AFT/SignedFirstCoefficient.lean, lean/AFT/SingletonFock.lean, lean/AFT/ActualJointFock.lean, lean/AFT/BlockCoefficientNorms.lean, lean/AFT/RestrictedBlockMean.lean, lean/AFT/ActualTaggedTail.lean, lean/AFT/ActualInputMixedTail.lean, lean/AFT/ActualFiniteControlTail.lean, lean/AFT/FiniteSetNumbering.lean, lean/AFT/PublicPools.lean, lean/AFT/PublicSourceEmbedding.lean, lean/AFT/ActualPublicSources.lean, lean/AFT/RoleSourceSlots.lean, lean/AFT/ActualPublicTaggedPlacement.lean, lean/AFT/JointSignedChannel.lean, lean/AFT/ActualRootResponse.lean, lean/AFT/Affine.lean, lean/AFT/Algebra.lean, lean/AFT/PermutationProgram.lean, lean/AFT/PermutationProgramCost.lean, lean/AFT/BinaryBitTape.lean, lean/AFT/BinaryNaturalCounter.lean, lean/AFT/RationalGaussianResources.lean, lean/AFT/RationalSeriesHeight.lean, lean/AFT/BinaryFiniteArithmetic.lean, lean/AFT/RejectionStability.lean, lean/AFT/RationalAcceptanceCoin.lean, lean/AFT/BinaryRationalFloor.lean, lean/AFT/BinaryDyadicFloor.lean, lean/AFT/BinaryAcceptanceCoin.lean, lean/AFT/Tree.lean, lean/AFT/BodyPathGeometry.lean, lean/AFT/BodyPaddingCovariance.lean, lean/AFT/BodyPaddingInverse.lean, lean/AFT/CountableFiniteChannel.lean, lean/AFT/CenteredGaussianProgram.lean, lean/AFT/TriangularGaussian.lean, lean/AFT/RationalGaussianChain.lean, lean/AFT/CountedGaussianArithmetic.lean, lean/AFT/CountedPositiveSampling.lean, lean/AFT/CanonicalJointInverse.lean, lean/AFT/FiniteDisintegration.lean, lean/AFT/PublicRecordExtension.lean, lean/AFT/RationalRejectionProgram.lean, lean/AFT/TensorMixedSchur.lean, lean/AFT/TensorMatrixCanonical.lean, lean/AFT/TwoPoolCanonical.lean, lean/AFT/CanonicalMomentBound.lean, lean/AFT/TwoPoolActivity.lean, lean/AFT/TwoPoolMomentBound.lean, lean/AFT/ExecutableGlobalRejection.lean, lean/AFT/CountedRationalRejection.lean, lean/AFT/OrderedSeedFactors.lean, lean/AFT/ParametricOrderedTable.lean, lean/AFT/ScalarProgramResources.lean, lean/AFT/ScalarOperationalEvaluation.lean, lean/AFT/BinaryChartArray.lean, lean/AFT/BinaryDataArrays.lean, lean/AFT/BinaryLoopControl.lean, lean/AFT/BinaryCounterDivision.lean, lean/AFT/ChartLegalize.lean, lean/AFT/ChartProgramHeight.lean, lean/AFT/CountedChartProgram.lean, lean/AFT/CachedPublicChartProgram.lean, lean/AFT/CountedFiniteScans.lean, lean/AFT/CountedChartSupports.lean, lean/AFT/BinaryProtectedFeature.lean, lean/AFT/BinaryChartMetadata.lean, lean/AFT/BinarySignedComparison.lean, lean/AFT/BinaryProtectedPalette.lean, lean/AFT/BinaryIntegerData.lean, lean/AFT/BinaryIntegerDivision.lean, lean/AFT/IntegerCoordinateProgram.lean, lean/AFT/BinaryPathInverse.lean, lean/AFT/BinaryRoundingInverse.lean, lean/AFT/BinaryAffineLoads.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 fccfed8f87e9deea34c14e00beb246b0b905f39c7169ca9f8db16a6f147102f9.

import Definitions.Def_InfoLossLAR_NativeBundle_01
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryDivision
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryNormalization
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalControl
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalIntegers
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalOperations
import Definitions.Def_InfoLossLAR_Native_AFT_BinarySignedAddition
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Definitions.Def_InfoLossLAR_Native_AFT_Histogram
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Definitions.Def_InfoLossLAR_Native_AFT_TransportBound
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

section




































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActivationApprox
end AFT.V7Calibration.actualActivationApprox
namespace AFT.V7Calibration.actualActivationInverseApprox
end AFT.V7Calibration.actualActivationInverseApprox
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Rational evaluation of the actual base-primary calibration -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualLegPopulationProgram (n : ℕ) : ℕ := (max 2 n)^30

def actualDimensionProgram (n : ℕ) : ℕ := (ParameterProgram.modulus n).value*(max 2 n)^20



noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false



























end
end AFT.V7Calibration

end

section





/-! # A counted fair-bit beta program with a rational output pair

The output is an unreduced pair of natural integers. This avoids requiring
rational arithmetic for the final typical-value check.
-/
namespace AFT.BetaReference
open scoped BigOperators

namespace CountedNatural







end CountedNatural

structure CountedFraction where
  numerator : ℕ
  denominator : ℕ
  work : ℕ

namespace CountedFraction



/-- Exactly one addition, six multiplications, and two comparisons determine
whether the rational grid point is typical. The result needs no division. -/
def safePoint (N K M index : ℕ) : CountedFraction :=
  let point := index+1
  let lowerLeft := K*M
  let lowerRight := (2*N)*point
  let upperLeft := point*N
  let upperRight := (2*K)*M
  if lowerLeft ≤ lowerRight ∧ upperLeft ≤ upperRight then ⟨point,M,9⟩ else ⟨K,N,9⟩

@[simp] theorem safePoint_work (N K M index : ℕ) : (safePoint N K M index).work=9 := by
  simp only [safePoint]
  split_ifs <;> rfl









end CountedFraction
end AFT.BetaReference

end

section













namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile





/-! # Actual safe-center charge mixing for the V7 family -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

attribute [local instance] actualModulusNeZero

def actualAnchorLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  (actualPrimaryLaw cutoffScale parameter beta).mix fun input =>
    ⟨fun output => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) input output.val,
      fun _ => publicAnchorKernel_nonneg _ _ _ _, (actual_anchor_safe_mass parameter input).1⟩

@[simp] theorem actualAnchorLaw_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (output : Fin (Parameters.modulus parameter)) :
    (actualAnchorLaw cutoffScale parameter beta).weight output =
      anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (actualPrimaryLaw cutoffScale parameter beta).weight output.val := rfl













end

end AFT.V7Calibration

end

section














namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.HistogramGenerating
end AFT.HistogramGenerating
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBoundaryFraction
end AFT.V7Calibration.actualBoundaryFraction


/-! # Conditioning the actual beta-reference histogram on total charge -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteDist
variable {State : Type*} [Fintype State] [Nonempty State]







end FiniteDist

namespace HistogramGenerating
variable {G : Type*} [Fintype G] [AddCommGroup G]




end HistogramGenerating

namespace V7Calibration
open GaussianSource HistogramGenerating Filter
open scoped Topology
attribute [local instance] actualModulusNeZero
local instance referenceChargeConditionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _



end V7Calibration
end
end AFT

end

section








































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.finiteLaw
end AFT.BetaReference.finiteLaw
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.integerCDFPrefix
end AFT.BetaReference.integerCDFPrefix
namespace AFT.BetaReference.integerCDFTerm
end AFT.BetaReference.integerCDFTerm
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BetaReference.safeGridValue
end AFT.BetaReference.safeGridValue
namespace AFT.BinaryCDFSampler
end AFT.BinaryCDFSampler
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.HistogramGenerating
end AFT.HistogramGenerating
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.ParameterProgram
end AFT.ParameterProgram
namespace AFT.ParameterProgram.beta
end AFT.ParameterProgram.beta
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBetaBufferedTail
end AFT.V7Calibration.actualBetaBufferedTail
namespace AFT.V7Calibration.actualBetaGridError
end AFT.V7Calibration.actualBetaGridError
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryCoefficient
end AFT.V7Calibration.actualBoundaryCoefficient
namespace AFT.V7Calibration.actualBoundaryCoefficientProgram
end AFT.V7Calibration.actualBoundaryCoefficientProgram
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualBoundaryUniformProgram
end AFT.V7Calibration.actualBoundaryUniformProgram
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualDimension_positive
end AFT.V7Calibration.actualDimension_positive
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorCountProgram
end AFT.V7Calibration.actualInteriorCountProgram
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualInteriorUniformProgram
end AFT.V7Calibration.actualInteriorUniformProgram
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryProgram
end AFT.V7Calibration.actualPrimaryProgram
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualReferenceZeroChargeHistogram
end AFT.V7Calibration.actualReferenceZeroChargeHistogram
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridCutoff
end AFT.V7Calibration.betaGridCutoff
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridRejectedMass
end AFT.V7Calibration.betaGridRejectedMass
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.modulus_population_upper
end AFT.V7Calibration.modulus_population_upper
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Rational entries of the physical body and root-only anchor matrices -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def publicAnchorStartProgram (modulus width color : ℕ) (coin : Bool) : ℤ :=
  if 2*color < modulus-1 then (modulus : ℤ)-color-2*width
  else if modulus-1 < 2*color then (modulus : ℤ)-1-color+width
  else if coin then (modulus : ℤ)-color-2*width else (modulus : ℤ)-1-color+width





noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance anchorProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _













end
end AFT.V7Calibration

end

section





/-!
# Positive repair on the safe affine-chart set

This file formalizes the finite-dimensional Neumann repair in V7's
`accuracy-boundary-chart` proof, including its pointwise positivity constants.
The affine-feature equivalences below supply the exact unrestricted uniform
and pairwise-independence statements used by that construction.
-/
namespace AFT
namespace BoundaryCalibration

open scoped BigOperators

section FiniteRepair
variable {Ω : Type*} [Fintype Ω]

/-- Restrict a chart density to the public safe set. -/
noncomputable def safeMask (safe : Ω → Prop) [DecidablePred safe] :
    (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  ContinuousLinearMap.pi fun x => if safe x then ContinuousLinearMap.proj x else 0

omit [Fintype Ω] in
@[simp] theorem safeMask_apply (safe : Ω → Prop) [DecidablePred safe]
    (f : Ω → ℝ) (x : Ω) :
    safeMask safe f x = if safe x then f x else 0 := by
  simp only [safeMask, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

/-- The actual deletion operator `P(1_{safeᶜ} f)`. -/
noncomputable def deletion (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] : (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  P * (ContinuousLinearMap.id ℝ (Ω → ℝ) - safeMask safe)

omit [Fintype Ω] in
@[simp] theorem deletion_apply (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] (f : Ω → ℝ) :
    deletion P safe f = P (f - safeMask safe f) := rfl

/-- Invert `Id - D` by its norm-convergent geometric series. -/
noncomputable def neumannSolve (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (f : Ω → ℝ) : Ω → ℝ :=
  (↑((Units.oneSub D hD)⁻¹) : (Ω → ℝ) →L[ℝ] (Ω → ℝ)) f

/-- The constructed inverse solves the required equation exactly. -/
theorem neumannSolve_equation (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (f : Ω → ℝ) :
    neumannSolve D hD f - D (neumannSolve D hD f) = f := by
  have h := congrArg (fun T : (Ω → ℝ) →L[ℝ] (Ω → ℝ) => T f)
    (Units.val_inv (Units.oneSub D hD))
  change ((1 - D) * (↑((Units.oneSub D hD)⁻¹) : (Ω → ℝ) →L[ℝ] (Ω → ℝ))) f = f at h
  simpa only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, neumannSolve] using h





/-- If `P` is a projection and the desired response is in its range, restricting
the Neumann solution to safe charts has exactly that response. -/
theorem safe_neumann_projection (P : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (safe : Ω → Prop) [DecidablePred safe] (hP : P * P = P)
    (hD : ‖deletion P safe‖ < 1) (f : Ω → ℝ) (hf : P f = f) :
    P (safeMask safe (neumannSolve (deletion P safe) hD f)) = f := by
  let h := neumannSolve (deletion P safe) hD f
  have heq : h - P (h - safeMask safe h) = f :=
    neumannSolve_equation (deletion P safe) hD f
  have hp := congrArg P heq
  have hPid (g : Ω → ℝ) : P (P g) = P g := by
    exact congrArg (fun T : (Ω → ℝ) →L[ℝ] (Ω → ℝ) => T g) hP
  simp only [map_sub, hPid, hf] at hp
  change P (safeMask safe h) = f
  convert hp using 1
  abel







end FiniteRepair
section FeatureProjections
open scoped Classical
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

/-- Exact expectation as a linear functional on finite chart densities. -/
noncomputable def expectation (p : FiniteDist Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ x, p.weight x * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_left_comm, ← Finset.mul_sum]

@[simp] theorem expectation_apply (p : FiniteDist Ω) (f : Ω → ℝ) :
    expectation p f = ∑ x, p.weight x * f x := rfl

@[simp] theorem expectation_const (p : FiniteDist Ω) (r : ℝ) :
    expectation p (fun _ => r) = r := by
  simp [expectation, ← Finset.sum_mul, p.sum_one]

/-- Pushforward is exact at the level of every test function. -/
theorem expectation_map (p : FiniteDist Ω) (feature : Ω → C) (g : C → ℝ) :
    expectation (p.map feature) g = expectation p (fun x => g (feature x)) := by
  simp only [expectation_apply, FiniteDist.map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- Normalized expectation conditioned on an equidistributed feature value. -/
noncomputable def conditional (p : FiniteDist Ω) (feature : Ω → C) :
    (Ω → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun f color := (Fintype.card C : ℝ) *
    expectation p (fun x => if feature x = color then f x else 0)
  map_add' f g := by
    funext color
    change (Fintype.card C : ℝ) * expectation p
      (fun x => if feature x = color then f x + g x else 0) = _
    have he : (fun x => if feature x = color then f x + g x else (0 : ℝ)) =
        (fun x => if feature x = color then f x else 0) +
          (fun x => if feature x = color then g x else 0) := by
      funext x
      split_ifs <;> simp_all
    rw [he, map_add, mul_add]
    rfl
  map_smul' r f := by
    funext color
    change (Fintype.card C : ℝ) * expectation p
      (fun x => if feature x = color then r * f x else 0) = _
    have he : (fun x => if feature x = color then r * f x else (0 : ℝ)) =
        r • (fun x => if feature x = color then f x else 0) := by
      funext x
      split_ifs <;> simp_all
    rw [he, map_smul]
    change (Fintype.card C : ℝ) * (r * _) = r * ((Fintype.card C : ℝ) * _)
    ring

@[simp] theorem conditional_apply (p : FiniteDist Ω) (feature : Ω → C)
    (f : Ω → ℝ) (color : C) :
    conditional p feature f color = (Fintype.card C : ℝ) *
      expectation p (fun x => if feature x = color then f x else 0) := rfl

/-- Conditioning a feature on itself recovers the exact color profile. -/
theorem conditional_same [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (g : C → ℝ) :
    conditional p feature (fun x => g (feature x)) = g := by
  funext color
  rw [conditional_apply]
  have he := expectation_map p feature (fun c => if c = color then g c else 0)
  rw [hfeature] at he
  rw [← he]
  simp [expectation_apply, FiniteDist.uniform_weight, mul_ite,
    Fintype.card_ne_zero]

/-- Conditioning on an independent uniform feature gives a constant profile. -/
theorem conditional_other [Nonempty C] (p : FiniteDist Ω) (first second : Ω → C)
    (hpair : p.map (fun x => (first x, second x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (g : C → ℝ) :
    conditional p first (fun x => g (second x)) =
      fun _ => expectation (FiniteDist.uniform C) g := by
  funext color
  rw [conditional_apply]
  have he := expectation_map p (fun x => (first x, second x))
    (fun pair => if pair.1 = color then g pair.2 else 0)
  rw [hpair] at he
  rw [← he]
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [expectation_apply, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, mul_ite, ← Finset.mul_sum]
  field_simp

/-- Keep a color profile on its allowed set and subtract its allowed-set mean. -/
noncomputable def centerAllowed (allowed : Finset C) : (C → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun g c := if c ∈ allowed then g c - (∑ a ∈ allowed, g a) / allowed.card else 0
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div]
    ring
  map_smul' r g := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_sub, mul_div_assoc]

omit [Fintype C] in
@[simp] theorem centerAllowed_apply (allowed : Finset C) (g : C → ℝ) (c : C) :
    centerAllowed allowed g c =
      if c ∈ allowed then g c - (∑ a ∈ allowed, g a) / allowed.card else 0 := rfl

omit [Fintype C] in
@[simp] theorem centerAllowed_const (allowed : Finset C) (r : ℝ) :
    centerAllowed allowed (fun _ => r) = 0 := by
  funext c
  rw [centerAllowed_apply]
  by_cases hc : c ∈ allowed
  · have hcard : (allowed.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨c, hc⟩)
    simp [hc, hcard]
  · simp [hc]

/-- Centering on the allowed palette removes all mass. -/
theorem centerAllowed_sum (allowed : Finset C) (g : C → ℝ) :
    ∑ c, centerAllowed allowed g c = 0 := by
  simp only [centerAllowed_apply, ← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  by_cases ha : allowed = ∅
  · simp [ha]
  · have hcard : (allowed.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ha))
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring

/-- Centering twice is exactly the same projection. -/
theorem centerAllowed_idempotent (allowed : Finset C) (g : C → ℝ) :
    centerAllowed allowed (centerAllowed allowed g) = centerAllowed allowed g := by
  have hsum : ∑ a ∈ allowed, centerAllowed allowed g a = 0 := by
    rw [← centerAllowed_sum allowed g]
    exact Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by simp [hc])
  funext c
  rw [centerAllowed_apply, hsum, zero_div, sub_zero]
  split_ifs with hc
  · rfl
  · simp [hc]

/-- Pull a color profile back to the corresponding chart feature. -/
def liftFeature (feature : Ω → C) : (C → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun g x := g (feature x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual centered feature projection from the boundary-chart proof. -/
noncomputable def featureProjection (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
  (liftFeature feature).comp ((centerAllowed allowed).comp (conditional p feature))

@[simp] theorem featureProjection_apply (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) (f : Ω → ℝ) (x : Ω) :
    featureProjection p feature allowed f x =
      centerAllowed allowed (conditional p feature f) (feature x) := rfl

/-- Each feature component is an exact projection. -/
theorem featureProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C)
    (allowed : Finset C) :
    (featureProjection p feature allowed).comp (featureProjection p feature allowed) =
      featureProjection p feature allowed := by
  apply LinearMap.ext
  intro f
  change liftFeature feature (centerAllowed allowed
    (conditional p feature (fun x => centerAllowed allowed
      (conditional p feature f) (feature x)))) = _
  rw [conditional_same p feature hfeature, centerAllowed_idempotent]
  rfl

/-- Different feature projections annihilate each other by exact pairwise independence. -/
theorem featureProjection_orthogonal [Nonempty C] (p : FiniteDist Ω)
    (first second : Ω → C)
    (hpair : p.map (fun x => (first x, second x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (A B : Finset C) :
    (featureProjection p first A).comp (featureProjection p second B) = 0 := by
  apply LinearMap.ext
  intro f
  change liftFeature first (centerAllowed A
    (conditional p first (fun x => centerAllowed B
      (conditional p second f) (second x)))) = 0
  rw [conditional_other p first second hpair, centerAllowed_const, map_zero]

/-- Projection onto the constant chart densities. -/
noncomputable def constantProjection (p : FiniteDist Ω) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun f _ := expectation p f
  map_add' _ _ := by funext x; simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by funext x; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem constantProjection_apply (p : FiniteDist Ω) (f : Ω → ℝ) (x : Ω) :
    constantProjection p f x = expectation p f := rfl

@[simp] theorem constantProjection_idempotent (p : FiniteDist Ω) :
    constantProjection p * constantProjection p = constantProjection p := by
  apply LinearMap.ext
  intro f
  funext x
  exact expectation_const p (expectation p f)

/-- Feature centering annihilates constants. -/
theorem featureProjection_const [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (r : ℝ) :
    featureProjection p feature allowed (fun _ => r) = 0 := by
  change liftFeature feature (centerAllowed allowed
    (conditional p feature (fun x => (fun _ : C => r) (feature x)))) = 0
  rw [conditional_same p feature hfeature (fun _ : C => r), centerAllowed_const, map_zero]

/-- Each centered feature has zero unrestricted mean. -/
theorem featureProjection_mean [Nonempty C] (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (f : Ω → ℝ) :
    expectation p (featureProjection p feature allowed f) = 0 := by
  change expectation p (fun x =>
    centerAllowed allowed (conditional p feature f) (feature x)) = 0
  rw [← expectation_map, hfeature]
  simp only [expectation_apply, FiniteDist.uniform_weight, ← Finset.mul_sum,
    centerAllowed_sum, mul_zero]

theorem featureProjection_constantProjection [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) :
    featureProjection p feature allowed * constantProjection p = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  exact congrFun (featureProjection_const p feature hfeature allowed (expectation p f)) x

theorem constantProjection_featureProjection [Nonempty C] (p : FiniteDist Ω)
    (feature : Ω → C) (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) :
    constantProjection p * featureProjection p feature allowed = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  exact featureProjection_mean p feature hfeature allowed f

/-- The paper's projection: constants plus all allowed centered feature components. -/
noncomputable def combinedProjection (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) :=
  constantProjection p + ∑ i, featureProjection p (features i) (allowed i)

/-- Pairwise-independent unrestricted features make the concrete sum operator
an exact projection. -/
theorem combinedProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    combinedProjection p features allowed * combinedProjection p features allowed =
      combinedProjection p features allowed := by
  have hcomp (i j : I) :
      featureProjection p (features i) (allowed i) * featureProjection p (features j) (allowed j) =
        if i = j then featureProjection p (features i) (allowed i) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [Module.End.mul_eq_comp, if_true] using featureProjection_idempotent p (features i) (hfeature i) (allowed i)
    · rw [if_neg hij]
      exact featureProjection_orthogonal p (features i) (features j) (hpair i j hij)
        (allowed i) (allowed j)
  unfold combinedProjection
  rw [add_mul, mul_add, mul_add]
  simp_rw [Finset.mul_sum, Finset.sum_mul,
    constantProjection_idempotent,
    constantProjection_featureProjection p _ (hfeature _),
    featureProjection_constantProjection p _ (hfeature _), hcomp]
  simp

@[simp] theorem combinedProjection_one [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    combinedProjection p features allowed 1 = 1 := by
  have hc : constantProjection p 1 = (1 : Ω → ℝ) := by
    funext x
    exact expectation_const p 1
  have hf (i : I) : featureProjection p (features i) (allowed i) 1 = 0 :=
    featureProjection_const p (features i) (hfeature i) (allowed i) 1
  simp [combinedProjection, LinearMap.sum_apply, hc, hf]

/-- Constants are an independent component: the projection preserves mass. -/
theorem combinedProjection_mean [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) (f : Ω → ℝ) :
    expectation p (combinedProjection p features allowed f) = expectation p f := by
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply,
    map_add, map_sum]
  have hc : expectation p (constantProjection p f) = expectation p f :=
    expectation_const p _
  rw [hc]
  simp_rw [featureProjection_mean p _ (hfeature _)]
  simp

/-- The concrete finite feature projection as a bounded operator for Neumann repair. -/
noncomputable def chartProjection (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) : (Ω → ℝ) →L[ℝ] (Ω → ℝ) :=
  (combinedProjection p features allowed).toContinuousLinearMap

@[simp] theorem chartProjection_apply (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (f : Ω → ℝ) (x : Ω) :
    chartProjection p features allowed f x = expectation p f +
      ∑ i, centerAllowed (allowed i) (conditional p (features i) f) (features i x) := by
  simp [chartProjection, combinedProjection]

/-- Idempotence of the bounded operator used by the actual safe-set deletion. -/
theorem chartProjection_idempotent [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    chartProjection p features allowed * chartProjection p features allowed =
      chartProjection p features allowed := by
  ext f x
  exact congrFun (congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
    (combinedProjection_idempotent p features allowed hfeature hpair)) x

/-- A nonnegative weighting controls arbitrary signed tests by their sup norm. -/
theorem expectation_abs_mul_le (p : FiniteDist Ω) (weight f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ weight x) :
    |expectation p (fun x => weight x * f x)| ≤ ‖f‖ * expectation p weight := by
  calc
    _ ≤ ∑ x, |p.weight x * (weight x * f x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p.weight x * weight x * |f x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_mul, abs_of_nonneg (p.nonneg x), abs_of_nonneg (hw x)]
      ring
    _ ≤ ∑ x, p.weight x * weight x * ‖f‖ := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f x)
        (mul_nonneg (p.nonneg x) (hw x))
    _ = ‖f‖ * expectation p weight := by
      rw [← Finset.sum_mul]
      unfold expectation
      dsimp
      ring

/-- The same test bound holds conditionally on each feature value. -/
theorem conditional_abs_mul_le (p : FiniteDist Ω) (feature : Ω → C)
    (weight f : Ω → ℝ) (hw : ∀ x, 0 ≤ weight x) (c : C) :
    |conditional p feature (fun x => weight x * f x) c| ≤
      ‖f‖ * conditional p feature weight c := by
  have he : (fun x => if feature x = c then weight x * f x else (0 : ℝ)) =
      fun x => (if feature x = c then weight x else 0) * f x := by
    funext x
    split_ifs <;> simp
  rw [conditional_apply, conditional_apply, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), he]
  have h := expectation_abs_mul_le p (fun x => if feature x = c then weight x else 0) f
    (fun x => by split_ifs <;> simp [hw])
  calc
    _ ≤ (Fintype.card C : ℝ) * (‖f‖ * expectation p
        (fun x => if feature x = c then weight x else 0)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

omit [Fintype C] in
/-- Centering an allowed-set profile costs at most twice its sup bound. -/
theorem centerAllowed_abs_le (allowed : Finset C) (g : C → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ c ∈ allowed, |g c| ≤ M) (c : C) :
    |centerAllowed allowed g c| ≤ 2 * M := by
  rw [centerAllowed_apply]
  by_cases hc : c ∈ allowed
  · rw [if_pos hc]
    have hcard : 0 < (allowed.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hc⟩)
    have havg : |(∑ a ∈ allowed, g a) / allowed.card| ≤ M := by
      rw [abs_div, abs_of_nonneg hcard.le, div_le_iff₀ hcard]
      calc
        _ ≤ ∑ a ∈ allowed, |g a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ allowed, M := Finset.sum_le_sum (fun a ha => hg a ha)
        _ = _ := by simp [mul_comm]
    exact (abs_sub _ _).trans (by linarith [hg c hc])
  · simp [hc, hM]

/-- The public deletion indicator used in the exact finite probability bounds. -/
noncomputable def badIndicator (safe : Ω → Prop) : Ω → ℝ :=
  fun x => if safe x then 0 else 1

/-- The actual `l∞` deletion norm bound, derived from scalar deletion
probabilities.  With `m` features this is exactly `(2m+1)ε` in V7. -/
theorem chartDeletion_norm (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (safe : Ω → Prop) [DecidablePred safe]
    (ε : ℝ) (hε : 0 ≤ ε)
    (hglobal : expectation p (badIndicator safe) ≤ ε)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ ε) :
    ‖deletion (Ω := Ω) (chartProjection (Ω := Ω) (C := C) (I := I) p features allowed) safe‖ ≤
      (2 * Fintype.card I + 1) * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro x
  have hb : ∀ y, 0 ≤ badIndicator safe y := by
    intro y
    unfold badIndicator
    split_ifs <;> norm_num
  have heq : f - safeMask safe f = fun y => badIndicator safe y * f y := by
    funext y
    simp only [Pi.sub_apply, safeMask_apply, badIndicator]
    split_ifs <;> simp
  have hg : |expectation p (f - safeMask safe f)| ≤ ε * ‖f‖ := by
    rw [heq]
    exact (expectation_abs_mul_le p (badIndicator safe) f hb).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hglobal (norm_nonneg f)])
  have hc (i : I) (c : C) (hca : c ∈ allowed i) :
      |conditional p (features i) (f - safeMask safe f) c| ≤ ε * ‖f‖ := by
    rw [heq]
    exact (conditional_abs_mul_le p (features i) (badIndicator safe) f hb c).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hconditional i c hca) (norm_nonneg f)])
  change |chartProjection p features allowed (f - safeMask safe f) x| ≤ _
  rw [chartProjection_apply]
  calc
    _ ≤ |expectation p (f - safeMask safe f)| +
        |∑ i, centerAllowed (allowed i)
          (conditional p (features i) (f - safeMask safe f)) (features i x)| := abs_add_le _ _
    _ ≤ ε * ‖f‖ + ∑ i, |centerAllowed (allowed i)
        (conditional p (features i) (f - safeMask safe f)) (features i x)| :=
      add_le_add hg (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε * ‖f‖ + ∑ _i : I, 2 * (ε * ‖f‖) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i _
      exact centerAllowed_abs_le (allowed i) _ (ε * ‖f‖)
        (mul_nonneg hε (norm_nonneg _)) (hc i) (features i x)
    _ = _ := by simp; ring

/-- Expectation is monotone for pointwise ordered tests. -/
theorem expectation_mono (p : FiniteDist Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    expectation p f ≤ expectation p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem conditional_mono (p : FiniteDist Ω) (feature : Ω → C)
    {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) (c : C) :
    conditional p feature f c ≤ conditional p feature g c := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply expectation_mono
  intro x
  split_ifs <;> simp [h]

/-- Indicator of a forbidden color in one palette. -/
noncomputable def paletteFailure (allowed : Finset C) (c : C) : ℝ :=
  if c ∈ allowed then 0 else 1

omit [Fintype C] in
@[simp] theorem paletteFailure_nonneg (allowed : Finset C) (c : C) :
    0 ≤ paletteFailure allowed c := by unfold paletteFailure; split_ifs <;> norm_num

/-- Simultaneously enforce nonzero scale (the auxiliary palette) and all
trimmed feature palettes. -/
def legalChart (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C) (x : Ω) : Prop :=
  auxiliary x ∈ auxAllowed ∧ ∀ i, features i x ∈ allowed i

omit [Fintype Ω] [Fintype C] in
/-- The union bound is pointwise before any probability or conditioning. -/
theorem badIndicator_le_palette_sum (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C) (x : Ω) :
    badIndicator (legalChart auxiliary auxAllowed features allowed) x ≤
      paletteFailure auxAllowed (auxiliary x) +
        ∑ i, paletteFailure (allowed i) (features i x) := by
  by_cases hs : legalChart auxiliary auxAllowed features allowed x
  · simp only [badIndicator, if_pos hs]
    exact add_nonneg (paletteFailure_nonneg _ _)
      (Finset.sum_nonneg (fun i _ => paletteFailure_nonneg _ _))
  · simp only [badIndicator, if_neg hs]
    by_cases ha : auxiliary x ∈ auxAllowed
    · have he : ∃ i, features i x ∉ allowed i := by
        simpa only [legalChart, ha, true_and, not_forall] using hs
      obtain ⟨i, hi⟩ := he
      have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        paletteFailure_nonneg (allowed j) (features j x)) (Finset.mem_univ i)
      simpa [paletteFailure, ha, hi] using hsum
    · rw [show paletteFailure auxAllowed (auxiliary x) = 1 by simp [paletteFailure, ha]]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => paletteFailure_nonneg _ _))

/-- Exact uniform probability of a forbidden palette. -/
theorem uniform_palette_failure [Nonempty C] (allowed : Finset C) :
    expectation (FiniteDist.uniform C) (paletteFailure allowed) =
      1 - (allowed.card : ℝ) / Fintype.card C := by
  have heq : paletteFailure allowed =
      (fun _ : C => (1 : ℝ)) - (fun c => if c ∈ allowed then (1 : ℝ) else 0) := by
    funext c
    unfold paletteFailure
    split_ifs <;> simp_all
  rw [heq, map_sub, expectation_const]
  congr 1
  simp only [expectation_apply, FiniteDist.uniform_weight, mul_ite, mul_one, mul_zero,
    ← Finset.sum_filter, Finset.filter_univ_mem]
  simp [div_eq_mul_inv]

/-- Uniform feature laws give the unconditional union deletion budget. -/
theorem legalChart_global_budget [Nonempty C] (p : FiniteDist Ω)
    (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C)
    (haux : p.map auxiliary = FiniteDist.uniform C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    expectation p (badIndicator (legalChart auxiliary auxAllowed features allowed)) ≤
      expectation (FiniteDist.uniform C) (paletteFailure auxAllowed) +
        ∑ i, expectation (FiniteDist.uniform C) (paletteFailure (allowed i)) := by
  have h := expectation_mono p (badIndicator_le_palette_sum auxiliary auxAllowed features allowed)
  have heq : (fun x => paletteFailure auxAllowed (auxiliary x) +
      ∑ i, paletteFailure (allowed i) (features i x)) =
      (fun x => paletteFailure auxAllowed (auxiliary x)) +
        ∑ i, (fun x => paletteFailure (allowed i) (features i x)) := by
    ext x
    simp
  rw [heq, map_add, map_sum] at h
  rw [← expectation_map p auxiliary (paletteFailure auxAllowed), haux] at h
  have hf (i : I) : expectation p (fun x => paletteFailure (allowed i) (features i x)) =
      expectation (FiniteDist.uniform C) (paletteFailure (allowed i)) := by
    rw [← expectation_map p (features i) (paletteFailure (allowed i)), hfeature i]
  simpa only [hf] using h

/-- The same deletion budget remains valid after fixing any allowed feature
value: its own violation disappears and all other violations remain uniform. -/
theorem legalChart_conditional_budget [Nonempty C] (p : FiniteDist Ω)
    (auxiliary : Ω → C) (auxAllowed : Finset C)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (hauxpair : ∀ i, p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (i : I) (c : C) (hc : c ∈ allowed i) :
    conditional p (features i)
      (badIndicator (legalChart auxiliary auxAllowed features allowed)) c ≤
      expectation (FiniteDist.uniform C) (paletteFailure auxAllowed) +
        ∑ j, expectation (FiniteDist.uniform C) (paletteFailure (allowed j)) := by
  have h := conditional_mono p (features i)
    (badIndicator_le_palette_sum auxiliary auxAllowed features allowed) c
  have heq : (fun x => paletteFailure auxAllowed (auxiliary x) +
      ∑ j, paletteFailure (allowed j) (features j x)) =
      (fun x => paletteFailure auxAllowed (auxiliary x)) +
        ∑ j, (fun x => paletteFailure (allowed j) (features j x)) := by
    ext x
    simp
  rw [heq, map_add, map_sum] at h
  have ha := conditional_other p (features i) auxiliary (hauxpair i) (paletteFailure auxAllowed)
  have hj (j : I) : conditional p (features i)
      (fun x => paletteFailure (allowed j) (features j x)) c ≤
      expectation (FiniteDist.uniform C) (paletteFailure (allowed j)) := by
    by_cases hij : i = j
    · subst j
      rw [conditional_same p (features i) (hfeature i)]
      simp only [paletteFailure, if_pos hc]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((FiniteDist.uniform C).nonneg x) (paletteFailure_nonneg _ _))
    · rw [conditional_other p (features i) (features j) (hpair i j hij)]
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      simp only [Pi.add_apply, Finset.sum_apply]
      rw [ha]
      exact add_le_add_right (Finset.sum_le_sum (fun j _ => hj j)) _

/-- A component is unchanged by applying the complete orthogonal projection. -/
theorem featureProjection_combined [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) (f : Ω → ℝ) :
    featureProjection p (features i) (allowed i) (combinedProjection p features allowed f) =
      featureProjection p (features i) (allowed i) f := by
  have hcomp (j : I) : featureProjection p (features i) (allowed i)
      (featureProjection p (features j) (allowed j) f) =
      if i = j then featureProjection p (features i) (allowed i) f else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
    · rw [if_neg hij]
      exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_orthogonal p (features i) (features j) (hpair i j hij)
          (allowed i) (allowed j))
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  have hc : featureProjection p (features i) (allowed i) (constantProjection p f) = 0 :=
    featureProjection_const p (features i) (hfeature i) (allowed i) _
  rw [hc]
  simp only [hcomp, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add]

/-- Summing conditional densities restores the unrestricted density mass. -/
theorem conditional_sum (p : FiniteDist Ω) (feature : Ω → C) (f : Ω → ℝ) :
    ∑ c, conditional p feature f c = (Fintype.card C : ℝ) * expectation p f := by
  simp only [conditional_apply, expectation_apply, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp [mul_ite]

/-- Zero centered component and palette support determine the entire marginal. -/
theorem centerAllowed_zero_profile (allowed : Finset C) (g : C → ℝ)
    (hcenter : centerAllowed allowed g = 0) (hsupport : ∀ c ∉ allowed, g c = 0) (c : C) :
    g c = if c ∈ allowed then (∑ a, g a) / allowed.card else 0 := by
  have hsum : ∑ a ∈ allowed, g a = ∑ a, g a :=
    Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hsupport a ha)
  by_cases hc : c ∈ allowed
  · have h := congrFun hcenter c
    simp only [centerAllowed_apply, if_pos hc, Pi.zero_apply, hsum] at h
    simpa only [if_pos hc] using sub_eq_zero.mp h
  · simp [hc, hsupport c hc]

/-- Safe support forces every forbidden feature marginal to vanish exactly. -/
theorem conditional_outside_zero (p : FiniteDist Ω) (feature : Ω → C)
    (allowed : Finset C) (safe : Ω → Prop) (f : Ω → ℝ)
    (hsupport : ∀ x, ¬ safe x → f x = 0)
    (hallowed : ∀ x, safe x → feature x ∈ allowed) (c : C) (hc : c ∉ allowed) :
    conditional p feature f c = 0 := by
  rw [conditional_apply]
  have heq : (fun x => if feature x = c then f x else (0 : ℝ)) = 0 := by
    funext x
    by_cases hx : feature x = c
    · have hn : ¬ safe x := by intro hs; exact hc (hx ▸ hallowed x hs)
      simp [hx, hsupport x hn]
    · simp [hx]
  rw [heq, map_zero, mul_zero]



/-- Turn a nonnegative mean-one chart density into its actual probability law. -/
noncomputable def densityLaw (p : FiniteDist Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : expectation p w = 1) : FiniteDist Ω where
  weight x := p.weight x * w x
  nonneg x := mul_nonneg (p.nonneg x) (hw x)
  sum_one := hmean

/-- Conditional densities and the probability law's marginal have the exact
uniform-reference conversion factor. -/
theorem densityLaw_marginal [Nonempty C] (p : FiniteDist Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmean : expectation p w = 1)
    (feature : Ω → C) (c : C) :
    ((densityLaw p w hw hmean).map feature).weight c =
      conditional p feature w c / Fintype.card C := by
  rw [FiniteDist.map_weight, conditional_apply]
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_div_cancel_left₀ _ hC]
  simp only [expectation_apply, densityLaw, mul_ite, mul_zero]

end FeatureProjections






section AffineFeatures
variable {F : Type*} [Field F]

/-- A chart stores the base, scale, and shear in that order. -/
abbrev Chart (F : Type*) := F × F × F

/-- The exact protected affine feature at source input `(first, second)`. -/
def feature (first second : F) (chart : Chart F) : F :=
  chart.1 + chart.2.1 * first + chart.2.2 * second

/-- Every feature is a free uniform coordinate jointly with scale and shear. -/
def featureChartEquiv (first second : F) : Chart F ≃ Chart F where
  toFun chart := (feature first second chart, chart.2)
  invFun output := (output.1 - output.2.1 * first - output.2.2 * second, output.2)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    dsimp [feature]
    congr 1
    ring
  right_inv output := by
    rcases output with ⟨color, scale, shear⟩
    dsimp [feature]
    congr 1
    ring

/-- Two features with different first inputs, together with the shear, are
three independent free coordinates. -/
def firstPairChartEquiv (u v u' v' : F) (hfirst : u' - u ≠ 0) : Chart F ≃ Chart F where
  toFun chart := (feature u v chart, feature u' v' chart, chart.2.2)
  invFun output :=
    let scale := (output.2.1 - output.1 - output.2.2 * (v' - v)) / (u' - u)
    (output.1 - scale * u - output.2.2 * v, scale, output.2.2)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring
  right_inv output := by
    rcases output with ⟨color, other, shear⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring

/-- Two features with different second inputs, together with the scale, are
three independent free coordinates. -/
def secondPairChartEquiv (u v u' v' : F) (hsecond : v' - v ≠ 0) : Chart F ≃ Chart F where
  toFun chart := (feature u v chart, feature u' v' chart, chart.2.1)
  invFun output :=
    let shear := (output.2.1 - output.1 - output.2.2 * (u' - u)) / (v' - v)
    (output.1 - output.2.2 * u - shear * v, output.2.2, shear)
  left_inv chart := by
    rcases chart with ⟨base, scale, shear⟩
    simp only [feature, Prod.mk.injEq, true_and]
    constructor <;> field_simp <;> ring
  right_inv output := by
    rcases output with ⟨color, other, scale⟩
    simp only [feature, Prod.mk.injEq, and_true]
    constructor <;> field_simp <;> ring

/-- For any two distinct source inputs, the ordered feature pair can be
completed to an explicit bijection of unrestricted charts. -/
noncomputable def pairChartEquiv (input other : F × F) (hne : input ≠ other) :
    Chart F ≃ Chart F := by
  classical
  by_cases hfirst : other.1 - input.1 = 0
  · have hsecond : other.2 - input.2 ≠ 0 := by
      intro h
      apply hne
      exact Prod.ext (sub_eq_zero.mp hfirst).symm (sub_eq_zero.mp h).symm
    exact secondPairChartEquiv input.1 input.2 other.1 other.2 hsecond
  · exact firstPairChartEquiv input.1 input.2 other.1 other.2 hfirst

@[simp] theorem pairChartEquiv_first (input other : F × F) (hne : input ≠ other)
    (chart : Chart F) :
    (pairChartEquiv input other hne chart).1 = feature input.1 input.2 chart := by
  classical
  unfold pairChartEquiv
  split_ifs <;> rfl

@[simp] theorem pairChartEquiv_second (input other : F × F) (hne : input ≠ other)
    (chart : Chart F) :
    (pairChartEquiv input other hne chart).2.1 = feature other.1 other.2 chart := by
  classical
  unfold pairChartEquiv
  split_ifs <;> rfl

end AffineFeatures

section UniformFeatures
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

/-- Projecting the first two unrestricted chart coordinates gives independent
uniform colors. -/
theorem uniform_chart_first_two :
    (FiniteDist.uniform (Chart F)).map (fun chart => (chart.1, chart.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  ext colors
  rcases colors with ⟨first, second⟩
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, FiniteDist.prod_weight]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul]
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [ite_and]
  field_simp

/-- Each affine chart feature is independent uniform with the scale. -/
theorem feature_scale_uniform (first second : F) :
    (FiniteDist.uniform (Chart F)).map (fun chart => (feature first second chart, chart.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  have h := FiniteDist.uniform_map_equiv (featureChartEquiv first second)
  have hh := congrArg (fun p : FiniteDist (Chart F) =>
    p.map (fun chart => (chart.1, chart.2.1))) h
  rw [FiniteDist.map_map, uniform_chart_first_two] at hh
  exact hh

/-- The exact pairwise-independence assertion in V7's boundary-chart proof,
proved from explicit invertible affine coordinate changes. -/
theorem feature_pair_uniform (input other : F × F) (hne : input ≠ other) :
    (FiniteDist.uniform (Chart F)).map
      (fun chart => (feature input.1 input.2 chart, feature other.1 other.2 chart)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := by
  have h := FiniteDist.uniform_map_equiv (pairChartEquiv input other hne)
  have hh := congrArg (fun p : FiniteDist (Chart F) =>
    p.map (fun chart => (chart.1, chart.2.1))) h
  rw [FiniteDist.map_map, uniform_chart_first_two] at hh
  simpa only [pairChartEquiv_first, pairChartEquiv_second] using hh

 theorem prod_map_first {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteDist α) (q : FiniteDist β) : (p.prod q).map Prod.fst = p := by
  ext a
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, q.sum_one]

 theorem prod_map_second {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteDist α) (q : FiniteDist β) : (p.prod q).map Prod.snd = q := by
  ext b
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  simp [← Finset.sum_mul, p.sum_one]

/-- Every unrestricted affine feature is exactly uniform. -/
theorem feature_uniform (first second : F) :
    (FiniteDist.uniform (Chart F)).map (feature first second) = FiniteDist.uniform F := by
  have h := congrArg (fun p : FiniteDist (F × F) => p.map Prod.fst)
    (feature_scale_uniform first second)
  rw [FiniteDist.map_map, prod_map_first] at h
  exact h

/-- The unrestricted scale is uniform and remains a public chart coordinate. -/
theorem scale_uniform :
    (FiniteDist.uniform (Chart F)).map (fun chart => chart.2.1) = FiniteDist.uniform F := by
  have h := congrArg (fun p : FiniteDist (F × F) => p.map Prod.snd)
    (feature_scale_uniform (0 : F) 0)
  rw [FiniteDist.map_map, prod_map_second] at h
  exact h

/-- The scale-zero probability contributes exactly one deleted field value. -/
theorem nonzero_palette_failure :
    expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase (0 : F))) =
      (Fintype.card F : ℝ)⁻¹ := by
  simp [expectation_apply, FiniteDist.uniform_weight, paletteFailure, mul_ite, ite_not]

variable {I : Type*} [Fintype I]

/-- The actual deleted-color union budget for unrestricted affine charts. -/
noncomputable def affineDeletionBudget (allowed : I → Finset F) : ℝ :=
  (Fintype.card F : ℝ)⁻¹ + ∑ i, (1 - (allowed i).card / (Fintype.card F : ℝ))



end UniformFeatures


end BoundaryCalibration
end AFT

end

section




/-!
# The isolated mark in the positive boundary chart

The spike is a normalized restriction of the genuine unrestricted chart law
onto the surviving marked fiber.  Its positive mass and marginal bounds follow
from uniform pairwise-independent features and the public deletion budget.
-/
namespace AFT
namespace BoundaryCalibration

open scoped BigOperators Classical

section RestrictedFiber
variable {Ω C J : Type*} [Fintype Ω] [Fintype C] [Nonempty C] [Fintype J]

/-- An event as a real-valued chart density. -/
noncomputable def eventIndicator (event : Ω → Prop) : Ω → ℝ :=
  fun x => if event x then 1 else 0

omit [Fintype Ω] in
@[simp] theorem eventIndicator_nonneg (event : Ω → Prop) (x : Ω) :
    0 ≤ eventIndicator event x := by unfold eventIndicator; split_ifs <;> norm_num

/-- Unrestricted probability of a finite chart event. -/
noncomputable def eventMass (p : FiniteDist Ω) (event : Ω → Prop) : ℝ :=
  expectation p (eventIndicator event)

theorem eventMass_nonneg (p : FiniteDist Ω) (event : Ω → Prop) :
    0 ≤ eventMass p event :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (eventIndicator_nonneg event x))

/-- A literal conditioning density relative to the unrestricted chart law. -/
noncomputable def restrictedDensity (p : FiniteDist Ω) (event : Ω → Prop) : Ω → ℝ :=
  fun x => eventIndicator event x / eventMass p event

theorem restrictedDensity_nonneg (p : FiniteDist Ω) (event : Ω → Prop) (x : Ω) :
    0 ≤ restrictedDensity p event x :=
  div_nonneg (eventIndicator_nonneg event x) (eventMass_nonneg p event)

theorem restrictedDensity_mean (p : FiniteDist Ω) (event : Ω → Prop)
    (hpos : 0 < eventMass p event) : expectation p (restrictedDensity p event) = 1 := by
  simp only [expectation_apply, restrictedDensity, ← mul_div_assoc, ← Finset.sum_div]
  exact div_self hpos.ne'











end RestrictedFiber
section SpikeRepair
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Nonempty C] [Fintype I]

/-- The complete projection fixes each of its feature components. -/
theorem combinedProjection_feature (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) (f : Ω → ℝ) :
    combinedProjection p features allowed (featureProjection p (features i) (allowed i) f) =
      featureProjection p (features i) (allowed i) f := by
  have hcomp (j : I) : featureProjection p (features j) (allowed j)
      (featureProjection p (features i) (allowed i) f) =
      if j = i then featureProjection p (features i) (allowed i) f else 0 := by
    by_cases hij : j = i
    · subst j
      simpa using congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
    · rw [if_neg hij]
      exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L f)
        (featureProjection_orthogonal p (features j) (features i) (hpair j i hij)
          (allowed j) (allowed i))
  simp only [combinedProjection, LinearMap.add_apply, LinearMap.sum_apply]
  have hc : constantProjection p (featureProjection p (features i) (allowed i) f) = 0 := by
    funext x
    exact featureProjection_mean p (features i) (hfeature i) (allowed i) f
  rw [hc]
  simp only [hcomp, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add]















/-- A zero feature component, palette support and the total density mass
already determine the complete conditional marginal. -/
theorem component_zero_marginal (p : FiniteDist Ω) (feature : Ω → C)
    (hfeature : p.map feature = FiniteDist.uniform C) (allowed : Finset C) (f : Ω → ℝ)
    (hcomponent : featureProjection p feature allowed f = 0)
    (hsupport : ∀ c ∉ allowed, conditional p feature f c = 0) (c : C) :
    conditional p feature f c =
      if c ∈ allowed then (Fintype.card C : ℝ) * expectation p f / allowed.card else 0 := by
  have hc := congrArg (conditional p feature) hcomponent
  change conditional p feature (fun x => centerAllowed allowed (conditional p feature f)
    (feature x)) = conditional p feature 0 at hc
  rw [conditional_same p feature hfeature, map_zero] at hc
  rw [centerAllowed_zero_profile allowed _ hc hsupport c, conditional_sum]



end SpikeRepair
section AffineMarkedChart
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]







end AffineMarkedChart
end BoundaryCalibration
end AFT

end

section









namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.activation
end AFT.GaussianSource.activation
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.legs
end AFT.Parameters.legs
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryCalibrationEnvelope
end AFT.primaryCalibrationEnvelope
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope




/-!
# Actual protected-input charts at the V7 parameter sizes
-/

namespace AFT.BoundaryCalibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section

def protectedInputs (cutoff modulus : ℕ) :
    (GaussianSource.Window cutoff × GaussianSource.Window cutoff) → ZMod modulus × ZMod modulus :=
  fun input => ((input.1 : ℤ), (input.2 : ℤ))

theorem window_cast_injective (cutoff modulus : ℕ) (hsize : 2 * cutoff < modulus) :
    Function.Injective (fun value : GaussianSource.Window cutoff => ((value : ℤ) : ZMod modulus)) := by
  intro a b hab
  have hd : (modulus : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab
  obtain ⟨ha0, ha1⟩ := Finset.mem_Icc.mp a.property
  obtain ⟨hb0, hb1⟩ := Finset.mem_Icc.mp b.property
  have hdiff : |(b : ℤ) - (a : ℤ)| < (modulus : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have habs : ((b : ℤ) - (a : ℤ)).natAbs < (modulus : ℤ).natAbs := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs]
    simpa only [Int.abs_natCast] using hdiff
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habs
  apply Subtype.ext
  omega

theorem protectedInputs_injective (cutoff modulus : ℕ) (hsize : 2 * cutoff < modulus) :
    Function.Injective (protectedInputs cutoff modulus) := by
  intro a b hab
  apply Prod.ext
  · exact window_cast_injective cutoff modulus hsize (congrArg Prod.fst hab)
  · exact window_cast_injective cutoff modulus hsize (congrArg Prod.snd hab)

theorem protectedInputs_card (cutoff : ℕ) :
    Fintype.card (GaussianSource.Window cutoff × GaussianSource.Window cutoff) = (2 * cutoff + 1) ^ 2 := by
  have hc : Fintype.card (GaussianSource.Window cutoff) = 2 * cutoff + 1 := by
    simp only [GaussianSource.Window, Fintype.card_coe, Int.card_Icc]
    omega
  rw [Fintype.card_prod, hc, pow_two]

def fieldPalette (modulus : ℕ) [NeZero modulus] (boundary shift : ℤ) : Finset (ZMod modulus) :=
  (TrimmedSlice.paletteSlice modulus boundary shift).map (ZMod.finEquiv modulus).toEquiv.toEmbedding

theorem fieldPalette_card (modulus : ℕ) [NeZero modulus] (boundary shift : ℤ) (hb : 0 ≤ boundary) :
    (fieldPalette modulus boundary shift).card = ((modulus : ℤ) - 2 * boundary - |shift|).toNat := by
  rw [fieldPalette, Finset.card_map, TrimmedSlice.paletteSlice_card modulus boundary shift hb]

def protectedPalettes (cutoff modulus : ℕ) [NeZero modulus] (boundary baseline : ℤ) :
    (GaussianSource.Window cutoff × GaussianSource.Window cutoff) → Finset (ZMod modulus) :=
  fun input => fieldPalette modulus boundary (baseline - (input.2 : ℤ))

theorem affineDeletionBudget_le {F I : Type*} [Fintype F] [Fintype I]
    (allowed : I → Finset F) (deleted : ℝ) (hcard : 0 < Fintype.card F)
    (hdeleted : ∀ i, (Fintype.card F : ℝ) - (allowed i).card ≤ deleted) :
    affineDeletionBudget allowed ≤
      (1 + (Fintype.card I : ℝ) * deleted) / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast hcard
  have hsum : (∑ i : I, (1 - (allowed i).card / (Fintype.card F : ℝ))) ≤
      (Fintype.card I : ℝ) * (deleted / (Fintype.card F : ℝ)) := by
    calc
      _ ≤ ∑ _i : I, deleted / (Fintype.card F : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [le_div_iff₀ hq]
        have hh := hdeleted i
        field_simp
        linarith
      _ = _ := by simp
  unfold affineDeletionBudget
  have heq : (1 + (Fintype.card I : ℝ) * deleted) / (Fintype.card F : ℝ) =
      (Fintype.card F : ℝ)⁻¹ + (Fintype.card I : ℝ) * (deleted / (Fintype.card F : ℝ)) := by ring
  rw [heq]
  exact add_le_add le_rfl hsum

theorem protectedPalette_budget (cutoff modulus : ℕ) [NeZero modulus]
    (boundary baseline shiftBound : ℤ) (hb : 0 ≤ boundary) (hs : |baseline| ≤ shiftBound)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    affineDeletionBudget (protectedPalettes cutoff modulus boundary baseline) ≤
      (1 + ((2 * cutoff + 1 : ℕ) : ℝ) ^ 2 *
        (2 * (boundary : ℝ) + shiftBound + cutoff)) / modulus := by
  have hq : 0 < modulus := Nat.pos_of_ne_zero (NeZero.ne modulus)
  have hbound (input : GaussianSource.Window cutoff × GaussianSource.Window cutoff) :
      |baseline - (input.2 : ℤ)| ≤ shiftBound + cutoff := by
    have ha : |(input.2 : ℤ)| ≤ cutoff := abs_le.mpr (Finset.mem_Icc.mp input.2.property)
    exact (abs_sub _ _).trans (add_le_add hs ha)
  have hbudget := affineDeletionBudget_le
    (protectedPalettes cutoff modulus boundary baseline)
    (2 * (boundary : ℝ) + shiftBound + cutoff) (by simpa using hq)
    (by
      intro input
      rw [protectedPalettes, fieldPalette_card modulus boundary _ hb, ZMod.card]
      have hi : 0 ≤ (modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)| := by
        have hh := hbound input
        omega
      have heq : (((modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)|).toNat : ℤ) =
          (modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)| := Int.toNat_of_nonneg hi
      have hh : (modulus : ℤ) - ((modulus : ℤ) - 2 * boundary - |baseline - (input.2 : ℤ)|).toNat ≤
          2 * boundary + shiftBound + cutoff := by rw [heq]; have := hbound input; omega
      exact_mod_cast hh)
  simpa only [ZMod.card, protectedInputs_card, Nat.cast_pow] using hbudget

end

end AFT.BoundaryCalibration

namespace AFT.BoundaryCalibration

open Filter
open scoped Topology



instance v7ModulusNeZero (parameter : ℕ) : NeZero (Parameters.modulus parameter) :=
  ⟨Nat.ne_of_gt (Parameters.modulus_prime parameter).pos⟩

instance v7ModulusPrime (parameter : ℕ) : Fact (Parameters.modulus parameter).Prime :=
  ⟨Parameters.modulus_prime parameter⟩





end AFT.BoundaryCalibration

namespace AFT.BoundaryCalibration

open Filter
open scoped Topology

noncomputable local instance _root_.AFT.BoundaryCalibration.instDecidableEqZModModulus (parameter : ℕ) : DecidableEq (ZMod (Parameters.modulus parameter)) := Classical.decEq _







end AFT.BoundaryCalibration

end

section




/-! # A computed common denominator with polynomial binary height -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Index : Type*} [Fintype Index]

def commonDenominator (values : Index → ℚ) : ℕ := ∏ index,(values index).den

def commonNumerator (values : Index → ℚ) (index : Index) : ℤ :=
  (values index).num*(commonDenominator values/(values index).den : ℕ)













end AFT.RationalNumerics

end

section






/-! # Executable linear iteration and stability in primary activity -/
namespace AFT.RationalNumerics
open scoped BigOperators

def matrixApply {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (profile : Color → ℚ) (output : Color) : ℚ :=
  ∑ input,matrix output input*profile input

/-- The same right-hand side and stored matrix are used at every step. -/
def linearIteration {Color : Type*} [Fintype Color]
    (matrix : Color → Color → ℚ) (rhs : Color → ℚ) : ℕ → Color → ℚ
  | 0 => 0
  | steps+1 => rhs-matrixApply matrix (linearIteration matrix rhs steps)





noncomputable section

def realMatrixOperator {Color : Type*} [Fintype Color] (matrix : Color → Color → ℚ) :
    Module.End ℝ (Color → ℝ) where
  toFun profile output := ∑ input,(matrix output input : ℝ)*profile input
  map_add' first second := by
    funext output
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' scalar profile := by
    funext output
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    ring

def realLinearIteration {Color : Type*}
    (operator : Module.End ℝ (Color → ℝ)) (rhs : Color → ℝ) : ℕ → Color → ℝ
  | 0 => 0
  | steps+1 => rhs-operator (realLinearIteration operator rhs steps)







end
end AFT.RationalNumerics

end

section






/-! # Common-denominator iteration with linear operand bit growth -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Color : Type*} [Fintype Color]

def integerLinearIteration (denominator : ℕ) (matrix : Color → Color → ℤ)
    (rhs : Color → ℤ) : ℕ → Color → ℤ
  | 0 => 0
  | steps+1 => fun output => rhs output*(denominator : ℤ)^steps-
      ∑ input,matrix output input*integerLinearIteration denominator matrix rhs steps input





def iterationHeightSlope (colors coefficientBits denominatorBits : ℕ) : ℕ :=
  coefficientBits+denominatorBits+colors+1





end AFT.RationalNumerics

end

section















namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.cachedLinearIteration
end AFT.RationalNumerics.cachedLinearIteration
namespace AFT.RationalNumerics.cachedLinearIteration.match_1
end AFT.RationalNumerics.cachedLinearIteration.match_1
namespace AFT.RationalNumerics.cachedMatrix
end AFT.RationalNumerics.cachedMatrix
namespace AFT.RationalNumerics.cachedMatrixApply
end AFT.RationalNumerics.cachedMatrixApply
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualCachedInverseProgram
end AFT.V7Calibration.actualCachedInverseProgram
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean




/-! # Rational finite chart projection and a cached Neumann program

All entries of the unrestricted uniform chart projection are rational.
The program stores its deletion matrix and complete iterate vectors.
-/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

def chartExpectationProgram (charts : ℕ) (value : Fin charts → ℚ) : ℚ :=
  (∑ chart,value chart)/(charts : ℚ)

def chartConditionalProgram (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) : ℚ :=
  (colors : ℚ)*chartExpectationProgram charts (fun chart => if feature chart=color then value chart else 0)

def chartFeatureProgram (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  if feature chart∈allowed then
    chartConditionalProgram charts colors feature value (feature chart)-
      (∑color∈allowed,chartConditionalProgram charts colors feature value color)/(allowed.card : ℚ)
  else 0

def chartProjectionProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  chartExpectationProgram charts value+∑index,chartFeatureProgram charts colors (feature index) (allowed index) value chart

def chartDeletionProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (value : Fin charts → ℚ) (chart : Fin charts) : ℚ :=
  chartProjectionProgram charts colors features feature allowed (fun input => if input∈safe then 0 else value input) chart

def chartDeletionMatrixProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) : ℚ :=
  -chartDeletionProgram charts colors features feature allowed safe (fun point => if point=input then 1 else 0) output



noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (charts colors features : ℕ) [NeZero charts]

 

 

 

 

 

 

 

end
end AFT.BoundaryCalibration

end

section










/-! # Executable positive normalization and finite fair-bit sampling -/
namespace AFT.RationalNumerics
open scoped BigOperators

def positivePartProgram {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) : ℚ := max 0 (raw index)
def positiveNormalizerProgram {count : ℕ} (raw : Fin (count+1) → ℚ) : ℚ := ∑index,positivePartProgram raw index

def positiveWeightProgram {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) : ℚ :=
  if positiveNormalizerProgram raw=0 then (if index=0 then 1 else 0)
  else positivePartProgram raw index/positiveNormalizerProgram raw

theorem positiveNormalizerProgram_nonneg {count : ℕ} (raw : Fin (count+1) → ℚ) : 0≤positiveNormalizerProgram raw :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

theorem positiveWeightProgram_nonneg {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) :
    0≤positiveWeightProgram raw index := by
  unfold positiveWeightProgram
  split_ifs
  · exact zero_le_one
  · exact le_refl _
  · exact div_nonneg (le_max_left _ _) (positiveNormalizerProgram_nonneg raw)

theorem positiveWeightProgram_sum {count : ℕ} (raw : Fin (count+1) → ℚ) :
    ∑index,positiveWeightProgram raw index=1 := by
  unfold positiveWeightProgram
  split_ifs with hz
  · simp
  · rw [←Finset.sum_div]
    exact div_self hz

def positiveNormalizeDraw {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) : Fin (count+1) :=
  RationalFiniteQuantization.draw (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (bits+(count+1)+1) word

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def positiveProgramLaw {count : ℕ} (raw : Fin (count+1) → ℚ) : FiniteDist (Fin (count+1)) where
  weight index := (positiveWeightProgram raw index : ℝ)
  nonneg index := by exact_mod_cast positiveWeightProgram_nonneg raw index
  sum_one := by exact_mod_cast positiveWeightProgram_sum raw





 

 

end
end AFT.RationalNumerics

end

section














namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration




/-! # Rational marked-chart density from the explicit protected repair -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

def chartSpikeProgram (charts : ℕ) (survivingFiber : Finset (Fin charts)) (point : Fin charts) : ℚ :=
  if point∈survivingFiber then (charts : ℚ)/survivingFiber.card else 0

def chartSpikeDefectProgram (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (point : Fin charts) : ℚ :=
  atom*∑ index,if index=marked then 0 else chartFeatureProgram charts colors (feature index) (allowed index) spike point





noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable (charts colors features : ℕ) [NeZero charts]

 

 

 

 

end
end AFT.BoundaryCalibration

end

section














namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity




/-! # Explicit array indexing of the actual affine F³ chart and protected inputs -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

/-- The order is base, scale, shear, as in the physical affine chart. -/
def finiteChartEquiv (modulus : ℕ) [NeZero modulus] :
    Fin (modulus*(modulus*modulus)) ≃ Chart (ZMod modulus) :=
  finProdFinEquiv.symm.trans ((ZMod.finEquiv modulus).toEquiv.prodCongr
    (finProdFinEquiv.symm.trans ((ZMod.finEquiv modulus).toEquiv.prodCongr (ZMod.finEquiv modulus).toEquiv)))

def finiteInputEquiv (cutoff : ℕ) :
    Fin ((2*cutoff+1)*(2*cutoff+1)) ≃ GaussianSource.Window cutoff × GaussianSource.Window cutoff :=
  finProdFinEquiv.symm.trans ((FiniteConvolutionProgram.windowIndexEquiv cutoff).prodCongr
    (FiniteConvolutionProgram.windowIndexEquiv cutoff))

def finiteAffineFeature (modulus : ℕ) [NeZero modulus] [Fact modulus.Prime] (first second : ZMod modulus)
    (chart : Fin (modulus*(modulus*modulus))) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (feature first second (finiteChartEquiv modulus chart))

def finiteAffineScale (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (finiteChartEquiv modulus chart).2.1

def finiteProtectedFeatures (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) : Fin (modulus*(modulus*modulus)) → Fin modulus :=
  finiteAffineFeature modulus ((finiteInputEquiv cutoff index).1 : ℤ) ((finiteInputEquiv cutoff index).2 : ℤ)

def finiteProtectedPalettes (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) : Finset (Fin modulus) :=
  Finset.univ.filter fun color =>
    boundary ≤ (color.val : ℤ) ∧ (color.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
      boundary ≤ (modulus : ℤ) - 1 + (baseline - ((finiteInputEquiv cutoff index).2 : ℤ)) - color.val ∧
      (modulus : ℤ) - 1 + (baseline - ((finiteInputEquiv cutoff index).2 : ℤ)) - color.val ≤
        (modulus : ℤ) - 1 - boundary



noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable (modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]

 

 

 

 

 

end
end AFT.BoundaryCalibration

end

section













namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity



/-! # Positive marked-chart laws on the explicitly indexed array -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

def finiteMarkedSafe {charts colors features : ℕ} [NeZero colors]
    (feature : Fin features → Fin charts → Fin colors) (auxiliary : Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) : Finset (Fin charts) :=
  Finset.univ.filter (fun x => auxiliary x≠0 ∧ ∀ i, feature i x∈allowed i)



noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 

end
end AFT.BoundaryCalibration

end

section
















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity
namespace AFT.BoundaryCalibration.finiteMarkedFiber
end AFT.BoundaryCalibration.finiteMarkedFiber
namespace AFT.BoundaryCalibration.finiteMarkedSafe
end AFT.BoundaryCalibration.finiteMarkedSafe
namespace AFT.BoundaryCalibration.finiteProtectedAtom
end AFT.BoundaryCalibration.finiteProtectedAtom




/-! # The executable F³ chart sampler at the actual V7 parameters -/
namespace AFT.BoundaryCalibration
open V7Calibration Filter
open scoped BigOperators

/-- Both parameters are produced by finite integer programs. -/
def chartProgramModulus (n : ℕ) : ℕ := (ParameterProgram.modulus n).value


instance chartProgramModulusNeZero (n : ℕ) : NeZero (chartProgramModulus n) :=
  ⟨by rw [chartProgramModulus,ParameterProgram.modulus_value];exact (Parameters.modulus_prime n).ne_zero⟩
instance chartProgramModulusPrime (n : ℕ) : Fact (chartProgramModulus n).Prime :=
  ⟨by rw [chartProgramModulus,ParameterProgram.modulus_value];exact Parameters.modulus_prime n⟩



noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000





 

end
end AFT.BoundaryCalibration

end

section















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.chartAtom
end AFT.BoundaryCalibration.chartAtom
namespace AFT.BoundaryCalibration.chartPairOutput
end AFT.BoundaryCalibration.chartPairOutput
namespace AFT.BoundaryCalibration.fieldPalette
end AFT.BoundaryCalibration.fieldPalette
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart



/-! # The true primary-dependent public sign branch -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance conditionalPairFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The baseline interval of the pair sum, before its actual body blur. -/
def conditionalBaselineStart (modulus width : ℕ) (mark : Fin modulus) (coin : Bool) : ℤ :=
  publicAnchorStart modulus width mark coin + mark.val - ((modulus : ℤ) - 1)



def conditionalPairStart (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) : ℤ :=
  conditionalBaselineStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) mark sample.2 +
    bodyShift cutoffScale parameter sample.1











end
end AFT.V7Calibration

end

section















/-! # Executable actual trimmed endpoint pairs, conditional on the shared source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- The exact integer pair sum fixes the only possible anchor offset. -/
def averagedPairProgram (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : ℕ) : ℚ :=
  let shift : ℤ := (first : ℤ)+second-((modulus : ℤ)-1)
  intervalProbabilityProgram start width (shift+source)*sliceProbabilityProgram modulus boundary shift first







noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
local instance conditionalPairProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _













end
end AFT.V7Calibration

end

section







/-! # Tensor Hilbert operator bounds for arbitrary joint finite kernels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

/-- Apply finite local linear channels to all coordinates of one arbitrary
joint kernel. No product decomposition of that kernel is used. -/
def apply : (count : ℕ) →
    (Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) →
    ((Fin count → Input) → ℝ) → (Fin count → Output) → ℝ
  | 0, _, kernel, _ => kernel Fin.elim0
  | count + 1, channel, kernel, output =>
      channel 0 (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)

omit [Fintype Input] [Fintype Output] in
@[simp] theorem apply_cons (count : ℕ)
    (channel : Fin (count + 1) → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin (count + 1) → Input) → ℝ) (first : Output) (rest : Fin count → Output) :
    apply (count + 1) channel kernel (Fin.cons first rest) =
      channel 0 (fun input => apply count (fun index => channel index.succ)
        (fun tail => kernel (Fin.cons input tail)) rest) first := by
  simp only [apply, Fin.cons_zero, Fin.cons_succ]

 theorem expectation_mono {Sample : Type*} [Fintype Sample]
    (law : FiniteDist Sample) {first second : Sample → ℝ} (h : ∀ point, first point ≤ second point) :
    law.expectation first ≤ law.expectation second :=
  Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (h point) (law.nonneg point)

/-- The Hilbert norm of the complete tensor channel is the product of its
local bounds. This applies to every joint kernel, including nonseparable
kernels with arbitrary dependencies among the distinguished coordinates. -/
theorem energy_le (count : ℕ) (input : Fin count → FiniteDist Input)
    (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (apply count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel Fin.elim0 := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [apply, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.independent (fun index : Fin count => input index.succ)
    let tailOutput := FiniteDist.independent (fun index : Fin count => output index.succ)
    let tailValue := fun first rest => apply count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input) : tailOutput.l2Sq (tailValue first) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => input index.succ) (fun index => output index.succ)
        (fun index => channel index.succ) (fun index => bound index.succ)
        (fun index => hchannel index.succ) _
    have hsplit : (FiniteDist.independent output).l2Sq (apply (count + 1) channel kernel) =
        tailOutput.expectation (fun rest => (output 0).l2Sq (channel 0 (fun first => tailValue first rest))) := by
      unfold FiniteDist.l2Sq
      rw [FiniteConcentration.expectation_cons]
      simp only [apply_cons]
      exact FiniteDist.expectation_comm _ _ _
    rw [hsplit]
    calc
      _ ≤ tailOutput.expectation (fun rest => bound 0 ^ 2 * (input 0).l2Sq (fun first => tailValue first rest)) :=
        expectation_mono tailOutput (fun rest => hchannel 0 _)
      _ = bound 0 ^ 2 * (input 0).expectation (fun first => tailOutput.l2Sq (tailValue first)) := by
        rw [FiniteDist.expectation_const_mul]
        congr 1
        exact FiniteDist.expectation_comm _ _ _
      _ ≤ bound 0 ^ 2 * (input 0).expectation (fun first =>
          (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest))) :=
        mul_le_mul_of_nonneg_left (expectation_mono (input 0) htail) (sq_nonneg _)
      _ = _ := by
        rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ]
        rw [mul_assoc]
        congr 2
        unfold FiniteDist.l2Sq
        exact (FiniteConcentration.expectation_cons count input (fun word => kernel word ^ 2)).symm








end
end AFT.TensorChannel

end

section





/-! # Exact canonical projection before finite local Hilbert channels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]

omit [Fintype Output] in
/-- Orthogonal centering with respect to the actual input law. -/
def center (law : FiniteDist Input) : (Input → ℝ) →ₗ[ℝ] (Input → ℝ) where
  toFun kernel := fun point => kernel point - law.expectation kernel
  map_add' first second := by
    funext point
    change first point + second point - law.expectation (fun x => first x + second x) = _
    rw [FiniteDist.expectation_add]
    simp only [Pi.add_apply]
    ring
  map_smul' scalar kernel := by
    funext point
    change scalar * kernel point - law.expectation (fun x => scalar * kernel x) = _
    rw [FiniteDist.expectation_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype Output] in
@[simp] theorem center_apply (law : FiniteDist Input) (kernel : Input → ℝ) (point : Input) :
    center law kernel point = kernel point - law.expectation kernel := rfl



omit [Fintype Output] in
/-- Exact variance identity gives contraction, including laws with zeros. -/
theorem center_energy (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) = law.l2Sq kernel - law.expectation kernel ^ 2 := by
  let mean := law.expectation kernel
  have hpoint (point : Input) : law.weight point * (kernel point - mean) ^ 2 =
      law.weight point * kernel point ^ 2 - 2 * mean * (law.weight point * kernel point) +
        law.weight point * mean ^ 2 := by ring
  change (∑ point, law.weight point * (kernel point - mean) ^ 2) = _
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, law.sum_one, one_mul]
  change law.l2Sq kernel - 2 * mean * mean + mean ^ 2 = law.l2Sq kernel - mean ^ 2
  ring

omit [Fintype Output] in
theorem center_energy_le (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) ≤ law.l2Sq kernel := by
  rw [center_energy]
  exact sub_le_self _ (sq_nonneg _)



omit [Fintype Input] [Fintype Output] in
theorem apply_add (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (first second : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (first + second) output = apply count channel first output + apply count channel second output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      ((fun rest => first (Fin.cons input rest)) + (fun rest => second (Fin.cons input rest)))
      (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 ((fun input => apply count (fun index => channel index.succ)
      (fun rest => first (Fin.cons input rest)) (fun index => output index.succ)) +
      (fun input => apply count (fun index => channel index.succ)
        (fun rest => second (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_add]
    rfl

omit [Fintype Input] [Fintype Output] in
theorem apply_smul (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (scalar : ℝ) (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (scalar • kernel) output = scalar * apply count channel kernel output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      (scalar • (fun rest => kernel (Fin.cons input rest))) (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 (scalar • (fun input => apply count (fun index => channel index.succ)
      (fun rest => kernel (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_smul]
    rfl

omit [Fintype Input] [Fintype Output] in
/-- The full tensor operation is itself a literal linear map. -/
def applyLinear (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) :
    ((Fin count → Input) → ℝ) →ₗ[ℝ] ((Fin count → Output) → ℝ) where
  toFun := apply count channel
  map_add' first second := funext (apply_add count channel first second)
  map_smul' scalar kernel := funext (apply_smul count channel scalar kernel)







end
end AFT.TensorChannel

end

section









namespace AFT
end AFT
namespace AFT.BlockProducts
end AFT.BlockProducts



/-! # Complete signed tails commute with the actual conditioning mixture -/

namespace AFT.HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color Source : Type*} [Fintype Slot] [Fintype Color] [Fintype Source]

omit [Fintype Slot] [Fintype Color] in
theorem expectation_square_le (source : FiniteDist Source) (value : Source → ℝ) :
    source.expectation value ^ 2 ≤ source.l2Sq value := by
  have h := CanonicalMoments.expectation_mul_sq_le source value (fun _ => 1)
  simpa only [mul_one, one_pow, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.sum_one] using h















end AFT.HistogramNormalization

end

section








namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # The complete signed tail of actual marked blocks and their complement -/

namespace AFT.BlockProducts

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

variable {Index Color TaggedSlot : Type*} [Fintype Index] [Fintype Color] [Fintype TaggedSlot]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

local instance _root_.AFT.BlockProducts.instDecidableEqSum_aFT {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance _root_.AFT.BlockProducts.instDecidableEqSigma_aFT : DecidableEq (Sigma Slots) := Classical.decEq _

/-- Actual signed mass: one arbitrary joint tagged output and every remaining
independent physical block. Dependence within the tagged outputs is retained. -/
def taggedBlockMass (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : (TaggedSlot ⊕ Sigma Slots) → Color) : ℝ :=
  tagged (word ∘ Sum.inl) * blockMass Slots law (word ∘ Sum.inr)



/-- The finite marked-coefficient budget computed from the actual signed mass. -/
def taggedCoefficientEnergy (reference : FiniteDist Color) (tagged : (TaggedSlot → Color) → ℝ)
    (population : ℕ) (radius : ℝ) : ℝ :=
  (Fintype.card TaggedSlot + 1 : ℕ) * ∑ degree ∈ Finset.range (Fintype.card TaggedSlot + 1),
    (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy
      (TensorFock.normalizedTensor population radius
        (LocalTensors.degreeTensor (fun _ : TaggedSlot => reference) tagged) degree)



/-- The three explicit local coefficient conditions of the independent-block
estimate, at its doubled radius. -/
def CubicBlockConditions (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (population capacity : ℕ) (radius : ℝ) : Prop :=
  (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word)
      (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
        (radius / Real.sqrt population) index word)).card ≤ capacity ∧
  (∑ index, ∑ color, (Real.sqrt 2 * normalizedLinear Slots reference law
      (radius / Real.sqrt population) index color) ^ 2) ≤ 1 / 8 ∧
  (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
            (radius / Real.sqrt population) index word) index)) ≤ 1 / 2



end

end AFT.BlockProducts

end

section










/-! # The actual finite Fock coefficients form one linear Hilbert channel -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
local instance localCoefficientLinearFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Actual finite tensor symmetrization is a linear operation. -/
def symmetrizeLinear : BlockFock.Tensor Slot Color →ₗ[ℝ] BlockFock.Tensor Slot Color where
  toFun := BlockFock.symmetrize
  map_add' first second := by
    funext word
    simp only [BlockFock.symmetrize, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar tensor := by
    funext word
    simp only [BlockFock.symmetrize, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro permutation _
    ring

/-- Every actual selected homogeneous piece is linear in the signed mass. -/
def degreePieceLinear (reference : Slot → FiniteDist Color) (degree : ℕ) (selected : Finset Slot) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color where
  toFun mass := degreePiece reference mass degree selected
  map_add' first second := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · simp only [degreePiece, dif_neg h, Pi.add_apply, add_zero]
  map_smul' scalar mass := by
    funext word
    by_cases h : Fintype.card selected = degree
    · simp only [degreePiece, dif_pos h, localTensor_formula, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _
      ring
    · simp only [degreePiece, dif_neg h, Pi.smul_apply, smul_eq_mul, mul_zero]

/-- All degree coefficients are the literal linear response of the signed
physical mass. This map includes the actual finite symmetrization. -/
def degreeTensorLinear (reference : Slot → FiniteDist Color) (degree : ℕ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) Color :=
  symmetrizeLinear.comp (∑ selected : Finset Slot, degreePieceLinear reference degree selected)

@[simp] theorem degreeTensorLinear_apply (reference : Slot → FiniteDist Color) (degree : ℕ)
    (mass : (Slot → Color) → ℝ) : degreeTensorLinear reference degree mass = degreeTensor reference mass degree := by
  simp only [degreeTensorLinear, LinearMap.comp_apply, LinearMap.sum_apply, symmetrizeLinear,
    LinearMap.coe_mk, AddHom.coe_mk, degreePieceLinear]
  unfold degreeTensor
  congr 1
  funext word
  exact Finset.sum_apply word Finset.univ (fun selected => degreePiece reference mass degree selected)

/-- Every degree and every color-word basis vector of the actual finite
marked Fock space, without choosing a basis of the centered subspace. -/
abbrev FockCoordinate (Slot Color : Type*) [Fintype Slot] :=
  Sigma (fun degree : Fin (Fintype.card Slot + 1) => Fin degree.val → Color)

/-- A single explicit linear channel whose counting norm is exactly the
marked coefficient budget. Scalar local-response estimates can therefore
be tensored directly on arbitrary joint input kernels. -/
def finiteFockChannel (reference : FiniteDist Color) (population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (FockCoordinate Slot Color → ℝ) where
  toFun mass coordinate :=
    Real.sqrt ((Fintype.card Slot + 1 : ℕ) * (coordinate.1.val.factorial : ℝ) * 2 ^ coordinate.1.val) *
      (radius / Real.sqrt population) ^ coordinate.1.val *
        degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, degreeTensorLinear_apply]
    ring



end
end AFT.LocalTensors

end

section








namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # Multiplying finite coefficient spaces without decomposing the input kernel -/

namespace AFT.JointFock

open MeasureTheory TensorFock NonlinearFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance jointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Choice : Index → Type*) [∀ index, Fintype (Choice index)]
variable (Slots : (index : Index) → Choice index → Type*) [∀ index choice, Fintype (Slots index choice)]

/-- Local degree/word coordinates are exactly a choice of all local degrees
and one word on their disjoint union. This reindexing does not separate the
joint coefficient array into rank-one terms. -/
def coordinateEquiv :
    ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) ≃
      Sigma (fun choice : (index : Index) → Choice index => (Sigma (fun index => Slots index (choice index))) → Color) where
  toFun point := ⟨(fun index => (point index).1), fun slot => (point slot.1).2 slot.2⟩
  invFun point := fun index => ⟨point.1 index, fun slot => point.2 ⟨index, slot⟩⟩
  left_inv point := by funext index; rfl
  right_inv point := by rcases point with ⟨choice, word⟩; rfl

/-- The homogeneous tensor for one vector of local degrees is just a slice
of the original arbitrary joint array. -/
def degreeTensor
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (choice : (index : Index) → Choice index) :
    BlockFock.Tensor (Sigma (fun index => Slots index (choice index))) Color :=
  fun word => coefficient (fun index => ⟨choice index, fun slot => word ⟨index, slot⟩⟩)



/-- Evaluate the actual arbitrary joint array by multiplying the local
monomials at one shared Gaussian color vector. -/
def evaluation
    (coefficient : ((index : Index) → Sigma (fun choice : Choice index => Slots index choice → Color)) → ℝ)
    (value : Color → ℂ) : ℂ :=
  ∑ point, (coefficient point : ℂ) * ∏ index, wordMonomial (point index).2 value





end
end AFT.JointFock

end

section





/-! # The tensor operator is the literal finite signed joint response -/

namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
variable {Input Output : Type*} [Fintype Input]

/-- A local linear response is the sum of its responses to the actual input
coordinate vectors. This does not impose any separability on joint inputs. -/
theorem channel_sum_single (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : Input → ℝ) (output : Output) :
    channel kernel output = ∑ point, kernel point * channel (Pi.single point 1) output := by
  have heq : kernel = ∑ point, kernel point • (Pi.single point (1 : ℝ) : Input → ℝ) := by
    funext point
    simp [Pi.single_apply]
  conv_lhs => rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual finite tensor response is a single signed sum over the full
joint input word, rather than a rank-one representation of the kernel. -/
theorem apply_formula (count : ℕ)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  induction count with
  | zero =>
    simp only [apply, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ count ih =>
    rw [show apply (count + 1) channel kernel output = channel 0
      (fun first => apply count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0) from rfl]
    rw [channel_sum_single]
    simp only [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count + 1) => Input)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    change (kernel (Fin.cons first rest) * ∏ x, channel x.succ (Pi.single (rest x) 1) (output x.succ)) *
      channel 0 (Pi.single first 1) (output 0) = _
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The exact finite formula is independent of the chosen decidable equality
on its finite coordinate set. -/
theorem apply_formula_instance (count : ℕ) [decision : DecidableEq (Fin count)]
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  have hd : decision = instDecidableEqFin count := Subsingleton.elim _ _
  cases hd
  exact apply_formula count channel kernel output



end
end AFT.TensorChannel

end

section












/-! # Exact joint signed mass and its physical generating polynomial -/

namespace AFT.JointPhysicalChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance jointPhysicalChannelSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

/-- The literal signed output of arbitrary local finite channels fed by one
joint input kernel. The joint kernel is retained inside the single input sum. -/
def mass (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (output : Sigma Slots → Color) : ℝ :=
  ∑ input, kernel input * ∏ index, channel index (Pi.single (input index) 1) (fun slot => output ⟨index, slot⟩)







end
end AFT.JointPhysicalChannel

end

section












/-! # One common finite Fock alphabet for heterogeneous local output blocks -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

abbrev PackedCoordinate (maximum : ℕ) (Color : Type*) :=
  Sigma (fun degree : Fin (maximum + 1) => Fin degree.val → Color)

/-- All local degrees are embedded into one common alphabet; unused higher
degrees are the actual zero coefficients, not an assumed truncation. -/
def packedFockChannel (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (PackedCoordinate maximum Color → ℝ) where
  toFun mass coordinate := Real.sqrt (coordinate.1.val.factorial : ℝ) *
    (Real.sqrt 2 * (radius / Real.sqrt population)) ^ coordinate.1.val *
      degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, degreeTensorLinear_apply]
    ring





end
end AFT.LocalTensors

end

section










/-! # Decoding the finite coefficient channel gives the actual polynomial -/
namespace AFT.LocalTensors
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance packedFockEvaluationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder of norm at most one. It converts the coefficient
Hilbert channel into its actual polynomial at the common Gaussian vector. -/
def fockDecoder (maximum : ℕ) (coordinate : PackedCoordinate maximum Color) : ℝ :=
  1 / Real.sqrt (coordinate.1.val.factorial : ℝ)









end
end AFT.LocalTensors

end

section












/-! # Arbitrary joint physical responses through their exact finite Fock channels -/
namespace AFT.JointPhysicalChannel
open MeasureTheory LocalTensors TensorFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
local instance jointPhysicalFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
local instance jointPhysicalFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder only contracts the complete joint coefficient array. -/
def decodedCoefficient (maximum : ℕ) (coefficient : (Index → PackedCoordinate maximum Color) → ℝ)
    (point : Index → PackedCoordinate maximum Color) : ℝ :=
  coefficient point * ∏ index, fockDecoder maximum (point index)





variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The actual packed response array, still containing the full joint input
kernel inside one finite sum. -/
def coefficient (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (point : Index → PackedCoordinate maximum Color) : ℝ :=
  ∑ input, kernel input * ∏ index,
    packedFockChannel reference maximum population radius
      (channel index (Pi.single (input index) 1)) (point index)







end
end AFT.JointPhysicalChannel

end

section







namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration


/-! # The complete positive chart and public-anchor conditional output -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance publicGaussianFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

abbrev PublicOffsets (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) :=
  {offset : ℤ // offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter)}





abbrev PublicChartFamily (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter)) :=
  (sample : bodySample cutoffScale parameter × Bool) → PublicOffsets cutoffScale parameter mark sample →
    FiniteDist (Chart (ZMod (Parameters.modulus parameter)))









end
end AFT.V7Calibration

end

section








namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # Weighted Hilbert energy of the literal four-term primary response -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

theorem profileSquareNorm_four_le (reference first second third fourth : Color → ℝ)
    (hr : ∀ color, 0 ≤ reference color) :
    profileSquareNorm reference (first + second + third - fourth) ≤
      4 * (profileSquareNorm reference first + profileSquareNorm reference second +
        profileSquareNorm reference third + profileSquareNorm reference fourth) := by
  simp only [profileSquareNorm, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro color _
  have hpoint : (first color + second color + third color - fourth color) ^ 2 ≤
      4 * (first color ^ 2 + second color ^ 2 + third color ^ 2 + fourth color ^ 2) := by
    nlinarith only [sq_nonneg (first color - second color), sq_nonneg (third color + fourth color),
      sq_nonneg (first color + second color - (third color - fourth color))]
  exact (div_le_div_of_nonneg_right hpoint (hr color)).trans_eq (by ring)

theorem profileSquareNorm_reference_comparison (primary reference profile : Color → ℝ)
    (comparison : ℝ) (hp : ∀ color, 0 < primary color) (hr : ∀ color, 0 < reference color)
    (hcompare : ∀ color, primary color ≤ comparison * reference color) :
    profileSquareNorm reference profile ≤ comparison * profileSquareNorm primary profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hr color)).mpr
  have hh := mul_le_mul_of_nonneg_right (hcompare color)
    (div_nonneg (sq_nonneg (profile color)) (hp color).le)
  have heq : primary color * (profile color ^ 2 / primary color) = profile color ^ 2 := by
    field_simp [ne_of_gt (hp color)]
  rw [heq] at hh
  nlinarith only [hh]

/-- The diagonal, sign response, full public anchor, and root compensator
are estimated in the actual output reference norm. -/
theorem four_channel_response_energy (primary reference sign response : Color → ℝ)
    (firstAnchor secondAnchor : Color → Color → ℝ) (activation diagonal majorant l1 anchorCost : ℝ)
    (hp : ∀ color, 0 < primary color) (hpmass : ∑ color, primary color = 1)
    (hr : ∀ color, 0 < reference color)
    (hdiag : ∀ color, primary color ≤ diagonal * reference color)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant) (hv : ∀ color, |response color| ≤ majorant * reference color)
    (hl1 : (∑ color, |response color|) ≤ l1)
    (hfirst0 : ∀ color output, 0 ≤ firstAnchor color output)
    (hsecond0 : ∀ color output, 0 ≤ secondAnchor color output)
    (hfirstMass : ∀ color, ∑ output, firstAnchor color output = 1)
    (hsecondMass : ∀ color, ∑ output, secondAnchor color output = 1)
    (hfirst : ∀ output, applyAnchor firstAnchor primary output ≤ anchorCost * reference output)
    (hsecond : ∀ output, applyAnchor secondAnchor primary output ≤ anchorCost * reference output)
    (profile : Color → ℝ) :
    profileSquareNorm reference
      (activation • profile + (signFunctional sign profile) • response +
        activation • applyAnchor firstAnchor profile - activation • applyAnchor secondAnchor profile) ≤
      4 * (activation ^ 2 * diagonal + majorant * l1 + 2 * activation ^ 2 * anchorCost) *
        profileSquareNorm primary profile := by
  have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  have hd := mul_le_mul_of_nonneg_left
    (profileSquareNorm_reference_comparison primary reference profile diagonal hp hr hdiag) (sq_nonneg activation)
  have h1 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference firstAnchor profile anchorCost hp hr
      hfirst0 hfirstMass hfirst) (sq_nonneg activation)
  have h2 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference secondAnchor profile anchorCost hp hr
      hsecond0 hsecondMass hsecond) (sq_nonneg activation)
  have hvnorm := (signProfile_square_bound reference response majorant hr hv).trans
    (mul_le_mul_of_nonneg_left hl1 hmajorant)
  have hsnorm := mul_le_mul (signFunctional_sq_le primary sign profile hp hpmass hsign)
    hvnorm (profileSquareNorm_nonneg reference response (fun color => (hr color).le)) hn
  have hfour := profileSquareNorm_four_le reference (activation • profile)
    ((signFunctional sign profile) • response) (activation • applyAnchor firstAnchor profile)
    (activation • applyAnchor secondAnchor profile) (fun color => (hr color).le)
  simp only [profileSquareNorm_smul] at hfour
  nlinarith only [hd, h1, h2, hsnorm, hfour]

end
end AFT

end

section






namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors


/-! # The exact first Fock coefficient of an arbitrary signed finite mass -/

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance signedFirstCoefficientFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The full signed one-point color count, before subtracting its total mass. -/
def signedColorCount (mass : (Slot → Color) → ℝ) (color : Color) : ℝ :=
  ∑ input, mass input * ∑ slot, if input slot = color then (1 : ℝ) else 0

/-- The actual first symmetric coefficient is the sum of the whitened
one-site responses, preserving cancellation between all physical outputs. -/
theorem signed_degreeTensor_one_formula (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ input, mass input * ∑ slot, atomCoefficient reference (input slot) color := by
  have hpiece (selected : Finset Slot) :
      degreePiece (fun _ => reference) mass 1 selected (fun _ => color) =
        if selected.card = 1 then localTensor (fun _ => reference) mass selected (fun _ => color) else 0 := by
    by_cases h : selected.card = 1
    · have hh : Fintype.card selected = 1 := by simpa using h
      simp only [degreePiece, dif_pos hh, if_pos h, Function.comp_def]
    · have hh : Fintype.card selected ≠ 1 := by simpa using h
      simp only [degreePiece, dif_neg hh, if_neg h]
  have hsym : degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ selected : Finset Slot, degreePiece (fun _ => reference) mass 1 selected (fun _ => color) := by
    unfold degreeTensor BlockFock.symmetrize
    simp only [Function.comp_def]
    rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rw [hsym]
  simp_rw [hpiece]
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun selected : Finset Slot => selected.card = 1) =
      Finset.univ.powersetCard 1 := by ext selected; simp
  rw [hsets, Finset.powersetCard_one, Finset.sum_map]
  simp_rw [localTensor_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  congr 1
  change (∏ selected : ({slot} : Finset Slot), atomCoefficient reference (input selected) color) = _
  exact (Finset.prod_coe_sort ({slot} : Finset Slot)
    (fun index => atomCoefficient reference (input index) color)).trans (Finset.prod_singleton _ _)

/-- For zero total signed mass the exact first coefficient is the whitened
signed count profile, with no loss from bounding the output slots separately. -/
theorem degreeTensor_one_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      signedColorCount mass color / Real.sqrt (reference.weight color) := by
  rw [signed_degreeTensor_one_formula]
  have hs : Real.sqrt (reference.weight color) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (href color))
  have hsq := Real.sq_sqrt (reference.nonneg color)
  have hatom (input : Color) : atomCoefficient reference input color =
      (if input = color then (1 : ℝ) else 0) / Real.sqrt (reference.weight color) -
        Real.sqrt (reference.weight color) := by
    unfold atomCoefficient Hoeffding.centeredAtom
    split_ifs <;> field_simp [hs, (href color).ne'] <;> nlinarith [hsq]
  simp_rw [hatom]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_sub]
  rw [← Finset.sum_mul, hmass, zero_mul, sub_zero]
  unfold signedColorCount
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.sum_div]
  ring

/-- The first-degree Fock energy equals the actual signed count-profile
energy exactly. This applies to every finite output block and signed mass. -/
theorem degreeTensor_one_energy_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) :
    BlockFock.tensorEnergy (degreeTensor (fun _ : Slot => reference) mass 1) =
      profileSquareNorm reference.weight (signedColorCount mass) := by
  unfold BlockFock.tensorEnergy profileSquareNorm
  have he := (Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word => degreeTensor (fun _ : Slot => reference) mass 1 word ^ 2)
  rw [← he]
  apply Finset.sum_congr rfl
  intro color _
  change degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) ^ 2 = _
  rw [degreeTensor_one_zero_mass reference href mass hmass, div_pow,
    Real.sq_sqrt (reference.nonneg color)]

end
end AFT.LocalTensors

end

section












/-! # Complete Fock energy of a genuine canonical singleton response -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance singletonFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]







end
end AFT.LocalTensors

end

section



































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedRootAnchor
end AFT.V7Calibration.fixedRootAnchor
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerAnchorShiftProfile
end AFT.V7Calibration.integerAnchorShiftProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.marginalRootAnchor
end AFT.V7Calibration.marginalRootAnchor
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # All actual primary and body channels on arbitrary joint canonical input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualJointFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualJointFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- A primary score changes its two endpoints, attached body and compensator;
a body score changes its single physical body output. -/
def actualRoleSlots : Bool → Type
  | true => Fin 4
  | false => Fin 1

instance actualRoleSlotsFintype (role : Bool) : Fintype (actualRoleSlots role) := by
  cases role <;> dsimp [actualRoleSlots] <;> infer_instance

def actualRoleInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (role : Bool) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  if role then actualPrimaryLaw cutoffScale parameter beta else actualBodyLaw cutoffScale parameter beta









end
end AFT.V7Calibration

end

section








/-! # Norms of normalized physical block coefficients -/

namespace AFT.BlockProducts

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.BlockProducts.instDecidableEqFin_aFT (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]











end

end AFT.BlockProducts

end

section











namespace AFT
end AFT
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.splitSlotsEquiv
end AFT.BlockProducts.splitSlotsEquiv
namespace AFT.V7Calibration
end AFT.V7Calibration



/-! # Exact removed-block means and their dimension-free bounds -/

namespace AFT.BlockProducts

open scoped BigOperators Classical
noncomputable section

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The literal degree-one block tensor in Euclidean color coordinates. -/
def linearVector (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) :
    EuclideanSpace ℝ Color := WithLp.toLp 2 (normalizedLinear Slots reference law scale index)

omit [Fintype Index] in
@[simp] theorem linearVector_apply (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) :
    (linearVector Slots reference law scale index).ofLp color = normalizedLinear Slots reference law scale index color := rfl








end
end AFT.BlockProducts

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
local instance restrictedBlockMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance restrictedBlockMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _







end
end AFT.V7Calibration

end

section































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.condition
end AFT.FiniteDist.condition
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.normalizedRoot
end AFT.GaussianSource.normalizedRoot
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.rootMomentConstant
end AFT.GaussianSource.rootMomentConstant
namespace AFT.GaussianSource.rootPrefixDensity
end AFT.GaussianSource.rootPrefixDensity
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.GaussianSource.v7RootKernelSq
end AFT.GaussianSource.v7RootKernelSq
namespace AFT.GaussianSource.v7RootThetaBound
end AFT.GaussianSource.v7RootThetaBound
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualFockScale
end AFT.V7Calibration.actualFockScale
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile


/-! # Complete physical marked-block tails with arbitrary joint signed output -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualTaggedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualTaggedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualTaggedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

abbrev actualMarkedSlots (parameter : ℕ) (selected : Finset (blockIndex parameter)) :=
  Sigma (fun index : {i : blockIndex parameter // i ∈ selected} => blockSlots parameter index)









end
end AFT.V7Calibration

end

section










namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration



/-! # The complete mixed tail of actual arbitrary joint primary/body input -/
namespace AFT.V7Calibration
open Filter GaussianSource LocalTensors JointPhysicalChannel HistogramNormalization BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualInputMixedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualInputMixedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualInputMixedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Physical slot placement together with the actual source coordinates used
by its primary, attached, compensator and singleton channels. -/
structure ActualTaggedPlacement (parameter count : ℕ) (role : Fin count → Bool)
    (selected : Finset (blockIndex parameter)) where
  attached : Fin count → blockIndex parameter
  compensator : Fin count → blockIndex parameter
  body : Fin count → blockIndex parameter
  slots : Sigma (fun index => actualRoleSlots (role index)) ≃ actualMarkedSlots parameter selected











end
end AFT.V7Calibration

end

section

















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.densityTail
end AFT.HistogramNormalization.densityTail
namespace AFT.JointPhysicalChannel
end AFT.JointPhysicalChannel
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualRolePoolCapacity
end AFT.V7Calibration.actualRolePoolCapacity
namespace AFT.V7Calibration.actualRoleRateFactor
end AFT.V7Calibration.actualRoleRateFactor



/-! # Complete tails of actual finite signed control representations -/
namespace AFT.V7Calibration
open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualFiniteControlTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualFiniteControlTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- A literal finite canonical joint input and its physical placement. -/
structure ActualCanonicalControl (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) where
  count : ℕ
  role : Fin count → Bool
  selected : Finset (blockIndex parameter)
  placement : ActualTaggedPlacement parameter count role selected
  kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ
  canonical : Hoeffding.Canonical
    (fun index => actualRoleInput cutoffScale parameter beta (role index)) Finset.univ kernel













end
end AFT.V7Calibration

end

section





/-! # Sorting a finite public set using an explicitly given coordinate code -/
namespace AFT

 def finiteSetNumbering {State : Type*} {size : ℕ} (index : State≃Fin size) (set : Finset State) :
    Fin set.card≃set :=
  letI : LinearOrder State := LinearOrder.lift' index index.injective
  (set.orderIsoOfFin rfl).toEquiv

 def finiteSetMatching {State : Type*} {size : ℕ} (index : State≃Fin size)
    (first second : Finset State) (hcard : first.card ≤ second.card) : first↪second :=
  (finiteSetNumbering index first).symm.toEmbedding.trans
    ((Fin.castLEEmb hcard).trans (finiteSetNumbering index second).toEmbedding)

end AFT

end

section













/-! # Actual disjoint public control and reserve pools -/

namespace AFT.PublicPools

open scoped BigOperators Classical

noncomputable section

variable {Position : Type*} [Fintype Position] [DecidableEq Position]

def controls (legs queue : Finset Position) := legs \ queue

def available (legs queue : Finset Position) := (legs ∪ queue)ᶜ

omit [Fintype Position] in
theorem controls_card_le (legs queue : Finset Position) : (controls legs queue).card ≤ legs.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem available_card_lower (legs queue : Finset Position) :
    Fintype.card Position - legs.card - queue.card ≤ (available legs queue).card := by
  rw [available, Finset.card_compl]
  have hh := Finset.card_union_le legs queue
  omega



def matchingPositions (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  Finset.univ.map ⟨fun control => (pairing control).val,
    fun _ _ h => pairing.injective (Subtype.ext h)⟩

@[simp] theorem matchingPositions_card (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    (matchingPositions legs queue pairing).card = (controls legs queue).card := by
  simp only [matchingPositions, Finset.card_map, Finset.card_univ, Fintype.card_coe]



def reserve (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  available legs queue \ matchingPositions legs queue pairing





end
end AFT.PublicPools

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration PublicPools FiniteDist

noncomputable section

/-- The actual V7 sizes leave more than half of all bodies after removing
all attachments, queue positions, and one compensator for each leg. -/
theorem actual_pool_budget (parameter : ℕ) :
    2 * (2 * Parameters.legs parameter + Parameters.modulus parameter) ≤ Parameters.bodies parameter := by
  have hsecurity : 1 ≤ Parameters.security parameter := (by decide : 1 ≤ 2).trans (Parameters.security_ge_two parameter)
  have hleg : Parameters.legs parameter ≤ Parameters.modulus parameter :=
    (pow_le_pow_right₀ hsecurity (by omega : 30 ≤ 40)).trans (Parameters.modulus_bounds parameter).1
  have hmean : 8 ≤ Parameters.meanDensity parameter := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 20
    dsimp [Parameters.meanDensity]
    omega
  have hdim : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    simpa only [Parameters.dimension, Nat.mul_comm] using Nat.mul_le_mul_left (Parameters.modulus parameter) hmean
  have hpop := Parameters.population_identity parameter
  omega

def actualLegBodies (parameter : ℕ) : Finset (blockIndex parameter) :=
  (Finset.univ : Finset (Fin (Parameters.legs parameter))).map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem actualLegBodies_card (parameter : ℕ) :
    (actualLegBodies parameter).card = Parameters.legs parameter := by
  simp only [actualLegBodies, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def actualControlMatching (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    controls (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) ↪
      available (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) :=
  finiteSetMatching (blockIndexNumbering parameter) _ _ (by
    have hc := controls_card_le (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    have ha := available_card_lower (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    simp only [actualLegBodies_card, permutationMask_card, actualQueueSelection_card, blockIndex_card] at hc ha
    have hh := actual_pool_budget parameter
    omega)

def actualReservedBodies (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    Finset (blockIndex parameter) :=
  reserve _ _ (actualControlMatching parameter placement)



end
end AFT.GaussianSource

end

section











/-! # Distinct physical sources from the real public matching and reserve -/
namespace AFT.PublicPools
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Position Primary Body : Type*} [Fintype Position] [DecidableEq Position]

/-- Attached sources, their injectively matched compensators, and reserved
body sources are three genuinely disjoint populations. -/
def sourceFunction (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body → Position
  | .inl (.inl index) => (primary index).val
  | .inl (.inr index) => (pairing (primary index)).val
  | .inr index => (body index).val

theorem sourceFunction_injective (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    Function.Injective (sourceFunction legs queue pairing primary body) := by
  have hp (i : Primary) : (primary i).val∈legs := (Finset.mem_sdiff.mp (primary i).property).1
  have hc (i : Primary) : (pairing (primary i)).val∉legs := by
    have hh := Finset.mem_compl.mp (pairing (primary i)).property
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hb (i : Body) : (body i).val∉legs := by
    have hh := Finset.mem_compl.mp (Finset.mem_sdiff.mp (body i).property).1
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hm (i : Primary) : (pairing (primary i)).val∈matchingPositions legs queue pairing :=
    Finset.mem_map.mpr ⟨primary i,Finset.mem_univ _,rfl⟩
  have hbm (i : Body) : (body i).val∉matchingPositions legs queue pairing :=
    (Finset.mem_sdiff.mp (body i).property).2
  rintro (⟨i|i⟩|i) (⟨j|j⟩|j) he <;> dsimp only [sourceFunction] at he
  · exact congrArg (Sum.inl ∘ Sum.inl) (primary.injective (Subtype.ext he))
  · exact False.elim (hc j (he ▸ hp i))
  · exact False.elim (hb j (he ▸ hp i))
  · exact False.elim (hc i (he.symm ▸ hp j))
  · exact congrArg (Sum.inl ∘ Sum.inr) (primary.injective (pairing.injective (Subtype.ext he)))
  · exact False.elim (hbm j (he ▸ hm i))
  · exact False.elim (hb i (he.symm ▸ hp j))
  · exact False.elim (hbm i (he.symm ▸ hm j))
  · exact congrArg Sum.inr (body.injective (Subtype.ext he))

def sourceEmbedding (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body ↪ Position :=
  ⟨sourceFunction legs queue pairing primary body,sourceFunction_injective legs queue pairing primary body⟩



variable [Fintype Primary] [Fintype Body]

def sourceSelection (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) : Finset Position :=
  Finset.univ.map (sourceEmbedding legs queue pairing primary body)

def sourceEquiv (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ sourceSelection legs queue pairing primary body :=
  Equiv.ofBijective (fun source => ⟨sourceEmbedding legs queue pairing primary body source,
    Finset.mem_map.mpr ⟨source,Finset.mem_univ _,rfl⟩⟩) ⟨
      fun a b h => (sourceEmbedding legs queue pairing primary body).injective (congrArg Subtype.val h),by
      rintro ⟨position,hposition⟩
      obtain ⟨source,_,hs⟩ := Finset.mem_map.mp hposition
      exact ⟨source,Subtype.ext hs⟩⟩

@[simp] theorem sourceEquiv_val (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (sourceEquiv legs queue pairing primary body source).val=sourceEmbedding legs queue pairing primary body source := rfl

end
end AFT.PublicPools

end

section













/-! # Actual public choices have disjoint, queue-free physical root sources -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev actualControlPool (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :=
  controls (actualLegBodies n) (permutationMask (actualQueueSelection n) placement)

abbrev ActualPublicPrimaryChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Primary : Type*) :=
  Primary ↪ actualControlPool n placement

abbrev ActualPublicBodyChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Body : Type*) :=
  Body ↪ actualReservedBodies n placement

def actualPublicSourceEmbedding (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (Primary ⊕ Primary) ⊕ Body ↪ blockIndex n :=
  sourceEmbedding _ _ (actualControlMatching n placement) primary body

def actualPublicSelected (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) : Finset (blockIndex n) :=
  sourceSelection _ _ (actualControlMatching n placement) primary body

def actualPublicSourceEquiv (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ actualPublicSelected n placement primary body :=
  sourceEquiv _ _ (actualControlMatching n placement) primary body

@[simp] theorem actualPublicSourceEquiv_val (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (actualPublicSourceEquiv n placement primary body source).val=actualPublicSourceEmbedding n placement primary body source := rfl



theorem mem_actualLegBodies_iff (n : ℕ) (index : blockIndex n) :
    index∈actualLegBodies n ↔ ∃ leg,index=Sum.inl leg := by
  simp only [actualLegBodies,Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coeFn_mk]
  exact exists_congr fun _ => eq_comm

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_attached (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ leg,actualPublicSourceEmbedding n placement primary body (.inl (.inl index))=Sum.inl leg := by
  apply (mem_actualLegBodies_iff n _).mp
  exact (Finset.mem_sdiff.mp (primary index).property).1

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_compensator (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inl (.inr index))=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inl (.inr index))∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (actualControlMatching n placement (primary index)).property)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_body (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Body) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inr index)=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inr index)∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (Finset.mem_sdiff.mp (body index).property).1)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inr index) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩


@[simp] theorem actualPublicSelected_card (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (actualPublicSelected n placement primary body).card=2*Fintype.card Primary+Fintype.card Body := by
  simp only [actualPublicSelected,sourceSelection,Finset.card_map,Finset.card_univ,Fintype.card_sum]
  omega











end
end AFT.V7Calibration

end

section










/-! # Exact physical output coordinates of primary and body roles -/
namespace AFT.V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev PrimaryRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // role i=true}
abbrev BodyRoles {count : ℕ} (role : Fin count → Bool) := {i : Fin count // ¬role i=true}
abbrev RoleSources {count : ℕ} (role : Fin count → Bool) := (PrimaryRoles role ⊕ PrimaryRoles role) ⊕ BodyRoles role

def roleSourceSlots {count : ℕ} (role : Fin count → Bool) : RoleSources role → Type
  | .inl (.inl _) => Fin 3
  | .inl (.inr _) => Fin 1
  | .inr _ => Fin 1

instance roleSourceSlotsFintype {count : ℕ} (role : Fin count → Bool) (source : RoleSources role) :
    Fintype (roleSourceSlots role source) := by rcases source with ⟨_|_⟩|_ <;> dsimp [roleSourceSlots] <;> infer_instance

def rolePartition {count : ℕ} (role : Fin count → Bool) : (PrimaryRoles role ⊕ BodyRoles role) ≃ Fin count :=
  Equiv.sumCompl (fun index => role index=true)

def primaryRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : PrimaryRoles role) :
    actualRoleSlots (role (rolePartition role (.inl index))) ≃ Fin 4 :=
  Equiv.cast (by change actualRoleSlots (role index.val)=Fin 4; rw [index.property]; rfl)

def bodyRoleSlotEquiv {count : ℕ} (role : Fin count → Bool) (index : BodyRoles role) :
    actualRoleSlots (role (rolePartition role (.inr index))) ≃ Fin 1 :=
  Equiv.cast (by
    change actualRoleSlots (role index.val)=Fin 1
    have hh : role index.val=false := by simpa using index.property
    rw [hh]
    rfl)

/-- Four primary outputs are the attached triple followed by its compensator. -/
def primaryOutputSplit (Primary : Type*) : (Primary × Fin 4) ≃ (Primary × Fin 3) ⊕ (Primary × Fin 1) :=
  (Equiv.prodCongr (Equiv.refl Primary) (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm).trans
    (Equiv.prodSumDistrib Primary (Fin 3) (Fin 1))

def roleOutputPartition {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃
      (PrimaryRoles role × Fin 4) ⊕ (BodyRoles role × Fin 1) :=
  ((Equiv.sigmaCongrLeft (β:=fun index => actualRoleSlots (role index)) (rolePartition role)).symm.trans
    (Equiv.sumSigmaDistrib (fun index => actualRoleSlots (role (rolePartition role index))))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProdOfEquiv (primaryRoleSlotEquiv role))
        (Equiv.sigmaEquivProdOfEquiv (bodyRoleSlotEquiv role)))

def sourceOutputPartition {count : ℕ} (role : Fin count → Bool) :
    Sigma (roleSourceSlots role) ≃
      ((PrimaryRoles role × Fin 3) ⊕ (PrimaryRoles role × Fin 1)) ⊕ (BodyRoles role × Fin 1) :=
  (Equiv.sumSigmaDistrib (roleSourceSlots role)).trans
    (Equiv.sumCongr ((Equiv.sumSigmaDistrib (fun index => roleSourceSlots role (.inl index))).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProd _ _) (Equiv.sigmaEquivProd _ _)))
      (Equiv.sigmaEquivProd _ _))

def roleOutputSourceEquiv {count : ℕ} (role : Fin count → Bool) :
    (Sigma (fun index => actualRoleSlots (role index))) ≃ Sigma (roleSourceSlots role) :=
  ((roleOutputPartition role).trans (Equiv.sumCongr (primaryOutputSplit (PrimaryRoles role))
    (Equiv.refl _))).trans (sourceOutputPartition role).symm


@[simp] theorem roleOutputSourceEquiv_symm_attached {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 3) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inl index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.castAdd 1 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_compensator {count : ℕ} (role : Fin count → Bool)
    (index : PrimaryRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inl (.inr index),slot⟩=
      ⟨index.val,(primaryRoleSlotEquiv role index).symm (Fin.natAdd 3 slot)⟩ := by rfl

@[simp] theorem roleOutputSourceEquiv_symm_body {count : ℕ} (role : Fin count → Bool)
    (index : BodyRoles role) (slot : Fin 1) :
    (roleOutputSourceEquiv role).symm ⟨.inr index,slot⟩=
      ⟨index.val,(bodyRoleSlotEquiv role index).symm slot⟩ := by rfl

end
end AFT.V7Calibration

end

section













/-! # Concrete tagged placements from the actual public pools -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {count : ℕ} (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (role : Fin count → Bool)
    (primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role))
    (body : ActualPublicBodyChoice n placement (BodyRoles role))

def actualPublicSourceSlotEquiv (source : RoleSources role) :
    roleSourceSlots role source ≃ blockSlots n (actualPublicSourceEmbedding n placement primary body source) :=
  Equiv.cast (by
    rcases source with ⟨index|index⟩|index
    · obtain ⟨leg,hleg⟩ := actualPublicSource_attached n placement primary body index
      rw [hleg]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_compensator n placement primary body index
      rw [hfree]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_body n placement primary body index
      rw [hfree]
      rfl)

def actualPublicSlotsEquiv : Sigma (fun index => actualRoleSlots (role index)) ≃
    actualMarkedSlots n (actualPublicSelected n placement primary body) :=
  ((roleOutputSourceEquiv role).trans (Equiv.sigmaCongrRight
    (actualPublicSourceSlotEquiv n placement role primary body))).trans
    (Equiv.sigmaCongrLeft (β:=fun source : actualPublicSelected n placement primary body => blockSlots n source.val)
      (actualPublicSourceEquiv n placement primary body))

def actualPublicAttached (index : Fin count) : blockIndex n :=
  if h : role index=true then (primary ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicCompensator (index : Fin count) : blockIndex n :=
  if h : role index=true then (actualControlMatching n placement (primary ⟨index,h⟩)).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicBody (index : Fin count) : blockIndex n :=
  if h : ¬role index=true then (body ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩



@[simp] theorem actualPublicAttached_source (index : PrimaryRoles role) :
    actualPublicAttached n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inl index)) := by
  simp only [actualPublicAttached,dif_pos index.property]
  rfl

@[simp] theorem actualPublicCompensator_source (index : PrimaryRoles role) :
    actualPublicCompensator n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) := by
  simp only [actualPublicCompensator,dif_pos index.property]
  rfl

@[simp] theorem actualPublicBody_source (index : BodyRoles role) :
    actualPublicBody n placement role body index.val=
      actualPublicSourceEmbedding n placement primary body (.inr index) := by
  simp only [actualPublicBody,dif_pos index.property]
  rfl




/-- The slot equivalence preserves the actual physical source index, rather
than merely its cardinality. -/
@[simp] theorem actualPublicSlotsEquiv_source
    (coordinate : Sigma (fun index => actualRoleSlots (role index))) :
    (actualPublicSlotsEquiv n placement role primary body coordinate).1.val=
      actualPublicSourceEmbedding n placement primary body ((roleOutputSourceEquiv role coordinate).1) := rfl





end
end AFT.V7Calibration

end

section




namespace AFT
end AFT


/-! # Joint source/input extension of actual signed finite channels -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

/-- Averaging a family of signed profiles is contractive in every fixed
weighted profile Hilbert space. Source probabilities remain inside the sum. -/
theorem profileSquareNorm_average_le {Source Output : Type*} [Fintype Source] [Fintype Output]
    (source : FiniteDist Source) (reference : Output → ℝ) (href : ∀ output, 0 ≤ reference output)
    (profile : Source → Output → ℝ) :
    profileSquareNorm reference (fun output => ∑ point, source.weight point * profile point output) ≤
      ∑ point, source.weight point * profileSquareNorm reference (profile point) := by
  calc
    _ ≤ ∑ output, (∑ point, source.weight point * profile point output ^ 2) / reference output := by
      apply Finset.sum_le_sum
      intro output _
      apply div_le_div_of_nonneg_right _ (href output)
      have hh : (∑ point, source.weight point * profile point output) ^ 2 ≤
          (∑ point, source.weight point) * (∑ point, source.weight point * profile point output ^ 2) := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
        · intro point _; exact source.nonneg point
        · intro point _; exact mul_nonneg (source.nonneg point) (sq_nonneg _)
        · intro point _; ring
      simpa only [source.sum_one, one_mul] using hh
    _ = _ := by
      simp only [Finset.sum_div, profileSquareNorm, Finset.mul_sum, mul_div_assoc]
      exact Finset.sum_comm

/-- Turning a density into its actual signed mass preserves its Hilbert
square exactly, including zero-probability input atoms. -/
theorem profileSquareNorm_weight_mul {Input : Type*} [Fintype Input]
    (input : FiniteDist Input) (density : Input → ℝ) :
    profileSquareNorm input.weight (fun color => input.weight color * density color) = input.l2Sq density := by
  apply Finset.sum_congr rfl
  intro color _
  change (input.weight color * density color) ^ 2 / input.weight color = input.weight color * density color ^ 2
  by_cases hz : input.weight color = 0
  · simp only [hz, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
  · field_simp

end
end AFT

end

section
























namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.densityTail
end AFT.HistogramNormalization.densityTail
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.centeredRootBodyProfile
end AFT.V7Calibration.centeredRootBodyProfile
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile




/-! # The actual finite root-response operator and exact source expansion -/

namespace AFT.Hoeffding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Source : Type*} [Fintype Index] [Fintype Source]



variable [DecidableEq Index]



end
end AFT.Hoeffding

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The literal centered histogram generating polynomial of an arbitrary
signed physical output mass, retaining all homogeneous degrees. -/
def centeredGeneratingLinear (reference : Color → ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun mass := ∑ word, mass word • ∏ slot, centeredFactor reference (word slot)
  map_add' first second := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' scalar mass := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.smul_sum,smul_smul]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualRootResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualRootResponseSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _



























end
end AFT.V7Calibration

end

section




/-!
# Affine evaluation and the exact AFT preservation interface

The linear part is an actual linear equivalence, so legality is represented
by invertibility, not by an arbitrary proposition named `legal`.
For the paper take `R = ZMod q` and `V = Fin d → ZMod q`.
This file does not construct the calibrated Gaussian sampler of Section 9.
-/

namespace AFT

open scoped Classical

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The reduced affine data returned by a legal AFT sampler. The paper permits
returning residues rather than integer lifts (immediately after Definition 5.1). -/
structure AffinePair where
  linear : V ≃ₗ[R] V
  offset : V

namespace AffinePair

variable {R V}

/-- The deterministic evaluator, exactly `Q x + b`. -/
def eval (pair : AffinePair R V) (input : V) : V :=
  pair.linear input + pair.offset

/-- Every legal affine evaluator is a bijection. -/
def equiv (pair : AffinePair R V) : V ≃ V where
  toFun := pair.eval
  invFun output := pair.linear.symm (output - pair.offset)
  left_inv input := by simp [eval]
  right_inv output := by simp [eval]

@[simp] theorem equiv_apply (pair : AffinePair R V) (input : V) :
    pair.equiv input = pair.eval input := rfl



/-- The always-legal fallback in Appendix A. -/
def fallback : AffinePair R V := ⟨LinearEquiv.refl R V, 0⟩

@[simp] theorem fallback_eval (input : V) :
    (fallback : AffinePair R V).eval input = input := by simp [eval, fallback]

/-- Left multiplication acts on each column of a public matrix. -/
def columnsEquiv (pair : AffinePair R V) (Column : Type*) :
    (Column → V) ≃ (Column → V) :=
  Equiv.piCongrRight (fun _ => pair.linear.toEquiv)

@[simp] theorem columnsEquiv_apply (pair : AffinePair R V) (Column : Type*)
    (matrix : Column → V) (column : Column) :
    pair.columnsEquiv Column matrix column = pair.linear (matrix column) := rfl



end AffinePair

section Probability

variable {R V} [Fintype V]
variable {Sample Column : Type*} [Fintype Sample] [Fintype Column]







end Probability
end AFT

end

section



/-!
# Integral algebra behind the V7 affine fiber transport construction

Vertices of the concrete path are `Fin (n + 1)` and its edges are `Fin n`.
All lattices and preimages in this file are over the integers. General tree
transport is stated in basis coordinates; the graph-to-basis bridge for an
arbitrary spanning tree is deliberately not asserted here.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped BigOperators

/-- The signed path incidence map: each edge goes from vertex `i` to `i+1`. -/
def pathLoad : (n : ℕ) → (Fin n → ℤ) → (Fin (n + 1) → ℤ)
  | 0, _ => 0
  | n + 1, e => Fin.cons (e 0)
      (fun i => pathLoad n (Fin.tail e) i - if i = 0 then e 0 else 0)

@[simp] theorem pathLoad_zero (n : ℕ) : pathLoad n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · have ht : Fin.tail (0 : Fin (n + 1) → ℤ) = 0 := rfl
        simp [pathLoad, ht, ih]

@[simp] theorem pathLoad_add (n : ℕ) (e f : Fin n → ℤ) :
    pathLoad n (e + f) = pathLoad n e + pathLoad n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ht : Fin.tail (e + f) = Fin.tail e + Fin.tail f := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp only [pathLoad, Fin.cons_succ, ht, ih, Pi.add_apply]
        split_ifs <;> ring

@[simp] theorem pathLoad_smul (n : ℕ) (a : ℤ) (e : Fin n → ℤ) :
    pathLoad n (a • e) = a • pathLoad n e := by
  induction n with
  | zero => simp [pathLoad]
  | succ n ih =>
      have ht : Fin.tail (a • e) = a • Fin.tail e := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp only [pathLoad, Fin.cons_succ, ht, ih, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring

/-- The integral linear map represented by the signed path incidence matrix. -/
def pathIncidence (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := pathLoad n
  map_add' := pathLoad_add n
  map_smul' := pathLoad_smul n

/-- Coordinate sum, i.e. total integer charge. -/
def totalCharge {ι : Type*} [Fintype ι] (v : ι → ℤ) : ℤ := ∑ i, v i

@[simp] theorem totalCharge_add {ι : Type*} [Fintype ι] (u v : ι → ℤ) :
    totalCharge (u + v) = totalCharge u + totalCharge v := by
  simp [totalCharge, Finset.sum_add_distrib]

@[simp] theorem totalCharge_sub {ι : Type*} [Fintype ι] (u v : ι → ℤ) :
    totalCharge (u - v) = totalCharge u - totalCharge v := by
  simp [totalCharge, Finset.sum_sub_distrib]

@[simp] theorem totalCharge_smul {ι : Type*} [Fintype ι] (a : ℤ) (v : ι → ℤ) :
    totalCharge (a • v) = a * totalCharge v := by
  simp [totalCharge, Finset.mul_sum]

@[simp] theorem totalCharge_pathLoad (n : ℕ) (e : Fin n → ℤ) :
    totalCharge (pathLoad n e) = 0 := by
  induction n with
  | zero => simp [pathLoad, totalCharge]
  | succ n ih =>
      change (∑ i, Fin.cons (e 0)
        (fun j => pathLoad n (Fin.tail e) j - if j = 0 then e 0 else 0) i) = 0
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_sub_distrib]
      change e 0 + ((totalCharge (pathLoad n (Fin.tail e))) - _) = 0
      simp [ih]

/-- The path edge coefficients are uniquely determined by their divergence. -/
theorem pathLoad_injective (n : ℕ) : Function.Injective (pathLoad n) := by
  induction n with
  | zero => intro e f h; exact Subsingleton.elim _ _
  | succ n ih =>
      intro e f h
      have h0 : e 0 = f 0 := congrFun h 0
      have ht : pathLoad n (Fin.tail e) = pathLoad n (Fin.tail f) := by
        funext i
        have hi := congrFun h i.succ
        simp only [pathLoad, Fin.cons_succ, h0] at hi
        exact sub_left_inj.mp hi
      have he := ih ht
      funext i
      exact Fin.cases h0 (fun j => congrFun he j) i

/-- Every zero-sum integer vertex load has integral path edge coefficients. -/
theorem exists_pathLoad (n : ℕ) (v : Fin (n + 1) → ℤ)
    (hv : totalCharge v = 0) : ∃ e, pathLoad n e = v := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simpa [pathLoad, totalCharge] using hv.symm
  | succ n ih =>
      let w : Fin (n + 1) → ℤ := fun i => v i.succ + if i = 0 then v 0 else 0
      have hw : totalCharge w = 0 := by
        have hv' : v 0 + (∑ i : Fin (n + 1), v i.succ) = 0 := by
          simpa [totalCharge, Fin.sum_univ_succ] using hv
        simp only [w, totalCharge, Finset.sum_add_distrib]
        simpa [add_comm] using hv'
      obtain ⟨e, he⟩ := ih w hw
      refine ⟨Fin.cons (v 0) e, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pathLoad]
      · simp [pathLoad, he, w]

/-- V7 Lemma `tree-incidence-basis`, proved for the actual fixed rounding path. -/
theorem path_integral_basis (n : ℕ) (v : Fin (n + 1) → ℤ) :
    (∃! e, pathLoad n e = v) ↔ totalCharge v = 0 := by
  constructor
  · rintro ⟨e, rfl, _⟩
    exact totalCharge_pathLoad n e
  · intro h
    obtain ⟨e, he⟩ := exists_pathLoad n v h
    exact ⟨e, he, fun f hf => pathLoad_injective n (hf.trans he.symm)⟩

/-- Simultaneous injection at the first `q` vertices, exactly as in V7. -/
def injectionColumn (n q : ℕ) : Fin (n + 1) → ℤ :=
  fun i => if i.val < q then 1 else 0

theorem totalCharge_injectionColumn (n q : ℕ) (hq : q ≤ n + 1) :
    totalCharge (injectionColumn n q) = (q : ℤ) := by
  simp [totalCharge, injectionColumn, Fin.card_filter_val_lt,
    Nat.min_eq_right hq]

/-- The fixed rounding matrix applied to path coordinates and the injection coordinate. -/
def roundingLoad (n : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ℤ) × ℤ) : Fin (n + 1) → ℤ :=
  pathLoad n x.1 + x.2 • c

/-- V7's image lattice characterization, with any injection column of total charge `q`. -/
theorem rounding_image_lattice (n : ℕ) (q : ℤ) (c : Fin (n + 1) → ℤ)
    (hc : totalCharge c = q) (v : Fin (n + 1) → ℤ) :
    (∃ x, roundingLoad n c x = v) ↔ q ∣ totalCharge v := by
  constructor
  · rintro ⟨⟨e, a⟩, rfl⟩
    simp only [roundingLoad, totalCharge_add, totalCharge_pathLoad, totalCharge_smul, hc, zero_add]
    exact dvd_mul_left q a
  · rintro ⟨a, ha⟩
    have hw : totalCharge (v - a • c) = 0 := by
      rw [totalCharge_sub, totalCharge_smul, hc, ha]
      ring
    obtain ⟨e, he⟩ := exists_pathLoad n (v - a • c) hw
    refine ⟨(e, a), ?_⟩
    simp [roundingLoad, he]



end AFT

namespace AFT

/-- The root lattice of integer zero-sum loads. -/
def zeroSumLattice (n : ℕ) : Submodule ℤ (Fin (n + 1) → ℤ) where
  carrier := {v | totalCharge v = 0}
  zero_mem' := by simp [totalCharge]
  add_mem' := by intro u v hu hv; simpa using (totalCharge_add u v).trans (by rw [hu, hv]; rfl)
  smul_mem' := by
    intro a v hv
    change totalCharge v = 0 at hv
    change totalCharge (a • v) = 0
    rw [totalCharge_smul, hv, mul_zero]

@[simp] theorem mem_zeroSumLattice (n : ℕ) (v : Fin (n + 1) → ℤ) :
    v ∈ zeroSumLattice n ↔ totalCharge v = 0 := Iff.rfl

/-- The path basis as an integral linear equivalence, with no graph hypothesis. -/
noncomputable def pathBasis (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n :=
  LinearEquiv.ofBijective
    ((pathIncidence n).codRestrict (zeroSumLattice n) (totalCharge_pathLoad n)) (by
      constructor
      · intro e f h
        exact pathLoad_injective n (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := exists_pathLoad n v hv
        exact ⟨e, Subtype.ext he⟩)

@[simp] theorem pathBasis_apply (n : ℕ) (e : Fin n → ℤ) :
    (pathBasis n e : Fin (n + 1) → ℤ) = pathLoad n e := rfl

/-- Divisibility lattice; for V7 this is the image of the rounding matrix. -/
def chargeLattice (n : ℕ) (q : ℤ) : Submodule ℤ (Fin (n + 1) → ℤ) where
  carrier := {v | q ∣ totalCharge v}
  zero_mem' := by simp [totalCharge]
  add_mem' := by intro u v hu hv; simpa using dvd_add hu hv
  smul_mem' := by
    intro a v hv
    change q ∣ totalCharge (a • v)
    rw [totalCharge_smul]
    exact dvd_mul_of_dvd_right hv a

@[simp] theorem mem_chargeLattice (n : ℕ) (q : ℤ) (v : Fin (n + 1) → ℤ) :
    v ∈ chargeLattice n q ↔ q ∣ totalCharge v := Iff.rfl

/-- Nonzero total injection makes the integer rounding map injective. -/
theorem roundingLoad_injective (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) :
    Function.Injective (roundingLoad n c) := by
  rintro ⟨e, a⟩ ⟨f, b⟩ h
  have hs := congrArg totalCharge h
  simp only [roundingLoad, totalCharge_add, totalCharge_pathLoad, totalCharge_smul,
    hc, zero_add] at hs
  have hab : a = b := mul_right_cancel₀ hq hs
  subst b
  have hef : pathLoad n e = pathLoad n f := add_right_cancel h
  exact Prod.ext (pathLoad_injective n hef) rfl

/-- The rounding map is an integral coordinate isomorphism onto its image lattice.
Its inverse supplies the integral preimage used in V7, without rational inverses. -/
noncomputable def roundingCoordinates (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) :
    ((Fin n → ℤ) × ℤ) ≃ₗ[ℤ] chargeLattice n q :=
  LinearEquiv.ofBijective
    ({ toFun := fun x => ⟨roundingLoad n c x, (rounding_image_lattice n q c hc _).1 ⟨x, rfl⟩⟩
       map_add' := by
         intro x y
         apply Subtype.ext
         change roundingLoad n c (x + y) = roundingLoad n c x + roundingLoad n c y
         simp only [roundingLoad, Prod.fst_add, Prod.snd_add, pathLoad_add, add_smul]
         abel
       map_smul' := by
         intro a x
         apply Subtype.ext
         change roundingLoad n c (a • x) = a • roundingLoad n c x
         simp only [roundingLoad, Prod.smul_fst, Prod.smul_snd, pathLoad_smul, smul_add, smul_smul, smul_eq_mul] } :
      ((Fin n → ℤ) × ℤ) →ₗ[ℤ] chargeLattice n q) (by
        constructor
        · intro x y h
          exact roundingLoad_injective n q hq c hc (congrArg Subtype.val h)
        · rintro ⟨v, hv⟩
          obtain ⟨x, hx⟩ := (rounding_image_lattice n q c hc v).2 hv
          exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem roundingCoordinates_apply (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q) (x : (Fin n → ℤ) × ℤ) :
    (roundingCoordinates n q hq c hc x : Fin (n + 1) → ℤ) = roundingLoad n c x := rfl

/-- Every admissible load has exactly one integral preimage. -/
theorem unique_integral_preimage (n : ℕ) (q : ℤ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = q)
    (v : Fin (n + 1) → ℤ) (hv : q ∣ totalCharge v) :
    ∃! x, roundingLoad n c x = v := by
  obtain ⟨x, hx⟩ := (rounding_image_lattice n q c hc v).2 hv
  exact ⟨x, hx, fun y hy => roundingLoad_injective n q hq c hc (hy.trans hx.symm)⟩

/-- Given a zero-sum basis `treeBasis`, change from those edge coordinates to path
coordinates. For a general tree, supplying `treeBasis` is the unproved graph bridge. -/
noncomputable def edgeBasisChange (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := treeBasis.trans (pathBasis n).symm

@[simp] theorem pathLoad_edgeBasisChange (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) (e : Fin n → ℤ) :
    pathLoad n (edgeBasisChange n treeBasis e) = (treeBasis e : Fin (n + 1) → ℤ) := by
  change ((pathBasis n) ((pathBasis n).symm (treeBasis e)) : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Explicit block-triangular transport. `B` is the edge-coordinate matrix, `U`
the integral basis change, and `a` the path preimage of the extension-column shift. -/
def blockTransport {R : Type*} [CommRing R] (n : ℕ)
    (U : (Fin n → R) ≃ₗ[R] (Fin n → R))
    (B : (Fin n → R) →ₗ[R] (Fin n → R)) (a : Fin n → R) :
    ((Fin n → R) × R) →ₗ[R] ((Fin n → R) × R) where
  toFun x := (U (B x.1) + x.2 • a, x.2)
  map_add' := by
    intro x y
    ext i <;> simp [add_smul, add_assoc, add_comm, add_left_comm]
  map_smul' := by
    intro r x
    ext i <;> simp [smul_add, smul_smul]





/-- Equal total charge of the original and extension columns provides the
integral correction vector used by `tree_transport_identity`. -/
theorem exists_extension_correction (n : ℕ) (c w : Fin (n + 1) → ℤ)
    (h : totalCharge w = totalCharge c) : ∃! a, pathLoad n a = w - c := by
  apply (path_integral_basis n (w - c)).2
  simp [h]

end AFT

namespace AFT

/-- Matrix of the triangular coordinate construction, indexed by edges plus one
injection coordinate. -/
def transportBlockMatrix {R : Type*} [CommRing R] (n : ℕ)
    (U B : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
  Matrix.fromBlocks (U * B) (fun i _ => a i) 0 1

/-- The extension-column correction does not change the transport determinant. -/
theorem det_transportBlockMatrix {R : Type*} [CommRing R] (n : ℕ)
    (U B : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    (transportBlockMatrix n U B a).det = U.det * B.det := by
  rw [transportBlockMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul]
  simp

/-- The matrix of an integral change of tree coordinates. -/
noncomputable def edgeBasisChangeMatrix (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
    (edgeBasisChange n treeBasis).toLinearMap

theorem edgeBasisChangeMatrix_det_unit (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n) :
    IsUnit (edgeBasisChangeMatrix n treeBasis).det :=
  (edgeBasisChange n treeBasis).isUnit_det _ _



/-- Reduction modulo a prime is invertible whenever the edge-coordinate
matrix has nonzero determinant modulo that prime. -/
theorem tree_transport_modular_invertible (n q : ℕ) [Fact q.Prime]
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℤ)
    (hB : (B.det : ZMod q) ≠ 0) :
    IsUnit ((transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a).map
      (Int.castRingHom (ZMod q))) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((Int.castRingHom (ZMod q)).mapMatrix
    (transportBlockMatrix n (edgeBasisChangeMatrix n treeBasis) B a)).det
  rw [← (Int.castRingHom (ZMod q)).map_det, det_transportBlockMatrix, map_mul]
  exact ((edgeBasisChangeMatrix_det_unit n treeBasis).map (Int.castRingHom (ZMod q))).mul
    (isUnit_iff_ne_zero.mpr hB)



end AFT

namespace AFT



end AFT

end

section








namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist





/-! # A finite fair-bit permutation sampler without enumerating permutations -/
namespace AFT.PermutationProgram
open scoped BigOperators

def choiceWeight (size : ℕ) : Fin (size+1) → ℚ := fun _ => ((size+1 : ℕ) : ℚ)⁻¹

theorem choiceWeight_nonneg (size : ℕ) (index : Fin (size+1)) : 0≤choiceWeight size index := by
  unfold choiceWeight
  positivity

theorem choiceWeight_sum (size : ℕ) : (∑ index,choiceWeight size index)=1 := by
  simp only [choiceWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

def choiceDraw (size bits : ℕ) : (Fin bits → Fin 2) → Fin (size+1) :=
  RationalFiniteQuantization.draw (choiceWeight size) (choiceWeight_nonneg size) (choiceWeight_sum size) bits

/-- Insert one newly drawn image, then permute the remaining positions.
There are exactly count recursive stages, each using bits fresh fair bits. -/
def rows (bits : ℕ) : (count : ℕ) → (Fin count → Fin bits → Fin 2) → Equiv.Perm (Fin count)
  | 0,_ => Equiv.refl _
  | count+1,word => Equiv.Perm.decomposeFin.symm (choiceDraw count bits (word 0),rows bits count (Fin.tail word))

def draw (count bits : ℕ) (word : Fin (count*bits) → Fin 2) : Equiv.Perm (Fin count) :=
  rows bits count (FiniteConditionProgram.groupBits count bits word)

noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false









def choiceLaw (size bits : ℕ) : FiniteDist (Fin (size+1)) :=
  (uniform (Fin bits → Fin 2)).map (choiceDraw size bits)



def permutationLaw (count bits : ℕ) : FiniteDist (Equiv.Perm (Fin count)) :=
  (uniform (Fin count → Fin bits → Fin 2)).map (rows bits count)







end
end AFT.PermutationProgram

end

section











/-! # Counted integer implementation of permutation insertion choices

The count table is computed using one integer quotient and one remainder.
Earlier permutation stages are stored, not sampled again. Arithmetic work
and all ticket sizes have explicit bounds; no list of permutations is built.
-/
namespace AFT.PermutationProgram
open BetaReference
open scoped BigOperators

/-- Integer-only form of the quantized uniform choice table. -/
def uniformCounts (size tickets : ℕ) (index : Fin (size+1)) : ℕ :=
  tickets/(size+1)+if index=0 then tickets%(size+1) else 0

theorem uniformCounts_eq (size tickets : ℕ) :
    uniformCounts size tickets=RationalFiniteQuantization.counts (choiceWeight size) tickets := by
  have hf (index : Fin (size+1)) :
      RationalFiniteQuantization.floorCount (choiceWeight size) tickets index=tickets/(size+1) := by
    simp only [RationalFiniteQuantization.floorCount,choiceWeight,← div_eq_mul_inv,Nat.floor_div_natCast,Nat.floor_natCast]
  have hd : RationalFiniteQuantization.deficit (choiceWeight size) tickets=tickets%(size+1) := by
    simp only [RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,hf,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change tickets-(size+1)*(tickets/(size+1))=tickets%(size+1)
    have hh := Nat.mod_add_div tickets (size+1)
    omega
  funext index
  simp only [uniformCounts,RationalFiniteQuantization.counts,hf,hd]

def powerTwo : ℕ → CountedNatural
  | 0 => ⟨1,0⟩
  | bits+1 => let previous := powerTwo bits; ⟨2*previous.value,previous.work+1⟩

@[simp] theorem powerTwo_value (bits : ℕ) : (powerTwo bits).value=2^bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwo,ih,pow_succ']

@[simp] theorem powerTwo_work (bits : ℕ) : (powerTwo bits).work=bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwo,ih]

def bitValue : (bits : ℕ) → (Fin bits → Fin 2) → CountedNatural
  | 0,_ => ⟨0,0⟩
  | bits+1,word =>
      let previous := bitValue bits (Fin.tail word)
      ⟨(word 0).val+2*previous.value,previous.work+2⟩

theorem bitValue_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitValue bits word).value=(FiniteTicketSampler.bitTicket bits word).val := by
  rw [FiniteTicketSampler.bitTicket_value]
  induction bits with
  | zero => simp [bitValue]
  | succ bits ih =>
    simp only [bitValue,ih,Fin.sum_univ_succ,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    simp only [Fin.tail]
    ring

@[simp] theorem bitValue_work (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitValue bits word).work=2*bits := by
  induction bits with
  | zero => simp [bitValue]
  | succ bits ih => simp only [bitValue,ih]; omega

def countedBucket : List ℕ → ℕ → CountedNatural
  | [],_ => ⟨0,0⟩
  | count::rest,ticket =>
      if ticket<count then ⟨0,1⟩ else
        let next := countedBucket rest (ticket-count)
        ⟨1+next.value,next.work+3⟩

theorem countedBucket_value (counts : List ℕ) (ticket : ℕ) :
    (countedBucket counts ticket).value=FiniteTicketSampler.bucket counts ticket := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons count rest ih => simp only [countedBucket,FiniteTicketSampler.bucket];split_ifs <;> simp [ih]



/-- Quotient/remainder and the dyadic ticket are materialized once. Each
list entry costs a comparison and an addition. -/
def countedChoice (size bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let tickets := powerTwo bits
  let ticket := bitValue bits word
  let quotient := tickets.value/(size+1)
  let remainder := tickets.value%(size+1)
  let counts := List.ofFn (fun index : Fin (size+1) => quotient+if index=0 then remainder else 0)
  let selected := countedBucket counts ticket.value
  ⟨selected.value,tickets.work+ticket.work+2*(size+1)+selected.work+3⟩

theorem countedChoice_value (size bits : ℕ) (word : Fin bits → Fin 2) :
    (countedChoice size bits word).value=(choiceDraw size bits word).val := by
  simp only [countedChoice,powerTwo_value,bitValue_value,countedBucket_value]
  change FiniteTicketSampler.bucket (List.ofFn (uniformCounts size (2^bits))) _=_
  rw [uniformCounts_eq]
  rfl



def countedChoiceFin (size bits : ℕ) (word : Fin bits → Fin 2) : Fin (size+1) :=
  ⟨(countedChoice size bits word).value,by rw [countedChoice_value];exact (choiceDraw size bits word).isLt⟩

@[simp] theorem countedChoiceFin_eq (size bits : ℕ) (word : Fin bits → Fin 2) :
    countedChoiceFin size bits word=choiceDraw size bits word := Fin.ext (countedChoice_value size bits word)

structure CountedPermutation (count : ℕ) where
  value : Equiv.Perm (Fin count)
  work : ℕ











end AFT.PermutationProgram

end

section









/-! Linear-time construction of powers of two and direct reading of a fair
bit tape into little-endian digits. There is no enumeration of its values. -/
namespace AFT.BinaryArithmetic

def powerTwoDigits : ℕ → Result
  | 0 => ⟨[true],2⟩
  | bits+1 => let previous := powerTwoDigits bits;⟨false::previous.digits,previous.work+2⟩

theorem powerTwoDigits_value (bits : ℕ) : value (powerTwoDigits bits).digits=2^bits := by
  induction bits with
  | zero => simp [powerTwoDigits,value]
  | succ bits ih => simp only [powerTwoDigits,value,Bool.toNat_false,Nat.zero_add,ih,pow_succ']





def digitBoolean (digit : Fin 2) : Bool := decide (digit.val=1)

theorem digitBoolean_value (digit : Fin 2) : (digitBoolean digit).toNat=digit.val := by
  fin_cases digit <;> rfl

/-- Each input bit is read exactly once in increasing position order. -/
def readBitTape : (bits : ℕ) → (Fin bits → Fin 2) → Result
  | 0,_ => ⟨[],2⟩
  | bits+1,word =>
      let previous := readBitTape bits (Fin.tail word)
      ⟨digitBoolean (word 0)::previous.digits,previous.work+3⟩

theorem readBitTape_value (bits : ℕ) (word : Fin bits → Fin 2) :
    value (readBitTape bits word).digits=(FiniteTicketSampler.bitTicket bits word).val := by
  rw [← PermutationProgram.bitValue_value]
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [readBitTape,value,digitBoolean_value,ih,PermutationProgram.bitValue]





end AFT.BinaryArithmetic

end

section




/-! # Converting bounded loop counters into binary digits

The input is a unary loop counter. Each successor calls the actual ripple
adder; no whole-integer arithmetic is used in the digit result. The bound
is deliberately polynomial in the counter's value. In finite Gaussian
series the counters themselves are polynomially bounded in the dimension.
This is not a claim of polynomial time in the bit length of an arbitrary
unbounded integer.
-/
namespace AFT.BinaryArithmetic

def counterDigits : ℕ → Result
  | 0 => ⟨[],2⟩
  | count+1 =>
      let previous := counterDigits count
      let next := add false previous.digits [true]
      ⟨next.digits,previous.work+next.work+3⟩

theorem counterDigits_value (count : ℕ) : value (counterDigits count).digits=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [counterDigits,add_value,value,Bool.toNat_true,Bool.toNat_false,ih]

theorem counterDigits_length (count : ℕ) : (counterDigits count).digits.length≤ 2*count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hh := add_length (counterDigits count).digits [true] false
      simp only [counterDigits,List.length_cons,List.length_nil] at hh ⊢
      omega

theorem counterDigits_work (count : ℕ) : (counterDigits count).work≤ 40*(count+1)^2 := by
  induction count with
  | zero => norm_num [counterDigits]
  | succ count ih =>
      have hl := counterDigits_length count
      have hm : max (counterDigits count).digits.length 1≤ 2*count+1 := by omega
      simp only [counterDigits,add_work,List.length_cons,List.length_nil,Nat.zero_add]
      nlinarith

/-- The normalized result is ready for canonical rational construction. -/
def canonicalCounter (count : ℕ) : Result :=
  let raw := counterDigits count
  let normalized := normalize raw.digits
  ⟨normalized.digits,raw.work+normalized.work+2⟩

theorem canonicalCounter_value (count : ℕ) : value (canonicalCounter count).digits=count := by
  simp only [canonicalCounter,normalize_value,counterDigits_value]

theorem canonicalCounter_length (count : ℕ) : (canonicalCounter count).digits.length=count.size := by
  simp only [canonicalCounter,normalize_length,counterDigits_value]

theorem canonicalCounter_work (count : ℕ) : (canonicalCounter count).work≤ 50*(count+1)^2 := by
  have hw := counterDigits_work count
  have hl := counterDigits_length count
  simp only [canonicalCounter,normalize_work]
  nlinarith

end AFT.BinaryArithmetic

end

section







/-! # Polynomial iteration lengths for the actual root Gaussian program

These bounds describe the finite series lengths and integer exponents of the
executable rational program. They do not identify rational arithmetic with
constant-cost machine operations.
-/

namespace AFT.RationalNumerics

open scoped BigOperators

def gaussianPiPrecision (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  bits + gaussianGuard squaredWidth point + 1

def gaussianExpScale (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  expScale (piApprox (gaussianPiPrecision squaredWidth point bits) *
    gaussianRatio squaredWidth point)

def gaussianTaylorTerms (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  bits + gaussianExpScale squaredWidth point bits + 2



noncomputable section

















end
end AFT.RationalNumerics

end

section







/-! # Binary heights of the actual finite pi and exponential series -/
namespace AFT.RationalNumerics
open scoped BigOperators





def piHeight (bits : ℕ) : ℕ := 2*((bits+3)*(6*(bits+3)+4))+3











end AFT.RationalNumerics

end

section











/-! Powers, factorials, and finite sums on actual canonical binary rationals. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

def one : RationalBits := ⟨false,[true],[true],by decide,by decide,by decide,by decide⟩
def minusOne : RationalBits := ⟨true,[true],[true],by decide,by decide,by decide,by decide⟩
def half : RationalBits := ⟨false,[true],[false,true],by decide,by decide,by decide,by decide⟩
def third : RationalBits := ⟨false,[true],[true,true],by decide,by decide,by decide,by decide⟩
def four : RationalBits := ⟨false,[false,false,true],[true],by decide,by decide,by decide,by decide⟩

@[simp] theorem one_value : one.decode=1 := by decide
@[simp] theorem minusOne_value : minusOne.decode=(-1 : ℚ) := by decide
@[simp] theorem half_value : half.decode=(1/2 : ℚ) := by rw [decode_fraction];norm_num [half,signedValue,value]
@[simp] theorem third_value : third.decode=(1/3 : ℚ) := by rw [decode_fraction];norm_num [third,signedValue,value]
@[simp] theorem four_value : four.decode=(4 : ℚ) := by decide



def quotient (first second : RationalBits) : RationalResult :=
  let inv := inverse second
  let result := multiply first inv.data
  ⟨result.data,inv.work+result.work+2⟩

theorem quotient_value (first second : RationalBits) :
    (quotient first second).data.decode=first.decode/second.decode := by
  simp only [quotient,multiply_value,inverse_value,div_eq_mul_inv]



/-- The natural here is a polynomially bounded unary loop counter. Its
rational value is constructed by the actual binary counter, not a cast. -/
def ofCounter (count : ℕ) : RationalResult :=
  let counter := canonicalCounter count
  let result := ofNat counter.digits
  ⟨result.data,counter.work+result.work+2⟩

theorem ofCounter_value (count : ℕ) : (ofCounter count).data.decode=(count : ℚ) := by
  simp only [ofCounter,ofNat_value,canonicalCounter_value]



def power (input : RationalBits) : ℕ → RationalResult
  | 0 => ⟨one,2⟩
  | count+1 =>
    let previous := power input count
    let result := multiply previous.data input
    ⟨result.data,previous.work+result.work+2⟩

theorem power_value (input : RationalBits) (count : ℕ) : (power input count).data.decode=input.decode^count := by
  induction count with
  | zero => simp [power]
  | succ count ih => simp only [power,multiply_value,ih,pow_succ]





def factorial : ℕ → RationalResult
  | 0 => ⟨one,2⟩
  | count+1 =>
    let previous := factorial count
    let coefficient := ofCounter (count+1)
    let result := multiply coefficient.data previous.data
    ⟨result.data,previous.work+coefficient.work+result.work+2⟩

theorem factorial_value (count : ℕ) : (factorial count).data.decode=(count.factorial : ℚ) := by
  induction count with
  | zero => simp [factorial]
  | succ count ih => simp only [factorial,multiply_value,ofCounter_value,ih,Nat.factorial_succ,Nat.cast_mul]

def factorialWorkStep (limit : ℕ) : ℕ := 60*(limit+2)^2+primitiveWorkBound ((limit+1)^2)+2



def sumRange (term : ℕ → RationalResult) : ℕ → RationalResult
  | 0 => ⟨zero,2⟩
  | count+1 =>
    let previous := sumRange term count
    let next := term count
    let result := add previous.data next.data
    ⟨result.data,previous.work+next.work+result.work+2⟩

theorem sumRange_value (term : ℕ → RationalResult) (count : ℕ) :
    (sumRange term count).data.decode=∑ index∈Finset.range count,(term index).data.decode := by
  induction count with
  | zero => simp [sumRange]
  | succ count ih => simp only [sumRange,add_value,ih,Finset.sum_range_succ]



end AFT.BinaryArithmetic.RationalBits

end

section




/-! # Proposal approximation propagates through a finite rejection loop -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]

def rejectionKernel (coin : State → ℝ) (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1)
    (remaining : FiniteDist State) (point : State) : FiniteDist State where
  weight output := (if point=output then coin point else 0)+(1-coin point)*remaining.weight output
  nonneg output := add_nonneg (by split_ifs; exact (hcoin point).1; rfl)
    (mul_nonneg (by linarith [(hcoin point).2]) (remaining.nonneg output))
  sum_one := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,remaining.sum_one,mul_one]
    simp







end
end AFT.FiniteDist

end

section





namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! # Executable acceptance coins from rational score approximations

All executable definitions use rational or integer arithmetic. Approximating
the actual real score is a separate obligation, not a real-floor oracle.
-/
namespace AFT.RationalAcceptanceCoin
open scoped BigOperators

/-- Clipping a rational approximation ensures a legal acceptance coin. -/
def clipped (value : ℚ) : ℚ := min 1 (max value 0)

theorem clipped_bounds (value : ℚ) : 0 ≤ clipped value ∧ clipped value ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_right _ _),min_le_left _ _⟩

def count (bits : ℕ) (value : ℚ) : ℕ := ⌊(2^bits : ℚ)*clipped value⌋₊

theorem count_le (bits : ℕ) (value : ℚ) : count bits value ≤ 2^bits := by
  have hh := Nat.floor_le (mul_nonneg (by positivity : (0 : ℚ) ≤ 2^bits) (clipped_bounds value).1)
  have hmul := mul_le_mul_of_nonneg_left (clipped_bounds value).2 (by positivity : (0 : ℚ) ≤ 2^bits)
  have hc : (count bits value : ℚ) ≤ (2^bits : ℕ) := by
    simpa only [count,mul_one,Nat.cast_pow,Nat.cast_ofNat] using hh.trans hmul
  exact_mod_cast hc

def counts (bits : ℕ) (value : ℚ) : Fin 2 → ℕ := ![count bits value,2^bits-count bits value]

theorem counts_total (bits : ℕ) (value : ℚ) : ∑ i,counts bits value i=2^bits := by
  have hc := count_le bits value
  simp only [counts,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  omega

/-- Output zero means acceptance. The procedure consumes exactly `bits`
fair bits and performs rational rounding followed by integer table selection. -/
def draw (bits : ℕ) (value : ℚ) (word : Fin bits → Fin 2) : Fin 2 :=
  FiniteTicketSampler.drawBitTable bits (counts bits value) (counts_total bits value) word

noncomputable section

def probability (bits : ℕ) (value : ℚ) : ℝ := (count bits value : ℝ)/(2 : ℝ)^bits













end
end AFT.RationalAcceptanceCoin

end

section









/-! Binary floor and clipping, for executable dyadic probability tables. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def floorNatural (input : RationalBits) : Result :=
  if input.negative then ⟨[],2⟩ else
    let division := divide input.numerator input.denominator
    let result := normalize division.quotient
    ⟨result.digits,division.work+result.work+3⟩

theorem floorNatural_value (input : RationalBits) : value (floorNatural input).digits=⌊input.decode⌋₊ := by
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      simp only [floorNatural,hs,ite_true,value,Nat.floor_of_nonpos hn]
  | false =>
      have hq := (divide_value input.numerator input.denominator input.denominator_positive).1
      rw [decode_fraction]
      simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast,Rat.natFloor_natCast_div_natCast,
        floorNatural,normalize_value,hq]









/-- Clipping tests the numerator against the denominator by borrow. -/
def clipUnit (input : RationalBits) : RationalResult :=
  if input.negative then ⟨zero,2⟩ else
    let comparison := subtract false input.numerator input.denominator
    ⟨if comparison.borrow then input else one,comparison.work+3⟩







end AFT.BinaryArithmetic.RationalBits

end

section









/-! Actual binary dyadic rounding. The exponential-size ticket count is
stored as a linear-length binary list and is never expanded into unary. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def dyadicPower (bits : ℕ) : RationalResult :=
  let digits := powerTwoDigits bits
  let result := ofNat digits.digits
  ⟨result.data,digits.work+result.work+2⟩

theorem dyadicPower_value (bits : ℕ) : (dyadicPower bits).data.decode=(2 : ℚ)^bits := by
  simp only [dyadicPower,ofNat_value,powerTwoDigits_value,Nat.cast_pow,Nat.cast_ofNat]





def dyadicFloor (input : RationalBits) (bits : ℕ) : Result :=
  let power := dyadicPower bits
  let scaled := multiply power.data input
  let floored := floorNatural scaled.data
  ⟨floored.digits,power.work+scaled.work+floored.work+3⟩

theorem dyadicFloor_value (input : RationalBits) (bits : ℕ) :
    value (dyadicFloor input bits).digits=⌊(2 : ℚ)^bits*input.decode⌋₊ := by
  simp only [dyadicFloor,floorNatural_value,multiply_value,dyadicPower_value]



def dyadicFloorWork (height bits : ℕ) : ℕ :=
  1000*(bits+height+2)^2+primitiveWorkBound (bits+height)+6*bits+16



end AFT.BinaryArithmetic.RationalBits

end

section







/-! # The actual binary acceptance coin

The program reads exactly the prescribed fair bits, clips and rounds the
encoded rational score, and decides acceptance by one binary borrow test.
It is pointwise identical to the earlier rational acceptance sampler.
-/
namespace AFT.BinaryArithmetic
open RationalNumerics PermutationProgram BetaReference



def binaryAcceptance (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let clipped := input.clipUnit
  let accepted := clipped.data.dyadicFloor bits
  let ticket := readBitTape bits word
  let comparison := subtract false ticket.digits accepted.digits
  ⟨if comparison.borrow then 0 else 1,
    clipped.work+accepted.work+ticket.work+comparison.work+4⟩



def binaryAcceptanceWork (height bits : ℕ) : ℕ :=
  RationalBits.dyadicFloorWork height bits+50*(height+bits+1)+20



end AFT.BinaryArithmetic

end

section




/-!
# Constructive tree incidence bases and the lobster architecture

A `GrowingTree n` is built from one vertex by `n` operations, each adjoining a
new leaf and connecting it to an explicitly chosen existing vertex. The new
vertex and edge receive index zero; all old indices shift by one. This is a
concrete combinatorial construction, not a structure assuming a basis theorem.
The integral basis is proved by leaf elimination. In particular the explicit
lobster builder below closes the tree-to-basis bridge for V7's architecture.
-/

namespace AFT

open scoped BigOperators

/-- A tree with `n` edges and `n+1` vertices, encoded by successive leaf additions. -/
inductive GrowingTree : ℕ → Type
  | root : GrowingTree 0
  | attach {n : ℕ} (previous : GrowingTree n) (parent : Fin (n + 1)) : GrowingTree (n + 1)

namespace GrowingTree







/-- Signed incidence applied to integer edge coefficients. -/
def load : {n : ℕ} → GrowingTree n → (Fin n → ℤ) → (Fin (n + 1) → ℤ)
  | 0, .root, _ => 0
  | _ + 1, .attach t parent, e => Fin.cons (e 0)
      (fun i => load t (Fin.tail e) i - if i = parent then e 0 else 0)

@[simp] theorem load_zero {n : ℕ} (t : GrowingTree n) : load t 0 = 0 := by
  induction t with
  | root => rfl
  | @attach n t parent ih =>
      have ht : Fin.tail (0 : Fin (n + 1) → ℤ) = 0 := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp [load, ht, ih]

@[simp] theorem load_add {n : ℕ} (t : GrowingTree n) (e f : Fin n → ℤ) :
    load t (e + f) = load t e + load t f := by
  induction t with
  | root => rfl
  | @attach n t parent ih =>
      have ht : Fin.tail (e + f) = Fin.tail e + Fin.tail f := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp only [load, Fin.cons_succ, ht, ih, Pi.add_apply]
        split_ifs <;> ring

@[simp] theorem load_smul {n : ℕ} (t : GrowingTree n) (a : ℤ) (e : Fin n → ℤ) :
    load t (a • e) = a • load t e := by
  induction t with
  | root => simp [load]
  | @attach n t parent ih =>
      have ht : Fin.tail (a • e) = a • Fin.tail e := rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp only [load, Fin.cons_succ, ht, ih, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring

/-- Integral signed incidence as a linear map. -/
def incidence {n : ℕ} (t : GrowingTree n) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := load t
  map_add' := load_add t
  map_smul' := load_smul t

@[simp] theorem totalCharge_load {n : ℕ} (t : GrowingTree n) (e : Fin n → ℤ) :
    totalCharge (load t e) = 0 := by
  induction t with
  | root => simp [load, totalCharge]
  | @attach n t parent ih =>
      change (∑ i, Fin.cons (e 0)
        (fun j => load t (Fin.tail e) j - if j = parent then e 0 else 0) i) = 0
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_sub_distrib]
      change e 0 + (totalCharge (load t (Fin.tail e)) - _) = 0
      simp [ih]

/-- Uniqueness of edge coefficients follows by eliminating the newest leaf. -/
theorem load_injective {n : ℕ} (t : GrowingTree n) : Function.Injective (load t) := by
  induction t with
  | root => intro e f h; exact Subsingleton.elim _ _
  | @attach n t parent ih =>
      intro e f h
      have h0 : e 0 = f 0 := congrFun h 0
      have ht : load t (Fin.tail e) = load t (Fin.tail f) := by
        funext i
        have hi := congrFun h i.succ
        simp only [load, Fin.cons_succ, h0] at hi
        exact sub_left_inj.mp hi
      have he := ih ht
      funext i
      exact Fin.cases h0 (fun j => congrFun he j) i

/-- Existence of integral edge coefficients follows by the same leaf elimination. -/
theorem exists_load {n : ℕ} (t : GrowingTree n) (v : Fin (n + 1) → ℤ)
    (hv : totalCharge v = 0) : ∃ e, load t e = v := by
  induction t with
  | root =>
      refine ⟨0, ?_⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simpa [load, totalCharge] using hv.symm
  | @attach n t parent ih =>
      let w : Fin (n + 1) → ℤ := fun i => v i.succ + if i = parent then v 0 else 0
      have hw : totalCharge w = 0 := by
        have hv' : v 0 + (∑ i : Fin (n + 1), v i.succ) = 0 := by
          simpa [totalCharge, Fin.sum_univ_succ] using hv
        simp only [w, totalCharge, Finset.sum_add_distrib]
        simpa [add_comm] using hv'
      obtain ⟨e, he⟩ := ih w hw
      refine ⟨Fin.cons (v 0) e, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [load]
      · simp [load, he, w]



/-- The basis interface consumed by the transport construction, now proved
from explicit leaf attachments rather than supplied as a hypothesis. -/
noncomputable def basis {n : ℕ} (t : GrowingTree n) :
    (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n :=
  LinearEquiv.ofBijective
    ((incidence t).codRestrict (zeroSumLattice n) (totalCharge_load t)) (by
      constructor
      · intro e f h
        exact load_injective t (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := exists_load t v hv
        exact ⟨e, Subtype.ext he⟩)

@[simp] theorem basis_apply {n : ℕ} (t : GrowingTree n) (e : Fin n → ℤ) :
    (basis t e : Fin (n + 1) → ℤ) = load t e := rfl

/-- A body path with `n+1` vertices, built by attaching at its current first vertex. -/
def path : (n : ℕ) → GrowingTree n
  | 0 => root
  | n + 1 => attach (path n) 0

/-- The body construction is exactly the path incidence used by the fixed rounding map. -/
@[simp] theorem load_path (n : ℕ) (e : Fin n → ℤ) : load (path n) e = pathLoad n e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [load, path, pathLoad, ih]













end GrowingTree
end AFT

namespace AFT.GrowingTree











end AFT.GrowingTree

end

section




/-! # The actual path incidence has the quantitative bounds of V7 Lemma 7.1

The bounds are established on the real incidence map, using adjacent
coordinates for the upper bound and exact prefix recovery for the lower.
-/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The incidence of the consistently oriented path, including both endpoints. -/
def realPath {edges : ℕ} (input : Fin edges → ℝ) : Fin (edges+1) → ℝ :=
  Fin.snoc input 0-Fin.cons 0 input

















end
end AFT.BodyPadding

end

section








/-! # Actual path Gram matrix and the conditional covariance of body padding -/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix

def pathLinear (edges : ℕ) : (Fin edges → ℝ) →ₗ[ℝ] (Fin (edges+1) → ℝ) where
  toFun := realPath
  map_add' first second := by
    funext vertex
    have hs : (Fin.snoc (first+second) (0 : ℝ) : Fin (edges+1) → ℝ) vertex=(Fin.snoc first (0 : ℝ) : Fin (edges+1) → ℝ) vertex+(Fin.snoc second (0 : ℝ) : Fin (edges+1) → ℝ) vertex := by
      refine Fin.lastCases ?_ (fun vertex => ?_) vertex <;> simp
    have hc : (Fin.cons (0 : ℝ) (first+second) : Fin (edges+1) → ℝ) vertex=(Fin.cons (0 : ℝ) first : Fin (edges+1) → ℝ) vertex+(Fin.cons (0 : ℝ) second : Fin (edges+1) → ℝ) vertex := by
      refine Fin.cases ?_ (fun vertex => ?_) vertex <;> simp
    dsimp only [realPath,Pi.sub_apply,Pi.add_apply]
    rw [hs,hc]
    ring
  map_smul' scalar input := by
    funext vertex
    have hs : (Fin.snoc (scalar • input) (0 : ℝ) : Fin (edges+1) → ℝ) vertex=scalar*(Fin.snoc input (0 : ℝ) : Fin (edges+1) → ℝ) vertex := by
      refine Fin.lastCases ?_ (fun vertex => ?_) vertex <;> simp
    have hc : (Fin.cons (0 : ℝ) (scalar • input) : Fin (edges+1) → ℝ) vertex=scalar*(Fin.cons (0 : ℝ) input : Fin (edges+1) → ℝ) vertex := by
      refine Fin.cases ?_ (fun vertex => ?_) vertex <;> simp
    dsimp only [realPath,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [hs,hc]
    ring

def pathMatrix (edges : ℕ) : Matrix (Fin (edges+1)) (Fin edges) ℝ :=
  LinearMap.toMatrix' (pathLinear edges)



@[simp] theorem pathMatrix_mulVec (edges : ℕ) (input : Fin edges → ℝ) :
    (pathMatrix edges).mulVec input=realPath input :=
  LinearMap.toMatrix'_mulVec (pathLinear edges) input





















end
end AFT.BodyPadding

end

section






/-! # Quantitative inverse bounds for the actual path Gram matrix -/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix

theorem pathMatrix_apply (edges : ℕ) (vertex : Fin (edges+1)) (edge : Fin edges) :
    pathMatrix edges vertex edge=
      (if vertex=edge.castSucc then 1 else 0)-(if vertex=edge.succ then 1 else 0) := by
  change realPath (Pi.single edge 1) vertex=_
  have hs : (Fin.snoc (Pi.single edge (1 : ℝ)) 0 : Fin (edges+1) → ℝ) vertex=
      if vertex=edge.castSucc then 1 else 0 := by
    refine Fin.lastCases ?_ (fun other => ?_) vertex
    · simp [ne_of_gt (Fin.castSucc_lt_last edge)]
    · simp [Pi.single_apply]
  have hc : (Fin.cons 0 (Pi.single edge (1 : ℝ)) : Fin (edges+1) → ℝ) vertex=
      if vertex=edge.succ then 1 else 0 := by
    refine Fin.cases ?_ (fun other => ?_) vertex
    · simp [Ne.symm (Fin.succ_ne_zero edge)]
    · simp [Pi.single_apply]
  exact congrArg₂ (·-·) hs hc

@[simp] theorem pathTranspose_mulVec (edges : ℕ) (input : Fin (edges+1) → ℝ) (edge : Fin edges) :
    ((pathMatrix edges)ᴴ.mulVec input) edge=input edge.castSucc-input edge.succ := by
  simp only [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,star_trivial,pathMatrix_apply,
    sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]




















end
end AFT.BodyPadding

end

section












/-! # Actual countable source laws through finite physical output channels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source Output : Type*} [Fintype Output]

 theorem weight_le_one (law : FiniteDist Output) (output : Output) : law.weight output ≤ 1 := by
  rw [← law.sum_one]
  exact Finset.single_le_sum (fun point _ => law.nonneg point) (Finset.mem_univ output)

 theorem countable_channel_summable (mass : Source → ℝ)
    (hmass : Summable mass) (channel : Source → FiniteDist Output) (output : Output) :
    Summable (fun source => mass source*(channel source).weight output) := by
  apply Summable.of_norm_bounded hmass.norm
  intro source
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel source).nonneg output)]
  exact mul_le_of_le_one_right (abs_nonneg _) (weight_le_one _ _)

/-- A genuine normalized finite output law for an unbounded integer source. -/
def countableMix (mass : Source → ℝ) (hnonneg : ∀ source,0 ≤ mass source)
    (hsum : Summable mass) (hone : ∑' source,mass source=1)
    (channel : Source → FiniteDist Output) : FiniteDist Output where
  weight output := ∑' source,mass source*(channel source).weight output
  nonneg output := tsum_nonneg fun source => mul_nonneg (hnonneg source) ((channel source).nonneg output)
  sum_one := by
    rw [← tsum_fintype (L := .unconditional Output) (f := fun output : Output => ∑' source,mass source*(channel source).weight output)]
    have hs : Summable (fun point : Output × Source => mass point.2*(channel point.2).weight point.1) := by
      exact (summable_prod_of_nonneg (fun point => mul_nonneg (hnonneg point.2) ((channel point.2).nonneg point.1))).mpr
        ⟨fun output => countable_channel_summable mass hsum channel output,(hasSum_fintype _).summable⟩
    rw [← Summable.tsum_comm hs]
    simp only [tsum_fintype,← Finset.mul_sum,FiniteDist.sum_one,mul_one,hone]





end
end AFT.FiniteDist

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier



/-! # Executable Gaussian weights at arbitrary rational centers

The denominator of the rational center is cleared exactly. The resulting
program calls the proved rational pi/exponential routine; it does not
invoke a real floor, square root, or Gaussian oracle.
-/
namespace AFT.RationalNumerics

/-- Clearing the center denominator retains the squared width exactly. -/
def centeredGaussianSquaredWidth (squaredWidth center : ℚ) : ℚ :=
  squaredWidth*(center.den : ℚ)^2

def centeredGaussianNumerator (center : ℚ) (point : ℤ) : ℤ :=
  point*(center.den : ℤ)-center.num

def centeredGaussianApprox (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) : ℚ :=
  gaussianApprox (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits



noncomputable section
set_option backward.isDefEq.respectTransparency false













end
end AFT.RationalNumerics

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.convolutionPairsEquiv
end AFT.GaussianSource.convolutionPairsEquiv
namespace AFT.GaussianSource.convolutionProbability
end AFT.GaussianSource.convolutionProbability


/-! # Finite-dimensional triangular Gaussian sums from scalar Poisson bounds

The center of each scalar Gaussian may depend on every later integer
coordinate. Thus these are correlated elliptic Gaussian weights, rather
than a product-independence assumption.
-/
namespace AFT.GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Reverse conditional Gaussian coordinates. Triangular quadratic forms
are represented by linear choices of `center`; the summation theorem even
allows arbitrary dependence on the complete later vector. -/
inductive GaussianChain : ℕ → Type
  | nil : GaussianChain 0
  | cons {count : ℕ} (width : ℝ) (center : (Fin count → ℤ) → ℝ)
      (tail : GaussianChain count) : GaussianChain (count+1)

















end
end AFT.GaussianSource

end

section




















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.countableMix
end AFT.FiniteDist.countableMix
namespace AFT.FiniteDist.massOn
end AFT.FiniteDist.massOn
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.GaussianChain
end AFT.GaussianSource.GaussianChain
namespace AFT.GaussianSource.GaussianChain.localNormalizer
end AFT.GaussianSource.GaussianChain.localNormalizer
namespace AFT.GaussianSource.GaussianChain.sequentialMass
end AFT.GaussianSource.GaussianChain.sequentialMass
namespace AFT.GaussianSource.GaussianChain.sequentialMass.match_1
end AFT.GaussianSource.GaussianChain.sequentialMass.match_1
namespace AFT.GaussianSource.matrixGaussianChain
end AFT.GaussianSource.matrixGaussianChain
namespace AFT.GaussianSource.upperGaussianChain
end AFT.GaussianSource.upperGaussianChain
namespace AFT.GaussianSource.upperGaussianChain.match_1
end AFT.GaussianSource.upperGaussianChain.match_1
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.centeredGaussianWeights
end AFT.RationalNumerics.centeredGaussianWeights
namespace AFT.RationalNumerics.centeredRetainedWeight
end AFT.RationalNumerics.centeredRetainedWeight
namespace AFT.RationalNumerics.centeredScalarMass
end AFT.RationalNumerics.centeredScalarMass
namespace AFT.RationalNumerics.centeredTicketCounts
end AFT.RationalNumerics.centeredTicketCounts
namespace AFT.RationalNumerics.centeredTicketLaw
end AFT.RationalNumerics.centeredTicketLaw
namespace AFT.RationalNumerics.centeredWindowApproxLaw
end AFT.RationalNumerics.centeredWindowApproxLaw
namespace AFT.RationalNumerics.centeredWindowLaw
end AFT.RationalNumerics.centeredWindowLaw
namespace AFT.RationalNumerics.centeredWindowMass
end AFT.RationalNumerics.centeredWindowMass
namespace AFT.RationalNumerics.centeredWindowRaw
end AFT.RationalNumerics.centeredWindowRaw
namespace AFT.RationalNumerics.centeredWindowWeight
end AFT.RationalNumerics.centeredWindowWeight





/-! # Executable conditional scalar Gaussian chains

Centers are rational functions of already realized integer coordinates.
The actual upper-triangular matrix specialization uses just finite rational
sums. Every recursive tail is stored before its head is computed.
-/
namespace AFT.RationalNumerics
open GaussianSource Matrix
open scoped BigOperators

inductive RationalGaussianChain : ℕ → Type
  | nil : RationalGaussianChain 0
  | cons {count : ℕ} (squaredWidth : ℚ) (center : (Fin count → ℤ) → ℚ)
      (tail : RationalGaussianChain count) : RationalGaussianChain (count+1)







noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000









end
end AFT.RationalNumerics

end

section



















namespace AFT
end AFT
namespace AFT.BodyPadding
end AFT.BodyPadding
namespace AFT.BodyPadding.greenPrimitive
end AFT.BodyPadding.greenPrimitive
namespace AFT.BodyPadding.greenPrimitive_last
end AFT.BodyPadding.greenPrimitive_last
namespace AFT.BodyPadding.greenPrimitive_succ
end AFT.BodyPadding.greenPrimitive_succ
namespace AFT.BodyPadding.pathGram
end AFT.BodyPadding.pathGram
namespace AFT.BodyPadding.pathGram_green_column
end AFT.BodyPadding.pathGram_green_column
namespace AFT.BodyPadding.rationalBodyPaddingCovariance
end AFT.BodyPadding.rationalBodyPaddingCovariance
namespace AFT.BodyPadding.rationalPathGreen
end AFT.BodyPadding.rationalPathGreen
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.countableMix
end AFT.FiniteDist.countableMix
namespace AFT.FiniteDist.paddingCoordinates
end AFT.FiniteDist.paddingCoordinates
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.GaussianChain
end AFT.GaussianSource.GaussianChain
namespace AFT.GaussianSource.GaussianChain.localNormalizer
end AFT.GaussianSource.GaussianChain.localNormalizer
namespace AFT.GaussianSource.GaussianChain.sequentialMass
end AFT.GaussianSource.GaussianChain.sequentialMass
namespace AFT.GaussianSource.GaussianChain.sequentialMass.match_1
end AFT.GaussianSource.GaussianChain.sequentialMass.match_1
namespace AFT.GaussianSource.matrixGaussianChain
end AFT.GaussianSource.matrixGaussianChain
namespace AFT.GaussianSource.reverseIntegerWord
end AFT.GaussianSource.reverseIntegerWord
namespace AFT.GaussianSource.upperGaussianChain
end AFT.GaussianSource.upperGaussianChain
namespace AFT.GaussianSource.upperGaussianChain.match_1
end AFT.GaussianSource.upperGaussianChain.match_1
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
namespace AFT.RationalNumerics.RationalGaussianChain
end AFT.RationalNumerics.RationalGaussianChain
namespace AFT.RationalNumerics.RationalGaussianChain.WidthsLe
end AFT.RationalNumerics.RationalGaussianChain.WidthsLe
namespace AFT.RationalNumerics.RationalGaussianChain.drawBits
end AFT.RationalNumerics.RationalGaussianChain.drawBits
namespace AFT.RationalNumerics.RationalGaussianChain.exactChannel
end AFT.RationalNumerics.RationalGaussianChain.exactChannel
namespace AFT.RationalNumerics.centeredGaussianAnchor
end AFT.RationalNumerics.centeredGaussianAnchor
namespace AFT.RationalNumerics.integerMatrix
end AFT.RationalNumerics.integerMatrix
namespace AFT.RationalNumerics.integer_det_bound
end AFT.RationalNumerics.integer_det_bound
namespace AFT.RationalNumerics.leadingMatrix
end AFT.RationalNumerics.leadingMatrix
namespace AFT.RationalNumerics.lowerInv_recurrence
end AFT.RationalNumerics.lowerInv_recurrence
namespace AFT.RationalNumerics.normalization_budget
end AFT.RationalNumerics.normalization_budget
namespace AFT.RationalNumerics.rationalBodyPaddingChain
end AFT.RationalNumerics.rationalBodyPaddingChain
namespace AFT.RationalNumerics.rationalBodyPaddingDraw
end AFT.RationalNumerics.rationalBodyPaddingDraw
namespace AFT.RationalNumerics.rationalLDLDiagonal
end AFT.RationalNumerics.rationalLDLDiagonal
namespace AFT.RationalNumerics.rationalLDLDiagonalHeight
end AFT.RationalNumerics.rationalLDLDiagonalHeight
namespace AFT.RationalNumerics.rationalLDLInner
end AFT.RationalNumerics.rationalLDLInner
namespace AFT.RationalNumerics.rationalLDLState
end AFT.RationalNumerics.rationalLDLState
namespace AFT.RationalNumerics.rationalLDLState.match_1
end AFT.RationalNumerics.rationalLDLState.match_1
namespace AFT.RationalNumerics.rationalMatrixGaussianChain
end AFT.RationalNumerics.rationalMatrixGaussianChain
namespace AFT.RationalNumerics.sum_before
end AFT.RationalNumerics.sum_before
namespace AFT.convolutionCoordinateEquiv
end AFT.convolutionCoordinateEquiv
namespace AFT.countableConvolution
end AFT.countableConvolution


/-! # An arithmetic-counted evaluator of the actual Gaussian finite series

Rational operations and integer floor/ceiling are counted here; their
operand lengths are supplied by the separate height theorems. Powers and
factorials use displayed repeated multiplication, never a real oracle.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

structure GaussianArithmetic where
  value : ℚ
  work : ℕ

namespace GaussianArithmetic

def literal (value : ℚ) : GaussianArithmetic := ⟨value,0⟩
def mul (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value*second.value,first.work+second.work+1⟩
def add (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value+second.value,first.work+second.work+1⟩

def div (first second : GaussianArithmetic) : GaussianArithmetic :=
  ⟨first.value/second.value,first.work+second.work+1⟩
def sum {Index : Type*} (indices : Finset Index) (term : Index → GaussianArithmetic) : GaussianArithmetic :=
  ⟨∑i∈indices,(term i).value,(∑i∈indices,(term i).work)+indices.card⟩

def power (value : ℚ) : ℕ → GaussianArithmetic
  | 0 => ⟨1,0⟩
  | exponent+1 => let previous := power value exponent;⟨previous.value*value,previous.work+1⟩

def factorial : ℕ → GaussianArithmetic
  | 0 => ⟨1,0⟩
  | count+1 => let previous := factorial count;⟨(count+1)*previous.value,previous.work+1⟩

@[simp] theorem power_value (value : ℚ) (exponent : ℕ) : (power value exponent).value=value^exponent := by
  induction exponent with
  | zero => simp only [power,pow_zero]
  | succ exponent ih => simp only [power,ih,pow_succ]
@[simp] theorem power_work (value : ℚ) (exponent : ℕ) : (power value exponent).work=exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [power,ih]
@[simp] theorem factorial_value (count : ℕ) : (factorial count).value=count.factorial := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [factorial,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
@[simp] theorem factorial_work (count : ℕ) : (factorial count).work=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [factorial,ih]

def arctan (value : ℚ) (terms : ℕ) : GaussianArithmetic :=
  sum (Finset.range terms) (fun index =>
    let numerator := (power (-1) index).mul (power value (2*index+1))
    let result := numerator.div (literal (2*index+1))
    ⟨result.value,result.work+2⟩)

def pi (bits : ℕ) : GaussianArithmetic :=
  (literal 4).mul ((arctan (1/2) (bits+3)).add (arctan (1/3) (bits+3)))

def taylor (value : ℚ) (terms : ℕ) : GaussianArithmetic :=
  sum (Finset.range terms) (fun index => (power value index).div (factorial index))

def exponential (argument : ℚ) (bits : ℕ) : GaussianArithmetic :=
  let clipped := max argument 0
  let scale := expScale argument
  let polynomial := taylor (clipped/(scale : ℚ)) (bits+scale+1)
  let result := power polynomial.value⁻¹ scale
  ⟨result.value,polynomial.work+result.work+8⟩

def gaussian (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : GaussianArithmetic :=
  let ratio := gaussianRatio squaredWidth point
  let precision := bits+⌈ratio⌉₊+1
  let piValue := pi precision
  let exponentialValue := exponential (piValue.value*ratio) (bits+1)
  ⟨exponentialValue.value,piValue.work+exponentialValue.work+8⟩

/-- Denominator clearing and the translated integer point are exact finite
integer/rational operations before the same Gaussian evaluator is run. -/
def centered (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) : GaussianArithmetic :=
  let computed := gaussian (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits
  ⟨computed.value,computed.work+6⟩

@[simp] theorem arctan_value (value : ℚ) (terms : ℕ) : (arctan value terms).value=arctanSum value terms := by
  simp only [arctan,sum,mul,div,literal,power_value,arctanSum,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
@[simp] theorem pi_value (bits : ℕ) : (pi bits).value=piApprox bits := by
  simp only [pi,mul,add,literal,arctan_value,piApprox]
@[simp] theorem taylor_value (value : ℚ) (terms : ℕ) : (taylor value terms).value=expSum value terms := by
  simp only [taylor,sum,div,power_value,factorial_value,expSum]
@[simp] theorem exponential_value (argument : ℚ) (bits : ℕ) : (exponential argument bits).value=expNegApprox argument bits := by
  simp only [exponential,power_value,taylor_value,expNegApprox,expNegScaled]
@[simp] theorem gaussian_value (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    (gaussian squaredWidth point bits).value=gaussianApprox squaredWidth point bits := by
  simp only [gaussian,exponential_value,pi_value,gaussianApprox,gaussianGuard]
@[simp] theorem centered_value (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ) :
    (centered squaredWidth center point bits).value=centeredGaussianApprox squaredWidth center point bits := by
  simp only [centered,gaussian_value,centeredGaussianApprox]









end GaussianArithmetic
end AFT.RationalNumerics

end

section







namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics



/-! # Materialized positive normalization and dyadic ticket sampling

Every rational weight and floor count is stored once. The counter counts
rational arithmetic, floor divisions, integer arithmetic and comparisons;
binary operand lengths are supplied separately by the height bounds.
-/
namespace AFT.RationalNumerics
open BetaReference PermutationProgram
open scoped BigOperators

structure NormalizedRationalArray (count : ℕ) where
  value : Vector ℚ (count+1)
  work : ℕ

def countedPositiveNormalize {count : ℕ} (raw : Vector ℚ (count+1)) : NormalizedRationalArray count :=
  let positive := Vector.ofFn (fun index => max 0 (raw.get index))
  let total := ∑ index,positive.get index
  let weights := if total=0 then Vector.ofFn (fun index => if index=0 then 1 else 0)
    else Vector.ofFn (fun index => positive.get index/total)
  ⟨weights,3*(count+1)+1⟩

 

@[simp] theorem countedPositiveNormalize_work {count : ℕ} (raw : Vector ℚ (count+1)) :
    (countedPositiveNormalize raw).work=3*(count+1)+1 := rfl



 

 

 

 

 

end AFT.RationalNumerics

end

section































namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Literal all-coordinate inverses of actual canonical joint coefficients -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Enumerate all retained coordinates once, retaining their literal order. -/
def allCoordinates : List Slot := Finset.univ.toList

omit [DecidableEq Slot] in
@[simp] theorem allCoordinates_length : (allCoordinates (Slot := Slot)).length = Fintype.card Slot := by
  simp [allCoordinates]









end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance canonicalJointSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _



end
end AFT.LocalTensors

end

section










namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! # Exact finite disintegration on the positive-probability public cells -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {State Record Output : Type*} [Fintype State] [Fintype Record] [Fintype Output]













omit [Fintype Record] in
theorem expectation_mix (law : FiniteDist State) (conditional : State → FiniteDist Output)
    (value : Output → ℝ) :
    (law.mix conditional).expectation value =
      law.expectation (fun point => (conditional point).expectation value) := by
  simp only [expectation, mix_weight, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]




end
end AFT.FiniteDist

end

section








/-! # Exact public extensions and coarse-record conditional marginals -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Sample the mark first and then all dependent public randomness.
The dependent pair retains the sampled data for the later charge choice. -/
def dependentJoint {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (law : FiniteDist Index)
    (conditional : ∀ index,FiniteDist (Fiber index)) : FiniteDist (Sigma Fiber) where
  weight point := law.weight point.1*(conditional point.1).weight point.2
  nonneg point := mul_nonneg (law.nonneg point.1) ((conditional point.1).nonneg point.2)
  sum_one := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum]
    simp_rw [(conditional _).sum_one,mul_one]
    exact law.sum_one





variable {State Mark Record : Type*} [Fintype State] [Fintype Mark] [Fintype Record]









end
end AFT.FiniteDist

end

section










namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint




/-! # A finite fair-bit implementation of rational-coin rejection

The program draws a fresh proposal and a fresh rational acceptance coin
at each attempt, then returns the first accepted proposal or its fallback.
-/
namespace AFT.RationalRejectionProgram
open FiniteDist FiniteConditionProgram
open scoped BigOperators
variable {State Tape : Type*}

 def run (fallback : State) : (attempts : ℕ) → (Fin attempts → State×Fin 2) → State
  | 0,_ => fallback
  | attempts+1,proposals => if (proposals 0).2=0 then (proposals 0).1
      else run fallback attempts (fun index => proposals index.succ)

 def proposal (decode : Tape → State) (coin : State → ℚ) (bits : ℕ)
    (tape : Tape×(Fin bits → Fin 2)) : State×Fin 2 :=
  let candidate := decode tape.1
  (candidate,RationalAcceptanceCoin.draw bits (coin candidate) tape.2)

 def draw (decode : Tape → State) (coin : State → ℚ) (bits attempts : ℕ) (fallback : State)
    (tape : Fin attempts → Tape×(Fin bits → Fin 2)) : State :=
  run fallback attempts (fun index => proposal decode coin bits (tape index))

 

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State] [Fintype Tape] [Nonempty Tape]

 

 

 

 

end
end AFT.RationalRejectionProgram

end

section










namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.MixedKernel
end AFT.MixedKernel




/-! # Alphabet-independent mixed-fiber bounds for finite signed tensor channels -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Slot Input Output : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Input] [Fintype Output]

/-- The literal joint matrix action, for an arbitrary finite coordinate set. -/
def matrixApply (matrix : Slot → Input → Output → ℝ)
    (kernel : (Slot → Input) → ℝ) (output : Slot → Output) : ℝ :=
  ∑ word, kernel word * ∏ slot, matrix slot (word slot) (output slot)








end
end AFT.MixedKernel

end

section





/-! # Actual canonicality is preserved by finite mean-preserving matrix channels -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Input Output : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Input] [Fintype Output]

omit [Fintype Output] in
 theorem centered_sum_product_zero (reference : Slot → FiniteDist Input)
    (kernel : (Slot → Input) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel)
    (slot : Slot) (factors : Slot → Input → ℝ) :
    (∑ word, (reference slot).weight (word slot) * kernel word *
      ∏ other ∈ Finset.univ.erase slot, factors other (word other)) = 0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  haveI : Nonempty Input := by
    by_contra hh
    haveI : IsEmpty Input := not_nonempty_iff.mp hh
    have hm := (reference slot).sum_one
    simp at hm
  rw [← (Equiv.funSplitAt slot Input).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro rest _
  let base := (Equiv.funSplitAt slot Input).symm (Classical.arbitrary Input, rest)
  have hu (point : Input) : (Equiv.funSplitAt slot Input).symm (point, rest) = Function.update base slot point := by
    funext other
    by_cases ho : other = slot
    · subst other; simp [base, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [base, Equiv.funSplitAt, Equiv.piSplitAt, ho]
  have hf (point : Input) : (∏ other ∈ Finset.univ.erase slot,
      factors other (Function.update base slot point other)) =
      ∏ other ∈ Finset.univ.erase slot, factors other (base other) := by
    apply Finset.prod_congr rfl
    intro other ho
    rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
  simp only [hu, Function.update_self, hf, ← Finset.sum_mul, hc.2 slot (Finset.mem_univ slot) base, zero_mul]

/-- A scalar expectation identity suffices to preserve every conditional
zero-mean input direction in the full tensor channel. -/
theorem matrixApply_canonical (input : Slot → FiniteDist Input)
    (output : Slot → FiniteDist Output) (matrix : Slot → Input → Output → ℝ)
    (scalar : Slot → ℝ)
    (hmean : ∀ slot point, (output slot).expectation (matrix slot point) = scalar slot * (input slot).weight point)
    (kernel : (Slot → Input) → ℝ) (hc : Hoeffding.Canonical input Finset.univ kernel) :
    Hoeffding.Canonical output Finset.univ (matrixApply matrix kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  constructor
  · intro first second hh
    have he : first = second := funext fun slot => hh slot (Finset.mem_univ slot)
    rw [he]
  · intro slot _ values
    have hlocal (word : Slot → Input) :
        (∑ value, (output slot).weight value * ∏ other, matrix other (word other) (Function.update values slot value other)) =
        (scalar slot * (input slot).weight (word slot)) *
          ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
      have he (value : Output) : (∏ other, matrix other (word other) (Function.update values slot value other)) =
          matrix slot (word slot) value * ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ slot), Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro other ho
        rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
      simp only [he, ← mul_assoc, ← Finset.sum_mul]
      rw [show (∑ value, (output slot).weight value * matrix slot (word slot) value) =
        scalar slot * (input slot).weight (word slot) from hmean slot (word slot)]
    change (∑ value, (output slot).weight value * ∑ word,
      kernel word * ∏ other, matrix other (word other) (Function.update values slot value other)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have he : (∑ word, ∑ value, (output slot).weight value *
        (kernel word * ∏ other, matrix other (word other) (Function.update values slot value other))) =
        scalar slot * ∑ word, (input slot).weight (word slot) * kernel word *
          ∏ other ∈ Finset.univ.erase slot, matrix other (word other) (values other) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      calc
        _ = kernel word * ∑ value, (output slot).weight value *
            ∏ other, matrix other (word other) (Function.update values slot value other) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro value _
          ring
        _ = _ := by rw [hlocal]; ring
    rw [he, centered_sum_product_zero input kernel hc slot (fun other point => matrix other point (values other)), mul_zero]


end
end AFT.MixedKernel

end

section








namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.roleScopes
end AFT.CanonicalMoments.roleScopes



/-! # Actual canonical statistics on two independent pools -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _


section Compatible

variable {Slot Pool Color Copy : Type*}
  [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]







end Compatible

section TwoPools

variable {PS BS PP BP Color Copy : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color] [Fintype Copy]

/-- Each copy chooses its actual primary and body indices independently. -/
def sumPattern (pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP)) : Copy → (PS ⊕ BS) ↪ (PP ⊕ BP) :=
  fun copy => (pattern.1 copy).sumMap (pattern.2 copy)



omit [Fintype Copy] in
/-- Ordered U-statistic with both exact distinct-index normalizers. -/
def twoPoolStatistic (kernel : ((PS ⊕ BS) → Color) → ℝ) (word : (PP ⊕ BP) → Color) : ℝ :=
  (∑ placement : (PS ↪ PP) × (BS ↪ BP), placedKernel kernel (placement.1.sumMap placement.2) word) /
    (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
      ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ))





end TwoPools

end

end AFT.CanonicalMoments

end

section







namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments


/-! # Palette-independent fixed moments of genuine canonical U-statistics -/

set_option maxHeartbeats 800000

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section


variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- An explicit constant depending only on kernel order and moment order. -/
def momentConstant (order power : ℕ) : ℝ :=
  (power * order + 1 : ℕ) * (2 : ℝ) ^ (power * order) * (power * order : ℕ) ^ (power * order)





end

end AFT.CanonicalMoments

end

section








namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments



/-! # Full mixed activity retains both population scales -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT_1 {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _


section Weighted

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]



end Weighted

section TwoPools

variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]
  {power : ℕ}













end TwoPools

end

end AFT.CanonicalMoments

end

section










/-! # Palette-independent high moments with two unequal sample pools -/

set_option maxHeartbeats 800000

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT_2 {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

section Counting

variable {Copy PS BS PP BP : Type*}
  [Fintype Copy] [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]



end Counting

variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]





end

end AFT.CanonicalMoments

end

section
































































namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.CanonicalMoments.twoPoolStatistic
end AFT.CanonicalMoments.twoPoolStatistic
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.chargeWordLaw
end AFT.FiniteDist.chargeWordLaw
namespace AFT.FiniteDist.conditionalRawMass
end AFT.FiniteDist.conditionalRawMass
namespace AFT.FiniteDist.weightedMass
end AFT.FiniteDist.weightedMass
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.monomialInputStatistic
end AFT.RepresentedPolynomial.monomialInputStatistic
namespace AFT.RepresentedPolynomial.monomialPairedStatistic
end AFT.RepresentedPolynomial.monomialPairedStatistic
namespace AFT.RepresentedPolynomial.monomialPlacementCount
end AFT.RepresentedPolynomial.monomialPlacementCount
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.tableBodyScope
end AFT.RepresentedPolynomial.tableBodyScope
namespace AFT.RepresentedPolynomial.tableLocalBound
end AFT.RepresentedPolynomial.tableLocalBound
namespace AFT.RepresentedPolynomial.tableLocalTerm
end AFT.RepresentedPolynomial.tableLocalTerm
namespace AFT.RepresentedPolynomial.tablePairedBodyScope
end AFT.RepresentedPolynomial.tablePairedBodyScope
namespace AFT.RepresentedPolynomial.tablePairedEnvelope
end AFT.RepresentedPolynomial.tablePairedEnvelope
namespace AFT.RepresentedPolynomial.tablePairedLocalTerm
end AFT.RepresentedPolynomial.tablePairedLocalTerm
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix



/-! # Executable global rejection with all three error sources separated -/
namespace AFT.RationalRejectionProgram
open FiniteDist
open scoped BigOperators
variable {State Tape : Type*}

 def positiveDraw (decode : Tape → State) (raw : State → ℚ)
    (envelope bits attempts : ℕ) (fallback : State) :
    (Fin attempts → Tape×(Fin bits → Fin 2)) → State :=
  draw decode (fun point => max (raw point) 0/(envelope : ℚ)) bits attempts fallback

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State] [Fintype Tape] [Nonempty Tape]

 



end
end AFT.RationalRejectionProgram

end

section






















/-! # Arithmetic counters for the executable outer rejection loop -/
namespace AFT.RationalRejectionProgram
open RationalNumerics PermutationProgram BetaReference
open scoped BigOperators

 structure CountedValue (State : Type*) where
  value : State
  work : ℕ

 

 

 

 variable {State Tape : Type*}



 

 

end AFT.RationalRejectionProgram

end

section


























































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.CanonicalColumnDomain
end AFT.RepresentedPolynomial.CanonicalColumnDomain
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.canonicalRestrictedColumn
end AFT.RepresentedPolynomial.canonicalRestrictedColumn
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryFiniteSeed
end AFT.RepresentedPolynomial.primaryFiniteSeed
namespace AFT.RepresentedPolynomial.primaryMonomialSeed
end AFT.RepresentedPolynomial.primaryMonomialSeed
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Finite ordered factor programs without equality tests on real kernels

The executable data keep occurrences separate.  Collisions between decoded
real seed labels are handled only by the semantic interpretation.
-/
namespace AFT.RationalNumerics

structure OrderedSeedTerm (Code : Type*) where
  coefficient : ℚ
  factors : List Code

abbrev OrderedSeedTable (Code : Type*) := List (OrderedSeedTerm Code)















open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Code Seed : Type*}



def OrderedSeedTerm.interpret (decode : Code → Seed) (term : OrderedSeedTerm Code) : Table Seed :=
  (term.coefficient : ℝ) • (term.factors.map (fun code => MvPolynomial.X (decode code))).prod

def OrderedSeedTable.interpret (decode : Code → Seed) (table : OrderedSeedTable Code) : Table Seed :=
  (table.map (OrderedSeedTerm.interpret decode)).sum













@[simp] theorem OrderedSeedTable.interpret_nil (decode : Code → Seed) :
    OrderedSeedTable.interpret decode []=0 := rfl

@[simp] theorem OrderedSeedTable.interpret_cons (decode : Code → Seed) (term : OrderedSeedTerm Code)
    (table : OrderedSeedTable Code) :
    OrderedSeedTable.interpret decode (term::table)=term.interpret decode+table.interpret decode := rfl









end
end AFT.RationalNumerics

end

section












namespace AFT
end AFT
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm



/-! # Ordered polynomial programs with explicit numerical scalar leaves

Scalar expressions distinguish the real coefficients in the proved table from
rational approximations evaluated by the sampler. No equality test on real
kernels or real coefficients occurs in the executable syntax.
-/
namespace AFT.RationalNumerics

inductive ScalarProgram (Scalar : Type*) where
  | rational : ℚ → ScalarProgram Scalar
  | atom : Scalar → ScalarProgram Scalar
  | add : ScalarProgram Scalar → ScalarProgram Scalar → ScalarProgram Scalar
  | multiply : ScalarProgram Scalar → ScalarProgram Scalar → ScalarProgram Scalar
  | negate : ScalarProgram Scalar → ScalarProgram Scalar
  | inverse : ScalarProgram Scalar → ScalarProgram Scalar

def ScalarProgram.run {Scalar : Type*} (leaf : Scalar → ℚ) : ScalarProgram Scalar → ℚ
  | .rational value => value
  | .atom code => leaf code
  | .add first second => first.run leaf+second.run leaf
  | .multiply first second => first.run leaf*second.run leaf
  | .negate term => -(term.run leaf)
  | .inverse term => (term.run leaf)⁻¹

structure ParametricSeedTerm (Scalar Code : Type*) where
  coefficient : ScalarProgram Scalar
  factors : List Code

abbrev ParametricSeedTable (Scalar Code : Type*) := List (ParametricSeedTerm Scalar Code)

def ParametricSeedTerm.scale {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (term : ParametricSeedTerm Scalar Code) : ParametricSeedTerm Scalar Code :=
  ⟨.multiply scalar term.coefficient,term.factors⟩



def ParametricSeedTable.one {Scalar Code : Type*} : ParametricSeedTable Scalar Code := [⟨.rational 1,[]⟩]
def ParametricSeedTable.seed {Scalar Code : Type*} (code : Code) : ParametricSeedTable Scalar Code := [⟨.rational 1,[code]⟩]
def ParametricSeedTable.constant {Scalar Code : Type*} (scalar : ScalarProgram Scalar) : ParametricSeedTable Scalar Code := [⟨scalar,[]⟩]

def ParametricSeedTable.scale {Scalar Code : Type*} (scalar : ScalarProgram Scalar)
    (table : ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Code := table.map (ParametricSeedTerm.scale scalar)















open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Scalar Code Seed : Type*}

def ScalarProgram.denote (leaf : Scalar → ℝ) : ScalarProgram Scalar → ℝ
  | .rational value => value
  | .atom code => leaf code
  | .add first second => first.denote leaf+second.denote leaf
  | .multiply first second => first.denote leaf*second.denote leaf
  | .negate term => -(term.denote leaf)
  | .inverse term => (term.denote leaf)⁻¹



def ParametricSeedTerm.interpret (leaf : Scalar → ℝ) (decode : Code → Seed) (term : ParametricSeedTerm Scalar Code) : Table Seed :=
  term.coefficient.denote leaf • (term.factors.map (fun code => MvPolynomial.X (decode code))).prod

def ParametricSeedTable.interpret (leaf : Scalar → ℝ) (decode : Code → Seed) (table : ParametricSeedTable Scalar Code) : Table Seed :=
  (table.map (ParametricSeedTerm.interpret leaf decode)).sum

@[simp] theorem ParametricSeedTable.interpret_nil (leaf : Scalar → ℝ) (decode : Code → Seed) :
    ParametricSeedTable.interpret leaf decode []=0 := rfl
@[simp] theorem ParametricSeedTable.interpret_cons (leaf : Scalar → ℝ) (decode : Code → Seed)
    (term : ParametricSeedTerm Scalar Code) (rest : ParametricSeedTable Scalar Code) :
    ParametricSeedTable.interpret leaf decode (term::rest)=term.interpret leaf decode+rest.interpret leaf decode := rfl





@[simp] theorem ParametricSeedTable.interpret_one (leaf : Scalar → ℝ) (decode : Code → Seed) :
    (one : ParametricSeedTable Scalar Code).interpret leaf decode=1 := by simp [one,interpret,ParametricSeedTerm.interpret,ScalarProgram.denote]

@[simp] theorem ParametricSeedTable.interpret_variable (leaf : Scalar → ℝ) (decode : Code → Seed) (code : Code) :
    (seed code : ParametricSeedTable Scalar Code).interpret leaf decode=MvPolynomial.X (decode code) := by
  simp [seed,interpret,ParametricSeedTerm.interpret,ScalarProgram.denote]

@[simp] theorem ParametricSeedTable.interpret_constant (leaf : Scalar → ℝ) (decode : Code → Seed) (scalar : ScalarProgram Scalar) :
    (constant scalar : ParametricSeedTable Scalar Code).interpret leaf decode=MvPolynomial.C (scalar.denote leaf) := by
  simp [constant,interpret,ParametricSeedTerm.interpret,MvPolynomial.smul_eq_C_mul]















end
end AFT.RationalNumerics

end

section





















/-! # Literal work and intermediate rational heights of scalar expressions -/
namespace AFT.RationalNumerics

/-- A computable bound for the height of a rational literal. -/
def rationalLiteralHeight (value : ℚ) : ℕ := value.num.natAbs.size+value.den.size



namespace ScalarProgram
variable {Scalar : Type*}

def nodes : ScalarProgram Scalar → ℕ
  | .rational _ => 1
  | .atom _ => 1
  | .add first second => first.nodes+second.nodes+1
  | .multiply first second => first.nodes+second.nodes+1
  | .negate term => term.nodes+1
  | .inverse term => term.nodes+1







/-- The literal heights are included rather than treated as unit-cost constants. -/
def heightBudget (leafHeight : Scalar → ℕ) : ScalarProgram Scalar → ℕ
  | .rational value => rationalLiteralHeight value
  | .atom code => leafHeight code
  | .add first second => first.heightBudget leafHeight+second.heightBudget leafHeight+1
  | .multiply first second => first.heightBudget leafHeight+second.heightBudget leafHeight
  | .negate term => term.heightBudget leafHeight
  | .inverse term => term.heightBudget leafHeight



/-- Proof-side list of all scalar-node results visited by `countedRun`.
Internal leaf computations use their separate actual-program height bounds. -/
def evaluationValues (leaf : Scalar → ℚ) : ScalarProgram Scalar → List ℚ
  | .rational value => [value]
  | .atom code => [leaf code]
  | .add first second => first.evaluationValues leaf ++ second.evaluationValues leaf ++ [first.run leaf+second.run leaf]
  | .multiply first second => first.evaluationValues leaf ++ second.evaluationValues leaf ++ [first.run leaf*second.run leaf]
  | .negate term => term.evaluationValues leaf ++ [-term.run leaf]
  | .inverse term => term.evaluationValues leaf ++ [(term.run leaf)⁻¹]



def literalsBounded (bits : ℕ) : ScalarProgram Scalar → Prop
  | .rational value => rationalLiteralHeight value≤bits
  | .atom _ => True
  | .add first second => first.literalsBounded bits ∧ second.literalsBounded bits
  | .multiply first second => first.literalsBounded bits ∧ second.literalsBounded bits
  | .negate term => term.literalsBounded bits
  | .inverse term => term.literalsBounded bits



end ScalarProgram
end AFT.RationalNumerics

end

section




















/-! # Executing scalar syntax in an explicit numeric representation

The evaluator calls the supplied numeric programs on the actual stored
child results. It never decodes to rationals during execution. Correctness
and bounded operand costs are separate proved interfaces for instantiation
by the binary numerator/denominator implementation.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram

structure RationalImplementation (Value : Type*) where
  literal : ℚ → CountedValue Value
  add : Value → Value → CountedValue Value
  multiply : Value → Value → CountedValue Value
  negate : Value → CountedValue Value
  inverse : Value → CountedValue Value



namespace ScalarProgram
variable {Scalar Value : Type*}









end ScalarProgram
end AFT.RationalNumerics

end

section




















/-! Explicit sequential array access and finite arithmetic accumulation.
A lookup scans a list and charges the array-to-list copy; it is not a unit
cost random-access operation on an unbounded index. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics
open scoped BigOperators

structure ReadResult (α : Type*) where
  data : Option α
  work : ℕ

def readList {α : Type*} : List α → ℕ → ReadResult α
  | [],_ => ⟨none,1⟩
  | head::_,0 => ⟨some head,2⟩
  | _::tail,index+1 => let result := readList tail index;⟨result.data,result.work+2⟩

theorem readList_value {α : Type*} (items : List α) (index : ℕ) :
    (readList items index).data=items[index]? := by
  induction items generalizing index with
  | nil => simp [readList]
  | cons head tail ih => cases index <;> simp [readList,ih]

theorem readList_work {α : Type*} (items : List α) (index : ℕ) :
    (readList items index).work ≤ 2*items.length+1 := by
  induction items generalizing index with
  | nil => simp [readList]
  | cons head tail ih =>
    cases index with
    | zero => simp only [readList,List.length_cons];omega
    | succ index => have hh := ih index;simp only [readList,List.length_cons];omega

def readVector {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) : CountedValue α :=
  let result := readList items.toList index.val
  ⟨result.data.getD fallback,result.work+count+2⟩

theorem readVector_value {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) :
    (readVector fallback items index).value=items.get index := by
  simp only [readVector,readList_value]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,Vector.getElem_toList]
  rfl

theorem readVector_work {α : Type*} {count : ℕ} (fallback : α) (items : Vector α count) (index : Fin count) :
    (readVector fallback items index).work ≤ 3*count+3 := by
  have hh := readList_work items.toList index.val
  simp only [Vector.length_toList] at hh
  simp only [readVector]
  omega

namespace RationalBits

def sumFin : (count : ℕ) → (Fin count → RationalResult) → RationalResult
  | 0,_ => ⟨zero,2⟩
  | count+1,term =>
    let previous := sumFin count (fun index => term index.castSucc)
    let next := term (Fin.last count)
    let result := add previous.data next.data
    ⟨result.data,previous.work+next.work+result.work+2⟩

theorem sumFin_value (count : ℕ) (term : Fin count → RationalResult) :
    (sumFin count term).data.decode=∑ index,(term index).data.decode := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih => simp only [sumFin,add_value,ih,Fin.sum_univ_castSucc]





structure ArrayResult (count : ℕ) where
  data : Vector RationalBits count
  work : ℕ

def buildArray (count : ℕ) (term : Fin count → RationalResult) : ArrayResult count :=
  let computed := Vector.ofFn term
  ⟨computed.map (fun result => result.data),(∑ index,(computed.get index).work)+2*count+2⟩

theorem buildArray_get (count : ℕ) (term : Fin count → RationalResult) (index : Fin count) :
    (buildArray count term).data.get index=(term index).data := by
  simp [buildArray]



end RationalBits
end AFT.BinaryArithmetic

end

section


















/-! Sequential materialization for finite metadata arrays. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 def storeData {α : Type*} (count : ℕ) (term : Fin count → CountedValue α) : CountedValue (Vector α count) :=
   let computed := Vector.ofFn term
   ⟨computed.map (fun entry => entry.value),(∑ index,(computed.get index).work)+2*count+2⟩

 theorem storeData_get {α : Type*} (count : ℕ) (term : Fin count → CountedValue α) (index : Fin count) :
     (storeData count term).value.get index=(term index).value := by
   simp only [storeData,Vector.get_map,Vector.get_ofFn]

 theorem storeData_work {α : Type*} (count bound : ℕ) (term : Fin count → CountedValue α)
     (h : ∀ index,(term index).work≤bound) :
     (storeData count term).work≤count*(bound+2)+2 := by
   have hs := Finset.sum_le_sum (s:=Finset.univ) (fun index _ => h index)
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
   simp only [storeData,Vector.get_ofFn]
   nlinarith

end AFT.BinaryArithmetic

end

section




/-! # Explicit unary loop control for polynomially bounded counters

The represented counter is a unary natural. Reading a binary counter costs
linear time in its numerical value and list length. This overhead is used
only when the surrounding finite-series proof bounds the counter itself
by a polynomial in the dimension.
-/
namespace AFT.BinaryArithmetic

structure UnaryCounterResult where
  count : ℕ
  work : ℕ

/-- Unary doubling uses two successor constructors per iteration. -/
def doubleCounter : ℕ → UnaryCounterResult
  | 0 => ⟨0,1⟩
  | count+1 =>
      let previous := doubleCounter count
      ⟨previous.count.succ.succ,previous.work+3⟩

theorem doubleCounter_value (count : ℕ) : (doubleCounter count).count=2*count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [doubleCounter,ih];omega

theorem doubleCounter_work (count : ℕ) : (doubleCounter count).work=3*count+1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [doubleCounter,ih];omega

/-- The execution uses only list cases, unary doubling and successor. -/
def readCounter : List Bool → UnaryCounterResult
  | [] => ⟨0,2⟩
  | bit::tail =>
      let previous := readCounter tail
      let doubled := doubleCounter previous.count
      ⟨if bit then doubled.count.succ else doubled.count,previous.work+doubled.work+3⟩

theorem readCounter_value (digits : List Bool) : (readCounter digits).count=value digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih =>
      cases bit <;> simp only [readCounter,doubleCounter_value,ih,value,Bool.false_eq_true,ite_false,
        ite_true,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem readCounter_work (digits : List Bool) :
    (readCounter digits).work≤ 6*value digits+4*digits.length+2 := by
  induction digits with
  | nil => simp only [readCounter,value,List.length_nil];omega
  | cons bit tail ih =>
      simp only [readCounter,doubleCounter_work,readCounter_value,value,List.length_cons]
      omega

/-- Unary addition traverses its first input; it is never charged as a
constant-time operation on an unbounded whole integer. -/
def addCounter : ℕ → ℕ → UnaryCounterResult
  | 0,second => ⟨second,1⟩
  | first+1,second =>
      let previous := addCounter first second
      ⟨previous.count.succ,previous.work+2⟩

theorem addCounter_value (first second : ℕ) : (addCounter first second).count=first+second := by
  induction first with
  | zero => simp only [addCounter,Nat.zero_add]
  | succ first ih => simp only [addCounter,ih];omega

theorem addCounter_work (first second : ℕ) : (addCounter first second).work=2*first+1 := by
  induction first with
  | zero => rfl
  | succ first ih => simp only [addCounter,ih];omega

/-- Unary multiplication is repeated actual unary addition. -/
def multiplyCounter : ℕ → ℕ → UnaryCounterResult
  | 0,_ => ⟨0,1⟩
  | first+1,second =>
      let previous := multiplyCounter first second
      let next := addCounter second previous.count
      ⟨next.count,previous.work+next.work+2⟩

theorem multiplyCounter_value (first second : ℕ) : (multiplyCounter first second).count=first*second := by
  induction first with
  | zero => simp only [multiplyCounter,Nat.zero_mul]
  | succ first ih => simp only [multiplyCounter,addCounter_value,ih];ring

theorem multiplyCounter_work (first second : ℕ) :
    (multiplyCounter first second).work=first*(2*second+3)+1 := by
  induction first with
  | zero => simp only [multiplyCounter,Nat.zero_mul,Nat.zero_add]
  | succ first ih => simp only [multiplyCounter,addCounter_work,ih];ring

end AFT.BinaryArithmetic

end

section






/-! Long division of polynomially bounded unary addresses. Conversion to
and from digit lists is executed and charged; division itself is binary. -/
namespace AFT.BinaryArithmetic

structure CounterDivisionResult where
  quotient : ℕ
  remainder : ℕ
  work : ℕ

def divideCounter (numerator denominator : ℕ) : CounterDivisionResult :=
  let first := canonicalCounter numerator
  let second := canonicalCounter denominator
  let division := divide first.digits second.digits
  let quotient := readCounter division.quotient
  let remainder := readCounter division.remainder
  ⟨quotient.count,remainder.count,first.work+second.work+division.work+quotient.work+remainder.work+5⟩

theorem divideCounter_value (numerator denominator : ℕ) (hd : 0<denominator) :
    (divideCounter numerator denominator).quotient=numerator/denominator ∧
      (divideCounter numerator denominator).remainder=numerator%denominator := by
  have h := divide_value (canonicalCounter numerator).digits (canonicalCounter denominator).digits
    (by simpa only [canonicalCounter_value] using hd)
  simpa only [divideCounter,readCounter_value,canonicalCounter_value] using h

theorem divideCounter_work (numerator denominator : ℕ) (hd : 0<denominator) :
    (divideCounter numerator denominator).work ≤ 500*(numerator+denominator+2)^2 := by
  have hn := canonicalCounter_work numerator
  have hm := canonicalCounter_work denominator
  have hdv := divide_work (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hq := readCounter_work (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).quotient
  have hr := readCounter_work (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).remainder
  have hv := divide_value (canonicalCounter numerator).digits (canonicalCounter denominator).digits
    (by simpa only [canonicalCounter_value] using hd)
  have hql := divide_quotient_length (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hrl := divide_remainder_length (canonicalCounter numerator).digits (canonicalCounter denominator).digits
  have hs (n : ℕ) : n.size≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  simp only [canonicalCounter_value,canonicalCounter_length] at hv hql hrl hdv
  rw [hv.1,hql] at hq
  rw [hv.2] at hr
  have hqbound := Nat.div_le_self numerator denominator
  have hrbound := Nat.mod_lt numerator hd
  have hdivbound : 20*(numerator.size+denominator.size+1)^2≤20*(numerator+denominator+1)^2 := by
    gcongr <;> exact hs _
  have hnsize := hs numerator
  have hdsize := hs denominator
  have hrl' : (divide (canonicalCounter numerator).digits (canonicalCounter denominator).digits).remainder.length≤numerator+denominator := by omega
  simp only [divideCounter]
  nlinarith

/-- Truncated subtraction is a genuine simultaneous unary traversal. -/
def differenceCounter : ℕ → ℕ → UnaryCounterResult
  | first,0 => ⟨first,1⟩
  | 0,_+1 => ⟨0,1⟩
  | first+1,second+1 =>
      let previous := differenceCounter first second
      ⟨previous.count,previous.work+2⟩

theorem differenceCounter_value (first second : ℕ) :
    (differenceCounter first second).count=first-second := by
  induction second generalizing first with
  | zero => simp [differenceCounter]
  | succ second ih =>
      cases first with
      | zero => simp [differenceCounter]
      | succ first => simpa only [differenceCounter,Nat.succ_sub_succ_eq_sub] using ih first

theorem differenceCounter_work (first second : ℕ) :
    (differenceCounter first second).work ≤ 2*first+1 := by
  induction second generalizing first with
  | zero => simp only [differenceCounter];omega
  | succ second ih =>
      cases first with
      | zero => simp [differenceCounter]
      | succ first => simp only [differenceCounter];have h := ih first;omega

end AFT.BinaryArithmetic

end

section



































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Support-preserving chart sampling with a finite legal fallback search -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

/-- The search is over the finite array, with no selection oracle. -/
def legalChartIndex (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts)) (point : Fin charts) : Fin charts :=
  if point∈legal then point else if h : legal.Nonempty then legal.min' h else 0





noncomputable section
open scoped Classical Topology
open Filter V7Calibration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 

 

 

 

 

 

 

 

end
end AFT.BoundaryCalibration

end

section













/-! # Polynomial rational operand heights in the cached chart computation -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

 def chartExpectationHeight (charts bits : ℕ) : ℕ := charts*(bits+1)+charts
 def chartConditionalHeight (charts colors bits : ℕ) : ℕ := colors+chartExpectationHeight charts bits
 def chartFeatureHeight (charts colors bits : ℕ) : ℕ :=
   chartConditionalHeight charts colors bits+colors*(chartConditionalHeight charts colors bits+1)+colors+1
 def chartProjectionHeight (charts colors features bits : ℕ) : ℕ :=
   chartExpectationHeight charts bits+features*(chartFeatureHeight charts colors bits+1)+1
 def chartStoredHeight (charts colors features atomBits : ℕ) : ℕ :=
   chartProjectionHeight charts colors features 0+atomBits+features*(chartFeatureHeight charts colors (2*charts)+1)
 def chartIterateHeight (charts colors features atomBits steps : ℕ) : ℕ :=
   steps*((3*(charts^2+charts)+1)*chartStoredHeight charts colors features atomBits+charts+1)
 def chartWeightHeight (charts colors features atomBits steps : ℕ) : ℕ :=
   2*chartIterateHeight charts colors features atomBits steps+2*atomBits+3*charts+3

 

 

 

 

 

 

 

 

end AFT.BoundaryCalibration

end

section













/-! # A materialized chart evaluator with a rational arithmetic counter

The metadata (finite feature and membership tables) are read as arrays.
The counter charges rational addition, subtraction, multiplication, division,
and the branch tests in the displayed evaluator. Integer metadata construction
and binary arithmetic costs are separate bounds.
-/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

structure ChartArithmetic where
  value : ℚ
  work : ℕ

namespace ChartArithmetic

def literal (value : ℚ) : ChartArithmetic := ⟨value,0⟩
def add (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value+second.value,first.work+second.work+1⟩
def sub (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value-second.value,first.work+second.work+1⟩
def mul (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value*second.value,first.work+second.work+1⟩
def div (first second : ChartArithmetic) : ChartArithmetic :=
  ⟨first.value/second.value,first.work+second.work+1⟩
def test (condition : Bool) (yes no : Unit → ChartArithmetic) : ChartArithmetic :=
  let result := if condition then yes () else no ()
  ⟨result.value,result.work+1⟩
def sum {Index : Type*} [DecidableEq Index] (set : Finset Index) (term : Index → ChartArithmetic) : ChartArithmetic :=
  ⟨∑i∈set,(term i).value,(∑i∈set,(term i).work)+set.card⟩

def expectation (charts : ℕ) (value : Fin charts → ℚ) : ChartArithmetic :=
  (sum Finset.univ (fun i => literal (value i))).div (literal charts)

def conditional (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) : ChartArithmetic :=
  (literal colors).mul (expectation charts (fun chart => if feature chart=color then value chart else 0))

def feature (charts colors : ℕ) (feature : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  test (decide (feature chart∈allowed))
    (fun _ => (conditional charts colors feature value (feature chart)).sub
      ((sum allowed (conditional charts colors feature value)).div (literal allowed.card)))
    (fun _ => literal 0)

def projection (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  (expectation charts value).add
    (sum Finset.univ (fun index => feature charts colors (featuresMap index) (allowed index) value chart))

def deletionEntry (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) : ChartArithmetic :=
  (literal 0).sub (projection charts colors features featuresMap allowed
    (fun point => if point∈safe then 0 else if point=input then 1 else 0) output)

def defect (charts colors features : ℕ)
    (featuresMap : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (chart : Fin charts) : ChartArithmetic :=
  (literal atom).mul (sum Finset.univ (fun index =>
    test (decide (index=marked)) (fun _ => literal 0)
      (fun _ => feature charts colors (featuresMap index) (allowed index) spike chart)))

@[simp] theorem expectation_value (charts : ℕ) (value : Fin charts → ℚ) :
    (expectation charts value).value=chartExpectationProgram charts value := rfl
@[simp] theorem conditional_value (charts colors : ℕ) (f : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (color : Fin colors) :
    (conditional charts colors f value color).value=chartConditionalProgram charts colors f value color := rfl
@[simp] theorem feature_value (charts colors : ℕ) (f : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (chart : Fin charts) :
    (feature charts colors f allowed value chart).value=chartFeatureProgram charts colors f allowed value chart := by
  simp only [feature,test,chartFeatureProgram]
  split_ifs <;> simp_all [sub,div,sum,literal,conditional_value]
@[simp] theorem projection_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (chart : Fin charts) :
    (projection charts colors features f allowed value chart).value=chartProjectionProgram charts colors features f allowed value chart := by
  simp only [projection,add,sum,expectation_value,feature_value,chartProjectionProgram]
@[simp] theorem deletionEntry_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) :
    (deletionEntry charts colors features f allowed safe output input).value=chartDeletionMatrixProgram charts colors features f allowed safe output input := by
  simp only [deletionEntry,sub,literal,projection_value,chartDeletionMatrixProgram,chartDeletionProgram]
  ring
@[simp] theorem defect_value (charts colors features : ℕ)
    (f : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (spike : Fin charts → ℚ) (chart : Fin charts) :
    (defect charts colors features f allowed marked atom spike chart).value=chartSpikeDefectProgram charts colors features f allowed marked atom spike chart := by
  simp only [defect,mul,literal,sum,chartSpikeDefectProgram]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  by_cases h : index=marked <;> simp [test,h,feature_value]

 
 

 
 

 

 

 

 

end ChartArithmetic

/-- The rational source and two Neumann iterates are materialized once. -/
structure CountedChartArray (charts : ℕ) where
  value : Vector ℚ charts
  work : ℕ



 

 

 

end AFT.BoundaryCalibration

end

section


























namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.ProtectedChartSupport
end AFT.BoundaryCalibration.ProtectedChartSupport
namespace AFT.BoundaryCalibration.chartPaletteFeature
end AFT.BoundaryCalibration.chartPaletteFeature
namespace AFT.BoundaryCalibration.countedMarkedChartDraw
end AFT.BoundaryCalibration.countedMarkedChartDraw
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity
namespace AFT.BoundaryCalibration.finiteAffineFeature
end AFT.BoundaryCalibration.finiteAffineFeature
namespace AFT.BoundaryCalibration.finiteAffineScale
end AFT.BoundaryCalibration.finiteAffineScale
namespace AFT.BoundaryCalibration.finiteProtectedFeatures
end AFT.BoundaryCalibration.finiteProtectedFeatures
namespace AFT.BoundaryCalibration.finiteProtectedMark
end AFT.BoundaryCalibration.finiteProtectedMark
namespace AFT.BoundaryCalibration.markedChartDraw
end AFT.BoundaryCalibration.markedChartDraw
namespace AFT.BoundaryCalibration.protectedInputs
end AFT.BoundaryCalibration.protectedInputs
namespace AFT.BoundaryCalibration.v7ProtectedPalettes
end AFT.BoundaryCalibration.v7ProtectedPalettes
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.V7Calibration
end AFT.V7Calibration




/-! # Stored public-chart metadata and legal finite-array output

The feature and palette tables are materialized before either Neumann loop.
The legal fallback uses that same stored safe/fiber union. This file proves
literal program agreement; the cost of constructing these integer metadata
is kept separate from the existing rational-arithmetic counter.
-/
namespace AFT.BoundaryCalibration
open V7Calibration RationalNumerics RationalRejectionProgram
open scoped BigOperators

structure PublicChartMetadata (charts colors features : ℕ) where
  feature : Vector (Vector (Fin colors) charts) features
  allowed : Vector (Finset (Fin colors)) features
  safe : Finset (Fin charts)
  fiber : Finset (Fin charts)































end AFT.BoundaryCalibration

end

section

















namespace AFT
end AFT
namespace AFT.RationalRejectionProgram
end AFT.RationalRejectionProgram


/-! # Counted finite scans

The loops inspect each entry once. Filtering preserves the input order and
its no-duplicate certificate, so forming the resulting finite set performs
no duplicate-removal or sorting pass.
-/
namespace AFT.RationalRejectionProgram
open scoped BigOperators













def countedListAll {State : Type*} (test : State → CountedValue Bool) :
    List State → CountedValue Bool
  | [] => ⟨true,0⟩
  | first::rest =>
      let selected := test first
      let remaining := countedListAll test rest
      ⟨selected.value && remaining.value,selected.work+remaining.work+1⟩





def countedFinAll (count : ℕ) (test : Fin count → CountedValue Bool) : CountedValue Bool :=
  let result := countedListAll test (List.ofFn id)
  ⟨result.value,result.work+count⟩





end AFT.RationalRejectionProgram

end

section




















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.countedLegalChartIndex
end AFT.BoundaryCalibration.countedLegalChartIndex
namespace AFT.BoundaryCalibration.countedLegalChartIndex.match_1
end AFT.BoundaryCalibration.countedLegalChartIndex.match_1
namespace AFT.BoundaryCalibration.countedListMinimum
end AFT.BoundaryCalibration.countedListMinimum
namespace AFT.BoundaryCalibration.countedListMinimum.match_1
end AFT.BoundaryCalibration.countedListMinimum.match_1



/-! # Building both chart supports by explicit stored-table scans

Every palette test reads a stored Boolean entry. The feature coordinates,
palette Boolean table and scale coordinates are supplied as materialized
arrays; their construction is accounted for separately.
-/
namespace AFT.BoundaryCalibration
open RationalRejectionProgram
open scoped BigOperators













structure StoredChartSupports (charts : ℕ) where
  safe : Finset (Fin charts)
  fiber : Finset (Fin charts)
  legal : Vector Bool charts











end AFT.BoundaryCalibration

end

section



















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.countedProtectedPaletteTest
end AFT.BoundaryCalibration.countedProtectedPaletteTest



/-! Protected affine features evaluated by explicit counter loops and binary
long division. `ZMod` appears only in the correctness statements. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration

 def modularDifference (address cutoff modulus : ℕ) : UnaryCounterResult :=
   let reduced := divideCounter cutoff modulus
   let offset := differenceCounter modulus reduced.remainder
   let shifted := addCounter address offset.count
   let result := divideCounter shifted.count modulus
   ⟨result.remainder,reduced.work+offset.work+shifted.work+result.work+4⟩

 

 

 def protectedFeatureAddress (cutoff modulus input chart : ℕ) : UnaryCounterResult :=
   let doubled := doubleCounter cutoff
   let width := doubled.count.succ
   let source := divideCounter input width
   let square := multiplyCounter modulus modulus
   let outer := divideCounter chart square.count
   let inner := divideCounter outer.remainder modulus
   let first := modularDifference source.quotient cutoff modulus
   let second := modularDifference source.remainder cutoff modulus
   let firstProduct := multiplyCounter inner.quotient first.count
   let secondProduct := multiplyCounter inner.remainder second.count
   let prefixSum := addCounter outer.quotient firstProduct.count
   let total := addCounter prefixSum.count secondProduct.count
   let result := divideCounter total.count modulus
   ⟨result.remainder,doubled.work+source.work+square.work+outer.work+inner.work+first.work+second.work+
     firstProduct.work+secondProduct.work+prefixSum.work+total.work+result.work+13⟩

 theorem protectedFeatureAddress_lt (cutoff modulus input chart : ℕ) (hm : 0 <  modulus) :
     (protectedFeatureAddress cutoff modulus input chart).count< modulus := by
   dsimp only [protectedFeatureAddress]
   rw [(divideCounter_value _ _ hm).2]
   exact Nat.mod_lt _ hm

 

 

 def protectedFeature (cutoff modulus : ℕ) [NeZero modulus]
     (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
     AFT.RationalRejectionProgram.CountedValue (Fin modulus) :=
   let result := protectedFeatureAddress cutoff modulus input.val chart.val
   ⟨⟨result.count,protectedFeatureAddress_lt cutoff modulus input.val chart.val (Nat.pos_of_ne_zero (NeZero.ne _))⟩,result.work⟩

 

end AFT.BinaryArithmetic

end

section




















/-! Runtime tests and cardinalities for the stored chart Boolean masks. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram
open scoped BigOperators

def equalCounter : ℕ → ℕ → CountedValue Bool
  | 0,0 => ⟨true,2⟩
  | 0,_+1 => ⟨false,2⟩
  | _+1,0 => ⟨false,2⟩
  | first+1,second+1 => let previous := equalCounter first second;⟨previous.value,previous.work+3⟩

theorem equalCounter_value (first second : ℕ) : (equalCounter first second).value=true ↔ first=second := by
  induction first generalizing second with
  | zero => cases second <;> simp [equalCounter]
  | succ first ih => cases second <;> simp [equalCounter,ih]

theorem equalCounter_work (first second : ℕ) :
    (equalCounter first second).work ≤ 3*(first+second)+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [equalCounter];all_goals omega
  | succ first ih =>
    cases second with
    | zero => simp only [equalCounter];omega
    | succ second => have hh := ih second;simp only [equalCounter];omega

def countFin : (count : ℕ) → (Fin count → CountedValue Bool) → UnaryCounterResult
  | 0,_ => ⟨0,2⟩
  | count+1,test =>
    let previous := countFin count (fun index => test index.castSucc)
    let current := test (Fin.last count)
    ⟨if current.value then previous.count.succ else previous.count,previous.work+current.work+3⟩





def maskCount {count : ℕ} (mask : Vector Bool count) : UnaryCounterResult :=
  countFin count (readVector false mask)

/-- The finite set occurs only in the specification, not in the program. -/
def maskSet {count : ℕ} (mask : Vector Bool count) : Finset (Fin count) :=
  Finset.univ.filter (fun index => mask.get index=true)







end AFT.BinaryArithmetic

end

section




















/-! Signed comparisons use subtraction, trimming and a Boolean test only. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 def signedLe (firstSign secondSign : Bool) (first second : List Bool) : CountedValue Bool :=
   let difference := signedAdd firstSign (!secondSign) first second
   let trimmed := normalize difference.digits
   ⟨difference.negative || trimmed.digits.isEmpty,difference.work+trimmed.work+4⟩

 theorem signedLe_value (firstSign secondSign : Bool) (first second : List Bool) :
     (signedLe firstSign secondSign first second).value=true ↔
       signedValue firstSign first≤ signedValue secondSign second := by
   have hv := signedAdd_value firstSign (!secondSign) first second
   have hn : signedValue (!secondSign) second= -signedValue secondSign second := by cases secondSign <;> simp [signedValue]
   rw [hn] at hv
   have hz : (normalize (signedAdd firstSign (!secondSign) first second).digits).digits.isEmpty=true ↔
       value (signedAdd firstSign (!secondSign) first second).digits=0 := by
     rw [List.isEmpty_iff,normalize_nil_iff]
   simp only [signedLe,Bool.or_eq_true,hz]
   cases hs : (signedAdd firstSign (!secondSign) first second).negative with
   | false =>
     rw [hs] at hv
     change (value (signedAdd firstSign (!secondSign) first second).digits : ℤ)=
       signedValue firstSign first+ -signedValue secondSign second at hv
     simp only [Bool.false_eq_true,false_or]
     omega
   | true =>
     rw [hs] at hv
     change -(value (signedAdd firstSign (!secondSign) first second).digits : ℤ)=
       signedValue firstSign first+ -signedValue secondSign second at hv
     simp only [true_or,true_iff]
     omega


 

end AFT.BinaryArithmetic

end

section





















/-! The protected palette predicate on actual signed digit strings.
Four explicit signed comparisons replace max/min endpoint tests. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 theorem signedValue_not (sign : Bool) (digits : List Bool) :
     signedValue (!sign) digits= -signedValue sign digits := by cases sign <;> simp [signedValue]

 def protectedPalette (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) : CountedValue Bool :=
   let doubled := doubleCounter cutoff
   let source := divideCounter input doubled.count.succ
   let address := canonicalCounter source.remainder
   let shiftRadius := canonicalCounter cutoff
   let modulusBits := canonicalCounter modulus
   let colorBits := canonicalCounter color
   let shiftStart := signedAdd baselineSign false baseline shiftRadius.digits
   let shift := signedAdd shiftStart.negative true shiftStart.digits address.digits
   let lower := signedAdd boundarySign shift.negative boundary shift.digits
   let upperStart := signedAdd false (!boundarySign) modulusBits.digits boundary
   let upper := signedAdd upperStart.negative shift.negative upperStart.digits shift.digits
   let lowerTest := signedLe boundarySign false boundary colorBits.digits
   let shiftedLowerTest := signedLe lower.negative false lower.digits colorBits.digits
   let upperTest := signedLe upperStart.negative false upperStart.digits colorBits.digits
   let shiftedUpperTest := signedLe upper.negative false upper.digits colorBits.digits
   ⟨lowerTest.value && shiftedLowerTest.value && !upperTest.value && !shiftedUpperTest.value,
     doubled.work+source.work+address.work+shiftRadius.work+modulusBits.work+colorBits.work+
     shiftStart.work+shift.work+lower.work+upperStart.work+upper.work+
     lowerTest.work+shiftedLowerTest.work+upperTest.work+shiftedUpperTest.work+20⟩

 

 

end AFT.BinaryArithmetic

end

section























/-! Signed integer data and actual bit algorithms. The decoded integers are
used only in proofs; all running operands remain Boolean lists. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

structure IntegerBits where
  negative : Bool
  digits : List Bool

namespace IntegerBits

def decode (input : IntegerBits) : ℤ := signedValue input.negative input.digits

def zero : IntegerBits := ⟨false,[]⟩
@[simp] theorem zero_value : zero.decode=0 := rfl

def ofSigned (input : SignedResult) : IntegerBits := ⟨input.negative,input.digits⟩

def negate (input : IntegerBits) : CountedValue IntegerBits := ⟨⟨!input.negative,input.digits⟩,2⟩
@[simp] theorem negate_value (input : IntegerBits) : (negate input).value.decode= -input.decode := signedValue_not ..
@[simp] theorem negate_length (input : IntegerBits) : (negate input).value.digits.length=input.digits.length := rfl
@[simp] theorem negate_work (input : IntegerBits) : (negate input).work=2 := rfl

def add (first second : IntegerBits) : CountedValue IntegerBits :=
  let result := signedAdd first.negative second.negative first.digits second.digits
  ⟨ofSigned result,result.work+1⟩
@[simp] theorem add_value (first second : IntegerBits) : (add first second).value.decode=first.decode+second.decode :=
  signedAdd_value ..



def subtract (first second : IntegerBits) : CountedValue IntegerBits :=
  let negative := negate second
  let result := add first negative.value
  ⟨result.value,negative.work+result.work+2⟩
@[simp] theorem subtract_value (first second : IntegerBits) :
    (subtract first second).value.decode=first.decode-second.decode := by
  simp only [subtract,add_value,negate_value,sub_eq_add_neg]



def multiply (first second : IntegerBits) : CountedValue IntegerBits :=
  let product := BinaryArithmetic.multiply first.digits second.digits
  ⟨⟨first.negative ^^ second.negative,product.digits⟩,product.work+2⟩
@[simp] theorem multiply_value (first second : IntegerBits) :
    (multiply first second).value.decode=first.decode*second.decode := by
  simp only [multiply,decode,signedValue,BinaryArithmetic.multiply_value]
  cases first.negative <;> cases second.negative <;> simp



def sumFin : (count : ℕ) → (Fin count → CountedValue IntegerBits) → CountedValue IntegerBits
  | 0,_ => ⟨zero,2⟩
  | count+1,term =>
      let previous := sumFin count (fun index => term index.castSucc)
      let next := term (Fin.last count)
      let result := add previous.value next.value
      ⟨result.value,previous.work+next.work+result.work+2⟩









end IntegerBits
end AFT.BinaryArithmetic

end

section



















/-! Euclidean residues and exact quotients of signed binary integers. No
loop depends on the decoded magnitude. -/
namespace AFT.BinaryArithmetic.IntegerBits
open AFT.RationalRejectionProgram

def residue (input : IntegerBits) (modulus : List Bool) : Result :=
  let division := divide input.digits modulus
  let rest := normalize division.remainder
  if input.negative && !rest.digits.isEmpty then
    let reflected := BinaryArithmetic.subtract false modulus rest.digits
    ⟨reflected.digits,division.work+rest.work+reflected.work+4⟩
  else ⟨rest.digits,division.work+rest.work+4⟩

theorem residue_value (input : IntegerBits) (modulus : List Bool) (hq : 0 < value modulus) :
    (value (residue input modulus).digits : ℤ)=input.decode%(value modulus : ℤ) := by
  have hr := (divide_value input.digits modulus hq).2
  have hn : value (normalize (divide input.digits modulus).remainder).digits=value input.digits%value modulus := by
    rw [normalize_value,hr]
  have hz : (normalize (divide input.digits modulus).remainder).digits.isEmpty=true ↔
      value input.digits%value modulus=0 := by
    rw [List.isEmpty_iff,normalize_nil_iff,hr]
  have hlt := Nat.mod_lt (value input.digits) hq
  cases hs : input.negative with
  | false =>
      simp only [residue,hs,Bool.false_and,Bool.false_eq_true,ite_false,hn,decode,signedValue,Int.natCast_emod]
  | true =>
      by_cases hd : value modulus ∣ value input.digits
      · have he : (normalize (divide input.digits modulus).remainder).digits.isEmpty=true := hz.mpr (Nat.mod_eq_zero_of_dvd hd)
        have hdi : (value modulus : ℤ) ∣ (value input.digits : ℤ) := by exact_mod_cast hd
        simp only [residue,hs,he,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false,hn,
          Nat.mod_eq_zero_of_dvd hd,Nat.cast_zero,decode,signedValue,ite_true,Int.neg_emod,hdi,ite_true]
      · have he : (normalize (divide input.digits modulus).remainder).digits.isEmpty=false := by
          apply Bool.eq_false_iff.mpr
          intro hh
          exact hd (Nat.dvd_of_mod_eq_zero (hz.mp hh))
        have hdi : ¬(value modulus : ℤ) ∣ (value input.digits : ℤ) := by exact_mod_cast hd
        have hsub := BinaryArithmetic.subtract_value modulus
          (normalize (divide input.digits modulus).remainder).digits (by rw [hn];omega)
        simp only [residue,hs,he,Bool.not_false,Bool.true_and,ite_true,hsub,hn,
          decode,signedValue,Int.neg_emod,hdi,ite_false,Int.natAbs_natCast,←Int.natCast_emod]
        exact Int.natCast_sub (by omega)





def exactQuotient (input : IntegerBits) (modulus : List Bool) : CountedValue IntegerBits :=
  let division := divide input.digits modulus
  ⟨⟨input.negative,division.quotient⟩,division.work+2⟩






end AFT.BinaryArithmetic.IntegerBits

end

section




/-! # Executable integral path and rounding-coordinate inverses

The runtime uses integer addition and division on materialized vectors.
The inverse is proved equal to the abstract integral coordinate isomorphism.
-/
namespace AFT
open scoped BigOperators



structure IntegerVectorRun (count : ℕ) where
  value : Vector ℤ count
  work : ℕ

/-- Eliminate the first path vertex, materializing the remaining load once. -/
def pathInverseProgram : (count : ℕ) → Vector ℤ (count+1) → IntegerVectorRun count
  | 0,_ => ⟨Vector.ofFn (fun index => Fin.elim0 index),0⟩
  | count+1,load =>
    let first := load.get 0
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then first else 0)
    let remaining := pathInverseProgram count tail
    ⟨Vector.ofFn (Fin.cons first remaining.value.get),remaining.work+4*(count+1)+2⟩

 

 

 

structure IntegerLoadRun (count : ℕ) where
  value : Vector ℤ (count+1)
  work : ℕ



 

 

 

noncomputable section
 
end

structure IntegerCoordinateRun (count : ℕ) where
  value : Vector ℤ count × ℤ
  work : ℕ

/-- The injection coordinate is the exact total charge divided by q. -/
def roundingInverseProgram (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1)) :
    IntegerCoordinateRun count :=
  let charge := (∑ index,load.get index)/modulus
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  let edges := pathInverseProgram count shifted
  ⟨(edges.value,charge),edges.work+4*(count+1)+3⟩

 

 





noncomputable section
 
end

end AFT

end

section





















/-! Integral path inversion on stored signed bit arrays. Each recursive
stage materializes its tail once and performs only actual bit additions. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def pathTailEntry {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (index : Fin (count+1)) : CountedValue IntegerBits :=
  let next := readVector IntegerBits.zero load index.succ
  let shifted := if index.val=0 then IntegerBits.add next.value first else ⟨next.value,1⟩
  ⟨shifted.value,next.work+shifted.work+3⟩

def binaryPathTail {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits) :
    CountedValue (Vector IntegerBits (count+1)) := storeData (count+1) (pathTailEntry load first)







def binaryPathInverse : (count : ℕ) → Vector IntegerBits (count+1) → CountedValue (Vector IntegerBits count)
  | 0,_ => ⟨#v[],2⟩
  | count+1,load =>
      let first := readVector IntegerBits.zero load 0
      let tail := binaryPathTail load first.value
      let remaining := binaryPathInverse count tail.value
      let result := storeData (count+1) (fun index => Fin.cases ⟨first.value,1⟩
        (fun rest => readVector IntegerBits.zero remaining.value rest) index)
      ⟨result.value,first.work+tail.work+remaining.work+result.work+4⟩





def binaryPathInverseWork (count bits : ℕ) : ℕ := count*(100*(count+bits+3)^2)+2



end AFT.BinaryArithmetic

end

section



















/-! The actual integer rounding-coordinate inverse uses bitwise charge
summation, exact binary long division, signed products and path inversion. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def shiftedLoadEntry {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size)
    (index : Fin size) : CountedValue IntegerBits :=
  let original := readVector IntegerBits.zero load index
  let direction := readVector IntegerBits.zero injection index
  let multiple := IntegerBits.multiply charge direction.value
  let result := IntegerBits.subtract original.value multiple.value
  ⟨result.value,original.work+direction.work+multiple.work+result.work+4⟩

def binaryShiftedLoad {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size) :
    CountedValue (Vector IntegerBits size) := storeData size (shiftedLoadEntry charge injection load)





def binaryShiftedLoadWork (size chargeBits bits : ℕ) : ℕ :=
  size*(6*size+20*(chargeBits+bits+1)^2+20*(2*chargeBits+bits)+27)+2



structure BinaryCoordinateResult (count : ℕ) where
  edges : Vector IntegerBits count
  charge : IntegerBits
  work : ℕ

def binaryRoundingInverse (count : ℕ) (modulus : List Bool)
    (injection load : Vector IntegerBits (count+1)) : BinaryCoordinateResult count :=
  let total := IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)
  let charge := IntegerBits.exactQuotient total.value modulus
  let shifted := binaryShiftedLoad charge.value injection load
  let edges := binaryPathInverse count shifted.value
  ⟨edges.value,charge.value,total.work+charge.work+shifted.work+edges.work+4⟩



def binaryRoundingInverseWork (count modulusBits bits : ℕ) : ℕ :=
  (count+1)*(3*(count+1)+3+20*(count+1+bits)+11)+2+
    (20*(count+1+bits+modulusBits+1)^2+2)+
    binaryShiftedLoadWork (count+1) (count+1+bits) bits+
    binaryPathInverseWork count (2*(count+1+bits)+bits+1)+4



end AFT.BinaryArithmetic

end

section



















/-! Materializing permuted matrix columns and the padded offset uses sequential
array reads and signed bit arithmetic, including every inner-product term. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def readIntegerMatrix {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (column row : Fin size) : CountedValue IntegerBits :=
   let selected := readList matrix.toList column.val
   match selected.data with
   | none => ⟨IntegerBits.zero,selected.work+size+4⟩
   | some entry =>
       let result := readVector IntegerBits.zero entry row
       ⟨result.value,selected.work+result.work+size+4⟩

 

 

 def binaryPermutedColumn (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column : Fin (count+1)) :
     CountedValue (Vector IntegerBits (count+1)) :=
   storeData (count+1) (fun vertex =>
     let row := readVector 0 permutation vertex
     let result := readIntegerMatrix matrix column row.value
     ⟨result.value,row.work+result.work+2⟩)

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

end AFT.BinaryArithmetic

end


