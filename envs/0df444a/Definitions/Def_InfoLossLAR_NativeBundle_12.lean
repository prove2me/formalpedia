-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_12
-- name    : InfoLossLAR_NativeBundle_12
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:44:12.741205+00:00
-- url     : https://prove2.me/theorems/088b52f5-d2c7-4c91-80c5-74eb02e4301c
-- title:
--   Numerical public rejection and final affine emission interfaces
-- statement:
--   This package supplies full-response approximation and numerical error budgets, materialized public proposals and capped rejection, fair-bit tape codecs, completion and integer affine emission, and the final public affine pipeline.
--
--   For fixed security and order, a table producer and public fair-bit tape determine concrete emitted data
--   $$\mathrm{run}(\mathrm{tape})=(M,b,\mathrm{work}),$$
--   where $M$ is stored by integer columns and $b$ is the integer offset. The pipeline draws its layout, evaluates the table producer, completes the public sample, and emits the affine data.
--
--   These definitions provide the common interface for later exact semantic, invertibility, bit-budget and distributional-accuracy theorems. The native work field does not replace the separate genuine PPT proof required by the platform.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/CurrentAFT/CalibratedWeightApproximation.lean, lean/CurrentAFT/CalibrationMatrixRates.lean, lean/CurrentAFT/CalibrationPrecisionRates.lean, lean/CurrentAFT/NumericReferenceBudgets.lean, lean/CurrentAFT/PolynomialErrorEnvelope.lean, lean/CurrentAFT/NumericalLocalConstants.lean, lean/CurrentAFT/NumericalPopulationConstants.lean, lean/CurrentAFT/RationalBackgroundPopulationBound.lean, lean/CurrentAFT/NumericalUnselectedConstants.lean, lean/CurrentAFT/RationalRootGroupBounds.lean, lean/CurrentAFT/NumericalGroupConstants.lean, lean/CurrentAFT/RationalPackedRootProduct.lean, lean/CurrentAFT/RationalPackedRootControl.lean, lean/CurrentAFT/RationalPackedRootSigned.lean, lean/CurrentAFT/RationalPackedRootUntagged.lean, lean/CurrentAFT/RationalPackedRootUntaggedBounds.lean, lean/CurrentAFT/RationalPackedRootScalar.lean, lean/CurrentAFT/RationalPackedRootApproximation.lean, lean/CurrentAFT/RationalPackedRootRates.lean, lean/CurrentAFT/RationalPackedRootBound.lean, lean/CurrentAFT/RationalFullResponseAverages.lean, lean/CurrentAFT/RationalFullResponseApproximation.lean, lean/CurrentAFT/RationalFullResponseRates.lean, lean/CurrentAFT/RationalFullResponseMatrix.lean, lean/CurrentAFT/BinaryFullResponseMatrixEntryProgram.lean, lean/CurrentAFT/CurrentCorePolynomialWork.lean, lean/CurrentAFT/CurrentLayoutDraw.lean, lean/CurrentAFT/CurrentReferenceDrawRates.lean, lean/CurrentAFT/CurrentCoreProposalLaw.lean, lean/CurrentAFT/CurrentCoreProposalRates.lean, lean/CurrentAFT/CurrentProposalPrecision.lean, lean/CurrentAFT/BinaryProposalPrecision.lean, lean/CurrentAFT/BinaryArrayRejection.lean, lean/CurrentAFT/BinaryCoreCharge.lean, lean/CurrentAFT/BinaryCoreChargeCost.lean, lean/CurrentAFT/BinaryCoreChargeResources.lean, lean/CurrentAFT/BinaryCoreWeightData.lean, lean/CurrentAFT/BinaryCoreWeightResources.lean, lean/CurrentAFT/BoundedRejection.lean, lean/CurrentAFT/OptionRejection.lean, lean/CurrentAFT/ClippedRejectionCoin.lean, lean/CurrentAFT/CurrentMaterializedCore.lean, lean/CurrentAFT/CurrentPreparedCoreProposal.lean, lean/CurrentAFT/BinaryPublicRejection.lean, lean/CurrentAFT/BinaryPublicRejectionResources.lean, lean/CurrentAFT/NumericalAffineTransport.lean, lean/CurrentAFT/NumericalPublicCompletion.lean, lean/CurrentAFT/BinaryPublicRejectionLaw.lean, lean/CurrentAFT/BinaryRejectionCap.lean, lean/CurrentAFT/NumericalProposalRates.lean, lean/CurrentAFT/CappedPublicRejection.lean, lean/CurrentAFT/CurrentFlagCostPolynomial.lean, lean/CurrentAFT/UniformPolynomialBound.lean, lean/CurrentAFT/CurrentCompletionResources.lean, lean/CurrentAFT/CurrentMaterializedCompletion.lean, lean/CurrentAFT/CurrentMaterializedCompletionLaw.lean, lean/CurrentAFT/PublicBitTapes.lean, lean/CurrentAFT/BinaryPublicBitCodec.lean, lean/CurrentAFT/BinaryPublicBitCodecResources.lean, lean/CurrentAFT/BinaryPublicBitSizes.lean, lean/CurrentAFT/BinaryPublicBitDecodeProgram.lean, lean/CurrentAFT/BinaryPublicBitDecode.lean, lean/CurrentAFT/CurrentAffineEmissionBridge.lean, lean/CurrentAFT/CurrentEmissionRootOrder.lean, lean/CurrentAFT/CurrentEmissionMetadata.lean, lean/CurrentAFT/CurrentBinaryChartData.lean, lean/CurrentAFT/CurrentBinaryIncidence.lean, lean/CurrentAFT/CurrentBinaryLoadColumns.lean, lean/CurrentAFT/CurrentBinaryBaselines.lean, lean/CurrentAFT/CurrentBinaryOffsetLoad.lean, lean/CurrentAFT/CurrentBinaryAffinePrimitives.lean, lean/CurrentAFT/CurrentBinaryAffineGuard.lean, lean/CurrentAFT/CurrentBinaryAffineEmitter.lean, lean/CurrentAFT/CurrentBinaryLoadResources.lean, lean/CurrentAFT/CurrentBinaryBaselineResources.lean, lean/CurrentAFT/CurrentBinaryOffsetResources.lean, lean/CurrentAFT/CurrentBinaryEmitterResources.lean, lean/CurrentAFT/CurrentBinaryEmitterPolynomial.lean, lean/CurrentAFT/CurrentLinearPhysicalLoad.lean, lean/CurrentAFT/CurrentBinaryLoadSemantic.lean, lean/CurrentAFT/CurrentOffsetPhysicalLoad.lean, lean/CurrentAFT/PublicAffinePipeline.lean, lean/CurrentAFT/PublicAffinePipelineLaw.lean, lean/CurrentAFT/PublicAffinePipelineResources.lean, lean/CurrentAFT/ActualConstructiveProgram.lean, lean/CurrentAFT/BinaryCalibrationWeightSemantic.lean, lean/CurrentAFT/BinaryFullResponseAssembly.lean, lean/CurrentAFT/BinaryRootMetadataMeaning.lean, lean/CurrentAFT/BinaryRootMetadataActual.lean, lean/CurrentAFT/BinaryRootMetadataInput.lean, lean/CurrentAFT/BinaryRootMetadataTransport.lean, lean/CurrentAFT/RationalFullWeightAccuracy.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 6eccfdd40aab3deedf4c774da194c3d7c3546266d64ce0e14f9553c940e779dc. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 6eccfdd40aab3deedf4c774da194c3d7c3546266d64ce0e14f9553c940e779dc. Native10/11 split fallback keeps every original scope-closed data body unchanged and retains the canonical module names as import facades. Current source SHA256 6eccfdd40aab3deedf4c774da194c3d7c3546266d64ce0e14f9553c940e779dc. Header-only omission of a zero-declaration import facade; direct last-part import retains every mathematical declaration, instance, attribute andoption. Lean parser/kernel evidence andfull9429native+2099runtime type/std3 audits pass in native_empty_facades_bypass; all non-import source bytes exact. Current sourceSHA256 f108ae81a83fe7780af1f7ccdaeefd6d0ba141c16228e890f0a1f9e7fdbe2d15. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 8755511f9466859cd2f6fc0dc7e5b3b5ad590645e1aec841e20f552263494f8e. Submission compatibility revision: five simple tactic macros were expanded at all 62 uses into their original ordinary tactic bodies. No mathematical declarations or claims were changed. Full generated-definition build, exact public type comparisons and recursive standard-axiom audits pass. Source SHA256 9546a8f62275ae1465e5decaa16b202a5f5f268fe0bcec2498b1ac251b7204b9.

import Definitions.Def_InfoLossLAR_NativeBundle_11_Part_4

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul































section






















/-! # From rational full-response iteration to the actual calibrated weight

The table error and the true coefficient bound are derived from the
established complete-response stability. The remaining matrix-entry premise
is explicitly a numerical evaluator obligation, not transport accuracy.
-/
namespace CurrentAFT.CalibratedWeightApproximation
open AFT ActualControls ProposalPrimary ControlCoordinates GradedControlAlgebra
  CalibrationPointCoordinates CalibrationTableNorm CalibrationMatrixApproximation
  ActualCompleteStability NumericalWeightEvaluation ControlProduct BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance calibrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def pointBudget (security order steps : ℕ) (entryError : ℝ) : ℝ :=
  (1 + encodeFactor security order) *
    (2 * (3 / 4 : ℝ)^steps + 8 * perturbationFactor security order * entryError)

def weightBudget (security bits order steps : ℕ) (entryError : ℝ) : ℝ :=
  pointBudget security order steps entryError + (Fintype.card (PositiveArity order) : ℝ) *
    (factor security^order * (pointBudget security order steps entryError +
      order * localError security bits * (2 * encodeFactor security order)))









end
end CurrentAFT.CalibratedWeightApproximation

end

section



















/-! # Polynomial conditioning of the actual stored calibration matrix -/
namespace CurrentAFT.CalibrationMatrixRates
open CalibrationTableNorm CalibrationMatrixApproximation CalibrationPointCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance ratesFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def encodeConstant (order : ℕ) : ℝ := (2 * 131072 * 131074 : ℝ)^order
def decodeConstant (order : ℕ) : ℝ := ((order + 1 : ℕ)^2 : ℝ) * (3 * 131072)^order
def countConstant (order : ℕ) : ℝ := ((order + 1 : ℕ)^2 : ℝ) * 131072^order
def comparisonConstant (order : ℕ) : ℝ := 1 + (1 + encodeConstant order) * decodeConstant order
def perturbationConstant (order : ℕ) : ℝ :=
  comparisonConstant order * countConstant order * (1 + encodeConstant order)















end
end CurrentAFT.CalibrationMatrixRates

end

section

































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
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



/-! # Linear bit precision and iteration counts suffice at every fixed order

Polynomial losses in the true coordinate condition number are dominated by
precision `bits = security`. The calibration order is kept fixed throughout;
only the numerical precision and iteration count grow with security.
-/
namespace CurrentAFT.CalibrationPrecisionRates
open AFT CalibrationTableNorm CalibrationMatrixApproximation CalibrationMatrixRates
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base



def entryBudget (constant : ℝ) (degree security : ℕ) : ℝ :=
  constant * (Parameters.base security : ℝ)^degree * (1 / 2 : ℝ)^security





def iterationBudget (order : ℕ) (constant : ℝ) (degree security : ℕ) : ℝ :=
  2 * (3 / 4 : ℝ)^security +
    8 * perturbationFactor security order * entryBudget constant degree security





end
end CurrentAFT.CalibrationPrecisionRates

end

section






















/-! # Current numerical reference budgets at `bits = security`

All constants below are derived from the actual current prime and
population bounds. Exponential precision dominates every fixed public
polynomial; the number of precision bits is not fixed in security.
-/
namespace CurrentAFT.NumericReferenceBudgets
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension







def pairedConstant : ℝ := 512*131072^3*131074















end
end CurrentAFT.NumericReferenceBudgets

end

section





















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.NumericalWeightEvaluation
end CurrentAFT.NumericalWeightEvaluation
namespace CurrentAFT.NumericalWeightEvaluation.localError
end CurrentAFT.NumericalWeightEvaluation.localError
namespace CurrentAFT.NumericalWeightRates
end CurrentAFT.NumericalWeightRates


/-! Polynomial envelopes in the current security base. These are analytic
bounds on explicitly defined errors, not parameters of an executable program. -/
namespace CurrentAFT
open AFT
noncomputable section

def PolynomialErrorEnvelope (value : ℕ → ℝ) : Prop :=
  ∃ constant : ℝ, ∃ degree : ℕ, 0 ≤ constant ∧
    ∀ security, |value security| ≤ constant*(Parameters.base security : ℝ)^degree

namespace PolynomialErrorEnvelope
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

theorem constant (value : ℝ) : PolynomialErrorEnvelope (fun _ => value) :=
  ⟨|value|, 0, abs_nonneg _, fun _ => by simp⟩

theorem mono {value bound : ℕ → ℝ} (h : PolynomialErrorEnvelope bound)
    (hle : ∀ security, |value security| ≤ |bound security|) : PolynomialErrorEnvelope value := by
  obtain ⟨C, d, hC, hh⟩ := h
  exact ⟨C, d, hC, fun n => (hle n).trans (hh n)⟩

theorem add {first second : ℕ → ℝ} (h : PolynomialErrorEnvelope first) (g : PolynomialErrorEnvelope second) :
    PolynomialErrorEnvelope (fun n => first n+second n) := by
  obtain ⟨C, c, hC, hc⟩ := h
  obtain ⟨D, d, hD, hd⟩ := g
  refine ⟨C+D, c+d, add_nonneg hC hD, fun n => ?_⟩
  have hb : (1 : ℝ) ≤ Parameters.base n := by exact_mod_cast (Parameters.base_ge_two n).trans' (by norm_num)
  have hfirst := pow_le_pow_right₀ hb (Nat.le_add_right c d)
  have hsecond := pow_le_pow_right₀ hb (Nat.le_add_left d c)
  exact (abs_add_le _ _).trans (((add_le_add (hc n) (hd n)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hfirst hC) (mul_le_mul_of_nonneg_left hsecond hD))).trans_eq (by ring))

theorem mul {first second : ℕ → ℝ} (h : PolynomialErrorEnvelope first) (g : PolynomialErrorEnvelope second) :
    PolynomialErrorEnvelope (fun n => first n*second n) := by
  obtain ⟨C, c, hC, hc⟩ := h
  obtain ⟨D, d, hD, hd⟩ := g
  refine ⟨C*D, c+d, mul_nonneg hC hD, fun n => ?_⟩
  rw [abs_mul]
  apply (mul_le_mul (hc n) (hd n) (abs_nonneg _) (by positivity)).trans_eq
  rw [pow_add]
  ring

theorem pow {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) (power : ℕ) :
    PolynomialErrorEnvelope (fun n => value n^power) := by
  obtain ⟨C, d, hC, hh⟩ := h
  refine ⟨C^power, d*power, pow_nonneg hC _, fun n => ?_⟩
  rw [abs_pow]
  apply (pow_le_pow_left₀ (abs_nonneg _) (hh n) power).trans_eq
  rw [mul_pow, ← pow_mul]

theorem neg {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) : PolynomialErrorEnvelope (fun n => -value n) :=
  h.mono (fun _ => by rw [abs_neg])

theorem absolute {value : ℕ → ℝ} (h : PolynomialErrorEnvelope value) : PolynomialErrorEnvelope (fun n => |value n|) :=
  h.mono (fun _ => by rw [abs_abs])



theorem sum {Index : Type*} (indices : Finset Index) (value : Index → ℕ → ℝ)
    (h : ∀ index ∈ indices, PolynomialErrorEnvelope (value index)) :
    PolynomialErrorEnvelope (fun security => ∑ index ∈ indices, value index security) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using constant 0
  | @insert index indices hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (h index (Finset.mem_insert_self _ _)).add
      (ih (fun element hm => h element (Finset.mem_insert_of_mem hm)))

theorem div_ge_one {value denominator : ℕ → ℝ} (h : PolynomialErrorEnvelope value)
    (hd : ∀ n, 1 ≤ denominator n) : PolynomialErrorEnvelope (fun n => value n/denominator n) := by
  apply h.mono
  intro n
  rw [abs_div]
  exact div_le_self (abs_nonneg _) ((hd n).trans (le_abs_self _))

theorem base : PolynomialErrorEnvelope (fun n => (Parameters.base n : ℝ)) :=
  ⟨1, 1, by norm_num, fun _ => by rw [abs_of_nonneg (Nat.cast_nonneg _), pow_one, one_mul]⟩

theorem modulus : PolynomialErrorEnvelope (fun n => (Parameters.modulus n : ℝ)) := by
  refine ⟨131072, 64, by norm_num, fun n => ?_⟩
  try dsimp only
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Parameters.modulus_bounds n).2

theorem dimension : PolynomialErrorEnvelope (fun n => (Parameters.dimension n : ℝ)) := by
  refine ⟨131074, 160, by norm_num, fun n => ?_⟩
  try dsimp only
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Parameters.dimension_bounds n).2

theorem legs : PolynomialErrorEnvelope (fun n => (Parameters.legCount n : ℝ)) := by
  simpa only [Parameters.legCount_eq, Nat.cast_pow] using base.pow 128

theorem body : PolynomialErrorEnvelope (fun n => (Parameters.bodySize n : ℝ)) := by
  apply dimension.mono
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (show Parameters.bodySize n ≤ Parameters.dimension n by rw [Parameters.dimension]; omega)



end PolynomialErrorEnvelope
end
end CurrentAFT

end

section
























/-! Polynomial growth of the literal mixed-data local approximation errors.
The fixed order may affect the polynomial; precision still grows in security. -/
namespace CurrentAFT.NumericalLocalConstants
open AFT PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize



theorem first_inverse : PolynomialErrorEnvelope RationalFirstResponseProgram.inverseErrorConstant := by
  unfold RationalFirstResponseProgram.inverseErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem inverse_bound : PolynomialErrorEnvelope RationalDensityInverseProgram.inverseBound := by
  unfold RationalDensityInverseProgram.inverseBound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem mass_lift : PolynomialErrorEnvelope RationalMassLiftProgram.errorConstant := by
  have hf := first_inverse
  have hi := inverse_bound
  unfold RationalMassLiftProgram.errorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem density_inverse : PolynomialErrorEnvelope RationalDensityInverseProgram.errorConstant := by
  have hf := first_inverse
  have hi := inverse_bound
  unfold RationalDensityInverseProgram.errorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem tensor_bound : PolynomialErrorEnvelope RationalTensorInverseProgram.actualBound := by
  have hi := inverse_bound
  unfold RationalTensorInverseProgram.actualBound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem center_error : PolynomialErrorEnvelope RationalBackgroundDensities.centerErrorConstant := by
  unfold RationalBackgroundDensities.centerErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem body_error : PolynomialErrorEnvelope RationalBackgroundDensities.bodyErrorConstant := by
  have hc := center_error
  unfold RationalBackgroundDensities.bodyErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem primary_error : PolynomialErrorEnvelope RationalBackgroundDensities.primaryErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalBackgroundDensities.primaryErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem residual_error : PolynomialErrorEnvelope RationalBackgroundDensities.residualErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalBackgroundDensities.residualErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem free_error : PolynomialErrorEnvelope RationalBackgroundProgram.freeErrorConstant := by
  exact primary_error.add body_error

theorem translation_error : PolynomialErrorEnvelope RationalBackgroundProgram.translationErrorConstant := by
  have hp := primary_error
  have hr := residual_error
  have hb := body_error
  unfold RationalBackgroundProgram.translationErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem coordinate_factor (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalActualFamilyApproximation.coordinateFactor security order) := by
  unfold RationalActualFamilyApproximation.coordinateFactor
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem translation_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.translationBound security order) := by
  unfold RationalBackgroundLinearProgram.translationBound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem mean_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.meanErrorConstant security order) := by
  exact translation_error.add (translation_bound order)

theorem free_mass : PolynomialErrorEnvelope ProposalPrimary.freeMass := by
  unfold ProposalPrimary.freeMass
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem linear_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.linearErrorConstant security order) := by
  apply (free_mass.mul free_error |>.add (PolynomialErrorEnvelope.modulus.mul (mean_error order))).div_ge_one
  intro security
  have hl : 0 < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact pow_pos (Parameters.base_pos security) _
  exact_mod_cast hl

theorem primary_deviation : PolynomialErrorEnvelope RationalPrimaryDeviationProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalPrimaryDeviationProgram.errorConstant RationalPrimaryDeviationProgram.profileErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem marked_seed : PolynomialErrorEnvelope RationalMarkedSeedProgram.inverseErrorConstant := by
  have hi := density_inverse
  have ht := tensor_bound
  have hb := body_error
  unfold RationalMarkedSeedProgram.inverseErrorConstant
  simp only [RationalMarkedSeedProgram.profileBound,
    RationalMarkedSeedProgram.seedErrorConstant, RationalMarkedSeedProgram.meanErrorConstant,
    RationalMarkedSeedProgram.uniformErrorConstant, RationalMarkedSeedProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem marked_pair (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalMarkedPairProgram.errorConstant security order) := by
  have hm := marked_seed
  have hp := primary_deviation
  have hf := free_error
  have hc := coordinate_factor order
  simp only [RationalMarkedPairProgram.errorConstant, RationalMarkedPairProgram.primaryBound,
    RationalMarkedPairProgram.freeBound, RationalActualFamilyApproximation.productError]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem conditional_pair : PolynomialErrorEnvelope RationalConditionalPairProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalConditionalPairProgram.errorConstant
  simp only [RationalConditionalPairProgram.computedBound,
    RationalConditionalPairProgram.profileErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem diffuse_pair : PolynomialErrorEnvelope RationalDiffuseFamilyProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  have hc := center_error
  unfold RationalDiffuseFamilyProgram.errorConstant
  simp only [RationalDiffuseFamilyProgram.primaryErrorConstant,
    RationalDiffuseCertificateProgram.bodyErrorConstant, RationalMassLiftTensorProgram.errorConstant,
    RationalMassLiftTensorProgram.factorBound, RationalDiffuseResidualProgram.pairBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem pair_quadratic (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalPairQuadraticProgram.errorConstant security order) := by
  have hd := diffuse_pair
  have hm := marked_pair order
  have hc := coordinate_factor order
  simp only [RationalPairQuadraticProgram.errorConstant, RationalPairQuadraticProgram.diffuseBound,
    RationalPairQuadraticProgram.markedBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem complete_leg (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalLegBackgroundProgram.errorConstant security order) := by
  have hl := linear_error order
  have hpair := pair_quadratic order
  have hp := conditional_pair
  have ht := translation_error
  have hb := translation_bound order
  have hc := coordinate_factor order
  simp only [RationalLegBackgroundProgram.errorConstant, RationalLegBackgroundProgram.conditionalQuadraticError,
    RationalLegBackgroundProgram.conditionalCubicError, RationalLegBackgroundProgram.conditionalLinearBound,
    RationalLegBackgroundProgram.pairBound, RationalLegBackgroundProgram.quadraticBound,
    RationalLegBackgroundProgram.cubicBound, RationalActualFamilyApproximation.productError]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem root_first : PolynomialErrorEnvelope RationalRootProfileProgram.firstErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalRootProfileProgram.firstErrorConstant
  simp only [RationalRootProfileProgram.preRootError,
    RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem root_mean : PolynomialErrorEnvelope RationalRootProfileProgram.meanErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalRootProfileProgram.meanErrorConstant
  simp only [RationalRootProfileProgram.preRootError,
    RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem singleton (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.errorConstant security order) := by
  have hf := root_first
  have hm := root_mean
  have ht := tensor_bound
  simp only [RationalSingletonProgram.errorConstant, RationalSingletonProgram.inverseBound,
    RationalSingletonProgram.inverseErrorConstant, RationalFamilyProductProgram.growth,
    RationalSingletonProgram.positiveBound, RationalSingletonProgram.firstBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub





end
end CurrentAFT.NumericalLocalConstants

end

section






















/-! # Polynomial errors for the literal fixed-queue three-population program -/
namespace CurrentAFT.NumericalPopulationConstants
open AFT PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize



theorem free_population : PolynomialErrorEnvelope (fun security => (BackgroundPopulationBounds.freeCount security:ℝ)) := by
  apply PolynomialErrorEnvelope.body.mono
  intro security
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (show BackgroundPopulationBounds.freeCount security≤Parameters.bodySize security by
    unfold BackgroundPopulationBounds.freeCount
    omega)

theorem population_bound (order : ℕ) (population : ℕ→ℕ) (A : ℕ→ℝ)
    (hp : PolynomialErrorEnvelope (fun security => (population security:ℝ)))
    (hA : PolynomialErrorEnvelope A) :
    PolynomialErrorEnvelope (fun security => RationalPopulationApproximation.bound order (population security) (A security)) := by
  simp only [RationalPopulationApproximation.bound, RationalFamilyProductProgram.growth, Nat.cast_add, Nat.cast_one]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem population_error (order : ℕ) (population : ℕ→ℕ) (A e : ℕ→ℝ)
    (hp : PolynomialErrorEnvelope (fun security => (population security:ℝ)))
    (hA : PolynomialErrorEnvelope A) (he : PolynomialErrorEnvelope e) :
    PolynomialErrorEnvelope (fun security => RationalPopulationApproximation.error order (population security) (A security) (e security)) := by
  simp only [RationalPopulationApproximation.error, RationalFamilyProductProgram.growth, Nat.cast_add, Nat.cast_one]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem free_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.freeBound security order) := by
  apply population_bound order _ _ free_population
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalMarkedPairProgram.freeBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem queue_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.queueBound security order) :=
  population_bound order _ _ PolynomialErrorEnvelope.modulus (NumericalLocalConstants.translation_bound order)

theorem leg_atom_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legAtomBound security order) := by
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalBackgroundPopulationProgram.legAtomBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem leg_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legBound security order) :=
  population_bound order _ _ PolynomialErrorEnvelope.legs (leg_atom_bound order)

theorem free_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.freeError security order) := by
  apply population_error order _ _ _ free_population _ NumericalLocalConstants.free_error
  have hc := NumericalLocalConstants.coordinate_factor order
  simp only [RationalMarkedPairProgram.freeBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem queue_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.queueError security order) :=
  population_error order _ _ _ PolynomialErrorEnvelope.modulus (NumericalLocalConstants.translation_bound order)
    NumericalLocalConstants.translation_error

theorem leg_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.legError security order) :=
  population_error order _ _ _ PolynomialErrorEnvelope.legs (leg_atom_bound order) (NumericalLocalConstants.complete_leg order)

theorem complete (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.errorConstant security order) := by
  have hfB := free_bound order
  have hqB := queue_bound order
  have hlB := leg_bound order
  have hfE := free_error order
  have hqE := queue_error order
  have hlE := leg_error order
  simp only [RationalBackgroundPopulationProgram.errorConstant, RationalBackgroundPopulationProgram.freeQueueBound,
    RationalBackgroundPopulationProgram.freeQueueError, RationalActualFamilyApproximation.productError]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow



end
end CurrentAFT.NumericalPopulationConstants

end

section




















/-! # A polynomial point bound for the actual complete fixed-queue data -/
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference

def bound (security order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*(freeQueueBound security order*legBound security order)





end
end CurrentAFT.RationalBackgroundPopulationProgram

namespace CurrentAFT.NumericalPopulationConstants
open AFT PolynomialErrorEnvelope
noncomputable section

theorem actual_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundPopulationProgram.bound security order) := by
  have h := (PolynomialErrorEnvelope.constant ((Fintype.card (GradedControlAlgebra.TruncatedArity order):ℝ)^2)).mul
    ((((PolynomialErrorEnvelope.constant ((Fintype.card (GradedControlAlgebra.TruncatedArity order):ℝ)^2)).mul
      (free_bound order)).mul (queue_bound order)).mul (leg_bound order))
  exact h

end
end CurrentAFT.NumericalPopulationConstants

end

section






















/-! Polynomial error growth for the original full three-slot root leg. -/
namespace CurrentAFT.NumericalUnselectedConstants
open AFT PolynomialErrorEnvelope NumericalLocalConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize



theorem leg_at_root : PolynomialErrorEnvelope RationalLegMassProgram.atRootErrorConstant := by
  unfold RationalLegMassProgram.atRootErrorConstant
  simp only [RationalPositiveReferenceProgram.fixedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem leg_mean : PolynomialErrorEnvelope RationalLegMassProgram.meanErrorConstant := by
  have ha := leg_at_root
  unfold RationalLegMassProgram.meanErrorConstant
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem leg_difference : PolynomialErrorEnvelope RationalLegMassProgram.differenceErrorConstant :=
  leg_at_root.add leg_mean

theorem normalized_error (degree : ℕ) (bound profileError : ℕ → ℝ)
    (hb : PolynomialErrorEnvelope bound) (he : PolynomialErrorEnvelope profileError) :
    PolynomialErrorEnvelope (fun security => RationalLegCoefficientExtraction.normalizedError security degree (bound security) (profileError security)) := by
  have ht := tensor_bound
  have hi := density_inverse
  simp only [RationalLegCoefficientExtraction.normalizedError, RationalLegCoefficientExtraction.extractionBound,
    RationalLegCoefficientExtraction.extractionError, RationalTensorInverseProgram.tensorErrorConstant,
    RationalTensorInverseProgram.factorBound, RationalLegCoefficientExtraction.atomErrorConstant,
    RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem higher_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.higherError := by
  unfold RationalUnselectedLegProgram.higherError RationalLegFamilyTable.higherError
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 2) RationalLegMassProgram.differenceErrorConstant
    (constant 2) leg_difference

theorem positive_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.positiveError := by
  unfold RationalUnselectedLegProgram.positiveError RationalLegFamilyTable.positiveError
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 1) RationalLegMassProgram.meanErrorConstant (constant 1) leg_mean

theorem selected_bound (bound : ℝ) : PolynomialErrorEnvelope
    (fun security => LegCoefficientPointBounds.selectedBound security bound) := by
  have ht := tensor_bound
  unfold LegCoefficientPointBounds.selectedBound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem positive_bound : PolynomialErrorEnvelope RationalUnselectedLegProgram.positiveBound := by
  have hb := selected_bound 1
  unfold RationalUnselectedLegProgram.positiveBound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.inverseBound security order) := by
  have hb := positive_bound
  simp only [RationalUnselectedLegProgram.inverseBound, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.inverseError security order) := by
  have hb := positive_bound
  have he := positive_error
  simp only [RationalUnselectedLegProgram.inverseError, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem numerator_bound : PolynomialErrorEnvelope RationalUnselectedLegProgram.numeratorBound := by
  have ht := tensor_bound
  have hs := selected_bound 2
  unfold RationalUnselectedLegProgram.numeratorBound
  simp only [RationalSingletonProgram.firstBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem numerator_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.numeratorError :=
  root_first.add higher_error

theorem unselected_leg (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.errorConstant security order) := by
  have hn := numerator_bound
  have hi := inverse_bound order
  have he := numerator_error
  have hie := inverse_error order
  simp only [RationalUnselectedLegProgram.errorConstant, RationalActualFamilyApproximation.productError]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub



end
end CurrentAFT.NumericalUnselectedConstants

end

section




















/-! # Actual point bounds for every reduced local root column -/
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance groupBoundsFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance groupBoundsSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference

def primaryBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (LocalCoefficientPointBounds.numeratorBound security * RationalNormalizedPrimaryProgram.inverseBound security order)



def ordinaryBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  RationalSingletonProgram.inverseBound security order + 2 * RationalOrdinaryFamilyProgram.atRootBound security order





def legBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalUnselectedLegProgram.numeratorBound security * RationalUnselectedLegProgram.inverseBound security order)



def singletonBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalSingletonProgram.firstBound security * RationalSingletonProgram.inverseBound security order)



def pointBound (security order : ℕ) : ℝ :=
  1 + |primaryBound security order| + |ordinaryBound security order| + |legBound security order| + |singletonBound security order|





end
end CurrentAFT.RationalRootGroupProgram

end

section






















/-! Polynomial bounds on the actual constants of all five grouped columns.
The order is fixed before the security parameter; no final error estimate
is supplied as a hypothesis. -/
namespace CurrentAFT.NumericalGroupConstants
open AFT PolynomialErrorEnvelope NumericalLocalConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize



theorem normalized_error (degree : ℕ) (bound profileError : ℕ → ℝ)
    (hb : PolynomialErrorEnvelope bound) (he : PolynomialErrorEnvelope profileError) :
    PolynomialErrorEnvelope (fun security => RationalCoefficientExtraction.normalizedError security degree (bound security) (profileError security)) := by
  have ht := tensor_bound
  have hi := density_inverse
  simp only [RationalCoefficientExtraction.normalizedError, RationalCoefficientExtraction.extractionBound,
    RationalCoefficientExtraction.extractionError, RationalTensorInverseProgram.tensorErrorConstant,
    RationalTensorInverseProgram.factorBound, RationalCoefficientExtraction.atomErrorConstant,
    RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem positive_reference : PolynomialErrorEnvelope RationalPositiveReferenceProgram.errorConstant := by
  unfold RationalPositiveReferenceProgram.errorConstant
  simp only [RationalPositiveReferenceProgram.fixedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem positive_family : PolynomialErrorEnvelope RationalPositiveFamilyProgram.errorConstant := by
  unfold RationalPositiveFamilyProgram.errorConstant
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 1) RationalPositiveReferenceProgram.errorConstant
    (constant 1) positive_reference

theorem primary_mass : PolynomialErrorEnvelope RationalPrimaryColumnProgram.massErrorConstant := by
  unfold RationalPrimaryColumnProgram.massErrorConstant
  simp only [RationalRootMassProgram.primaryMassErrorConstant, RationalRootMassProgram.fixedErrorConstant,
    RationalRootMassProgram.weightedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem numerator_error : PolynomialErrorEnvelope RationalLocalFamilyProgram.numeratorErrorConstant := by
  unfold RationalLocalFamilyProgram.numeratorErrorConstant
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun security => 2*(Parameters.modulus security : ℝ)^2)
    RationalPrimaryColumnProgram.massErrorConstant ((constant 2).mul (PolynomialErrorEnvelope.modulus.pow 2)) primary_mass

theorem numerator_bound : PolynomialErrorEnvelope LocalCoefficientPointBounds.numeratorBound := by
  have ht := tensor_bound
  unfold LocalCoefficientPointBounds.numeratorBound
  simp only [LocalCoefficientPointBounds.selectedBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem positive_bound (order : ℕ) : PolynomialErrorEnvelope (fun security => PositiveFamilyPointBound.bound security order) := by
  unfold PositiveFamilyPointBound.bound
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem primary_inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.inverseBound security order) := by
  have hp := positive_bound order
  simp only [RationalNormalizedPrimaryProgram.inverseBound, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem primary_inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.inverseErrorConstant security order) := by
  have hp := positive_bound order
  have he := positive_family
  simp only [RationalNormalizedPrimaryProgram.inverseErrorConstant, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem primary_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.primaryErrorConstant security order) := by
  have hn := numerator_bound
  have he := numerator_error
  have hib := primary_inverse_bound order
  have hie := primary_inverse_error order
  simp only [RationalNormalizedPrimaryProgram.primaryErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem singleton_inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.inverseBound security order) := by
  have ht := tensor_bound
  simp only [RationalSingletonProgram.inverseBound, RationalSingletonProgram.positiveBound,
    RationalSingletonProgram.firstBound, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem singleton_inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.inverseErrorConstant security order) := by
  have ht := tensor_bound
  have he := root_mean
  simp only [RationalSingletonProgram.inverseErrorConstant, RationalSingletonProgram.positiveBound,
    RationalSingletonProgram.firstBound, RationalFamilyProductProgram.growth]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem ordinary_profile : PolynomialErrorEnvelope RationalOrdinaryProfileProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  have hc := center_error
  unfold RationalOrdinaryProfileProgram.errorConstant
  simp only [RationalOrdinaryProfileProgram.profileErrorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem ordinary_at_root_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalOrdinaryFamilyProgram.atRootBound security order) := by
  have ht := tensor_bound
  have hi := singleton_inverse_bound order
  simp only [RationalOrdinaryFamilyProgram.atRootBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem ordinary_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalOrdinaryFamilyProgram.errorConstant security order) := by
  have ht := tensor_bound
  have hi := singleton_inverse_bound order
  have hie := singleton_inverse_error order
  have ho := ordinary_profile
  have hb := ordinary_at_root_bound order
  have hc := center_error
  simp only [RationalOrdinaryFamilyProgram.errorConstant, RationalOrdinaryFamilyProgram.meanError,
    RationalOrdinaryFamilyProgram.atRootError, RationalOrdinaryFamilyProgram.independentError,
    RationalActualFamilyApproximation.productError]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalRootGroupProgram.errorConstant security order) := by
  have hp := primary_error order
  have ho := ordinary_error order
  have hl := NumericalUnselectedConstants.unselected_leg order
  have hs := singleton order
  simp only [RationalRootGroupProgram.errorConstant]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub

theorem point_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalRootGroupProgram.pointBound security order) := by
  have hn := numerator_bound
  have hip := primary_inverse_bound order
  have his := singleton_inverse_bound order
  have ho := ordinary_at_root_bound order
  have hnl := NumericalUnselectedConstants.numerator_bound
  have hil := NumericalUnselectedConstants.inverse_bound order
  have ht := tensor_bound
  simp only [RationalRootGroupProgram.pointBound, RationalRootGroupProgram.primaryBound,
    RationalRootGroupProgram.ordinaryBound, RationalRootGroupProgram.legBound,
    RationalRootGroupProgram.singletonBound, RationalSingletonProgram.firstBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub



end
end CurrentAFT.NumericalGroupConstants

end

section






















/-! # The packed product preserves every actual local factor and its joint source -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedProductFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def productActual {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : BackgroundFamilies.ActualFamily security order :=
  ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)





def localGrowth (security order : ℕ) : ℝ :=
  growth order (RationalRootGroupProgram.pointBound security order) (RationalRootGroupProgram.errorConstant security order)



def localProductError (security order count : ℕ) : ℝ :=
  count * RationalRootGroupProgram.errorConstant security order * (localGrowth security order)^count





end
end CurrentAFT.RationalPackedRootProgram

end

section




















/-! # The weighted point column is evaluated on the actual joint controls -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedControlFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedControlSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount











end
end CurrentAFT.RationalPackedRootProgram

end

section




















/-! # The sorted tagged-root entry computes the original joint signed cycle mass -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedSignedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedSignedVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) := instDecidableEqFin _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference rootLaw





def sortedOutput {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : Fin tagged.card → Root security :=
  fun index => (source (tagEmbedding selection tagged (tagOrdering tagged index)).fst).1
    (tagEmbedding selection tagged (tagOrdering tagged index)).snd

def sortedLabels {security : ℕ} (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security) :
    CycleSelections.Selection (Parameters.bodySize security) tagged.card :=
  (tagOrdering tagged).toEmbedding.trans ((Function.Embedding.subtype _).trans layout.toEmbedding)









end
end CurrentAFT.RationalPackedRootProgram

end

section




















/-! # The untagged references in the native joint source program -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedUntaggedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedUntaggedSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
local instance packedUntaggedSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedUntaggedProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference







def untaggedFactor {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) : ℚ :=
  if rootEmbedding selection tagged root ∈ tagged then 1 else
    RootSignedMassProgram.referenceEntry security bits ((source root.fst).1 root.snd).val







end
end CurrentAFT.RationalPackedRootProgram

end

section




















/-! # Untagged reference errors use one factor per actual root slot -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedUntaggedBoundsFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedUntaggedBoundsSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedUntaggedBoundsSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference











end
end CurrentAFT.RationalPackedRootProgram

end

section






















/-! # Scalar errors for the original joint root and control coefficient -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedScalarFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedScalarSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedScalarSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def scalarError (security r s count tags : ℕ) : ℝ :=
  (WeightedPointKernelProgram.errorConstant security r s + 4*count)*(1+4*tags)+4*tags

def scalarBound (security r s tags : ℕ) : ℝ :=
  (1+WeightedPointKernelProgram.errorConstant security r s)*(1+4*tags)

def sourceScalar {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (source : PairedRootInput.GroupInput selection tagged) : ℚ :=
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
    (fun index => (sourceBody index).val.val) word * untagged security bits (actualMetadata selection tagged) word *
      signed security bits (actualMetadata selection tagged) word

def actualScalar {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) : ℝ :=
  PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
    (fun group => (source group).2) * RootWeightedSynthesis.untaggedWeight selection tagged source *
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source













end
end CurrentAFT.RationalPackedRootProgram

end

section






















/-! # The native rational joint sum approximates the actual response data -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  ControlCoordinates GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedApproxFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedApproxSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedApproxSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedApproxSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def sourceError (security order r s count tags : ℕ) : ℝ :=
  (scalarBound security r s tags * count * RationalRootGroupProgram.errorConstant security order +
    scalarError security r s count tags) * (localGrowth security order)^count





def rawErrorConstant (security order r s count tags : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security : ℝ)^(count*3) * sourceError security order r s count tags



end
end CurrentAFT.RationalPackedRootProgram

end

section






















/-! # A polynomial error envelope for the complete packed root channel -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation PolynomialErrorEnvelope
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedRatesFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedRatesSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedRatesSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def kernelErrorBound (security order : ℕ) : ℝ :=
  order*(RationalRootMassProgram.primaryErrorConstant security+
    (RationalRootMassProgram.primaryErrorConstant security*Parameters.modulus security+2))

def uniformScalarBound (security order : ℕ) : ℝ := (1+kernelErrorBound security order)*(1+4*order)

def uniformScalarError (security order : ℕ) : ℝ :=
  (kernelErrorBound security order+8*order)*(1+4*order)+4*order

def errorConstant (security order : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security:ℝ)^(6*order) *
    ((uniformScalarBound security order*(2*order)*RationalRootGroupProgram.errorConstant security order+
      uniformScalarError security order)*(localGrowth security order)^(2*order))











theorem error_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => errorConstant security order) := by
  have hp := NumericalGroupConstants.error order
  have hb := NumericalGroupConstants.point_bound order
  have hc : PolynomialErrorEnvelope RationalRootMassProgram.primaryErrorConstant := by
    change PolynomialErrorEnvelope (fun security => RationalRootMassProgram.primaryErrorConstant security)
    simp only [RationalRootMassProgram.primaryErrorConstant]
    repeat' first
      | exact PolynomialErrorEnvelope.base
      | exact PolynomialErrorEnvelope.dimension
      | exact PolynomialErrorEnvelope.constant _
      | apply PolynomialErrorEnvelope.mul
  simp only [errorConstant, uniformScalarBound, uniformScalarError, kernelErrorBound, localGrowth,
    RationalFamilyProductProgram.growth, CurrentRectangleIndex.colors_eq]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow



end
end CurrentAFT.RationalPackedRootProgram

end

section




















/-! # An actual point bound for the full packed joint response -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedBoundFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedBoundSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedBoundSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedBoundSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def responseBound (security order : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security:ℝ)^(6*order)*(localGrowth security order)^(2*order)







theorem responseBound_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => responseBound security order) := by
  have hp := NumericalGroupConstants.error order
  have hb := NumericalGroupConstants.point_bound order
  simp only [responseBound, localGrowth, RationalFamilyProductProgram.growth, CurrentRectangleIndex.colors_eq]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

end
end CurrentAFT.RationalPackedRootProgram

end

section






















/-! Uniform approximation bounds through bounded tag sums and the actual
two-pool without-replacement average. No number of choices multiplies error. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference

def tagCountBound (security order : ℕ) : ℝ := 1+(order+1)*(Parameters.bodySize security:ℝ)^order
def rootBound (security order : ℕ) : ℝ := tagCountBound security order*RationalPackedRootProgram.responseBound security order
def rootError (security order : ℕ) : ℝ := tagCountBound security order*RationalPackedRootProgram.errorConstant security order



















end
end CurrentAFT.RationalFullResponseProgram

end

section






















/-! Uniform error for the full response with its one shared queue. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference

def fixedQueueBound (security order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order):ℝ)^2*RationalBackgroundPopulationProgram.bound security order*rootBound security order

def fixedQueueError (security order : ℕ) : ℝ :=
  productError order (RationalBackgroundPopulationProgram.bound security order) (rootBound security order)
    (RationalBackgroundPopulationProgram.errorConstant security order) (rootError security order)

def responseError (security order : ℕ) : ℝ := fixedQueueError security order+fixedQueueBound security order

def errorConstant (security order : ℕ) : ℝ := responseError security order+RationalPackedRootProgram.kernelErrorBound security order











end
end CurrentAFT.RationalFullResponseProgram

end

section




















/-! All losses in the literal bounded response calculation are polynomial
at each fixed order; linear precision therefore gives negligible entry error. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT GradedControlAlgebra RationalActualFamilyApproximation PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 1600000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

theorem error_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => errorConstant security order) := by
  have hB := RationalPackedRootProgram.responseBound_polynomial order
  have hE := RationalPackedRootProgram.error_polynomial order
  have hfB := NumericalPopulationConstants.actual_bound order
  have hfE := NumericalPopulationConstants.complete order
  have hc : PolynomialErrorEnvelope RationalRootMassProgram.primaryErrorConstant := by
    change PolynomialErrorEnvelope (fun security => RationalRootMassProgram.primaryErrorConstant security)
    simp only [RationalRootMassProgram.primaryErrorConstant]
    repeat' first
      | exact PolynomialErrorEnvelope.base
      | exact PolynomialErrorEnvelope.dimension
      | exact PolynomialErrorEnvelope.constant _
      | apply PolynomialErrorEnvelope.mul
  simp only [errorConstant, responseError, fixedQueueError, fixedQueueBound, productError, rootBound,
    rootError, tagCountBound, RationalPackedRootProgram.kernelErrorBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow



end
end CurrentAFT.RationalFullResponseProgram

end

section






















/-! Actual rational entries of the full calibration defect. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula RationalActualFamilyApproximation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def matrix (security bits order : ℕ) (output source : Index security order) : ℚ :=
  defect security bits order source.1 (fun index => (source.2.1 index).val)
    (fun index => (source.2.2 index).val.val) output.1
    (fun index => (output.2.1 index).val) (fun index => (output.2.2 index).val.val)

noncomputable section
open scoped Classical
local instance matrixFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference



end
end CurrentAFT.RationalFullResponseProgram

end

section



































/-! The actual full-response program inserted into each valid rectangular entry.
Every query-buffer copy, address decode, and zero-padding branch is executed. -/
namespace CurrentAFT.BinaryFullResponseMatrixEntry
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFullResponseData BinaryRectangleMaterialization
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def validEntry (security bits order : ℕ) (data : Data order)
    (output source : CurrentBinaryRectangleDecode.Data security order) : CountedValue RationalBits :=
  let primary := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.primary
  let body := BinaryNaturalCoordinates.current (CurrentBinaryRectangleDecode.colors_positive security) output.body
  let value := BinaryFullResponseProgram.current security bits order data source.arity source.primary source.body output.arity primary.value body.value
  ⟨value.value,primary.work+body.work+value.work+3⟩

def current (security bits order : ℕ) (data : Data order)
    (output source : Fin (Size security order)) : CountedValue RationalBits :=
  BinaryRectangleEntry.current security order (validEntry security bits order data) output source

noncomputable section
attribute [local irreducible] PublicParameterProgram.modulus
  BinaryFullResponseProgram.current BinaryNaturalCoordinates.current

noncomputable def heightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseResources.heightPolynomial order data precision
noncomputable def validWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseResources.workPolynomial order data precision+Polynomial.C (2*order*(3*order+6)+7)
noncomputable def workPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRectangleEntry.workPolynomial order (validWorkPolynomial order data precision)





end
end CurrentAFT.BinaryFullResponseMatrixEntry

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseMatrixEntry.validWorkPolynomial
  pure ()

end

section


























/-! Closed polynomial bounds for every buffer of the executed current core proposal. -/
namespace CurrentAFT.CurrentCorePolynomialWork
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
open CurrentProposalResources CurrentProposalSamplerPolynomial
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
attribute [local irreducible] PublicParameterProgram.modulus CurrentReferenceDraw.counts CurrentProposalDimensions.current

noncomputable def safePolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial + binaryUniformDrawPolynomial countPolynomial bits + 2 * countPolynomial + 3
noncomputable def anchorPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  widthWorkPolynomial + binaryUniformDrawPolynomial countPolynomial bits + 1
noncomputable def activationPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  2 * primitiveWorkPolynomial height + ticketPolynomial 2 (height + 1) bits + 6
noncomputable def seedPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  activationPolynomial height bits + anchorPolynomial bits + 2 * edgeWorkPolynomial bits + 5
noncomputable def controlPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + ticketPolynomial countPolynomial height bits + 1 +
    CurrentReferenceCacheWork.countsWorkPolynomial + ticketPolynomial countPolynomial height bits + 2 * countPolynomial + 3 + 2
noncomputable def legPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  seedPolynomial height bits + safePolynomial bits + 2
noncomputable def permutationPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPermutationFromTapePolynomial countPolynomial bits +
    countPolynomial * (countPolynomial * (9 * countPolynomial + 8) + 3) + 5

 

 

 

 

 

 



 

noncomputable def workPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial +
    (countPolynomial * (5 * countPolynomial + 5 + controlPolynomial height bits + 4) + 2) +
    (countPolynomial * (legPolynomial height bits + 2) + 2) +
    (countPolynomial * (safePolynomial bits + 2) + 2) +
    permutationPolynomial bits + permutationPolynomial bits +
    (metadataWorkPolynomial + countPolynomial * (6 * countPolynomial + 10) + 4) +
    countPolynomial * bits + countPolynomial * bits + 9

 

 

end
end CurrentAFT.CurrentCorePolynomialWork

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.activationPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.anchorPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.controlPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.legPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.permutationPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.safePolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.seedPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCorePolynomialWork.workPolynomial
  pure ()

end

section




























/-! An independently sampled placement, retained outside the rejection loop.
A canonical role numbering is followed by the same executed finite permutation
program; its two directions remain cached. -/
namespace CurrentAFT.CurrentLayoutDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources
open ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Polynomial
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount CurrentProposalDimensions.current


def canonicalLayout (security : ℕ) : RoleIndex security ≃ BodyIndex security :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by
    have h := ProposalPrimary.population_room security
    unfold BackgroundPopulationBounds.freeCount
    omega))

abbrev Cache (security : ℕ) := CurrentPermutationDraw.CachedPermutation (current security).body
abbrev Tape (security bits : ℕ) := Fin ((current security).body * bits) → Fin 2

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (Cache security) :=
  let result := CurrentPermutationDraw.draw (current security).body bits (Vector.ofFn word)
  ⟨result.value, (current security).work + result.work + (current security).body * bits + 2⟩

def Cache.layout {security : ℕ} (cache : Cache security) : RoleIndex security ≃ BodyIndex security :=
  (canonicalLayout security).trans ((bodyEquiv security).permCongr cache.toEquiv)

noncomputable section
open scoped Classical
local instance layoutNonempty (security : ℕ) : Nonempty (RoleIndex security ≃ BodyIndex security) :=
  ⟨canonicalLayout security⟩









noncomputable def workPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial + CurrentCorePolynomialWork.permutationPolynomial bits + countPolynomial * bits + 2



end
end CurrentAFT.CurrentLayoutDraw

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentLayoutDraw.workPolynomial
  pure ()

end

section
























namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! Actual approximation bounds for the executed primary and safe-body draws.
The table-precision conditions are the explicit current primary-positivity
budget, rather than an assumption on an unspecified proposal oracle. -/
namespace CurrentAFT.CurrentReferenceDrawRates
open AFT ProposalPrimary CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 600000
noncomputable local instance safeFintype (security : ℕ) : Fintype (ActualControls.SafePalette security) := by
  classical
  exact Subtype.fintype _









end
end CurrentAFT.CurrentReferenceDrawRates

end

section





























namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint




/-! Exact law of the executed materialized current proposal, before rejection.
The product decomposition is proved from the actual independent input tapes. -/
namespace CurrentAFT.CurrentCoreProposalLaw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions CurrentCoreProposal
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentCoreProposal.draw CurrentPermutationDraw.draw

abbrev Source (security : ℕ) :=
  (((PublicOutputExperiment.PublicWord security × (Fin (Parameters.legCount security) → LegCore security)) ×
    (Fin (Parameters.modulus security) → FirstHistogram.Palette security)) ×
      Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)) × Equiv.Perm (Fin (Parameters.dimension security))

def assemble (security : ℕ) (source : Source security) : Core security :=
  ⟨source.1.1.1.1, source.1.1.1.2, source.1.1.2, source.1.2, source.2⟩

def controlTapeLaw (security bits : ℕ) : FiniteDist (ControlTape security bits) :=
  (FiniteDist.uniform (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).prod
    (FiniteDist.uniform (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2))

def controlLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    FiniteDist (SafeControlGroups.SafeGroup security) :=
  (controlTapeLaw security bits).map (fun word => (controlDraw security tableBits bits cache word).value)

def legTapeLaw (security bits : ℕ) : FiniteDist (LegTape security bits) :=
  (CurrentPublicSeedDraw.tapeLaw security bits).prod (FiniteDist.uniform (CurrentSafeDraw.Tape security bits))

def legLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (LegCore security) :=
  (legTapeLaw security bits).map (fun word => (legDraw security tableBits bits cache word).value)

def bodyPermutationLaw (security bits : ℕ) : FiniteDist (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)) :=
  (CurrentPermutationDraw.law (current security).body bits).map (CurrentProposalDimensions.bodyEquiv security).permCongr

def endpointPermutationLaw (security bits : ℕ) : FiniteDist (Equiv.Perm (Fin (Parameters.dimension security))) :=
  (CurrentPermutationDraw.law (current security).dimension bits).map (endpointEquiv security).permCongr

def sourceLaw (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (Source security) :=
  (((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlLaw security tableBits bits cache)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legLaw security tableBits bits cache))).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => CurrentSafeDraw.law security bits))).prod
    (bodyPermutationLaw security bits)).prod (endpointPermutationLaw security bits))

def tapeLaw (security bits : ℕ) : FiniteDist (Tapes security bits) :=
  (((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))).prod
    (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2))).prod
    (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2)))

def sourceValue (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) : Source security :=
  (((((fun index => (controlDraw security tableBits bits cache (word.1.1.1.1 index)).value),
      (fun index => (legDraw security tableBits bits cache (word.1.1.1.2 index)).value)),
      (fun index => (CurrentSafeDraw.draw security bits (word.1.1.2 index)).value)),
      (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word.1.2)),
      (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word.2))







def law (security tableBits bits : ℕ) (cache : Cache security tableBits) : FiniteDist (Core security) :=
  (tapeLaw security bits).map (fun word => (draw security tableBits bits cache word).value.core)



end
end CurrentAFT.CurrentCoreProposalLaw

end

section


























/-! Product error of the actual finite-bit current public proposal. -/
namespace CurrentAFT.CurrentCoreProposalRates
open AFT ActualPublicCharge CurrentReferenceDraw CurrentReferenceDrawRates CurrentProposalDimensions
  CurrentCoreProposal CurrentCoreProposalLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize

abbrev ticketError (bits : ℕ) : ℝ := 1 / (2 : ℝ)^bits

def controlError (security tableBits bits : ℕ) : ℝ :=
  2 * ticketError bits + (Parameters.modulus security : ℝ) *
    (64 * (Parameters.base security : ℝ) * Parameters.dimension security +
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2)) * ticketError tableBits

def error (security tableBits bits : ℕ) : ℝ :=
  ((current security).controls : ℝ) * controlError security tableBits bits +
    (Parameters.legCount security : ℝ) * (5 * ticketError bits + ticketError tableBits) +
    (Parameters.modulus security : ℝ) * ticketError bits +
    2 * ((current security).body : ℝ)^2 * ticketError bits +
    2 * ((current security).dimension : ℝ)^2 * ticketError bits















end
end CurrentAFT.CurrentCoreProposalRates

end

section


























/-! A fixed polynomial amount of table precision discharges the actual
primary-positivity budget for every security parameter. Requested ticket
precision remains dynamic. -/
namespace CurrentAFT.CurrentProposalPrecision
open AFT CurrentCoreProposalRates CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base

abbrev padding (security : ℕ) : ℕ := 2^44 * (security + 2)^226
abbrev tableBits (security bits : ℕ) : ℕ := bits + padding security











noncomputable def paddingPolynomial : Polynomial ℕ := 2^44 * (Polynomial.X + 2)^226
@[simp] theorem paddingPolynomial_eval (security : ℕ) : paddingPolynomial.eval security = padding security := by
  simp only [paddingPolynomial, padding, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

end
end CurrentAFT.CurrentProposalPrecision

end

section




























/-! The proposal's polynomial padding is computed by actual counters. -/
namespace CurrentAFT.BinaryProposalPrecision
open AFT BinaryArithmetic Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] addCounter powerCounter multiplyCounter

def current (security bits : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let powered := powerCounter base.count 226
  let padding := multiplyCounter (2^44) powered.count
  let result := addCounter bits padding.count
  ⟨result.count, base.work+powered.work+padding.work+result.work+4⟩



noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  (2*X+1)+227*(6*(X+3)^228+4)+(2^44*(2*(X+2)^226+3)+1)+(2*precision+1)+4



end CurrentAFT.BinaryProposalPrecision

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryProposalPrecision.workPolynomial
  pure ()

end

section




















/-! Binary rejection with sequential reads of the stored random tape.
Every failed attempt materializes its remaining tape suffix explicitly. -/
namespace CurrentAFT.BinaryArrayRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State Tape : Type*} [Inhabited Tape]

def run (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State) :
    (attempts : ℕ) → Vector (Tape × (Fin bits → Fin 2)) attempts → CountedValue State
  | 0, _ => fallback
  | attempts+1, words =>
    let word := readVector default words 0
    let candidate := sample word.value.1
    let raw := score candidate.value
    let ratio := binaryPositiveRatio raw.value envelope
    let accepted := binaryAcceptance ratio.data bits word.value.2
    let used := word.work+candidate.work+raw.work+ratio.work+accepted.work+4
    if accepted.value = 0 then ⟨candidate.value, used⟩ else
      let tail := storeData attempts (fun index => readVector default words index.succ)
      let remaining := run sample score envelope bits fallback attempts tail.value
      ⟨remaining.value, used+tail.work+remaining.work+2⟩



def overhead (limit : ℕ) : ℕ := (limit+1)*(3*limit+5)+15





end CurrentAFT.BinaryArrayRejection

end

section






























/-! # The actual public charge test on materialized core buffers -/
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

def controlTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).controls) :
    CountedValue IntegerBits :=
  let control := readVector (defaultControl security) data.controls index
  let result := CurrentPublicShiftProgram.encode (control.value.2.val.val : ℤ)
  ⟨result.value, control.work+result.work+2⟩

def legTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).legs) :
    CountedValue IntegerBits :=
  let leg := readVector (defaultLeg security) data.legs index
  let input := readVector (CurrentChartsDraw.defaultInput security) data.inputs (legEquiv security index)
  let baseline := CurrentPublicShiftProgram.encode (leg.value.2.val : ℤ)
  let shift := CurrentPublicShiftProgram.current security input.value.1 input.value.2
  let result := IntegerBits.add baseline.value shift.value
  ⟨result.value, leg.work+input.work+baseline.work+shift.work+result.work+5⟩

def queueTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).colors) :
    CountedValue IntegerBits :=
  let baseline := readVector (defaultControl security).1 data.baselines index
  let result := CurrentPublicShiftProgram.encode (baseline.value.val : ℤ)
  ⟨result.value, baseline.work+result.work+2⟩

def total (security : ℕ) (data : MaterializedCore security) : CountedValue IntegerBits :=
  let sizes := CurrentProposalDimensions.current security
  let controls := IntegerBits.sumFin sizes.controls (controlTerm security data)
  let legs := IntegerBits.sumFin sizes.legs (legTerm security data)
  let queues := IntegerBits.sumFin sizes.colors (queueTerm security data)
  let first := IntegerBits.add controls.value legs.value
  let second := IntegerBits.add first.value queues.value
  let removed := CurrentPublicShiftProgram.encode (sizes.legs : ℤ)
  let result := IntegerBits.subtract second.value removed.value
  ⟨result.value, sizes.work+controls.work+legs.work+queues.work+first.work+second.work+removed.work+result.work+8⟩

def current (security : ℕ) (data : MaterializedCore security) : CountedValue Bool :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := canonicalCounter modulus.count
  let numerator := total security data
  let residue := IntegerBits.residue numerator.value encoded.digits
  let reduced := normalize residue.digits
  ⟨reduced.digits.isEmpty, modulus.work+encoded.work+numerator.work+residue.work+reduced.work+6⟩

noncomputable section
open scoped Classical

def numerator (security : ℕ) (core : Core security) : ℤ :=
  (∑ index : PublicOutputExperiment.PublicIndex security, (core.controls index).2.val.val) +
    (∑ leg, (((core.legs leg).2.val : ℤ) + legShift security core leg)) +
    (∑ index, ((core.queueBaselines index).val : ℤ)) - Parameters.legCount security













end
end CurrentAFT.BinaryCoreCharge

end

section


























/-! Complete bit work of the source-independent public charge test. -/
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension CurrentProposalDimensions.current

def colorsBound (security : ℕ) : ℕ := 131072*(security+2)^64
def leafLength (security : ℕ) : ℕ := colorsBound security+2*(security+2)^48+2*(security+2)^2+3
def leafWork (security : ℕ) : ℕ :=
  CurrentPublicShiftProgram.workBound security+100*(colorsBound security+1)^2+
    6*(CurrentProposalDimensions.current security).controls+6*(CurrentProposalDimensions.current security).legs+
    6*(CurrentProposalDimensions.current security).colors+20*leafLength security+30









def totalLength (security : ℕ) : ℕ :=
  (CurrentProposalDimensions.current security).controls+2*(CurrentProposalDimensions.current security).legs+
    (CurrentProposalDimensions.current security).colors+3*leafLength security+5

def totalWork (security : ℕ) : ℕ :=
  let sizes := CurrentProposalDimensions.current security
  sizes.work + sizes.controls*(leafWork security+20*(sizes.controls+leafLength security)+11)+
    sizes.legs*(leafWork security+20*(sizes.legs+leafLength security)+11)+
    sizes.colors*(leafWork security+20*(sizes.colors+leafLength security)+11)+
    50*(sizes.legs+1)^2+60*totalLength security+60



def work (security : ℕ) : ℕ :=
  PublicParameterProgram.workBound security+50*(colorsBound security+1)^2+totalWork security+
    60*(totalLength security+colorsBound security+1)^2+4*(totalLength security+colorsBound security)+18



end CurrentAFT.BinaryCoreCharge

end

section




























/-! Fixed explicit polynomial resources for the actual current charge guard. -/
namespace CurrentAFT.BinaryCoreCharge
open AFT CurrentProposalResources
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current

def colorsPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
def leafLengthPolynomial : Polynomial ℕ := colorsPolynomial+2*(Polynomial.X+2)^48+2*(Polynomial.X+2)^2+3
def leafWorkPolynomial : Polynomial ℕ :=
  shiftWorkPolynomial+100*(colorsPolynomial+1)^2+18*countPolynomial+20*leafLengthPolynomial+30
def totalLengthPolynomial : Polynomial ℕ := 4*countPolynomial+3*leafLengthPolynomial+5
def totalWorkPolynomial : Polynomial ℕ :=
  metadataWorkPolynomial+3*countPolynomial*(leafWorkPolynomial+20*(countPolynomial+leafLengthPolynomial)+11)+
    50*(countPolynomial+1)^2+60*totalLengthPolynomial+60
def workPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+50*(colorsPolynomial+1)^2+totalWorkPolynomial+
    60*(totalLengthPolynomial+colorsPolynomial+1)^2+4*(totalLengthPolynomial+colorsPolynomial)+18













end
end CurrentAFT.BinaryCoreCharge

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreCharge.colorsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreCharge.leafLengthPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreCharge.leafWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreCharge.totalLengthPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreCharge.totalWorkPolynomial
  pure ()

end

section





























/-! Materializing the two actual public control pools for weight evaluation. -/
namespace CurrentAFT.BinaryCoreWeightData
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions BinaryWeightLocal
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.legCount Parameters.bodySize Parameters.dimension

def ordinaryEquiv (security : ℕ) : Fin (CurrentProposalDimensions.current security).ordinary ≃
    Fin (BackgroundRates.ordinaryPool security) := finCongr (current_values security).2.2.2.2.1

def color (security : ℕ) (value : FirstHistogram.Palette security) : Fin (colors security) :=
  value.cast (PublicParameterProgram.modulus_value security).symm

def primaryAddress (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).legs) :
    Fin (CurrentProposalDimensions.current security).controls :=
  ⟨index.val, by
    have h := index.isLt
    have hl := (current_values security).2.1
    have hc := (current_values security).2.2.2.2.2
    omega⟩

def ordinaryAddress (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    CountedValue (Fin (CurrentProposalDimensions.current security).controls) :=
  let sizes := CurrentProposalDimensions.current security
  let address := addCounter sizes.legs index.val
  ⟨⟨address.count, by
    rw [addCounter_value, (current_values security).2.1, (current_values security).2.2.2.2.2]
    have h := index.isLt
    have he := (current_values security).2.2.2.2.1
    omega⟩, sizes.work+address.work+2⟩





def primaryEntry (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) : CountedValue (Fin (colors security) × Fin (colors security)) :=
  let group := readVector (defaultControl security) data.controls (primaryAddress security index)
  ⟨(color security group.value.1, color security group.value.2.val), group.work+2⟩

def ordinaryEntry (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).ordinary) : CountedValue (Fin (colors security)) :=
  let address := ordinaryAddress security index
  let group := readVector (defaultControl security) data.controls address.value
  ⟨color security group.value.2.val, address.work+group.work+2⟩

def groups (security : ℕ) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (colors security) × Fin (colors security)) (CurrentProposalDimensions.current security).legs) :=
  let sizes := CurrentProposalDimensions.current security
  let result := storeData sizes.legs (primaryEntry security data)
  ⟨result.value, sizes.work+result.work+2⟩

def centers (security : ℕ) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (colors security)) (CurrentProposalDimensions.current security).ordinary) :=
  let sizes := CurrentProposalDimensions.current security
  let result := storeData sizes.ordinary (ordinaryEntry security data)
  ⟨result.value, sizes.work+result.work+2⟩





theorem primaryPool_pos (security : ℕ) : 0 < (CurrentProposalDimensions.current security).legs := by
  rw [(current_values security).2.1]
  exact BinaryWeightResources.primaryPool_pos security

theorem bodyPool_pos (security : ℕ) : 0 < (CurrentProposalDimensions.current security).ordinary := by
  rw [(current_values security).2.2.2.2.1]
  exact BackgroundRates.ordinaryPool_pos security

def current (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) : CountedValue RationalBits :=
  let sizes := CurrentProposalDimensions.current security
  let primary := groups security data
  let body := centers security data
  let value := BinaryWeightProgram.current security bits order sizes.legs sizes.ordinary
    (primaryPool_pos security) (bodyPool_pos security) table primary.value body.value
  ⟨value.data, sizes.work+primary.work+body.work+value.work+4⟩

noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current







end
end CurrentAFT.BinaryCoreWeightData

end

section





























/-! Full public-buffer reads and true current weight evaluation resources. -/
namespace CurrentAFT.BinaryCoreWeightData
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions
  CurrentProposalResources BinaryWeightLocal
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current BinaryWeightProgram.current



def entryWorkPolynomial : Polynomial ℕ := metadataWorkPolynomial+5*countPolynomial+8
def gatherWorkPolynomial : Polynomial ℕ := metadataWorkPolynomial+countPolynomial*(entryWorkPolynomial+2)+4









def heightPolynomial (order : ℕ) (precision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightResources.outputHeightPolynomial BinaryPrimaryTable.countPolynomial countPolynomial countPolynomial
    precision tableBound order

def workPolynomial (order : ℕ) (precision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial+2*gatherWorkPolynomial+
    BinaryWeightResources.currentWorkPolynomial BinaryPrimaryTable.countPolynomial countPolynomial countPolynomial
      precision tableBound order+4



end
end CurrentAFT.BinaryCoreWeightData

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreWeightData.entryWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreWeightData.gatherWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoreWeightData.workPolynomial
  pure ()

end

section







/-!
# Finite capped public rejection at one fixed placement

The actual acceptance coin is the public charge indicator times the clipped
weight divided by two. Exact finite-distribution semantics and a legal
fallback give the stated exponential timeout cost. No real-valued coin is
claimed to be a finite-bit implementation by this module.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Core : Type*} [Fintype Core]

def clippedChargeCoin (weight : Core → ℝ) (charge : Core → Prop) (core : Core) : ℝ :=
  if charge core then clip (weight core) / 2 else 0

omit [Fintype Core] in
theorem clippedChargeCoin_bounds (weight : Core → ℝ) (charge : Core → Prop) :
    ∀ core, 0 ≤ clippedChargeCoin weight charge core ∧
      clippedChargeCoin weight charge core ≤ 1 := by
  intro core
  unfold clippedChargeCoin
  split_ifs
  · constructor <;> linarith [clip_nonneg (weight core), clip_le_two (weight core)]
  · norm_num











end

end CurrentAFT

end

section










/-! # Capped public rejection with an explicit failed outcome

Failure returns `none`; it never requires constructing a public core by
choice. The accepted target is exactly the original positive core law.
-/
namespace CurrentAFT.OptionRejection
open AFT
open scoped BigOperators Classical
noncomputable section
variable {Core : Type*} [Fintype Core]
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def weight (value : Core → ℝ) : Option Core → ℝ
  | none => 0
  | some core => value core

def charge (predicate : Core → Prop) : Option Core → Prop
  | none => False
  | some core => predicate core









def ideal (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop) (trials : ℕ) : FiniteDist (Option Core) :=
  (proposal.map some).cappedRejection (clippedChargeCoin (weight value) (charge predicate))
    (clippedChargeCoin_bounds (weight value) (charge predicate)) (CanonicalMoments.pointLaw none) trials





end
end CurrentAFT.OptionRejection

end

section




















/-! # The finite binary coin approximates the actual clipped public weight -/
set_option backward.isDefEq.respectTransparency false

namespace CurrentAFT.ClippedRejectionCoin
open AFT
set_option maxHeartbeats 400000

def raw (accepted : Bool) (score : ℚ) : ℚ := if accepted then score else 0

noncomputable section
open scoped Classical

def probability (bits : ℕ) (accepted : Bool) (score : ℚ) : ℝ :=
  RationalAcceptanceCoin.probability bits (max (raw accepted score) 0 / 2)









def optionCoin {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ) : Option Core → ℝ
  | none => 0
  | some core => probability bits (accepted core) (score core)





end
end CurrentAFT.ClippedRejectionCoin

end

section


























/-! The stored buffers are a representation of the public core, with no
additional sampling freedom in the chart-input vector or inverse rows. -/
namespace CurrentAFT.CurrentCoreProposal
open AFT CurrentProposalDimensions
set_option maxHeartbeats 700000
attribute [local irreducible] CurrentProposalDimensions.current Parameters.legCount Parameters.dimension Parameters.bodySize

 theorem materialized_core_injective (security : ℕ) : Function.Injective (@MaterializedCore.core security) := by
  intro first second hequal
  have hc : first.controls = second.controls := by
    apply Vector.ext
    intro index hindex
    change first.controls.get ⟨index,hindex⟩ = second.controls.get ⟨index,hindex⟩
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.controls (controlsEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hl : first.legs = second.legs := by
    apply Vector.ext
    intro index hindex
    change first.legs.get ⟨index,hindex⟩ = second.legs.get ⟨index,hindex⟩
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.legs (legEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hq : first.baselines = second.baselines := by
    apply Vector.ext
    intro index hindex
    change first.baselines.get ⟨index,hindex⟩ = second.baselines.get ⟨index,hindex⟩
    have h := congrArg (fun core : ActualPublicCharge.Core security =>
      core.queueBaselines (queueEquiv security ⟨index, hindex⟩)) hequal
    simpa only [MaterializedCore.core, decode, Equiv.symm_apply_apply] using h
  have hb : first.body = second.body := by
    apply (CurrentPermutationDraw.cachedEquiv (current security).body).injective
    apply (CurrentProposalDimensions.bodyEquiv security).permCongr.injective
    exact congrArg ActualPublicCharge.Core.bodyPermutation hequal
  have he : first.endpoints = second.endpoints := by
    apply (CurrentPermutationDraw.cachedEquiv (current security).dimension).injective
    apply (endpointEquiv security).permCongr.injective
    exact congrArg ActualPublicCharge.Core.endpointPermutation hequal
  have hi : first.inputs = second.inputs := by
    apply Vector.ext
    intro index hindex
    change first.inputs.get ⟨index, hindex⟩ = second.inputs.get ⟨index, hindex⟩
    rw [first.inputs_correct, second.inputs_correct, hc, hl]
  cases first
  cases second
  cases hc
  cases hl
  cases hq
  cases hb
  cases he
  cases hi
  rfl

noncomputable instance materializedCoreFintype (security : ℕ) : Fintype (MaterializedCore security) :=
  Fintype.ofInjective MaterializedCore.core (materialized_core_injective security)



 

end CurrentAFT.CurrentCoreProposal

end

section






























/-! A complete public proposal program: it generates the shared rational
reference cache, prepares its safe restriction, then emits the materialized
core buffers. Its runtime is bounded by an explicit polynomial for any fixed
polynomial choices of table and fair-bit precision. -/
namespace CurrentAFT.CurrentPreparedCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.RationalRejectionProgram
open CurrentReferenceDraw CurrentCoreProposal CurrentProposalResources
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentCoreProposal.draw BinaryReferenceTables.current
  CurrentReferenceDraw.counts PublicParameterProgram.modulus


def draw (security tableBits bits : ℕ) (word : Tapes security bits) : CountedValue (MaterializedCore security) :=
  let reference := BinaryReferenceTables.current security tableBits
  let cache := prepare security tableBits reference rfl
  let result := CurrentCoreProposal.draw security tableBits bits cache.value word
  ⟨result.value, reference.work + cache.work + result.work + 3⟩

noncomputable section
open scoped Classical

noncomputable def preparePolynomial : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial + countPolynomial * (5 * countPolynomial + 8) + 5

 

noncomputable def workPolynomial (tablePrecision drawPrecision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial tablePrecision + preparePolynomial +
    CurrentCorePolynomialWork.workPolynomial (BinaryReferenceTables.heightPolynomial tablePrecision) drawPrecision + 3

 

noncomputable def cache (security tableBits : ℕ) : Cache security tableBits :=
  (prepare security tableBits (BinaryReferenceTables.current security tableBits) rfl).value

noncomputable def law (security tableBits bits : ℕ) : FiniteDist (MaterializedCore security) :=
  (CurrentCoreProposalLaw.tapeLaw security bits).map (fun word => (draw security tableBits bits word).value)

 

 

end
end CurrentAFT.CurrentPreparedCoreProposal

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentPreparedCoreProposal.preparePolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentPreparedCoreProposal.workPolynomial
  pure ()

end

section






























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RejectionProjection
end CurrentAFT.RejectionProjection






/-! # Actual finite-bit current public rejection

Each attempt produces its public proposal and reference cache, reads the
materialized controls to evaluate the complete joint weight, executes charge,
and uses a binary rational acceptance coin. Failure returns `none`.
-/
namespace CurrentAFT.BinaryPublicRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentPreparedCoreProposal.draw BinaryCoreWeightData.current BinaryCoreCharge.current

def sample (security tableBits drawBits : ℕ) (word : Tapes security drawBits) :
    CountedValue (Option (MaterializedCore security)) :=
  let result := CurrentPreparedCoreProposal.draw security tableBits drawBits word
  ⟨some result.value, result.work+1⟩

def score (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    Option (MaterializedCore security) → CountedValue RationalBits
  | none => ⟨RationalBits.zero, 1⟩
  | some core =>
    let value := BinaryCoreWeightData.current security weightBits order table core
    let charge := BinaryCoreCharge.current security core
    ⟨if charge.value then value.value else RationalBits.zero, value.work+charge.work+3⟩

def current (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Vector (Tapes security drawBits × (Fin coinBits → Fin 2)) attempts) :
    CountedValue (Option (MaterializedCore security)) :=
  let envelope := RationalBits.ofCounter 2
  let result := BinaryArrayRejection.run (sample security tableBits drawBits) (score security weightBits order table)
    envelope.data coinBits ⟨none, 1⟩ attempts words
  ⟨result.value, envelope.work+result.work+1⟩

def decodeResult (security : ℕ) : Option (MaterializedCore security) → Option (ActualPublicCharge.Core security) :=
  Option.map MaterializedCore.core

def draw (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2)) :
    CountedValue (Option (MaterializedCore security)) :=
  let stored := storeData attempts (fun index => ⟨words index, 1⟩)
  let result := current security tableBits drawBits weightBits coinBits order attempts table stored.value
  ⟨result.value, stored.work+result.work+2⟩

noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current

def coreWeight (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (core : ActualPublicCharge.Core security) : ℚ :=
  RationalWeightProgram.current security weightBits order (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (BinaryWeightLocal.rawTable security order table)
    (fun index => ((core.controls (.inl index)).1.val, (core.controls (.inl index)).2.val.val))
    (fun index => (core.controls (.inr index)).2.val.val)

def coreScore (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    Option (ActualPublicCharge.Core security) → ℚ
  | none => 0
  | some core => if ActualPublicCharge.publicCharge security core then coreWeight security weightBits order table core else 0







end
end CurrentAFT.BinaryPublicRejection

end

section





























/-! Polynomial work of the complete proposal, actual joint score, charge,
binary acceptance and all random-tape array reads in the capped loop. -/
namespace CurrentAFT.BinaryPublicRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryCoreWeightData.current BinaryCoreCharge.current CurrentPreparedCoreProposal.draw

def sampleWorkPolynomial (tablePrecision drawPrecision : Polynomial ℕ) : Polynomial ℕ :=
  CurrentPreparedCoreProposal.workPolynomial tablePrecision drawPrecision+1
def scoreWorkPolynomial (order : ℕ) (weightPrecision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoreWeightData.workPolynomial order weightPrecision tableBound+BinaryCoreCharge.workPolynomial+3





def acceptanceWorkPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  dyadicFloorWorkPolynomial height bits+50*(height+bits+1)+20



def stepWorkPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound : Polynomial ℕ) : Polynomial ℕ :=
  let height := BinaryCoreWeightData.heightPolynomial order weightPrecision tableBound
  sampleWorkPolynomial tablePrecision drawPrecision+scoreWorkPolynomial order weightPrecision tableBound+
    2*RationalBits.primitiveWorkPolynomial (height+2)+acceptanceWorkPolynomial (height+2) coinPrecision+9

def workPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ) : Polynomial ℕ :=
  542+cap*(stepWorkPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound+
    (cap+1)*(3*cap+5)+15)



def drawWorkPolynomial (order : ℕ) (tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap : Polynomial ℕ) : Polynomial ℕ :=
  workPolynomial order tablePrecision drawPrecision weightPrecision coinPrecision tableBound cap+3*cap+4



end
end CurrentAFT.BinaryPublicRejection

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.acceptanceWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.drawWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.sampleWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.scoreWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.stepWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPublicRejection.workPolynomial
  pure ()

end

section















/-! # Passing a finite public implementation error to the real Gaussian output

The extra `none` branch realizes the integral identity fallback. A numerical
sampler supplies a distribution on these finite public results, independently
of the hidden source. Its total-variation error is paid once, after all public
sampling steps have been composed. This is an implementation bridge, not a
claim that the required finite-bit sampler has already been constructed.
-/
namespace CurrentAFT.NumericalAffineTransport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport CurrentZeroFiber
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

abbrev PublicResult (security : ℕ) := Option (Sample security)

def realizeResult (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) : PublicResult security → Data security
  | none => fallback security
  | some sample => realize security layout sample

def gaussianChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (result : PublicResult security) : FiniteDist (Word security) :=
  hiddenGaussianOutput security (fun input => (FiniteDist.uniform Unit).map
    (fun _ index => ((realizeResult security layout result).eval input index : ZMod (Parameters.modulus security))))

def gaussianOutput (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (distribution : FiniteDist (PublicResult security)) : FiniteDist (Word security) :=
  distribution.mix (gaussianChannel security layout)









end
end CurrentAFT.NumericalAffineTransport

end

section






















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound




/-! # Composing the current finite-bit core and completion errors

The same fixed placement is used for the full public experiment. A failed
core remains failed, and completion uses the inputs stored by the proposal.
-/
namespace CurrentAFT.NumericalPublicCompletion
open AFT ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize



def targetCore (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist (Option (CachedCore security)) :=
  ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map
    (coreEquiv security).symm).map some











end
end CurrentAFT.NumericalPublicCompletion

end

section





























/-! Probability semantics of the actual binary public rejection program. -/
namespace CurrentAFT.BinaryPublicRejection
open AFT CurrentCoreProposal ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  CurrentPreparedCoreProposal.draw BinaryPublicRejection.draw RationalWeightProgram.current



def law (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (MaterializedCore security)) :=
  (FiniteDist.uniform (Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2))).map
    (fun words => (draw security tableBits drawBits weightBits coinBits order attempts table words).value)



def coin (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) : Option (Core security) → ℝ :=
  ClippedRejectionCoin.optionCoin coinBits (fun core => decide (publicCharge security core))
    (coreWeight security weightBits order table)













end
end CurrentAFT.BinaryPublicRejection

end

section






















/-! Executed polynomial rejection cap and its exact exponential timeout. -/
namespace CurrentAFT.BinaryRejectionCap
open AFT BinaryArithmetic
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus multiplyCounter

def current (security : ℕ) : UnaryCounterResult :=
  let prime := PublicParameterProgram.modulus security
  let scaled := multiplyCounter 8 prime.count
  let result := multiplyCounter scaled.count security
  ⟨result.count, prime.work+scaled.work+result.work+3⟩

theorem current_value (security : ℕ) : (current security).count = 8*Parameters.modulus security*security := by
  simp only [current, multiplyCounter_value, PublicParameterProgram.modulus_value]

noncomputable def countPolynomial : Polynomial ℕ := 8*(131072*(Polynomial.X+2)^64)*Polynomial.X
noncomputable def workPolynomial : Polynomial ℕ := PublicParameterProgram.workPolynomial+
  8*(2*(131072*(Polynomial.X+2)^64)+3)+1+(8*(131072*(Polynomial.X+2)^64))*(2*Polynomial.X+3)+1+3

theorem count_bound (security : ℕ) : (current security).count ≤ countPolynomial.eval security := by
  rw [current_value]
  have hq : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  simp only [countPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  exact Nat.mul_le_mul_right security (Nat.mul_le_mul_left 8 hq)

theorem current_work (security : ℕ) : (current security).work ≤ workPolynomial.eval security := by
  have hq : (PublicParameterProgram.modulus security).count ≤ 131072*(security+2)^64 := by
    rw [PublicParameterProgram.modulus_value]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hw := PublicParameterProgram.modulus_polynomial_work security
  have hs := multiplyCounter_work 8 (PublicParameterProgram.modulus security).count
  have hr := multiplyCounter_work (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security
  have hr' : (multiplyCounter (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security).work ≤
      (8*(PublicParameterProgram.modulus security).count)*(2*security+3)+1 := by
    simpa only [multiplyCounter_value] using hr.le
  have hscaled := Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hq) 3)) 1
  have hresult := Nat.add_le_add_right (Nat.mul_le_mul_right (2*security+3) (Nat.mul_le_mul_left 8 hq)) 1
  change (PublicParameterProgram.modulus security).work+(multiplyCounter 8 (PublicParameterProgram.modulus security).count).work+
    (multiplyCounter (multiplyCounter 8 (PublicParameterProgram.modulus security).count).count security).work+3 ≤ _
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega





end CurrentAFT.BinaryRejectionCap

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRejectionCap.countPolynomial
  pure ()

end

section































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.NumericalWeightEvaluation
end CurrentAFT.NumericalWeightEvaluation
namespace CurrentAFT.NumericalWeightEvaluation.localError
end CurrentAFT.NumericalWeightEvaluation.localError
namespace CurrentAFT.NumericalWeightRates
end CurrentAFT.NumericalWeightRates






/-! All proposal, completion and retry errors of the current finite-bit
public sampler are negligible at the dynamic precision `bits = security`. -/
namespace CurrentAFT.NumericalProposalRates
open AFT Filter NumericalWeightRates Polynomial
open scoped Polynomial Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentProposalDimensions.current







def proposalPolynomial : Polynomial ℕ :=
  let size := CurrentProposalResources.countPolynomial
  size*(2+size*(64*(X+2)*size+(64*(X+2)*size*size+2)))+6*size+size+4*size^2







def completionPolynomial : Polynomial ℕ := 5*CurrentProposalResources.countPolynomial+1







end
end CurrentAFT.NumericalProposalRates

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.NumericalProposalRates.completionPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.NumericalProposalRates.proposalPolynomial
  pure ()

end

section































/-! A single finite-bit rejection driver computes its own retry cap and
reference-table precision. Its input calibration table is materialized data. -/
namespace CurrentAFT.CappedPublicRejection
open AFT BinaryArithmetic RationalNumerics RationalRejectionProgram CurrentCoreProposal
open ActualPublicCharge
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryPublicRejection.draw BinaryRejectionCap.current BinaryProposalPrecision.current

abbrev Tapes (security : ℕ) := Fin (BinaryRejectionCap.current security).count →
  CurrentCoreProposal.Tapes security security × (Fin security → Fin 2)

def current (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (word : Tapes security) : CountedValue (Option (MaterializedCore security)) :=
  let cap := BinaryRejectionCap.current security
  let precision := BinaryProposalPrecision.current security security
  let result := BinaryPublicRejection.draw security precision.count security security security order cap.count table word
  ⟨result.value, cap.work+precision.work+result.work+3⟩



noncomputable section
open scoped Classical
open Polynomial

def tablePrecision : Polynomial ℕ := X+CurrentProposalPrecision.paddingPolynomial



def workPolynomial (order : ℕ) (tableBound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRejectionCap.workPolynomial+BinaryProposalPrecision.workPolynomial X+
    BinaryPublicRejection.drawWorkPolynomial order tablePrecision X X X tableBound BinaryRejectionCap.countPolynomial+3



def law (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (MaterializedCore security)) :=
  (FiniteDist.uniform (Tapes security)).map (fun word => (current security order table word).value)



def error (security : ℕ) (weightError : ℝ) : ℝ :=
  ((BinaryRejectionCap.current security).count : ℝ)*
    (CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security security) security/2+
      (1/(2 : ℝ)^security+weightError/2))+Real.exp (-(security : ℝ))







end
end CurrentAFT.CappedPublicRejection

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CappedPublicRejection.tablePrecision
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CappedPublicRejection.workPolynomial
  pure ()

end

section






















namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration



/-! Actual cost polynomial of the current all-line flag repair and draw. -/
namespace CurrentAFT.CurrentFlagCostPolynomial
open AFT BinaryArithmetic BinaryArithmetic.RationalBits BoundaryCalibration RationalNumerics Polynomial
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def metadata (cutoff modulus baseline : Polynomial ℕ) : Polynomial ℕ :=
  let charts := modulus*(modulus*modulus)
  let features := (2*cutoff+1)*(2*cutoff+1)
  let onLine := 3*cutoff+1+500*(features+(2*cutoff+1)+2)^2+3*(features+cutoff)+5
  let fiber := features*(9*features+4*charts+4*modulus+23)+9*charts+12*modulus+25
  protectedMetadataWorkPolynomial cutoff modulus 1 baseline+(features*(onLine+2)+2)+
    2*(charts*(protectedScaleWorkPolynomial modulus charts+6)+2)+(charts*(fiber+2)+2)+5

def targetHeight (charts colors features atomBits spikeBits : Polynomial ℕ) : Polynomial ℕ :=
  2*atomBits+features*(chartFeatureHeightPolynomial charts colors spikeBits+1)+2

def storedHeight (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  chartProjectionHeightPolynomial charts colors features 0+targetHeight charts colors features 1 (2*charts)

def iterateHeight (charts colors features steps : Polynomial ℕ) : Polynomial ℕ :=
  steps*((3*(charts^2+charts)+1)*storedHeight charts colors features+charts+1)

def targetWork (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors (2*charts))
    (featureWorkPolynomial charts colors (2*charts)+12*features+charts+colors+13)+
    7*primitiveWorkPolynomial (targetHeight charts colors features 1 (2*charts))+11

def regularWork (charts colors features steps : Polynomial ℕ) : Polynomial ℕ :=
  (charts*(spikeWorkPolynomial charts+2)+2)+deletionMatrixWorkPolynomial charts colors features+
    (charts*(targetWork charts colors features+2)+2)+
    (steps*iterationWorkStepPolynomial charts (storedHeight charts colors features) steps+2*charts+2)+
    (charts*(6*charts+10)+2)+5

def scaleWork (charts height : Polynomial ℕ) : Polynomial ℕ :=
  charts*(3*charts+3+60*(charts+1)^2+2*primitiveWorkPolynomial (height+charts)+5+2)+2

def drawWork (charts height bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPositiveDrawPolynomial charts height bits+7*charts+13

def current (cutoff modulus baseline precision bits : Polynomial ℕ) : Polynomial ℕ :=
  let charts := modulus*(modulus*modulus)
  let features := (2*cutoff+1)*(2*cutoff+1)
  let steps := precision+(4*(2*cutoff+1)^2+4)
  let height := iterateHeight charts modulus features steps
  let storedMetadata := metadata cutoff modulus baseline
  let regular := storedMetadata+(storedMetadata+C CurrentFlagPublicProgram.half.work+regularWork charts modulus features steps+3+
    scaleWork charts height+2)+drawWork charts (height+charts) bits+3
  let marked := storedMetadata+(storedMetadata+(charts*(spikeWorkPolynomial charts+2)+2)+scaleWork charts (2*charts)+3)+
    drawWork charts (3*charts) bits+3
  regular+marked+2+protectedScaleWorkPolynomial modulus charts+6





end
end CurrentAFT.CurrentFlagCostPolynomial

end

section





/-! Polynomial witnesses for specified natural-number resource functions,
uniform at every security parameter. This predicate has no program field. -/
namespace CurrentAFT

def UniformPolynomialBound (resource : ℕ → ℕ) : Prop :=
  ∃ polynomial : Polynomial ℕ, ∀ security, resource security ≤ polynomial.eval security

namespace UniformPolynomialBound

theorem constant (value : ℕ) : UniformPolynomialBound (fun _ => value) :=
  ⟨Polynomial.C value, fun _ => by simp⟩

theorem identity : UniformPolynomialBound id :=
  ⟨Polynomial.X, fun _ => by simp⟩

theorem polynomial (value : Polynomial ℕ) : UniformPolynomialBound value.eval :=
  ⟨value, fun _ => le_rfl⟩

theorem mono {first second : ℕ → ℕ} (h : UniformPolynomialBound second)
    (hle : ∀ security, first security ≤ second security) : UniformPolynomialBound first := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun security => (hle security).trans (hp security)⟩

theorem add {first second : ℕ → ℕ} (h : UniformPolynomialBound first) (g : UniformPolynomialBound second) :
    UniformPolynomialBound (fun n => first n+second n) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := g
  exact ⟨p+q, fun n => by simpa only [Polynomial.eval_add] using Nat.add_le_add (hp n) (hq n)⟩

theorem mul {first second : ℕ → ℕ} (h : UniformPolynomialBound first) (g : UniformPolynomialBound second) :
    UniformPolynomialBound (fun n => first n*second n) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := g
  exact ⟨p*q, fun n => by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul (hp n) (hq n)⟩

theorem pow {resource : ℕ → ℕ} (h : UniformPolynomialBound resource) (power : ℕ) :
    UniformPolynomialBound (fun n => resource n^power) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p^power, fun n => by simpa only [Polynomial.eval_pow] using Nat.pow_le_pow_left (hp n) power⟩



end UniformPolynomialBound
end CurrentAFT

end

section
































namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration






/-! Polynomial work of the actual completed public flag/chart draws.
All public inputs are stored by the proposal; no chart or shift oracle is
supplied to the runtime theorem. -/
namespace CurrentAFT.CurrentCompletionResources
open AFT BinaryArithmetic RationalNumerics RationalRejectionProgram
open BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount
  CurrentFlagCompletionProgram.draw CurrentChartsDraw.draw PublicParameterProgram.modulus



def flagWork (security precision bits : ℕ) : ℕ :=
  PublicParameterProgram.workBound security+(2*security+1)+powerCounterWork (security+2) 2+
    (2*(security+2)^2+1)+CurrentPublicShiftProgram.workBound security+
    CurrentFlagChartDraw.workBound (Parameters.sourceCutoff security-1) (Parameters.modulus security)
      (2*(security+2)^48+2*(security+2)^2+2) precision bits+6



def chartsWork (security precision bits : ℕ) : ℕ :=
  (2*security+1)+powerCounterWork (security+2) 128+
    Parameters.legCount security*(3*Parameters.legCount security+flagWork security precision bits+7)+5



def work (security precision bits edgeBits : ℕ) : ℕ :=
  chartsWork security precision bits+CurrentEdgeDrawProgram.workBound security edgeBits+3



noncomputable section
open Polynomial

def flagPolynomial (precision bits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+(2*X+1)+3*(6*(X+3)^4+4)+(2*(X+2)^2+1)+
    CurrentProposalResources.shiftWorkPolynomial+
    CurrentFlagCostPolynomial.current ((X+2)^2) CurrentProposalResources.primeSizePolynomial
      (2*(X+2)^48+2*(X+2)^2+2) precision bits+6



def chartsPolynomial (precision bits : Polynomial ℕ) : Polynomial ℕ :=
  let count := CurrentProposalResources.countPolynomial
  (2*X+1)+129*(6*(X+3)^130+4)+count*(3*count+flagPolynomial precision bits+7)+5



def workPolynomial (precision bits edgeBits : Polynomial ℕ) : Polynomial ℕ :=
  chartsPolynomial precision bits+CurrentProposalSamplerPolynomial.edgeWorkPolynomial edgeBits+3



end
end CurrentAFT.CurrentCompletionResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCompletionResources.chartsPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCompletionResources.flagPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentCompletionResources.workPolynomial
  pure ()

end

section






























/-! The completed public sample retains every actual buffer required by the
integer affine emitter. The semantic sample is only its decoder. -/
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT GaussianSource BinaryArithmetic RationalRejectionProgram
open CurrentCoreProposal CurrentAffineData
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentChartsDraw.drawStored CurrentEdgeDrawProgram.draw
  CappedPublicRejection.current

structure Result (security : ℕ) where
  core : MaterializedCore security
  charts : Vector (Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))) (Parameters.legCount security)
  edge : Window (DiffuseProfiles.edgeCutoff security)

def Result.sample {security : ℕ} (result : Result security) : CurrentPublicAffineSample.Sample security :=
  ((result.core.core, result.charts.get), result.edge)

def complete (security : ℕ) (input : Option (MaterializedCore security)) (precision bits edgeBits : ℕ)
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) : CountedValue (Option (Result security)) :=
  match input with
  | none => ⟨none, 1⟩
  | some core =>
    let charts := CurrentChartsDraw.drawStored security core.inputs precision bits word.1
    let edge := CurrentEdgeDrawProgram.draw security edgeBits word.2
    ⟨some ⟨core, charts.value, edge.value⟩, charts.work+edge.work+3⟩





abbrev Tapes (security : ℕ) := CappedPublicRejection.Tapes security × CurrentPublicCompletion.Tapes security security security

def current (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (word : Tapes security) :
    CountedValue (Option (Result security)) :=
  let core := CappedPublicRejection.current security order table word.1
  let result := complete security core.value security security security word.2
  ⟨result.value, core.work+result.work+2⟩

noncomputable section
open scoped Classical
open Polynomial

def workPolynomial (order : ℕ) (tableBound : Polynomial ℕ) : Polynomial ℕ :=
  CappedPublicRejection.workPolynomial order tableBound+CurrentCompletionResources.workPolynomial X X X+2



end
end CurrentAFT.CurrentMaterializedCompletion

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentMaterializedCompletion.workPolynomial
  pure ()

end

section




























/-! Exact probability semantics and Gaussian error of the executed public
core-and-completion program, uniformly for every fixed public placement. -/
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT ActualPublicCharge CurrentCoreProposal CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CappedPublicRejection.current CurrentMaterializedCompletion.current





def publicLaw (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    FiniteDist (Option (CurrentPublicAffineSample.Sample security)) :=
  (FiniteDist.uniform (CurrentMaterializedCompletion.Tapes security)).map
    (fun word => Option.map Result.sample (current security order table word).value)



def totalError (security : ℕ) (weightError : ℝ) : ℝ :=
  CappedPublicRejection.error security weightError+CurrentPublicCompletion.errorBound security security security security/2









end
end CurrentAFT.CurrentMaterializedCompletion

end

section






























/-! Explicit flat fair-bit tapes for all current public sampling stages.
Products split consecutive bits; indexed families use the native role
numberings, never an arbitrarily chosen finite equivalence. -/
namespace CurrentAFT.PublicBitTapes
open AFT CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

structure Encoding (State : Type*) where
  bits : ℕ
  equiv : (Fin bits → Fin 2) ≃ State

def bits (count : ℕ) : Encoding (Fin count → Fin 2) := ⟨count, Equiv.refl _⟩

def flag : Encoding Bool := ⟨1,
  { toFun := fun word => finTwoEquiv (word 0)
    invFun := fun value _ => finTwoEquiv.symm value
    left_inv := by intro word; funext index; have h : index=0 := Subsingleton.elim _ _; subst index; simp
    right_inv := fun _ => finTwoEquiv.apply_symm_apply _ }⟩

def split (first second : ℕ) : (Fin (first+second) → Fin 2) ≃
    ((Fin first → Fin 2) × (Fin second → Fin 2)) where
  toFun word := (fun index => word (finSumFinEquiv (.inl index)), fun index => word (finSumFinEquiv (.inr index)))
  invFun pair index := Sum.elim pair.1 pair.2 (finSumFinEquiv.symm index)
  left_inv word := by
    funext index
    obtain ⟨left | right, rfl⟩ := finSumFinEquiv.surjective index <;> simp
  right_inv pair := by
    apply Prod.ext <;> funext index <;> simp

def Encoding.prod {First Second : Type*} (first : Encoding First) (second : Encoding Second) : Encoding (First×Second) :=
  ⟨first.bits+second.bits, (split first.bits second.bits).trans (Equiv.prodCongr first.equiv second.equiv)⟩

def Encoding.indexed {Index State : Type*} {count : ℕ} (ordering : Fin count ≃ Index)
    (encoding : Encoding State) : Encoding (Index → State) :=
  ⟨count*encoding.bits, (FiniteConditionProgram.groupBits count encoding.bits).trans
    (Equiv.arrowCongr ordering encoding.equiv)⟩

def edge (security precision : ℕ) : Encoding (CurrentPublicSeedDraw.EdgeTape security precision) :=
  bits (AFT.RationalNumerics.windowTicketBits (DiffuseProfiles.edgeCutoff security) precision)

def safe (security precision : ℕ) : Encoding (CurrentSafeDraw.Tape security precision) :=
  bits (precision+(CurrentReferenceDraw.counts security).safe+1)

def control (security precision : ℕ) : Encoding (ControlTape security precision) :=
  (bits (precision+(PublicParameterProgram.modulus security).count+1)).prod (safe security precision)

def seed (security precision : ℕ) : Encoding (CurrentPublicSeedDraw.Tape security precision) :=
  (bits (precision+2+1)).prod (flag.prod
    ((bits (precision+(CurrentAnchorIndexDraw.width security).count+1)).prod
      ((edge security precision).prod (edge security precision))))

def leg (security precision : ℕ) : Encoding (LegTape security precision) :=
  (seed security precision).prod (safe security precision)

def core (security precision : ℕ) : Encoding (CurrentCoreProposal.Tapes security precision) :=
  ((((control security precision).indexed (CurrentProposalDimensions.controlsEquiv security)).prod
      ((leg security precision).indexed (CurrentProposalDimensions.legEquiv security))).prod
    ((safe security precision).indexed (CurrentProposalDimensions.queueEquiv security))).prod
      (bits ((CurrentProposalDimensions.current security).body*precision)) |>.prod
      (bits ((CurrentProposalDimensions.current security).dimension*precision))

def charts (security precision : ℕ) : Encoding (CurrentChartsDraw.Tapes security precision) :=
  (flag.prod (bits (precision+Parameters.modulus security*(Parameters.modulus security*Parameters.modulus security)+1))).indexed
    (CurrentProposalDimensions.legEquiv security)

def completion (security : ℕ) : Encoding (CurrentPublicCompletion.Tapes security security security) :=
  (charts security security).prod (edge security security)

def rejection (security : ℕ) : Encoding (CappedPublicRejection.Tapes security) :=
  ((core security security).prod (bits security)).indexed (Equiv.refl (Fin (BinaryRejectionCap.current security).count))

def materialized (security : ℕ) : Encoding (CurrentMaterializedCompletion.Tapes security) :=
  (rejection security).prod (completion security)

abbrev Tapes (security : ℕ) := CurrentLayoutDraw.Tape security security × CurrentMaterializedCompletion.Tapes security

def current (security : ℕ) : Encoding (Tapes security) :=
  (bits ((CurrentProposalDimensions.current security).body*security)).prod (materialized security)

noncomputable section
open scoped Classical





end
end CurrentAFT.PublicBitTapes

end

section
































/-! Counted materialization of nested finite bit buffers. Every leaf is copied
from the stored flat input by sequential reads. Product offsets and row-major
addresses are computed by the actual unary counter programs. -/
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram PublicBitTapes
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

structure Codec (State : Type*) where
  encoding : Encoding State
  prepare : UnaryCounterResult
  prepare_value : prepare.count = encoding.bits
  read : {total : ℕ} → Vector (Fin 2) total → (offset : ℕ) →
    offset + encoding.bits ≤ total → CountedValue State
  bound : ℕ → ℕ
  read_value : ∀ {total} (input : Vector (Fin 2) total) offset room,
    (read input offset room).value = encoding.equiv
      (fun index => input.get ⟨offset+index.val, by omega⟩)
  read_work : ∀ {total} (input : Vector (Fin 2) total) offset room,
    (read input offset room).work ≤ bound total

def copy {total : ℕ} (input : Vector (Fin 2) total) (offset count : ℕ)
    (room : offset+count≤total) : CountedValue (Vector (Fin 2) count) :=
  storeData count (fun index =>
    let address := addCounter offset index.val
    let entry := readVector 0 input ⟨address.count, by rw [addCounter_value]; omega⟩
    ⟨entry.value,address.work+entry.work+2⟩)

theorem copy_get {total} (input : Vector (Fin 2) total) offset count room (index : Fin count) :
    (copy input offset count room).value.get index = input.get ⟨offset+index.val, by omega⟩ := by
  simp only [copy,storeData_get,readVector_value,addCounter_value]

theorem copy_work {total} (input : Vector (Fin 2) total) offset count room :
    (copy input offset count room).work ≤ count*(5*total+8)+2 := by
  apply storeData_work count (5*total+6)
  intro index
  have h := readVector_work (0:Fin 2) input
    (⟨(addCounter offset index.val).count, by rw [addCounter_value]; omega⟩:Fin total)
  have ho : offset≤total := by omega
  simp only [addCounter_work]
  omega

def bits (count : ℕ) : Codec (Fin count → Fin 2) where
  encoding := PublicBitTapes.bits count
  prepare := ⟨count,1⟩
  prepare_value := rfl
  read := fun input offset room =>
    let result := copy input offset count room
    ⟨result.value.get,result.work+1⟩
  bound := fun total => count*(5*total+8)+3
  read_value := by
    intro total input offset room
    funext index
    exact copy_get input offset count room index
  read_work := by
    intro total input offset room
    have h := copy_work input offset count room
    change _+1≤_
    omega

def map {First Second : Type*} (codec : Codec First) (equiv : First ≃ Second) : Codec Second where
  encoding := ⟨codec.encoding.bits,codec.encoding.equiv.trans equiv⟩
  prepare := codec.prepare
  prepare_value := codec.prepare_value
  read := fun input offset room =>
    let result := codec.read input offset room
    ⟨equiv result.value,result.work+2⟩
  bound := fun total => codec.bound total+2
  read_value := by
    intro total input offset room
    simp only [codec.read_value,Equiv.trans_apply]
  read_work := by
    intro total input offset room
    exact Nat.add_le_add_right (codec.read_work input offset room) 2

def bitsCast (count other : ℕ) (same : count=other) : Codec (Fin other → Fin 2) :=
  map (bits count) (Equiv.arrowCongr (finCongr same) (Equiv.refl _))

theorem bitsCast_encoding (count other : ℕ) (same : count=other) :
    (bitsCast count other same).encoding = PublicBitTapes.bits other := by
  subst other
  rfl

def flag : Codec Bool := map (bits 1)
  { toFun := fun word => finTwoEquiv (word 0)
    invFun := fun value _ => finTwoEquiv.symm value
    left_inv := by intro word; funext index; have h : index=0 := Subsingleton.elim _ _; subst index; simp
    right_inv := fun _ => finTwoEquiv.apply_symm_apply _ }

theorem flag_encoding : flag.encoding = PublicBitTapes.flag := rfl

def prod {First Second : Type*} (first : Codec First) (second : Codec Second) : Codec (First×Second) where
  encoding := first.encoding.prod second.encoding
  prepare :=
    let left := first.prepare
    let right := second.prepare
    let result := addCounter left.count right.count
    ⟨result.count,left.work+right.work+result.work+2⟩
  prepare_value := by simp only [addCounter_value,first.prepare_value,second.prepare_value,Encoding.prod]
  read := fun input offset room =>
    let address := addCounter offset first.encoding.bits
    let left := first.read input offset (by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    let right := second.read input address.count (by rw [addCounter_value]; change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    ⟨(left.value,right.value),address.work+left.work+right.work+3⟩
  bound := fun total => first.bound total+second.bound total+2*total+4
  read_value := by
    intro total input offset room
    simp only [first.read_value,second.read_value,addCounter_value,Encoding.prod,
      Equiv.trans_apply,Equiv.prodCongr_apply,PublicBitTapes.split,Equiv.coe_fn_mk]
    congr 1
    apply congrArg
    funext index
    congr 1
    apply Fin.ext
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
    omega
  read_work := by
    intro total input offset room
    have hl := first.read_work input offset (by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    have hr := second.read_work input (addCounter offset first.encoding.bits).count (by rw [addCounter_value]; change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega)
    have ho : offset≤total := by change offset+(first.encoding.bits+second.encoding.bits)≤_ at room; omega
    change (addCounter offset first.encoding.bits).work+_+_+3≤_
    rw [addCounter_work]
    omega

def indexed {Index State : Type*} {count : ℕ} (ordering : Fin count ≃ Index)
    (codec : Codec State) : Codec (Index → State) where
  encoding := codec.encoding.indexed ordering
  prepare :=
    let inner := codec.prepare
    let result := multiplyCounter count inner.count
    ⟨result.count,inner.work+result.work+2⟩
  prepare_value := by simp only [multiplyCounter_value,codec.prepare_value,Encoding.indexed]
  read := fun {total} input offset room =>
    let stored := storeData count (fun row =>
      let product := multiplyCounter row.val codec.encoding.bits
      let address := addCounter offset product.count
      let result := codec.read input address.count (by
        rw [addCounter_value,multiplyCounter_value]
        change offset+count*codec.encoding.bits≤total at room
        have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
        nlinarith)
      ⟨result.value,product.work+address.work+result.work+3⟩)
    ⟨fun index => stored.value.get (ordering.symm index),stored.work+1⟩
  bound := fun total =>
    count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+5)+3
  read_value := by
    intro total input offset room
    funext index
    simp only [storeData_get,codec.read_value,addCounter_value,multiplyCounter_value,
      Encoding.indexed,Equiv.trans_apply,Equiv.arrowCongr_apply,
      AFT.FiniteConditionProgram.groupBits,Equiv.coe_fn_mk]
    apply congrArg
    funext bit
    congr 1
    apply Fin.ext
    simp only [finProdFinEquiv, Equiv.coe_fn_mk]
    ring
  read_work := by
    intro total input offset room
    have hs := storeData_work count
      (count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+3)
      (fun row =>
        let product := multiplyCounter row.val codec.encoding.bits
        let address := addCounter offset product.count
        let result := codec.read input address.count (by
          rw [addCounter_value,multiplyCounter_value]
          change offset+count*codec.encoding.bits≤total at room
          have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
          nlinarith)
        (⟨result.value,product.work+address.work+result.work+3⟩:CountedValue State)) (by
        intro row
        have hh := codec.read_work input (addCounter offset (multiplyCounter row.val codec.encoding.bits).count).count (by
          rw [addCounter_value,multiplyCounter_value]
          change offset+count*codec.encoding.bits≤total at room
          have hm := Nat.mul_le_mul_right codec.encoding.bits (show row.val+1≤count by omega)
          nlinarith)
        have hm := Nat.mul_le_mul_right (2*codec.encoding.bits+3) (show row.val≤count by omega)
        have ho : offset≤total := by change offset+count*codec.encoding.bits≤total at room; omega
        simp only [multiplyCounter_work,addCounter_work]
        omega)
    change _+1≤_
    have heq : count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+3+2) =
        count*(count*(2*codec.encoding.bits+3)+1+(2*total+1)+codec.bound total+5) := by ring
    rw [heq] at hs
    omega

/-- Read the input tape once into an actual stored flat buffer, then build all
nested output buffers with the counted codec. -/
def decode {State : Type*} (codec : Codec State)
    (word : Fin codec.encoding.bits → Fin 2) : CountedValue State :=
  let preparation := codec.prepare
  let input := storeData preparation.count
    (fun index => ⟨word (Fin.cast codec.prepare_value index),1⟩)
  let stored := input.value.cast codec.prepare_value
  let result := codec.read stored 0 (by omega)
  ⟨result.value,preparation.work+input.work+result.work+2⟩

def decodeBound {State : Type*} (codec : Codec State) : ℕ :=
  codec.prepare.work+3*codec.encoding.bits+codec.bound codec.encoding.bits+4





/-- Type casts only identify the native computed lengths with their specified
lengths. They do not evaluate a separate semantic parameter search. -/
def decodeAs {State : Type*} (codec : Codec State) (target : Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) : CountedValue State :=
  decode codec (fun index => word (Fin.cast (congrArg Encoding.bits same) index))





end CurrentAFT.BinaryPublicBitCodec

end

section






























/-! Compositional polynomial bounds for materialized bit-buffer codecs.
These lemmas follow the actual preparation and sequential-copy programs; no
runtime bound for a completed decoder is assumed. -/
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] UniformPolynomialBound

structure UniformCodec {State : ℕ → Type*} (codec : ∀ security, Codec (State security)) : Prop where
  bits : UniformPolynomialBound (fun n => (codec n).encoding.bits)
  prepare : UniformPolynomialBound (fun n => (codec n).prepare.work)
  bound : ∀ total : ℕ → ℕ, UniformPolynomialBound total →
    UniformPolynomialBound (fun n => (codec n).bound (total n))

theorem bits_uniform (count : ℕ → ℕ) (hc : UniformPolynomialBound count) :
    UniformCodec (fun n => bits (count n)) := by
  refine ⟨hc,UniformPolynomialBound.constant 1,?_⟩
  intro total ht
  exact (hc.mul (((UniformPolynomialBound.constant 5).mul ht).add
    (UniformPolynomialBound.constant 8))).add (UniformPolynomialBound.constant 3)

theorem map_uniform {First Second : ℕ → Type*} (codec : ∀ n, Codec (First n))
    (equiv : ∀ n, First n ≃ Second n) (h : UniformCodec codec) :
    UniformCodec (fun n => map (codec n) (equiv n)) := by
  refine ⟨h.bits,h.prepare,?_⟩
  intro total ht
  exact (h.bound total ht).add (UniformPolynomialBound.constant 2)

theorem bitsCast_uniform (count other : ℕ → ℕ) (same : ∀ n, count n=other n)
    (hc : UniformPolynomialBound count) :
    UniformCodec (fun n => bitsCast (count n) (other n) (same n)) :=
  map_uniform _ _ (bits_uniform count hc)

theorem flag_uniform : UniformCodec (fun _ => flag) :=
  map_uniform _ _ (bits_uniform (fun _ => 1) (UniformPolynomialBound.constant 1))

theorem prod_uniform {First Second : ℕ → Type*} (first : ∀ n, Codec (First n))
    (second : ∀ n, Codec (Second n)) (hf : UniformCodec first) (hs : UniformCodec second) :
    UniformCodec (fun n => prod (first n) (second n)) := by
  refine ⟨hf.bits.add hs.bits,?_,?_⟩
  · have hp := ((hf.prepare.add hs.prepare).add
      (((UniformPolynomialBound.constant 2).mul hf.bits).add (UniformPolynomialBound.constant 1))).add
        (UniformPolynomialBound.constant 2)
    simpa only [prod,addCounter_work,Codec.prepare_value] using hp
  · intro total ht
    exact (((hf.bound total ht).add (hs.bound total ht)).add
      ((UniformPolynomialBound.constant 2).mul ht)).add (UniformPolynomialBound.constant 4)

theorem indexed_uniform {Index State : ℕ → Type*} (count : ℕ → ℕ)
    (ordering : ∀ n, Fin (count n) ≃ Index n) (codec : ∀ n, Codec (State n))
    (hc : UniformPolynomialBound count) (h : UniformCodec codec) :
    UniformCodec (fun n => indexed (ordering n) (codec n)) := by
  refine ⟨hc.mul h.bits,?_,?_⟩
  · have hp := (h.prepare.add ((hc.mul (((UniformPolynomialBound.constant 2).mul h.bits).add
      (UniformPolynomialBound.constant 3))).add (UniformPolynomialBound.constant 1))).add
        (UniformPolynomialBound.constant 2)
    simpa only [indexed,multiplyCounter_work,Codec.prepare_value] using hp
  · intro total ht
    exact (hc.mul (((((hc.mul (((UniformPolynomialBound.constant 2).mul h.bits).add
      (UniformPolynomialBound.constant 3))).add (UniformPolynomialBound.constant 1)).add
      (((UniformPolynomialBound.constant 2).mul ht).add (UniformPolynomialBound.constant 1))).add
      (h.bound total ht)).add (UniformPolynomialBound.constant 5))).add
        (UniformPolynomialBound.constant 3)

theorem decode_uniform {State : ℕ → Type*} (codec : ∀ n, Codec (State n)) (h : UniformCodec codec) :
    UniformPolynomialBound (fun n => decodeBound (codec n)) :=
  ((h.prepare.add ((UniformPolynomialBound.constant 3).mul h.bits)).add
    (h.bound _ h.bits)).add (UniformPolynomialBound.constant 4)

end
end CurrentAFT.BinaryPublicBitCodec

end

section




























/-! Executed lengths and preparation of every current flat-tape leaf. The
native prime, safe interval, anchor width, edge window, placement dimensions,
and rejection cap are computed by their counted parameter programs. -/
namespace CurrentAFT.BinaryPublicBitSizes
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics
open scoped Polynomial
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

structure Lengths where
  activation : ℕ
  control : ℕ
  safe : ℕ
  anchor : ℕ
  edge : ℕ
  chart : ℕ
  body : ℕ
  endpoint : ℕ
  work : ℕ

def assemble (security colors safeCount anchorWidth cutoff population dimension : ℕ) : Lengths :=
  let activation := addCounter security 3
  let controlFirst := addCounter security colors
  let control := addCounter controlFirst.count 1
  let safeFirst := addCounter security safeCount
  let safe := addCounter safeFirst.count 1
  let anchorFirst := addCounter security anchorWidth
  let anchor := addCounter anchorFirst.count 1
  let doubleCutoff := doubleCounter cutoff
  let interval := addCounter doubleCutoff.count 1
  let edgeFirst := addCounter security interval.count
  let edge := addCounter edgeFirst.count 2
  let square := multiplyCounter colors colors
  let cube := multiplyCounter colors square.count
  let chartFirst := addCounter security cube.count
  let chart := addCounter chartFirst.count 1
  let body := multiplyCounter population security
  let endpoint := multiplyCounter dimension security
  ⟨activation.count,control.count,safe.count,anchor.count,edge.count,chart.count,body.count,endpoint.count,
    activation.work+controlFirst.work+control.work+safeFirst.work+safe.work+anchorFirst.work+anchor.work+
      doubleCutoff.work+interval.work+edgeFirst.work+edge.work+square.work+cube.work+chartFirst.work+chart.work+
      body.work+endpoint.work+20⟩

structure Data extends Lengths where
  dimensions : CurrentProposalDimensions.Result
  retries : UnaryCounterResult

def current (security : ℕ) : Data :=
  let dimensions := CurrentProposalDimensions.current security
  let reference := CurrentReferenceDraw.counts security
  let anchor := CurrentAnchorIndexDraw.width security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let retry := BinaryRejectionCap.current security
  let result := assemble security dimensions.colors reference.safe anchor.count cutoff.quotient
    dimensions.body dimensions.dimension
  { toLengths := {result with work := dimensions.work+reference.work+anchor.work+cutoff.work+retry.work+result.work+6}
    dimensions := dimensions
    retries := retry }

theorem dimensions_value (security : ℕ) :
    (current security).dimensions = CurrentProposalDimensions.current security := rfl

theorem retries_value (security : ℕ) :
    (current security).retries = BinaryRejectionCap.current security := rfl

theorem activation_value (security : ℕ) : (current security).activation = security+3 := by
  simp only [current,assemble,addCounter_value]

theorem control_value (security : ℕ) :
    (current security).control = security+(PublicParameterProgram.modulus security).count+1 := by
  simp only [current,assemble,addCounter_value]
  rw [(CurrentProposalDimensions.current_values security).1,PublicParameterProgram.modulus_value]

theorem safe_value (security : ℕ) :
    (current security).safe = security+(CurrentReferenceDraw.counts security).safe+1 := by
  simp only [current,assemble,addCounter_value]

theorem anchor_value (security : ℕ) :
    (current security).anchor = security+(CurrentAnchorIndexDraw.width security).count+1 := by
  simp only [current,assemble,addCounter_value]

theorem edge_value (security : ℕ) :
    (current security).edge = windowTicketBits (DiffuseProfiles.edgeCutoff security) security := by
  simp only [current,assemble,addCounter_value,doubleCounter_value,CurrentEdgeDrawProgram.cutoff_value,
    windowTicketBits]

theorem chart_value (security : ℕ) :
    (current security).chart = security+Parameters.modulus security*(Parameters.modulus security*Parameters.modulus security)+1 := by
  simp only [current,assemble,addCounter_value,multiplyCounter_value,
    (CurrentProposalDimensions.current_values security).1]

theorem body_value (security : ℕ) :
    (current security).body = (CurrentProposalDimensions.current security).body*security := by
  simp only [current,assemble,multiplyCounter_value]

theorem endpoint_value (security : ℕ) :
    (current security).endpoint = (CurrentProposalDimensions.current security).dimension*security := by
  simp only [current,assemble,multiplyCounter_value]

/-- Polynomial expression for the work of the actual fixed arithmetic plan. -/
def formula {R : Type*} [Semiring R] (security colors safeCount anchorWidth cutoff population dimension : R) : R :=
  (2*security+1)+(2*security+1)+(2*(security+colors)+1)+
    (2*security+1)+(2*(security+safeCount)+1)+(2*security+1)+(2*(security+anchorWidth)+1)+
    (3*cutoff+1)+(2*(2*cutoff)+1)+(2*security+1)+(2*(security+(2*cutoff+1))+1)+
    (colors*(2*colors+3)+1)+(colors*(2*(colors*colors)+3)+1)+
    (2*security+1)+(2*(security+colors*(colors*colors))+1)+
    (population*(2*security+3)+1)+(dimension*(2*security+3)+1)+20

theorem assemble_work (security colors safeCount anchorWidth cutoff population dimension : ℕ) :
    (assemble security colors safeCount anchorWidth cutoff population dimension).work =
      formula security colors safeCount anchorWidth cutoff population dimension := by
  simp only [assemble,addCounter_value,multiplyCounter_value,doubleCounter_value,
    addCounter_work,multiplyCounter_work,doubleCounter_work,formula]

theorem formula_mono {security first second anchor cutoff population dimension
    colors safeCount width window body endpoints : ℕ}
    (hc : first≤colors) (hs : second≤ safeCount) (ha : anchor≤width)
    (hw : cutoff≤window) (hb : population≤body) (hd : dimension≤endpoints) :
    formula security first second anchor cutoff population dimension ≤
      formula security colors safeCount width window body endpoints := by
  unfold formula
  gcongr

noncomputable section
open CurrentProposalResources CurrentProposalSamplerPolynomial CurrentReferenceCacheWork
attribute [local irreducible] CurrentProposalDimensions.current CurrentReferenceDraw.counts
  CurrentAnchorIndexDraw.width CurrentEdgeDrawProgram.cutoffProgram BinaryRejectionCap.current
  PublicParameterProgram.modulus

def workPolynomial : Polynomial ℕ :=
  metadataWorkPolynomial+countsWorkPolynomial+widthWorkPolynomial+edgeCutoffWorkPolynomial+
    BinaryRejectionCap.workPolynomial+
    formula Polynomial.X countPolynomial countPolynomial countPolynomial
      cutoffSizePolynomial countPolynomial countPolynomial+6

theorem current_work (security : ℕ) :
    (current security).work ≤ workPolynomial.eval security := by
  have hm := CurrentProposalResources.metadata_work security
  have hr := CurrentReferenceCacheWork.counts_work security
  have ha := CurrentProposalSamplerPolynomial.width_work security
  have he := CurrentEdgeDrawProgram.cutoff_work security
  rw [← edgeCutoffWorkPolynomial_eval] at he
  have ht := BinaryRejectionCap.current_work security
  have hc := (CurrentProposalResources.count_bounds security).2.2.1
  have hs := (CurrentReferenceCacheWork.native_bounds security).2.1
  have hw := CurrentProposalSamplerPolynomial.width_count security
  have hb := (CurrentProposalResources.count_bounds security).2.2.2.1
  have hd := (CurrentProposalResources.count_bounds security).2.2.2.2
  have hcut : (CurrentEdgeDrawProgram.cutoffProgram security).quotient ≤ cutoffSizePolynomial.eval security := by
    rw [CurrentEdgeDrawProgram.cutoff_value]
    simp only [cutoffSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_ofNat]
    unfold DiffuseProfiles.edgeCutoff
    exact (Nat.div_le_self _ _).trans (by
      simpa only [Parameters.sourceCutoff,Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have hf := formula_mono (security:=security) hc hs hw hcut hb hd
  change (CurrentProposalDimensions.current security).work+(CurrentReferenceDraw.counts security).work+
    (CurrentAnchorIndexDraw.width security).work+(CurrentEdgeDrawProgram.cutoffProgram security).work+
    (BinaryRejectionCap.current security).work+_+6≤_
  rw [assemble_work]
  simp only [workPolynomial,formula,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] at hf ⊢
  omega

end
end CurrentAFT.BinaryPublicBitSizes

end

section































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PublicBitResources
end CurrentAFT.PublicBitResources




/-! The literal flat random tape is copied and split into stored public
buffers. All lengths are computed once by the counted preparation program. -/
namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current

variable (security : ℕ) (sizes : BinaryPublicBitSizes.Data) (correct : sizes=BinaryPublicBitSizes.current security)

def edge : Codec (CurrentPublicSeedDraw.EdgeTape security security) :=
  bitsCast sizes.edge _ (by rw [correct]; exact BinaryPublicBitSizes.edge_value security)

def safe : Codec (CurrentSafeDraw.Tape security security) :=
  bitsCast sizes.safe _ (by rw [correct]; exact BinaryPublicBitSizes.safe_value security)

def control : Codec (ControlTape security security) :=
  prod (bitsCast sizes.control _ (by rw [correct]; exact BinaryPublicBitSizes.control_value security))
    (safe security sizes correct)

def seed : Codec (CurrentPublicSeedDraw.Tape security security) :=
  prod (bitsCast sizes.activation _ (by rw [correct]; simpa only [Nat.add_assoc] using BinaryPublicBitSizes.activation_value security))
    (prod flag (prod (bitsCast sizes.anchor _ (by rw [correct]; exact BinaryPublicBitSizes.anchor_value security))
      (prod (edge security sizes correct) (edge security sizes correct))))

def leg : Codec (LegTape security security) :=
  prod (seed security sizes correct) (safe security sizes correct)

def withCount {Index State : Type*} {count other : ℕ} (same : count=other)
    (ordering : Fin other ≃ Index) (codec : Codec State) : Codec (Index → State) :=
  indexed ((finCongr same).trans ordering) codec

def core : Codec (CurrentCoreProposal.Tapes security security) :=
  prod (prod (prod (prod
    (withCount (count:=sizes.dimensions.controls) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.controlsEquiv security) (control security sizes correct))
    (withCount (count:=sizes.dimensions.legs) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.legEquiv security) (leg security sizes correct)))
    (withCount (count:=sizes.dimensions.colors) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.queueEquiv security) (safe security sizes correct)))
    (bitsCast sizes.body _ (by rw [correct]; exact BinaryPublicBitSizes.body_value security)))
    (bitsCast sizes.endpoint _ (by rw [correct]; exact BinaryPublicBitSizes.endpoint_value security))

def charts : Codec (CurrentChartsDraw.Tapes security security) :=
  withCount (count:=sizes.dimensions.legs) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
    (CurrentProposalDimensions.legEquiv security)
    (prod flag (bitsCast sizes.chart _ (by rw [correct]; exact BinaryPublicBitSizes.chart_value security)))

def completion : Codec (CurrentPublicCompletion.Tapes security security security) :=
  prod (charts security sizes correct) (edge security sizes correct)

def rejection : Codec (CappedPublicRejection.Tapes security) :=
  withCount (count:=sizes.retries.count) (by rw [correct,BinaryPublicBitSizes.retries_value])
    (Equiv.refl (Fin (BinaryRejectionCap.current security).count))
    (prod (core security sizes correct) (bits security))

def materialized : Codec (CurrentMaterializedCompletion.Tapes security) :=
  prod (rejection security sizes correct) (completion security sizes correct)

def codec : Codec (PublicBitTapes.Tapes security) :=
  prod (bitsCast sizes.body _ (by rw [correct]; exact BinaryPublicBitSizes.body_value security))
    (materialized security sizes correct)

 theorem prod_encoding {First Second : Type*} (first : Codec First) (second : Codec Second) :
    (prod first second).encoding=first.encoding.prod second.encoding := rfl

 theorem withCount_encoding {Index State : Type*} {count other : ℕ} (same : count=other)
    (ordering : Fin other ≃ Index) (code : Codec State) :
    (withCount same ordering code).encoding=code.encoding.indexed ordering := by
  subst other
  rfl

theorem codec_encoding : (codec security sizes correct).encoding=PublicBitTapes.current security := by
  simp only [codec,materialized,rejection,completion,charts,core,leg,seed,control,safe,edge,
    prod_encoding,withCount_encoding,bitsCast_encoding,flag_encoding]
  unfold PublicBitTapes.current
  rfl

def current (security : ℕ) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CountedValue (PublicBitTapes.Tapes security) :=
  let sizes := BinaryPublicBitSizes.current security
  let decoded := decodeAs (codec security sizes rfl) (PublicBitTapes.current security)
    (codec_encoding security sizes rfl) word
  ⟨decoded.value,sizes.work+decoded.work+1⟩



noncomputable section


attribute [local irreducible] UniformPolynomialBound

def workBound (security : ℕ) : ℕ :=
  (BinaryPublicBitSizes.current security).work+
    decodeBound (codec security (BinaryPublicBitSizes.current security) rfl)+1



end
end CurrentAFT.BinaryPublicBitDecode

end

section






























namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current

 theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (bound : ∀ security, resource security≤polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,bound⟩
attribute [local irreducible] UniformPolynomialBound

theorem work_uniform : UniformPolynomialBound workBound := by
  have hcontrols : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).controls) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).1)
  have hlegs : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).legs) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.1)
  have hcolors : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).colors) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.1)
  have hbody : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).body) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.2.1)
  have hdimension : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).dimension) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.2.2)
  have hq : UniformPolynomialBound Parameters.modulus :=
    hcolors.mono (fun n => by rw [(CurrentProposalDimensions.current_values n).1])
  have hnativeq : UniformPolynomialBound (fun n => (PublicParameterProgram.modulus n).count) :=
    hq.mono (fun n => by rw [PublicParameterProgram.modulus_value])
  have hsafe : UniformPolynomialBound (fun n => (CurrentReferenceDraw.counts n).safe) :=
    hq.mono (fun n => by rw [(CurrentReferenceDraw.counts_values n).2.2]; exact Nat.sub_le ..)
  have hanchor : UniformPolynomialBound (fun n => (CurrentAnchorIndexDraw.width n).count) := by
    refine of_bound _ CurrentProposalResources.anchorSizePolynomial (fun n => ?_)
    simp only [CurrentAnchorIndexDraw.width_value,DiffuseProfiles.anchorWidth_eq,
      CurrentProposalResources.anchorSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_ofNat,Parameters.base,le_refl]
  have hcutoff : UniformPolynomialBound DiffuseProfiles.edgeCutoff := by
    refine of_bound _ CurrentProposalResources.cutoffSizePolynomial (fun n => ?_)
    simp only [CurrentProposalResources.cutoffSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_ofNat,DiffuseProfiles.edgeCutoff,Parameters.sourceCutoff,Parameters.base]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hretry : UniformPolynomialBound (fun n => (BinaryRejectionCap.current n).count) :=
    of_bound _ BinaryRejectionCap.countPolynomial BinaryRejectionCap.count_bound
  have hprep : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).work) :=
    of_bound _ BinaryPublicBitSizes.workPolynomial BinaryPublicBitSizes.current_work
  have hactivation : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).activation) := by
    simpa only [id_eq,BinaryPublicBitSizes.activation_value] using UniformPolynomialBound.identity.add (UniformPolynomialBound.constant 3)
  have hcontrol : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).control) := by
    simpa only [id_eq,BinaryPublicBitSizes.control_value] using (UniformPolynomialBound.identity.add hnativeq).add (UniformPolynomialBound.constant 1)
  have hsafeBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).safe) := by
    simpa only [id_eq,BinaryPublicBitSizes.safe_value] using (UniformPolynomialBound.identity.add hsafe).add (UniformPolynomialBound.constant 1)
  have hanchorBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).anchor) := by
    simpa only [id_eq,BinaryPublicBitSizes.anchor_value] using (UniformPolynomialBound.identity.add hanchor).add (UniformPolynomialBound.constant 1)
  have hedge : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).edge) := by
    simpa only [id_eq,BinaryPublicBitSizes.edge_value,RationalNumerics.windowTicketBits] using
      (UniformPolynomialBound.identity.add (((UniformPolynomialBound.constant 2).mul hcutoff).add (UniformPolynomialBound.constant 1))).add (UniformPolynomialBound.constant 2)
  have hchart : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).chart) := by
    simpa only [id_eq,BinaryPublicBitSizes.chart_value] using
      (UniformPolynomialBound.identity.add (hq.mul (hq.mul hq))).add (UniformPolynomialBound.constant 1)
  have hbodyBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).body) := by
    simpa only [id_eq,BinaryPublicBitSizes.body_value] using hbody.mul UniformPolynomialBound.identity
  have hendpoint : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).endpoint) := by
    simpa only [id_eq,BinaryPublicBitSizes.endpoint_value] using hdimension.mul UniformPolynomialBound.identity
  have hc : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.controls) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hcontrols
  have hl : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.legs) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hlegs
  have hq' : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.colors) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hcolors
  have hr : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).retries.count) := by
    simpa only [BinaryPublicBitSizes.retries_value] using hretry
  have hcodec : UniformCodec (fun n => codec n (BinaryPublicBitSizes.current n) rfl) := by
    unfold codec materialized rejection completion charts core leg seed control safe edge withCount
    repeat' first
      | apply prod_uniform
      | apply indexed_uniform
      | apply bitsCast_uniform
      | apply bits_uniform
      | exact flag_uniform
      | exact hactivation
      | exact hcontrol
      | exact hsafeBits
      | exact hanchorBits
      | exact hedge
      | exact hchart
      | exact hbodyBits
      | exact hendpoint
      | exact hc
      | exact hl
      | exact hq'
      | exact hr
      | exact UniformPolynomialBound.identity
  exact (hprep.add (decode_uniform _ hcodec)).add (UniformPolynomialBound.constant 1)

theorem work_exists : ∃ polynomial : Polynomial ℕ, ∀ security, workBound security≤polynomial.eval security := by
  simpa only [UniformPolynomialBound] using work_uniform

noncomputable def workPolynomial : Polynomial ℕ := Classical.choose work_exists



end
end CurrentAFT.BinaryPublicBitDecode

end

section























/-! Identifying executable path-coordinate inversion with the current affine
data. The identification uses injectivity of the fixed rounding matrix. The
noncomputable extension-correction witness is never an executed input. -/
namespace CurrentAFT.CurrentAffineEmissionBridge
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean CurrentAffineGeometry CurrentAffineLoad
  LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount


def linearLoad (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) : Fin (Parameters.dimension security) → ℤ :=
  fun vertex =>
    ((relabeledBasis (bodyEdges security) (Parameters.legCount security)
      (placement security core) (attachments security layout) (relabeling security layout core)
      ((numberedMatrix (bodyEdges security) (Parameters.legCount security) scale shear).mulVec
        (splitSource security input).1)).val +
      (splitSource security input).2 • AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core))
          ((dimensionEquiv security).symm vertex)

 

 

 

 

 



end
end CurrentAFT.CurrentAffineEmissionBridge

end

section




























/-! Actual cached path-root positions for the physical root order
attachments, centers, queues. The explicit rotation maps that order to the
placement's center, queue, attachment order before two stored permutation reads. -/
namespace CurrentAFT.CurrentEmissionRootOrder
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources CurrentCoreProposal
open ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount
  CurrentCoreProposal.draw addCounter subtractCounter lessCounter


def rotate (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) : CountedValue (Fin count) :=
  let boundary := subtractCounter count front
  let selected := lessCounter index.val front
  if h : selected.value then
    let added := addCounter boundary.count index.val
    have hi : added.count < count := by
      have hs := (lessCounter_value _ _).mp h
      rw [addCounter_value, subtractCounter_value]
      omega
    ⟨⟨added.count, hi⟩, boundary.work + selected.work + added.work + 3⟩
  else
    let reduced := subtractCounter index.val front
    have hi : reduced.count < count := by rw [subtractCounter_value]; exact (Nat.sub_le _ _).trans_lt index.isLt
    ⟨⟨reduced.count, hi⟩, boundary.work + selected.work + reduced.work + 3⟩

 

 

abbrev RootIndex (security : ℕ) := Fin (Parameters.legCount security) ⊕
  (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))

 theorem root_count (security : ℕ) : Parameters.legCount security + (centerCount security + Parameters.modulus security) =
    (current security).body := by
  rw [(current_values security).2.2.1]
  have h := ProposalPrimary.population_room security
  unfold centerCount
  omega

def rootNumbering (security : ℕ) : RootIndex security ≃ Fin (current security).body :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (root_count security))

def rootToRole (security : ℕ) : RootIndex security ≃ RoleIndex security where
  toFun
    | .inl leg => .inr (.inr leg)
    | .inr (.inl center) => .inl center
    | .inr (.inr queue) => .inr (.inl queue)
  invFun
    | .inl center => .inr (.inl center)
    | .inr (.inl queue) => .inr (.inr queue)
    | .inr (.inr leg) => .inl leg
  left_inv := by rintro (leg | (center | queue)) <;> rfl
  right_inv := by rintro (center | (queue | leg)) <;> rfl

 theorem legs_le_body (security : ℕ) : (current security).legs ≤ (current security).body := by
  rw [(current_values security).2.1, (current_values security).2.2.1]
  have h := ProposalPrimary.population_room security
  omega

 


def positions (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (current security).body) (current security).body) :=
  storeData (current security).body (fun index =>
    let rotated := rotate (current security).body (current security).legs (legs_le_body security) index
    let placed := readVector index layout.forward rotated.value
    let path := readVector index data.body.inverse placed.value
    ⟨path.value, rotated.work + placed.work + path.work + 3⟩)

 

 




 

end CurrentAFT.CurrentEmissionRootOrder

end

section






























/-! Executed counters and explicit physical coordinates of the current affine emitter. -/
namespace CurrentAFT.CurrentEmissionMetadata
open AFT AFT.BinaryArithmetic CurrentProposalDimensions CurrentProposalResources
open ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount Parameters.dimension
  subtractCounter

structure Result where
  bodyEdges : ℕ
  edges : ℕ
  rest : ℕ
  centers : ℕ
  work : ℕ


def current (security : ℕ) : Result :=
  let dimensions := CurrentProposalDimensions.current security
  let bodyEdges := subtractCounter dimensions.body 1
  let edges := subtractCounter dimensions.dimension 1
  let rest := subtractCounter dimensions.body dimensions.legs
  let centers := subtractCounter rest.count dimensions.colors
  ⟨bodyEdges.count, edges.count, rest.count, centers.count,
    dimensions.work + bodyEdges.work + edges.work + rest.work + centers.work + 5⟩

 theorem current_values (security : ℕ) :
    (current security).bodyEdges = Parameters.bodySize security - 1 ∧
    (current security).edges = CurrentAffineGeometry.edgeCount security ∧
    (current security).rest = centerCount security + Parameters.modulus security ∧
    (current security).centers = centerCount security := by
  rcases CurrentProposalDimensions.current_values security with ⟨hq, hl, hb, hd, _, _⟩
  have hroom := ProposalPrimary.population_room security
  have he := LobsterCoordinates.current_edge_count security
  simp only [current, subtractCounter_value, hq, hl, hb, hd]
  constructor
  · trivial
  constructor
  · exact he.symm
  constructor
  · unfold centerCount; omega
  · rfl

attribute [local irreducible] CurrentEmissionMetadata.current

 theorem current_counts (security : ℕ) :
    (current security).bodyEdges + 1 = (CurrentProposalDimensions.current security).body ∧
    (current security).edges + 1 = (CurrentProposalDimensions.current security).dimension ∧
    (CurrentProposalDimensions.current security).legs + (current security).rest = (CurrentProposalDimensions.current security).body ∧
    (CurrentProposalDimensions.current security).legs * 3 + (current security).rest = (current security).edges + 1 ∧
    (current security).centers + (CurrentProposalDimensions.current security).colors = (current security).rest ∧
    (current security).bodyEdges + ((CurrentProposalDimensions.current security).legs + (CurrentProposalDimensions.current security).legs) =
      (current security).edges := by
  rcases CurrentEmissionMetadata.current_values security with ⟨hb, he, hr, hc⟩
  rcases CurrentProposalDimensions.current_values security with ⟨hq, hl, hp, hd, _, _⟩
  have hroom := ProposalPrimary.population_room security
  have hpositive := LobsterCoordinates.current_body_positive security
  have hvertex := LobsterCoordinates.current_vertex_count security
  have hedge := LobsterCoordinates.current_edge_count security
  unfold CurrentAffineGeometry.edgeCount CurrentAffineGeometry.bodyEdges at he
  simp only [hb, he, hr, hc, hq, hl, hp, hd]
  unfold centerCount Parameters.dimension at *
  refine ⟨by omega, hvertex, by omega, ?_, trivial, trivial⟩
  omega


def vertexEquiv (security : ℕ) : Fin ((current security).edges + 1) ≃ Fin (Parameters.dimension security) :=
  finCongr ((current_counts security).2.1.trans (CurrentProposalDimensions.current_values security).2.2.2.1)

def legEquiv (security : ℕ) : Fin (CurrentProposalDimensions.current security).legs ≃ Fin (Parameters.legCount security) :=
  CurrentProposalDimensions.legEquiv security

def restEquiv (security : ℕ) : Fin (current security).rest ≃ Fin (centerCount security + Parameters.modulus security) :=
  finCongr (current_values security).2.2.1


def pointEquiv (security : ℕ) : Sigma (blockSlotsProgram (CurrentProposalDimensions.current security).legs (current security).rest) ≃
    Sigma (Slots security) where
  toFun
    | ⟨.inl leg, slot⟩ => ⟨.inl (legEquiv security leg), slot⟩
    | ⟨.inr body, slot⟩ => match finSumFinEquiv.symm (restEquiv security body) with
      | .inl center => ⟨.inr (.inl center), slot⟩
      | .inr queue => ⟨.inr (.inr queue), slot⟩
  invFun
    | ⟨.inl leg, slot⟩ => ⟨.inl ((legEquiv security).symm leg), slot⟩
    | ⟨.inr (.inl center), slot⟩ => ⟨.inr ((restEquiv security).symm (finSumFinEquiv (.inl center))), slot⟩
    | ⟨.inr (.inr queue), slot⟩ => ⟨.inr ((restEquiv security).symm (finSumFinEquiv (.inr queue))), slot⟩
  left_inv := by
    rintro ⟨leg | body, slot⟩
    · exact Sigma.ext (congrArg Sum.inl ((legEquiv security).symm_apply_apply leg)) (HEq.rfl)
    · obtain ⟨center | queue, h⟩ := finSumFinEquiv.surjective (restEquiv security body)
      all_goals
        simp only [← h, Equiv.symm_apply_apply]
        exact Sigma.ext (congrArg Sum.inr (by rw [h, Equiv.symm_apply_apply])) (HEq.rfl)
  right_inv := by
    rintro ⟨leg | (center | queue), slot⟩
    · exact Sigma.ext (congrArg Sum.inl ((legEquiv security).apply_symm_apply leg)) (HEq.rfl)
    · simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    · simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

 

end CurrentAFT.CurrentEmissionMetadata

end

section
































/-! Materialization of actual chart scalars and public leg shifts. Every chart
and public input is read from its stored vector; no chart-function oracle is used. -/
namespace CurrentAFT.CurrentBinaryChartData
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

abbrev Charts (security : ℕ) := Vector (CurrentAffineLegCarry.PublicChart security) (Parameters.legCount security)

def defaultChart (security : ℕ) : CurrentAffineLegCarry.PublicChart security := (false, 0, 0, 0)

def fieldArray (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security)) :
    CountedValue (Vector IntegerBits (CurrentProposalDimensions.current security).legs) :=
  storeData (CurrentProposalDimensions.current security).legs (fun leg =>
    let chart := readVector (defaultChart security) charts (legEquiv security leg)
    let encoded := CurrentPublicShiftProgram.encode (field chart.value).val
    ⟨encoded.value, chart.work + encoded.work + 2⟩)








def shiftArray (security : ℕ) (core : MaterializedCore security) :
    CountedValue (Vector IntegerBits (CurrentProposalDimensions.current security).legs) :=
  storeData (CurrentProposalDimensions.current security).legs (fun leg =>
    let input := readVector (CurrentChartsDraw.defaultInput security) core.inputs (legEquiv security leg)
    let shifted := CurrentPublicShiftProgram.current security input.value.1 input.value.2
    ⟨shifted.value, input.work + shifted.work + 2⟩)





end CurrentAFT.CurrentBinaryChartData

end

section

























/-! Executed entries of the actual path-plus-two-leg incidence loads.
The edge order is body, first leg edges, second leg edges, then the shared
queue column. Every indicator is an actual counter comparison. -/
namespace CurrentAFT.CurrentBinaryIncidence
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 700000
set_option maxRecDepth 4096





def pathEntry (bodyEdges column root : ℕ) : CountedValue IntegerBits :=
  let inside := lessCounter column bodyEdges
  let positive := equalCounter root column
  let next := addCounter column 1
  let negative := equalCounter root next.count
  let difference := IntegerBits.subtract (if positive.value then IntegerBits.one else IntegerBits.zero)
    (if negative.value then IntegerBits.one else IntegerBits.zero)
  ⟨if inside.value then difference.value else IntegerBits.zero,
    inside.work + positive.work + next.work + negative.work + difference.work + 5⟩

 

 

def pathEntryWork (bodyEdges column root : ℕ) : ℕ :=
  3 * (column + bodyEdges) + 3 * (root + column) + 2 * column + 3 * (root + column + 1) + 100

 


def legEntries {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs) :
    CountedValue (IntegerBits × (IntegerBits × IntegerBits)) :=
  let firstAddress := addCounter bodyEdges leg.val
  let secondAddress := addCounter firstAddress.count legs
  let firstHit := equalCounter column firstAddress.count
  let secondHit := equalCounter column secondAddress.count
  let scaleEntry := readVector IntegerBits.zero scale leg
  let shearEntry := readVector IntegerBits.zero shear leg
  let primary := IntegerBits.add (if firstHit.value then scaleEntry.value else IntegerBits.zero)
    (if secondHit.value then shearEntry.value else IntegerBits.zero)
  let second := if secondHit.value then IntegerBits.one else IntegerBits.zero
  let negative := IntegerBits.negate primary.value
  let companion := IntegerBits.subtract negative.value second
  ⟨(primary.value, (companion.value, second)), firstAddress.work + secondAddress.work + firstHit.work + secondHit.work +
    scaleEntry.work + shearEntry.work + primary.work + negative.work + companion.work + 7⟩

 


 

 def legEntriesWork (bodyEdges column legs bits : ℕ) : ℕ :=
   10 * bodyEdges + 20 * legs + 6 * column + 40 * bits + 100

 

end CurrentAFT.CurrentBinaryIncidence

end

section


























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentPathImpulse
end CurrentAFT.CurrentPathImpulse



/-! Literal entries of the current physical load matrix, including the shared
queue column. The stored root-order array is read for every physical body root;
scales and shears are read once per leg entry. -/
namespace CurrentAFT.CurrentBinaryLoadColumns
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentEmissionMetadata
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

abbrev Legs (security : ℕ) := (CurrentProposalDimensions.current security).legs
abbrev Body (security : ℕ) := (CurrentProposalDimensions.current security).body
abbrev Point (security : ℕ) := Sigma (blockSlotsProgram (Legs security) (current security).rest)
abbrev Roots (security : ℕ) := Vector (Fin (Body security)) (Body security)


def rootZero (security : ℕ) : Fin (Body security) := ⟨0, by
  change 0 < (CurrentProposalDimensions.current security).body
  rw [(CurrentProposalDimensions.current_values security).2.2.1]
  exact LobsterCoordinates.current_body_positive security⟩

def rootRead (security : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    CountedValue (Fin (Body security)) :=
  let address := binaryRootAddress (Legs security) (current security).rest point
  let selected := readVector (rootZero security) roots (address.value.cast (current_counts security).2.2.1)
  ⟨selected.value, address.work + selected.work + 2⟩

 


def entry (security column : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security) :
    Point security → CountedValue IntegerBits
  | ⟨.inl leg, slot⟩ =>
    let root := rootRead security roots (.inl leg)
    let path := CurrentBinaryIncidence.pathEntry (current security).bodyEdges column root.value.val
    let legValues := CurrentBinaryIncidence.legEntries (current security).bodyEdges column scale shear leg
    let attached := IntegerBits.add path.value legValues.value.2.2
    ⟨![legValues.value.1, legValues.value.2.1, attached.value] slot,
      root.work + path.work + legValues.work + attached.work + 4⟩
  | ⟨.inr body, _⟩ =>
    let root := rootRead security roots (.inr body)
    let path := CurrentBinaryIncidence.pathEntry (current security).bodyEdges column root.value.val
    let center := lessCounter body.val (current security).centers
    let charge := equalCounter column (current security).edges
    let injection := if (!center.value) && charge.value then IntegerBits.one else IntegerBits.zero
    let result := IntegerBits.add path.value injection
    ⟨result.value, root.work + path.work + center.work + charge.work + result.work + 5⟩


def primaryEntry (security column : ℕ) (scale shear : Fin (Legs security) → ℤ) (leg : Fin (Legs security)) : ℤ :=
  (if column = (current security).bodyEdges + leg.val then scale leg else 0) +
    (if column = (current security).bodyEdges + leg.val + Legs security then shear leg else 0)

def secondEntry (security column : ℕ) (leg : Fin (Legs security)) : ℤ :=
  if column = (current security).bodyEdges + leg.val + Legs security then 1 else 0

def pathValue (security column : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) : ℤ :=
  let vertex := roots.get ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)
  pathLoad (current security).bodyEdges (fun edge => if edge.val = column then 1 else 0)
    (vertex.cast (current_counts security).1.symm)


def loadEntry (security column : ℕ) (scale shear : Fin (Legs security) → ℤ) (roots : Roots security) : Point security → ℤ
  | ⟨.inl leg, slot⟩ => ![primaryEntry security column scale shear leg,
      -primaryEntry security column scale shear leg - secondEntry security column leg,
      pathValue security column roots (.inl leg) + secondEntry security column leg] slot
  | ⟨.inr body, _⟩ => pathValue security column roots (.inr body) +
      if (current security).centers ≤ body.val ∧ column = (current security).edges then 1 else 0

 


def matrix (security : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security) :
    CountedValue (Vector (Vector IntegerBits ((current security).edges + 1)) ((current security).edges + 1)) :=
  storeData ((current security).edges + 1) (fun column => storeData ((current security).edges + 1) (fun row =>
    let point := binaryPhysicalVertex (Legs security) (current security).rest (current security).edges
      (current_counts security).2.2.2.1 row
    let result := entry security column.val scale shear roots point.value
    ⟨result.value, point.work + result.work + 2⟩))

 

end CurrentAFT.CurrentBinaryLoadColumns

end

section




























/-! Stored body baselines in the executed attachment, center, queue ordering. -/
namespace CurrentAFT.CurrentBinaryBaselines
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

 theorem controls_count (security : ℕ) : (CurrentProposalDimensions.current security).controls = (current security).centers := by
  rw [(CurrentProposalDimensions.current_values security).2.2.2.2.2, (current_values security).2.2.2]
  exact UniformTaggedOutput.centerCount_split security


def read (security : ℕ) (core : MaterializedCore security) :
    (Fin (Legs security) ⊕ Fin (current security).rest) → CountedValue IntegerBits
  | .inl leg =>
    let selected := readVector (defaultLeg security) core.legs leg
    let encoded := CurrentPublicShiftProgram.encode selected.value.2.val
    ⟨encoded.value, selected.work + encoded.work + 2⟩
  | .inr body =>
    let selected := lessCounter body.val (current security).centers
    if h : selected.value = true then
      let index : Fin (CurrentProposalDimensions.current security).controls := ⟨body.val, by
        rw [controls_count]; exact (lessCounter_value _ _).mp h⟩
      let selectedControl := readVector (defaultControl security) core.controls index
      let encoded := CurrentPublicShiftProgram.encode selectedControl.value.2.val.val
      ⟨encoded.value, selected.work + selectedControl.work + encoded.work + 3⟩
    else
      let address := subtractCounter body.val (current security).centers
      let index : Fin (CurrentProposalDimensions.current security).colors := ⟨address.count, by
        rw [subtractCounter_value]
        have hi : ¬body.val < (current security).centers := fun hi => h ((lessCounter_value _ _).mpr hi)
        have hc := (current_counts security).2.2.2.2.1
        have hb := body.isLt
        omega⟩
      let selectedBaseline := readVector (defaultControl security).1 core.baselines index
      let encoded := CurrentPublicShiftProgram.encode selectedBaseline.value.val
      ⟨encoded.value, selected.work + address.work + selectedBaseline.work + encoded.work + 4⟩


def role (security : ℕ) : Fin (Legs security) ⊕ Fin (current security).rest → ConditionalHistogramMean.RoleIndex security
  | .inl leg => .inr (.inr (legEquiv security leg))
  | .inr body => match finSumFinEquiv.symm (restEquiv security body) with
    | .inl center => .inl center
    | .inr queue => .inr (.inl queue)

 

 

end CurrentAFT.CurrentBinaryBaselines

end

section


























/-! Executed baseline and public cycle-closure load, before the final endpoint
permutation. The same stored leg shift is used in its companion coordinate. -/
namespace CurrentAFT.CurrentBinaryOffsetLoad
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current


def closure (bodyEdges root : ℕ) (scalar : IntegerBits) : CountedValue IntegerBits :=
  let last := equalCounter root bodyEdges
  let first := equalCounter root 0
  let positive := if last.value then scalar else IntegerBits.zero
  let negative := if first.value then scalar else IntegerBits.zero
  let result := IntegerBits.subtract positive negative
  ⟨result.value, last.work + first.work + result.work + 4⟩




def entry (security : ℕ) (core : MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits) :
    Point security → CountedValue IntegerBits
  | ⟨.inl leg, slot⟩ =>
    let root := rootRead security roots (.inl leg)
    let closed := closure (current security).bodyEdges root.value.val scalar
    let baseline := CurrentBinaryBaselines.read security core (.inl leg)
    let attached := IntegerBits.add baseline.value closed.value
    let translated := readVector IntegerBits.zero shift leg
    let anchored := readVector IntegerBits.zero intercept leg
    let reduced := IntegerBits.subtract modulus IntegerBits.one
    let shifted := IntegerBits.add reduced.value translated.value
    let companion := IntegerBits.subtract shifted.value anchored.value
    ⟨![anchored.value, companion.value, attached.value] slot,
      root.work + closed.work + baseline.work + attached.work + translated.work + anchored.work +
        reduced.work + shifted.work + companion.work + 9⟩
  | ⟨.inr body, _⟩ =>
    let root := rootRead security roots (.inr body)
    let closed := closure (current security).bodyEdges root.value.val scalar
    let baseline := CurrentBinaryBaselines.read security core (.inr body)
    let result := IntegerBits.add baseline.value closed.value
    ⟨result.value, root.work + closed.work + baseline.work + result.work + 4⟩


def physicalLoad (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : ℤ) (shift intercept : Fin (Legs security) → ℤ) (roots : Roots security) (scalar : ℤ) : Point security → ℤ
  | ⟨.inl leg, slot⟩ => ![intercept leg, modulus - 1 + shift leg - intercept leg,
      ActualPublicCharge.centerAt security layout core.core (layout (CurrentBinaryBaselines.role security (.inl leg))) +
        AffineBaseline.closure (current security).bodyEdges scalar
          ((roots.get ((blockNumbering (Legs security) (current security).rest (.inl leg)).cast (current_counts security).2.2.1)).cast
            (current_counts security).1.symm)] slot
  | ⟨.inr body, _⟩ =>
    ActualPublicCharge.centerAt security layout core.core (layout (CurrentBinaryBaselines.role security (.inr body))) +
      AffineBaseline.closure (current security).bodyEdges scalar
        ((roots.get ((blockNumbering (Legs security) (current security).rest (.inr body)).cast (current_counts security).2.2.1)).cast
          (current_counts security).1.symm)

 


def load (security : ℕ) (core : MaterializedCore security) (modulus : IntegerBits)
    (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits) :
    CountedValue (Vector IntegerBits ((current security).edges + 1)) :=
  storeData ((current security).edges + 1) (fun row =>
    let point := binaryPhysicalVertex (Legs security) (current security).rest (current security).edges
      (current_counts security).2.2.2.1 row
    let result := entry security core modulus shift intercept roots scalar point.value
    ⟨result.value, point.work + result.work + 2⟩)

 

end CurrentAFT.CurrentBinaryOffsetLoad

end

section































/-! The current fixed rounding injection and the stored final endpoint
permutation are produced by charged comparisons and vector reads. -/
namespace CurrentAFT.CurrentBinaryAffinePrimitives
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Size (security : ℕ) := (current security).edges + 1


def injection (security : ℕ) : CountedValue (Vector IntegerBits (Size security)) :=
  storeData (Size security) (fun row =>
    let hit := lessCounter row.val (CurrentProposalDimensions.current security).colors
    ⟨if hit.value then IntegerBits.one else IntegerBits.zero, hit.work + 2⟩)

 

 

 


def endpointPermutation (security : ℕ) (core : MaterializedCore security) :
    CountedValue (Vector (Fin (Size security)) (Size security)) :=
  storeData (Size security) (fun row =>
    let index := row.cast (current_counts security).2.1
    let selected := readVector index core.endpoints.forward index
    ⟨selected.value.cast (current_counts security).2.1.symm, selected.work + 2⟩)

 

 


def permuteLoad (security : ℕ) (data : Vector IntegerBits (Size security))
    (permutation : Vector (Fin (Size security)) (Size security)) : CountedValue (Vector IntegerBits (Size security)) :=
  storeData (Size security) (fun row =>
    let position := readVector 0 permutation row
    let selected := readVector IntegerBits.zero data position.value
    ⟨selected.value, position.work + selected.work + 2⟩)

 

 

end CurrentAFT.CurrentBinaryAffinePrimitives

end

section





























/-! The emitter executes the same public validity predicate as assemble.
The test reads every stored chart and uses the actual binary public-charge guard. -/
namespace CurrentAFT.CurrentBinaryAffineGuard
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentBinaryChartData
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize

def scale (security : ℕ) (charts : Charts security) (leg : Fin (Parameters.legCount security)) : CountedValue Bool :=
  let chart := readVector (defaultChart security) charts leg
  let tested := equalCounter chart.value.2.2.1.val 0
  ⟨!tested.value, chart.work + tested.work + 2⟩

 

 


def current (security : ℕ) (core : MaterializedCore security) (charts : Charts security) : CountedValue Bool :=
  let charge := BinaryCoreCharge.current security core
  let scales := BinaryProposalGuard.allFin (Parameters.legCount security) (scale security charts)
  ⟨charge.value && scales.value, charge.work + scales.work + 2⟩

 

 

end CurrentAFT.CurrentBinaryAffineGuard

end

section

































/-! The executed integer affine emitter. It consumes only stored public
buffers. All legal columns and the offset are computed by binary rounding
inversion, while failed validity and absent samples emit the integer identity. -/
namespace CurrentAFT.CurrentBinaryAffineEmitter
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryAffinePrimitives CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Data (security : ℕ) := BinaryAffineData (CurrentEmissionMetadata.current security).edges
abbrev Coordinate (security : ℕ) := Vector IntegerBits (CurrentEmissionMetadata.current security).edges × IntegerBits


def fallbackColumn (security : ℕ) (column : Fin (Size security)) : CountedValue (Coordinate security) :=
  let edges := storeData (CurrentEmissionMetadata.current security).edges (fun row =>
    let equal := equalCounter row.val column.val
    ⟨if equal.value then IntegerBits.one else IntegerBits.zero, equal.work + 2⟩)
  let chargeHit := equalCounter column.val (CurrentEmissionMetadata.current security).edges
  ⟨(edges.value, if chargeHit.value then IntegerBits.one else IntegerBits.zero), edges.work + chargeHit.work + 3⟩


def fallback (security : ℕ) : Data security :=
  let metadata := CurrentEmissionMetadata.current security
  let columns := storeData (Size security) (fallbackColumn security)
  let offset := storeData metadata.edges (fun _ => ⟨IntegerBits.zero, 1⟩)
  ⟨columns.value, (offset.value, IntegerBits.zero), metadata.work + columns.work + offset.work + 3⟩


def assembled (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) : Data security :=
  let metadata := CurrentEmissionMetadata.current security
  let q := PublicParameterProgram.modulus security
  let qbits := canonicalCounter q.count
  let modulus : IntegerBits := ⟨false, qbits.digits⟩
  let scale := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.1)
  let shear := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.2.2)
  let intercept := CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)
  let shift := CurrentBinaryChartData.shiftArray security sample.core
  let closure := CurrentPublicShiftProgram.encode sample.edge.val
  let roots := CurrentEmissionRootOrder.positions security layout sample.core
  let matrix := CurrentBinaryLoadColumns.matrix security scale.value shear.value roots.value
  let initial := CurrentBinaryOffsetLoad.load security sample.core modulus shift.value intercept.value roots.value closure.value
  let injection := CurrentBinaryAffinePrimitives.injection security
  let permutation := CurrentBinaryAffinePrimitives.endpointPermutation security sample.core
  let columns := storeData (Size security) (binaryAffineColumn metadata.edges qbits.digits injection.value matrix.value permutation.value)
  let offsetLoad := CurrentBinaryAffinePrimitives.permuteLoad security initial.value permutation.value
  let offset := binaryRoundingInverse metadata.edges qbits.digits injection.value offsetLoad.value
  ⟨columns.value, (offset.edges, offset.charge),
    metadata.work + q.work + qbits.work + scale.work + shear.work + intercept.work + shift.work + closure.work +
      roots.work + matrix.work + initial.work + injection.work + permutation.work + columns.work + offsetLoad.work + offset.work + 16⟩


def emit (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) : Data security :=
  match input with
  | none => fallback security
  | some sample =>
    let tested := CurrentBinaryAffineGuard.current security sample.core sample.charts
    let result := if tested.value then assembled security layout sample else fallback security
    ⟨result.columns, result.offset, tested.work + result.work + 2⟩

noncomputable section

def decodeCoordinate (security : ℕ) (point : Coordinate security) : Fin (Parameters.dimension security) → ℤ :=
  CurrentAffineLoad.packSource security
    ((fun edge => (point.1.get (edge.cast (CurrentEmissionMetadata.current_values security).2.1.symm)).decode), point.2.decode)


def matrix (security : ℕ) (data : Data security) : Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ :=
  fun row column => decodeCoordinate security (data.columns.get ((vertexEquiv security).symm column)) row


def offset (security : ℕ) (data : Data security) : Fin (Parameters.dimension security) → ℤ :=
  decodeCoordinate security data.offset

 

 

 

end
end CurrentAFT.CurrentBinaryAffineEmitter

end

section


























/-! Bit length and work of the current executed physical load matrix. -/
namespace CurrentAFT.CurrentBinaryLoadResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current



 


def entryWork (security column bits : ℕ) : ℕ := 100 * ((current security).bodyEdges + Legs security + Body security +
    (current security).edges + (current security).rest + column + bits + 10)

 

 


def matrixWork (security bits : ℕ) : ℕ :=
  let size := (current security).edges + 1
  size * (size * (1000 * (size + 6)^2 + entryWork security size bits + 4) + 4) + 2

 

end CurrentAFT.CurrentBinaryLoadResources

end

section


























/-! Actual baseline-buffer reading and color encoding have bounded bit cost. -/
namespace CurrentAFT.CurrentBinaryBaselineResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current



 

 


def readWork (security : ℕ) : ℕ :=
  20 * ((CurrentProposalDimensions.current security).legs + (CurrentProposalDimensions.current security).controls +
    (CurrentProposalDimensions.current security).colors + (current security).rest + 1) +
    50 * (Parameters.modulus security + 1)^2 + 20

 

end CurrentAFT.CurrentBinaryBaselineResources

end

section






























/-! Bit lengths and work of actual offset-load production. -/
namespace CurrentAFT.CurrentBinaryOffsetResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryOffsetLoad
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

 

 

 


def entryWork (security bits : ℕ) : ℕ :=
  CurrentBinaryBaselineResources.readWork security + 100 * (Body security + Legs security + (current security).bodyEdges + bits + 10)

 

 


def loadWork (security bits : ℕ) : ℕ :=
  let size := (current security).edges + 1
  size * (1000 * (size + 6)^2 + entryWork security bits + 4) + 2

 

end CurrentAFT.CurrentBinaryOffsetResources

end

section
































namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.binaryAffineAssemblyPolynomial
end AFT.BinaryArithmetic.binaryAffineAssemblyPolynomial
namespace AFT.BinaryArithmetic.binaryPaddedEntryPolynomial
end AFT.BinaryArithmetic.binaryPaddedEntryPolynomial
namespace AFT.BinaryArithmetic.binaryPaddedEntryWork
end AFT.BinaryArithmetic.binaryPaddedEntryWork
namespace AFT.BinaryArithmetic.binaryPathInversePolynomial
end AFT.BinaryArithmetic.binaryPathInversePolynomial
namespace AFT.BinaryArithmetic.binaryRoundingInversePolynomial
end AFT.BinaryArithmetic.binaryRoundingInversePolynomial
namespace AFT.BinaryArithmetic.binaryRoundingInverseWork
end AFT.BinaryArithmetic.binaryRoundingInverseWork
namespace AFT.BinaryArithmetic.binaryShiftedLoadPolynomial
end AFT.BinaryArithmetic.binaryShiftedLoadPolynomial
namespace AFT.BinaryArithmetic.binaryShiftedLoadWork
end AFT.BinaryArithmetic.binaryShiftedLoadWork






/-! Explicit work bounds for the current stored-buffer integer emitter. -/
namespace CurrentAFT.CurrentBinaryEmitterResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentProposalResources
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount


def operandBits (security : ℕ) : ℕ := Parameters.modulus security + 2*(security+2)^48 + 2*(security+2)^2 + 10

def fieldWork (security : ℕ) : ℕ := Legs security * (3*Parameters.legCount security + 50*(Parameters.modulus security+1)^2 + 10)+2

def shiftWork (security : ℕ) : ℕ := Legs security * (3*Parameters.legCount security + CurrentPublicShiftProgram.workBound security + 9)+2


def assembledWork (security : ℕ) : ℕ :=
  let e := (current security).edges
  let size := e+1
  let body := (CurrentProposalDimensions.current security).body
  let bits := operandBits security
  (current security).work + PublicParameterProgram.workBound security + 50*(Parameters.modulus security+1)^2 +
    3*fieldWork security + shiftWork security + (50*((security+2)^2+1)^2+1) +
    (body*(13*body+19)+2) + CurrentBinaryLoadResources.matrixWork security bits +
    CurrentBinaryOffsetResources.loadWork security bits + (size*(3*size+7)+2) + (size*(3*size+7)+2) +
    (size*((size*(9*size+15)+2)+binaryRoundingInverseWork e (Parameters.modulus security) (bits+3)+4)+2) +
    (size*(6*size+10)+2) + binaryRoundingInverseWork e (Parameters.modulus security) (bits+3) + 16

 


def fallbackWork (security : ℕ) : ℕ :=
  let size := Size security
  (current security).work + (size * (size*(6*size+6)+6*size+9)+2) + (3*size+2) + 3

 


noncomputable def guardWork (security : ℕ) : ℕ := BinaryCoreCharge.workPolynomial.eval security +
  Parameters.legCount security*(3*Parameters.legCount security+3*Parameters.modulus security+11)+3


noncomputable def workBound (security : ℕ) : ℕ := assembledWork security + fallbackWork security + guardWork security + 2

 

end CurrentAFT.CurrentBinaryEmitterResources

end

section































/-! A single polynomial bounds the complete executed integer emitter,
uniformly over every stored public record, including invalid records. -/
namespace CurrentAFT.CurrentBinaryEmitterPolynomial
open AFT BinaryArithmetic CurrentEmissionMetadata CurrentProposalResources CurrentBinaryEmitterResources
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section

 theorem metadata_work (security : ℕ) : (current security).work ≤
    (metadataWorkPolynomial + 8*countPolynomial+13).eval security := by
  let sizes := CurrentProposalDimensions.current security
  have hw := CurrentProposalResources.metadata_work security
  have hb := (count_bounds security).2.2.2.1
  have hd := (count_bounds security).2.2.2.2
  have hbe := subtractCounter_work_left sizes.body 1
  have he := subtractCounter_work_left sizes.dimension 1
  have hr := subtractCounter_work_left sizes.body sizes.legs
  have hc := subtractCounter_work_left (subtractCounter sizes.body sizes.legs).count sizes.colors
  have hrs : (subtractCounter sizes.body sizes.legs).count ≤ sizes.body := by
    rw [subtractCounter_value]; exact Nat.sub_le _ _
  unfold CurrentEmissionMetadata.current
  change sizes.work + (subtractCounter sizes.body 1).work + (subtractCounter sizes.dimension 1).work +
    (subtractCounter sizes.body sizes.legs).work + (subtractCounter (subtractCounter sizes.body sizes.legs).count sizes.colors).work + 5 ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  dsimp only [sizes] at *
  omega

 theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (h : ∀ security, resource security ≤ polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,h⟩

attribute [local irreducible] UniformPolynomialBound

 theorem hcontrols_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).controls) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).1)

 theorem hlegs_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).legs) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.1)

 theorem hcolors_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).colors) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.1)

 theorem hbody_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).body) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.2.1)

 theorem hedge_uniform : UniformPolynomialBound (fun n => (current n).edges) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).2.1
    have hd := (count_bounds n).2.2.2.2
    omega)

 theorem hbodyedge_uniform : UniformPolynomialBound (fun n => (current n).bodyEdges) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).1
    have hd := (count_bounds n).2.2.2.1
    omega)

 theorem hrest_uniform : UniformPolynomialBound (fun n => (current n).rest) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).2.2.1
    have hd := (count_bounds n).2.2.2.1
    omega)

 theorem hq_uniform : UniformPolynomialBound Parameters.modulus := of_bound _ countPolynomial (fun n => by
    have h := (count_bounds n).2.2.1
    simpa only [(CurrentProposalDimensions.current_values n).1] using h)

 theorem hl_uniform : UniformPolynomialBound Parameters.legCount := of_bound _ countPolynomial (fun n => by
    have h := (count_bounds n).2.1
    simpa only [(CurrentProposalDimensions.current_values n).2.1] using h)

 theorem hm_uniform : UniformPolynomialBound (fun n => (current n).work) :=
    of_bound _ (metadataWorkPolynomial + 8*countPolynomial+13) metadata_work

 theorem hp_uniform : UniformPolynomialBound PublicParameterProgram.workBound := of_bound _ PublicParameterProgram.workPolynomial (fun n => by
    rw [PublicParameterProgram.workPolynomial_eval])

 theorem hs_uniform : UniformPolynomialBound CurrentPublicShiftProgram.workBound := of_bound _ shiftWorkPolynomial (fun n => by
    rw [shiftWorkPolynomial_eval])

attribute [local irreducible] Nat.add Nat.mul Nat.pow



 theorem operand_uniform : UniformPolynomialBound operandBits := by
  unfold operandBits
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem field_uniform : UniformPolynomialBound fieldWork := by
  unfold fieldWork CurrentBinaryLoadColumns.Legs
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem shift_uniform : UniformPolynomialBound shiftWork := by
  unfold shiftWork CurrentBinaryLoadColumns.Legs
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem matrix_uniform : UniformPolynomialBound (fun n => CurrentBinaryLoadResources.matrixWork n (operandBits n)) := by
  have ho := operand_uniform
  unfold CurrentBinaryLoadResources.matrixWork CurrentBinaryLoadResources.entryWork
  dsimp only [CurrentBinaryLoadColumns.Legs, CurrentBinaryLoadColumns.Body]
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem offset_uniform : UniformPolynomialBound (fun n => CurrentBinaryOffsetResources.loadWork n (operandBits n)) := by
  have ho := operand_uniform
  unfold CurrentBinaryOffsetResources.loadWork CurrentBinaryOffsetResources.entryWork CurrentBinaryBaselineResources.readWork
  dsimp only [CurrentBinaryLoadColumns.Legs, CurrentBinaryLoadColumns.Body]
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem inverse_uniform {count modulus bits : ℕ → ℕ}
    (hc : UniformPolynomialBound count) (hq : UniformPolynomialBound modulus) (hb : UniformPolynomialBound bits) :
    UniformPolynomialBound (fun n => binaryRoundingInverseWork (count n) (modulus n) (bits n)) := by
  unfold binaryRoundingInverseWork binaryShiftedLoadWork binaryPathInverseWork
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem assembled_uniform : UniformPolynomialBound assembledWork := by
  have hf := field_uniform
  have hs := shift_uniform
  have hm := matrix_uniform
  have ho := offset_uniform
  have hi := inverse_uniform hedge_uniform hq_uniform (operand_uniform.add (UniformPolynomialBound.constant 3))
  unfold assembledWork
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem fallback_uniform : UniformPolynomialBound fallbackWork := by
  unfold fallbackWork
  dsimp only [CurrentBinaryAffinePrimitives.Size]
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem guard_uniform : UniformPolynomialBound guardWork := by
  have hg : UniformPolynomialBound BinaryCoreCharge.workPolynomial.eval := UniformPolynomialBound.polynomial _
  unfold guardWork
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add

 theorem work_uniform : UniformPolynomialBound workBound := by
  unfold workBound
  exact ((assembled_uniform.add fallback_uniform).add guard_uniform).add (UniformPolynomialBound.constant 2)

 theorem work_exists : ∃ polynomial : Polynomial ℕ, ∀ security, workBound security ≤ polynomial.eval security := by
  simpa only [UniformPolynomialBound] using work_uniform

noncomputable def workPolynomial : Polynomial ℕ := Classical.choose work_exists

 

end
end CurrentAFT.CurrentBinaryEmitterPolynomial

end

section























/-! The actual linear load in the explicitly numbered physical slots. -/
namespace CurrentAFT.CurrentLinearPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates LobsterMixerMatrix PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev sourceEdges (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :=
  edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security) (splitSource security input).1

def path (security : ℕ) (core : Core security) (input : Fin (Parameters.dimension security) → ℤ)
    (vertex : BodyIndex security) : ℤ :=
  pathLoad (bodyEdges security) (sourceEdges security input).1
    (CurrentAffineGeometry.bodyEquiv security (core.bodyPermutation.symm vertex))

def primary (security : ℕ) (scale shear : Fin (Parameters.legCount security) → ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) (leg : Fin (Parameters.legCount security)) : ℤ :=
  scale leg * (sourceEdges security input).2.1 leg + shear leg * (sourceEdges security input).2.2 leg

def physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    Sigma (Slots security) → ℤ
  | ⟨.inl leg, slot⟩ => ![primary security scale shear input leg,
      -primary security scale shear input leg - (sourceEdges security input).2.2 leg,
      path security core input (layout (.inr (.inr leg))) + (sourceEdges security input).2.2 leg] slot
  | ⟨.inr (.inl center), _⟩ => path security core input (layout (.inl center))
  | ⟨.inr (.inr queue), _⟩ => path security core input (layout (.inr (.inl queue))) + (splitSource security input).2





end
end CurrentAFT.CurrentLinearPhysicalLoad

end

section





























/-! Exact current semantics of the executed integral load arrays. -/
namespace CurrentAFT.CurrentBinaryLoadSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata
open CurrentCoreProposal (MaterializedCore)
open
  CurrentLinearPhysicalLoad CurrentAffineGeometry CurrentAffineLoad
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current

def blockEquiv (security : ℕ) : (Fin (Legs security) ⊕ Fin (current security).rest) ≃ BlockIndex security :=
  Equiv.sumCongr (CurrentEmissionMetadata.legEquiv security)
    ((restEquiv security).trans finSumFinEquiv.symm)







def basisInput (security : ℕ) (column : Fin ((current security).edges+1)) : Fin (Parameters.dimension security) → ℤ :=
  Pi.single (vertexEquiv security column) 1



















end
end CurrentAFT.CurrentBinaryLoadSemantic

end

section





















/-! The actual affine offset has exactly the executed physical baseline
and closure load before the final endpoint permutation. -/
namespace CurrentAFT.CurrentOffsetPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def rootLoad (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scalar : ℤ) (role : RoleIndex security) : ℤ :=
  centerAt security layout core (layout role) + closure (bodyEdges security) scalar
    (CurrentAffineGeometry.bodyEquiv security (core.bodyPermutation.symm (layout role)))

def physical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) : Sigma (Slots security) → ℤ
  | ⟨.inl leg, slot⟩ => ![intercept leg, (Parameters.modulus security : ℤ)-1+legShift security core leg-intercept leg,
      rootLoad security layout core scalar (.inr (.inr leg))] slot
  | ⟨.inr (.inl center), _⟩ => rootLoad security layout core scalar (.inl center)
  | ⟨.inr (.inr queue), _⟩ => rootLoad security layout core scalar (.inr (.inl queue))





end
end CurrentAFT.CurrentOffsetPhysicalLoad

end

section

































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.intercepts
end CurrentAFT.CurrentAffineData.intercepts
namespace CurrentAFT.CurrentAffineData.shears
end CurrentAFT.CurrentAffineData.shears
namespace CurrentAFT.CurrentBinaryAffineEmitter
end CurrentAFT.CurrentBinaryAffineEmitter
namespace CurrentAFT.CurrentBinaryAffineEmitter.assembled
end CurrentAFT.CurrentBinaryAffineEmitter.assembled
namespace CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
end CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallback
end CurrentAFT.CurrentBinaryAffineEmitter.fallback
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
end CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
namespace CurrentAFT.CurrentBinaryAffineEmitter.matrix
end CurrentAFT.CurrentBinaryAffineEmitter.matrix
namespace CurrentAFT.CurrentBinaryAffineEmitter.offset
end CurrentAFT.CurrentBinaryAffineEmitter.offset
namespace CurrentAFT.CurrentBinaryEmitterSemantic
end CurrentAFT.CurrentBinaryEmitterSemantic
namespace CurrentAFT.CurrentBinaryFallbackSemantic
end CurrentAFT.CurrentBinaryFallbackSemantic
namespace CurrentAFT.CurrentBinaryMatrixSemantic
end CurrentAFT.CurrentBinaryMatrixSemantic
namespace CurrentAFT.CurrentBinaryOffsetSemantic
end CurrentAFT.CurrentBinaryOffsetSemantic
namespace CurrentAFT.CurrentEmissionMetadata
end CurrentAFT.CurrentEmissionMetadata
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv
end CurrentAFT.CurrentEmissionMetadata.pointEquiv
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.Result
end CurrentAFT.CurrentMaterializedCompletion.Result
namespace CurrentAFT.CurrentMaterializedCompletion.Result.sample
end CurrentAFT.CurrentMaterializedCompletion.Result.sample
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
namespace CurrentAFT.CurrentPublicAffineSample.realize
end CurrentAFT.CurrentPublicAffineSample.realize
namespace CurrentAFT.NumericalAffineTransport
end CurrentAFT.NumericalAffineTransport
namespace CurrentAFT.NumericalAffineTransport.realizeResult
end CurrentAFT.NumericalAffineTransport.realizeResult
namespace CurrentAFT.NumericalAffineTransport.realizeResult.match_1
end CurrentAFT.NumericalAffineTransport.realizeResult.match_1
namespace CurrentAFT.PublicBitResources
end CurrentAFT.PublicBitResources



/-! Composition of the table producer with the executed public sampler and
integer emitter. Placement is sampled once, before calibration and rejection.
The producer's resource and approximation obligations are explicit here. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

abbrev Table (security order : ℕ) := BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order
abbrev Producer (security order : ℕ) := CurrentLayoutDraw.Cache security → CountedValue (Table security order)

def addWork (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.Data security := ⟨data.columns, data.offset, extra+data.work⟩

def forLayout (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.Data security :=
  let table := producer layout
  let sample := CurrentMaterializedCompletion.current security order table.value word
  let result := CurrentBinaryAffineEmitter.emit security layout sample.value
  ⟨result.columns, result.offset, table.work+sample.work+result.work+3⟩

def run (security order : ℕ) (producer : Producer security order) (word : PublicBitTapes.Tapes security) :
    CurrentBinaryAffineEmitter.Data security :=
  let layout := CurrentLayoutDraw.draw security security word.1
  let result := forLayout security order producer layout.value word.2
  addWork security (layout.work+2) result

def fairBitRun (security order : ℕ) (producer : Producer security order)
    (word : Fin (PublicBitTapes.current security).bits → Fin 2) : CurrentBinaryAffineEmitter.Data security :=
  run security order producer ((PublicBitTapes.current security).equiv word)

noncomputable section
open scoped Classical

















end
end CurrentAFT.PublicAffinePipeline

end

section





























/-! Gaussian output laws of the literal integer arrays. The public placement
is held fixed throughout calibration and rejection, then averaged once. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

def gaussianChannel (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  CurrentHiddenSourceTransport.hiddenGaussianOutput security (fun input =>
    (FiniteDist.uniform Unit).map (fun _ index =>
      (((CurrentBinaryAffineEmitter.matrix security data).mulVec input index+
        CurrentBinaryAffineEmitter.offset security data index : ℤ) : ZMod (Parameters.modulus security))))





def fixedGaussian (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) : FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (CurrentMaterializedCompletion.Tapes security)).mix
    (fun word => gaussianChannel security (forLayout security order producer layout word))



def runGaussian (security order : ℕ) (producer : Producer security order) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (PublicBitTapes.Tapes security)).mix
    (fun word => gaussianChannel security (run security order producer word))

def fairGaussian (security order : ℕ) (producer : Producer security order) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix
    (fun word => gaussianChannel security (fairBitRun security order producer word))









end
end CurrentAFT.PublicAffinePipeline

end

section































namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

def workPolynomial (order : ℕ) (producerWork tableHeight : Polynomial ℕ) : Polynomial ℕ :=
  CurrentLayoutDraw.workPolynomial Polynomial.X + producerWork +
    CurrentMaterializedCompletion.workPolynomial order tableHeight +
    CurrentBinaryEmitterPolynomial.workPolynomial+5




end
end CurrentAFT.PublicAffinePipeline

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.PublicAffinePipeline.workPolynomial
  pure ()

end

section








































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualAffineEvaluator
end CurrentAFT.ActualAffineEvaluator
namespace CurrentAFT.ActualAffineEvaluator.budgetPolynomial
end CurrentAFT.ActualAffineEvaluator.budgetPolynomial
namespace CurrentAFT.ActualAffineEvaluator.coordinateEntry
end CurrentAFT.ActualAffineEvaluator.coordinateEntry
namespace CurrentAFT.ActualAffineEvaluator.decodeInput
end CurrentAFT.ActualAffineEvaluator.decodeInput
namespace CurrentAFT.ActualAffineEvaluator.dotWork
end CurrentAFT.ActualAffineEvaluator.dotWork
namespace CurrentAFT.ActualAffineEvaluator.evaluate
end CurrentAFT.ActualAffineEvaluator.evaluate
namespace CurrentAFT.ActualAffineEvaluator.nativeCoordinate
end CurrentAFT.ActualAffineEvaluator.nativeCoordinate
namespace CurrentAFT.ActualAffineEvaluator.productEntry
end CurrentAFT.ActualAffineEvaluator.productEntry
namespace CurrentAFT.ActualAffineEvaluator.productWork
end CurrentAFT.ActualAffineEvaluator.productWork
namespace CurrentAFT.ActualAffineEvaluator.row
end CurrentAFT.ActualAffineEvaluator.row
namespace CurrentAFT.ActualAffineEvaluator.rowWork
end CurrentAFT.ActualAffineEvaluator.rowWork
namespace CurrentAFT.ActualAffineEvaluator.workBound
end CurrentAFT.ActualAffineEvaluator.workBound
namespace CurrentAFT.ActualCalibratedPublic
end CurrentAFT.ActualCalibratedPublic
namespace CurrentAFT.ActualCalibratedPublic.weight
end CurrentAFT.ActualCalibratedPublic.weight
namespace CurrentAFT.ActualGaussianRemainder
end CurrentAFT.ActualGaussianRemainder
namespace CurrentAFT.ActualGaussianRemainder.chargedClip
end CurrentAFT.ActualGaussianRemainder.chargedClip
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.intercepts
end CurrentAFT.CurrentAffineData.intercepts
namespace CurrentAFT.CurrentAffineData.shears
end CurrentAFT.CurrentAffineData.shears
namespace CurrentAFT.CurrentAffineTransport
end CurrentAFT.CurrentAffineTransport
namespace CurrentAFT.CurrentAffineTransport.gaussianLaw
end CurrentAFT.CurrentAffineTransport.gaussianLaw
namespace CurrentAFT.CurrentBinaryAffineEmitter
end CurrentAFT.CurrentBinaryAffineEmitter
namespace CurrentAFT.CurrentBinaryAffineEmitter.assembled
end CurrentAFT.CurrentBinaryAffineEmitter.assembled
namespace CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
end CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallback
end CurrentAFT.CurrentBinaryAffineEmitter.fallback
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
end CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
namespace CurrentAFT.CurrentBinaryAffineEmitter.matrix
end CurrentAFT.CurrentBinaryAffineEmitter.matrix
namespace CurrentAFT.CurrentBinaryAffineEmitter.offset
end CurrentAFT.CurrentBinaryAffineEmitter.offset
namespace CurrentAFT.CurrentBinaryEmitterSemantic
end CurrentAFT.CurrentBinaryEmitterSemantic
namespace CurrentAFT.CurrentBinaryFallbackSemantic
end CurrentAFT.CurrentBinaryFallbackSemantic
namespace CurrentAFT.CurrentBinaryMatrixSemantic
end CurrentAFT.CurrentBinaryMatrixSemantic
namespace CurrentAFT.CurrentBinaryOffsetSemantic
end CurrentAFT.CurrentBinaryOffsetSemantic
namespace CurrentAFT.CurrentEmissionMetadata
end CurrentAFT.CurrentEmissionMetadata
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv
end CurrentAFT.CurrentEmissionMetadata.pointEquiv
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.Result
end CurrentAFT.CurrentMaterializedCompletion.Result
namespace CurrentAFT.CurrentMaterializedCompletion.Result.sample
end CurrentAFT.CurrentMaterializedCompletion.Result.sample
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
namespace CurrentAFT.CurrentPublicAffineSample.realize
end CurrentAFT.CurrentPublicAffineSample.realize
namespace CurrentAFT.NumericalAffineTransport
end CurrentAFT.NumericalAffineTransport
namespace CurrentAFT.NumericalAffineTransport.realizeResult
end CurrentAFT.NumericalAffineTransport.realizeResult
namespace CurrentAFT.NumericalAffineTransport.realizeResult.match_1
end CurrentAFT.NumericalAffineTransport.realizeResult.match_1
namespace CurrentAFT.NumericalGaussianAccuracy
end CurrentAFT.NumericalGaussianAccuracy
namespace CurrentAFT.PublicAffinePipeline
end CurrentAFT.PublicAffinePipeline







/-! The current construction's complete finite-bit sampler. Static arithmetic
programs are fixed once for the requested order. All security-dependent tables,
calibration iterates, rejection trials, public completions, and integer affine
outputs are executed by the concrete programs in this import chain. -/
namespace CurrentAFT.ActualConstructiveSampler
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open ActualCalibrationRates BinaryFullResponseData
open Filter
open scoped Classical Topology
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

def producer (security order : ℕ) (data : Data order) : PublicAffinePipeline.Producer security order := fun _ =>
  BinaryRectangleMaterialization.run security order security (BinaryFullResponseMatrixEntry.current security security order data)

def run (security order : ℕ) (data : Data order) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CurrentBinaryAffineEmitter.Data security :=
  let decoded := BinaryPublicBitDecode.current security word
  PublicAffinePipeline.addWork security decoded.work
    (PublicAffinePipeline.run security order (producer security order data) decoded.value)

noncomputable section
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus
  BinaryPublicBitDecode.current PublicAffinePipeline.run
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset

def law (security order : ℕ) (data : Data order) : FiniteDist (CurrentZeroFiber.Word security) :=
  PublicAffinePipeline.fairGaussian security order (producer security order data)









def producerHeight (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryCalibrationIteration.heightPolynomial (BinaryRectangleResources.sizePolynomial order)
    (BinaryFullResponseMatrixEntry.heightPolynomial order data Polynomial.X) Polynomial.X

def producerWork (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryRectangleResources.runPolynomial order
    (BinaryFullResponseMatrixEntry.heightPolynomial order data Polynomial.X)
    (BinaryFullResponseMatrixEntry.workPolynomial order data Polynomial.X) Polynomial.X

def workPolynomial (order : ℕ) (data : Data order) : Polynomial ℕ :=
  BinaryPublicBitDecode.workPolynomial+
    PublicAffinePipeline.workPolynomial order (producerWork order data) (producerHeight order data)







local instance uniformFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩











end
end CurrentAFT.ActualConstructiveSampler

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.ActualConstructiveSampler.workPolynomial
  pure ()

end

section































/-! The materialized rectangular iterate is read by the actual public-weight
program at the same joint coefficient coordinates. This connects matrix
iteration error to the rejection program's public core weight. -/
namespace CurrentAFT.BinaryCalibrationWeightSemantic
open AFT BinaryArithmetic RationalRejectionProgram
open ActualControls ControlCoordinates GradedControlAlgebra
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  PublicParameterProgram.modulus
noncomputable section
open scoped Classical
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

 

 

 

end
end CurrentAFT.BinaryCalibrationWeightSemantic

end

section





























/-! # Exact outer algebra of the actual full response

The only local semantic bridge used here is the independently verified
selection/tag serialization. No response error or runtime estimate is
assumed by this finite-sum algebra.
-/
namespace CurrentAFT.BinaryFullResponseProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct ActualBlockFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFullResponseCounts.current
  Parameters.bodySize Parameters.legCount BackgroundRates.ordinaryPool
  RationalFullResponseProgram.selected RationalFullResponseProgram.selection

def TaggedCorrect (security bits order : ℕ) (data : Data order)
    (numbering : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security) : Prop :=
  ∀ (queue : IntegerBits) (source : TruncatedArity order)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val)
    (choice : BinaryControlChoiceAverage.Choice security source.val.1.val source.val.2.val) (tag : Tag security order)
    (output : TruncatedArity order) (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val),
    (∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) → (∀ i, centers.get i<BinaryFirstInverseProgram.colors security) →
    (tagged security bits order data queue source sourcePrimary sourceBody (Vector.ofFn choice.1) (Vector.ofFn choice.2) tag output inputs centers).value.decode=
      RationalPackedRootProgram.current security bits order queue.decode
        (RationalPackedRootProgram.actualMetadata
          (RationalFullResponseProgram.selection security _ _ (BinaryControlChoiceAverage.choiceEquiv security _ _ choice))
          (numbering.finsetCongr tag.set))
        (fun index => (sourcePrimary.get index).val) (fun index => (sourceBody.get index).val) output inputs.get centers.get


















end
end CurrentAFT.BinaryFullResponseProgram

end

section



























/-! Exact ordinal meaning of the bounded root metadata serialization. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

def numbering (security : ℕ) : BlockIndex security ≃ Fin (population (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
  (CurrentRootOrdering.blockNumbering security).trans (finCongr (by
    have h := UniformTaggedOutput.centerCount_split security
    unfold population
    omega))

def primaryInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) :
    Vector (Fin (Parameters.legCount security)) r := Vector.ofFn choice.1
def ordinaryInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) :
    Vector (Fin (BackgroundRates.ordinaryPool security)) s := Vector.ofFn choice.2
def tagsInput {security : ℕ} (tagged : Finset (BlockIndex security)) :
    Vector (Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security)
      (Parameters.modulus security))) tagged.card :=
  Vector.ofFn (fun index => numbering security (CurrentRootOrdering.tagOrdering tagged index).val)

 

theorem numbering_primary (security : ℕ) (index : Fin (Parameters.legCount security)) :
    (numbering security (.inl index)).val=index.val := rfl

theorem numbering_compensator {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (index : Fin r) :
    (numbering security (.inr (.inl ((RationalFullResponseProgram.selection security r s choice).compensator index)))).val=
      Parameters.legCount security+(choice.1 index).val := rfl

theorem numbering_ordinary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (index : Fin s) :
    (numbering security (.inr (.inl ((RationalFullResponseProgram.selection security r s choice).body index)))).val=
      Parameters.legCount security+Parameters.legCount security+(choice.2 index).val := by
  change Parameters.legCount security+(Parameters.legCount security+(choice.2 index).val)=_
  omega

theorem isKept_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s) (block : BlockIndex security) :
    (isKept (primaryInput choice) (ordinaryInput choice) (numbering security block)).value=true ↔
      CurrentRootOrdering.isKept (RationalFullResponseProgram.selection security r s choice) block := by
  rw [isKept_value]
  simp only [primaryInput,ordinaryInput,Vector.get_ofFn,CurrentRootOrdering.isKept]
  constructor
  · rintro ⟨hp,hb⟩
    refine ⟨fun index he => ?_,fun index he => ?_,fun index he => ?_⟩
    · apply (hp index).1
      rw [he]
      exact numbering_primary _ _
    · apply (hp index).2
      rw [he]
      exact numbering_compensator choice index
    · apply hb index
      rw [he]
      exact numbering_ordinary choice index
  · rintro ⟨hp,hc,hb⟩
    constructor
    · intro index
      constructor
      · intro he
        apply hp index
        apply (numbering security).injective
        apply Fin.ext
        simpa only [numbering_primary,RationalFullResponseProgram.selection] using he
      · intro he
        apply hc index
        apply (numbering security).injective
        apply Fin.ext
        simpa only [numbering_compensator] using he
    · intro index he
      apply hb index
      apply (numbering security).injective
      apply Fin.ext
      simpa only [numbering_ordinary] using he

theorem tagsInput_increasing {security : ℕ} (tagged : Finset (BlockIndex security)) :
    StrictMono (tagsInput tagged).get := by
  intro i j hij
  simp only [tagsInput,Vector.get_ofFn]
  change (numbering security (CurrentRootOrdering.tagOrdering tagged i).val).val<
    (numbering security (CurrentRootOrdering.tagOrdering tagged j).val).val
  change (CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.tagOrdering tagged i).val).val<
    (CurrentRootOrdering.blockNumbering security (CurrentRootOrdering.tagOrdering tagged j).val).val
  rw [CurrentRootOrdering.tagOrdering_number,CurrentRootOrdering.tagOrdering_number]
  exact (Finset.orderIsoOfFin (CurrentRootOrdering.tagIndices tagged) (Finset.card_map _)).strictMono hij

theorem tagsInput_range {security : ℕ} (tagged : Finset (BlockIndex security))
    (block : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    block∈(tagsInput tagged).toList ↔ (numbering security).symm block∈tagged := by
  simp only [tagsInput,Vector.toList_ofFn,List.mem_ofFn]
  constructor
  · rintro ⟨index,he⟩
    rw [← he,Equiv.symm_apply_apply]
    exact (CurrentRootOrdering.tagOrdering tagged index).property
  · intro h
    obtain ⟨index,he⟩ := (CurrentRootOrdering.tagOrdering tagged).surjective ⟨(numbering security).symm block,h⟩
    refine ⟨index,?_⟩
    rw [he]
    exact (numbering security).apply_symm_apply block

def retainedInput {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) := (kept (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).value

theorem retainedInput_membership {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (block : Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security))) :
    block∈retainedInput choice tagged ↔
      (numbering security).symm block∈CurrentRootOrdering.keptTags (RationalFullResponseProgram.selection security r s choice) tagged := by
  simp only [retainedInput,kept_value,List.mem_filter,tagsInput_range,CurrentRootOrdering.keptTags,Finset.mem_filter]
  rw [← isKept_actual choice ((numbering security).symm block),Equiv.apply_symm_apply]

theorem retainedInput_increasing {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) : (retainedInput choice tagged).Pairwise (·<·) := by
  rw [retainedInput,kept_value]
  apply List.Pairwise.filter
  have h := tagsInput_increasing tagged
  have he : (tagsInput tagged).toList=List.ofFn (tagsInput tagged).get := by
    simp only [tagsInput,Vector.toList_ofFn]
    congr 1
    funext index
    exact (Vector.get_ofFn (fun index => numbering security (CurrentRootOrdering.tagOrdering tagged index).val) index).symm
  rw [he,List.pairwise_ofFn]
  exact h


theorem retainedInput_nodup {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) : (retainedInput choice tagged).Nodup :=
  (retainedInput_increasing choice tagged).nodup

theorem retainedInput_finset {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    (retainedInput choice tagged).toFinset=
      (CurrentRootOrdering.keptTags (RationalFullResponseProgram.selection security r s choice) tagged).map (numbering security).toEmbedding := by
  classical
  ext color
  rw [List.mem_toFinset,retainedInput_membership,Finset.mem_map]
  constructor
  · intro h
    exact ⟨(numbering security).symm color,h,(numbering security).apply_symm_apply color⟩
  · rintro ⟨block,h,he⟩
    rw [← he]
    simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using h

theorem retainedInput_length {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    (retainedInput choice tagged).length=
      (CurrentRootOrdering.keptIndices (RationalFullResponseProgram.selection security r s choice) tagged).card := by
  classical
  have h := congrArg Finset.card (retainedInput_finset choice tagged)
  rw [List.toFinset_card_of_nodup (retainedInput_nodup choice tagged),Finset.card_map] at h
  simpa only [CurrentRootOrdering.keptIndices,CurrentRootOrdering.tagIndices,Finset.card_map] using h





end CurrentAFT.BinaryRootMetadataSerializer

end

section



























/-! The executed role and tagged-slot arrays agree with the actual sorted
active-group numbering. All cardinal transports are proof-only. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize


def groupCast {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) ≃
    Fin (RationalPackedRootProgram.groupCount (RationalFullResponseProgram.selection security r s choice) tagged) :=
  finCongr (congrArg (fun count => (r+s)+count) (retainedInput_length choice tagged))


def inputOrdering {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) ≃
      ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged :=
  (groupCast choice tagged).trans (RationalPackedRootProgram.ordering (RationalFullResponseProgram.selection security r s choice) tagged)

 

 

 

 

 


def keptRole {security : ℕ} : BlockIndex security → RationalRootGroupProgram.LocalRole
  | .inl _ => .leg
  | .inr (.inl _) => .center
  | .inr (.inr _) => .queue

 

 

 

 

 

 

 

end CurrentAFT.BinaryRootMetadataSerializer

end

section

































/-! Runtime count and input casts for root metadata are proof transports.
All index values, and hence all executed comparisons, are preserved. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT ActualBlockFock TaggedSelection
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

theorem population_counts (security : ℕ) :
    population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue=
    population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security) := by
  rcases BinaryFullResponseCounts.current_value security with ⟨hl,ho,hq,_⟩
  rw [hl,ho,hq]

def countEquiv (security : ℕ) :
    Fin (population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue) ≃
    Fin (population (Parameters.legCount security) (BackgroundRates.ordinaryPool security) (Parameters.modulus security)) :=
  finCongr (population_counts security)

def tagBlockEquiv (security : ℕ) : Fin (BinaryFullResponseCounts.current security).body ≃ BlockIndex security :=
  (finCongr (BinaryFullResponseCounts.body_decomposition security).symm).trans
    ((countEquiv security).trans (numbering security).symm)

def tagBlocks {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) : Finset (BlockIndex security) :=
  tag.set.map (tagBlockEquiv security).toEmbedding



def actualChoice {security r s : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get) : UniformTaggedOutput.Choice security r s :=
  (⟨fun index => Fin.cast (BinaryFullResponseCounts.current_value security).1 (primary.get index),by
      intro i j he
      apply hp
      exact Fin.cast_injective _ he⟩,
    ⟨fun index => Fin.cast (BinaryFullResponseCounts.current_value security).2.1 (body.get index),by
      intro i j he
      apply hb
      exact Fin.cast_injective _ he⟩)





def nativeTag {security order : ℕ}
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body order) :
    Vector (Fin (population (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      (BinaryFullResponseCounts.current security).queue)) tag.values.length :=
  Eq.mpr (congrArg (fun count => Vector (Fin count) tag.values.length)
    (BinaryFullResponseCounts.body_decomposition security)) tag.store.value























def Result.castTags {r s first second : ℕ} (h : first=second) (value : Result r s first) : Result r s second :=
  ⟨value.kept,⟨value.data.roles,value.data.tagged.cast h⟩,value.work⟩





end CurrentAFT.BinaryRootMetadataSerializer

end

section



























/-! Proof-only cardinal transport identifies the produced finite metadata
with the paper's actual arrays, before any polynomial physical image. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open RationalRootGroupProgram
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize


def castMetadata {r s kept kept' tags : ℕ} (h : kept=kept') (data : RationalPackedRootProgram.Metadata r s kept tags) :
    RationalPackedRootProgram.Metadata r s kept' tags where
  roles index := data.roles ((finCongr (congrArg (fun count => (r+s)+count) h)).symm index)
  taggedSlots tag := ((finCongr (congrArg (fun count => (r+s)+count) h)) (data.taggedSlots tag).1,(data.taggedSlots tag).2)

 

 

 

end CurrentAFT.BinaryRootMetadataSerializer

end

section































/-! Numerical stability for the literal full-response entries. The constants
below occur only in error bounds, never in executable sampling. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula
  CalibrationPrecisionRates CalibratedWeightApproximation CalibrationTableNorm
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance accuracyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference

def entryConstant (order : ℕ) : ℝ := Classical.choose (error_polynomial order)
def entryDegree (order : ℕ) : ℕ := Classical.choose (Classical.choose_spec (error_polynomial order))



def entryError (security order : ℕ) : ℝ := entryBudget (entryConstant order) (entryDegree order) security

def weightError (security order : ℕ) : ℝ := weightBudget security security order security (entryError security order)















end
end CurrentAFT.RationalFullResponseProgram

end

end


