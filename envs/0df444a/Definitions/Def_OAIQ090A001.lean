-- Prove2me | Definitions.Def_OAIQ090A001
-- name    : OAIQ090A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T19:33:16.864781+00:00
-- url     : https://prove2.me/theorems/96ee0173-7819-4ce5-b667-bc895ddd2795
-- title:
--   Definitions bundle OAIQ090A001 of the split of OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 636 declarations of OpenAI's Lean: 465 definitions, 4 inductive types or structures, 9 instances and 158 theorems. The definitions and types are `OAI.LipschitzHilbert.HilbertPlane`, `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry`, `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry.enlargeVertical`, `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry.inner`, `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry.outer`, `OAI.LipschitzHilbert.PacketRepresentation.LatticeRow`, `OAI.LipschitzHilbert.PacketRepresentation.LatticeSiteIndex`, `OAI.LipschitzHilbert.PacketRepresentation.MasterSymbolSpace`, `OAI.LipschitzHilbert.PacketRepresentation.NarrowWindow`, `OAI.LipschitzHilbert.PacketRepresentation.PlanarSchwartz`, `OAI.LipschitzHilbert.PacketRepresentation.SymbolSpace`, `OAI.LipschitzHilbert.PacketRepresentation.analysisProfile`, `OAI.LipschitzHilbert.PacketRepresentation.analyzingWave`, `OAI.LipschitzHilbert.PacketRepresentation.annularBandSymbol`, `OAI.LipschitzHilbert.PacketRepresentation.annularBoundedComponent`, `OAI.LipschitzHilbert.PacketRepresentation.annularCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.annularDerivativeBudget`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVBoundConstant`, `OAI.LipschitzHilbert.PacketRepresentation.annularProfile`, `OAI.LipschitzHilbert.PacketRepresentation.binSquareStep`, `OAI.LipschitzHilbert.PacketRepresentation.boundedVerticalMultiplierLM`, `OAI.LipschitzHilbert.PacketRepresentation.centeredPositiveCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.compactDirectionCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorConstant`, `OAI.LipschitzHilbert.PacketRepresentation.conjugateReflectedCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.dilatedSlopeWindow`, `OAI.LipschitzHilbert.PacketRepresentation.directionTent`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicCarlesonConstant`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicCommutatorCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicDifference`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicResolutionScale`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicResolutionSymbol`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicResolutionWindow`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicSchwartzSum`, `OAI.LipschitzHilbert.PacketRepresentation.endpointErrorMajorant`, `OAI.LipschitzHilbert.PacketRepresentation.finiteBinError`, `OAI.LipschitzHilbert.PacketRepresentation.finiteSiteFiber`, `OAI.LipschitzHilbert.PacketRepresentation.finiteSiteFiberEquiv`, `OAI.LipschitzHilbert.PacketRepresentation.finiteSlopeCenter`, `OAI.LipschitzHilbert.PacketRepresentation.finiteSlopeLabels` and 429 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LipschitzHilbert_Estimates_AmplitudeAllWeights`, `LipschitzHilbert_Estimates_AmplitudeApproximation`, `LipschitzHilbert_Estimates_AmplitudeEnergy`, `LipschitzHilbert_Estimates_AmplitudeLp`, `LipschitzHilbert_Estimates_BinaryDensityBound`, `LipschitzHilbert_Estimates_BoundedDuality`, `LipschitzHilbert_Estimates_ChartPullback`, `LipschitzHilbert_Estimates_CompactMollificationFamily`, `LipschitzHilbert_Estimates_ComparableCommutatorSum`, `LipschitzHilbert_Estimates_ComplexVariation`, `LipschitzHilbert_Estimates_CountableCarleson`, `LipschitzHilbert_Estimates_DyadicMeasureClass`, `LipschitzHilbert_Estimates_FiniteBinCommutator`, `LipschitzHilbert_Estimates_FiniteNarrowPartition`, `LipschitzHilbert_Estimates_FiniteRemovalIteration`, `LipschitzHilbert_Estimates_FiniteRestrictedStrong`, `LipschitzHilbert_Estimates_FiniteSignedEnergy`, `LipschitzHilbert_Estimates_FiniteSignedFunctions`, `LipschitzHilbert_Estimates_FirstArrival`, `LipschitzHilbert_Estimates_FirstExceed`, `LipschitzHilbert_Estimates_FrozenSlopeMultiplier`, `LipschitzHilbert_Estimates_HalfPowerDualTest`, `LipschitzHilbert_Estimates_Hellinger`, `LipschitzHilbert_Estimates_HilbertTimeProfile`, `LipschitzHilbert_Estimates_HorizontalDilation`, `LipschitzHilbert_Estimates_L2Conjugation`, `LipschitzHilbert_Estimates_L2Indicator`, `LipschitzHilbert_Estimates_LaminarCarleson`, `LipschitzHilbert_Estimates_LaminarChains`, `LipschitzHilbert_Estimates_LayerEnergyMoments`, `LipschitzHilbert_Estimates_LocalizedMihlinProfile`, `LipschitzHilbert_Estimates_LogEnergy`, `LipschitzHilbert_Estimates_LogEnergyGradient`, `LipschitzHilbert_Estimates_MartingaleGoodLambda`, `LipschitzHilbert_Estimates_MartingaleLocalMaximal`, `LipschitzHilbert_Estimates_MeanOscillation`, `LipschitzHilbert_Estimates_MeasureClassLog`, `LipschitzHilbert_Estimates_MovingExponentialWeights`, `LipschitzHilbert_Estimates_MovingSegmentLogs`, `LipschitzHilbert_Estimates_NarrowPartitionBound`, `LipschitzHilbert_Estimates_NestedAverage`, `LipschitzHilbert_Estimates_NormalizedProfileBudget`, `LipschitzHilbert_Estimates_OrderDistribution`, `LipschitzHilbert_Estimates_ParityPartialSums`, `LipschitzHilbert_Estimates_PlaneCoordinates`, `LipschitzHilbert_Estimates_PlaneSlopeLipschitz`, `LipschitzHilbert_Estimates_PolynomialLocalization`, `LipschitzHilbert_Estimates_PolynomialMomentBound`, `LipschitzHilbert_Estimates_ProductPVContinuity`, `LipschitzHilbert_Estimates_ProductPVPointwiseBound`, `LipschitzHilbert_Estimates_ProductSlopePrincipalValue`, `LipschitzHilbert_Estimates_ProductSlopePrincipalValueBound`, `LipschitzHilbert_Estimates_RadialShrink`, `LipschitzHilbert_Estimates_RelativeExitScales`, `LipschitzHilbert_Estimates_RestrictedLogDensity`, `LipschitzHilbert_Estimates_RestrictedStrongForm`, `LipschitzHilbert_Estimates_RetainedAmplitudeMatrix`, `LipschitzHilbert_Estimates_ScalarRestrictedStrong`, `LipschitzHilbert_Estimates_ScaledUnitSelector`, `LipschitzHilbert_Estimates_SegmentWeights`, `LipschitzHilbert_Estimates_SequenceExponents`, `LipschitzHilbert_Estimates_SequenceNorms`, `LipschitzHilbert_Estimates_SharpTimeParameters`, `LipschitzHilbert_Estimates_ShearedLatticePeriodization`, `LipschitzHilbert_Estimates_ShiftedBlocks`, `LipschitzHilbert_Estimates_ShortL2Operator`, `LipschitzHilbert_Estimates_ShortSlopeCommutation`, `LipschitzHilbert_Estimates_ShortSlopeLp`, `LipschitzHilbert_Estimates_ShortSlopeOperator`, `LipschitzHilbert_Estimates_ShortTimeAverageEnergy`, `LipschitzHilbert_Estimates_SignedPVCommutator`, `LipschitzHilbert_Estimates_SlicedIntegral`, `LipschitzHilbert_Estimates_SlopeOrthonormal`, `LipschitzHilbert_Estimates_SlopePartition`, `LipschitzHilbert_Estimates_SlopeTopNeighborhood`, `LipschitzHilbert_Estimates_SmoothCarlesonSynthesis`, `LipschitzHilbert_Estimates_SmoothedCommutatorEnergy`, `LipschitzHilbert_Estimates_StoppedScalarExpansion`, `LipschitzHilbert_Estimates_TimeErrorEnvelope`, `LipschitzHilbert_Estimates_TopFamilyException`, `LipschitzHilbert_Estimates_TopShape`, `LipschitzHilbert_Estimates_TopWeight`, `LipschitzHilbert_Estimates_TopWeightIntegral`, `LipschitzHilbert_Estimates_TopWeightedPair`, `LipschitzHilbert_Estimates_TotalBinErrorScale`, `LipschitzHilbert_Estimates_UniformTranslatedProfileBounds`, `LipschitzHilbert_Estimates_VariationDisjointExact`, `LipschitzHilbert_Estimates_VariationIntervals`, `LipschitzHilbert_Estimates_WeightedCauchySchwarz`, `LipschitzHilbert_Estimates_WeightedIntegral`, `LipschitzHilbert_Estimates_WeightedMomentIndex`, `LipschitzHilbert_Estimates_WeightedOrder`, `LipschitzHilbert_Estimates_WeightedTranslatedProfiles`, `LipschitzHilbert_Estimates_WitnessTransfer`, `LipschitzHilbert_Fourier_AnnularBoundedSynthesis`, `LipschitzHilbert_Fourier_AnnularCutoffConstruction`, `LipschitzHilbert_Fourier_AnnularEnlargement`, `LipschitzHilbert_Fourier_AnnularPVCommutatorSquare`, `LipschitzHilbert_Fourier_AnnularPVFromNarrow`, `LipschitzHilbert_Fourier_AnnularPVPartialBound`, `LipschitzHilbert_Fourier_AnnularPositiveCutoff`, `LipschitzHilbert_Fourier_AnnularResolutionSymbols`, `LipschitzHilbert_Fourier_AnnularSelector`, `LipschitzHilbert_Fourier_BandAverageComparison`, `LipschitzHilbert_Fourier_BoundedConvolutionComposition`, `LipschitzHilbert_Fourier_BoundedVerticalMultiplier`, `LipschitzHilbert_Fourier_CenteredBandProjection`, `LipschitzHilbert_Fourier_ConvolutionPowerTail`, `LipschitzHilbert_Fourier_CoordinateFourierSupport`, `LipschitzHilbert_Fourier_DemodulatedVertical`, `LipschitzHilbert_Fourier_DyadicCommutatorCutoff`, `LipschitzHilbert_Fourier_DyadicKernelTelescoping`, `LipschitzHilbert_Fourier_DyadicLineResolution`, `LipschitzHilbert_Fourier_DyadicProjectionCarleson`, `LipschitzHilbert_Fourier_DyadicResolutionSymbol`, `LipschitzHilbert_Fourier_DyadicSmoothCutoff`, `LipschitzHilbert_Fourier_FiniteBandMultiplier`, `LipschitzHilbert_Fourier_FiniteTimeKernelMoment`, `LipschitzHilbert_Fourier_FiniteVerticalBins`, `LipschitzHilbert_Fourier_FourierAveragingConvolution`, `LipschitzHilbert_Fourier_FourierAveragingKernel`, `LipschitzHilbert_Fourier_FourierAveragingMeasure`, `LipschitzHilbert_Fourier_FourierHomogeneity`, `LipschitzHilbert_Fourier_FourierKernelFirstMoment`, `LipschitzHilbert_Fourier_GeneralAnnularComparison`, `LipschitzHilbert_Fourier_HilbertCutoffProfile`, `LipschitzHilbert_Fourier_HilbertFiniteSymbol`, `LipschitzHilbert_Fourier_KernelDifferencePairing`, `LipschitzHilbert_Fourier_LineBoundedCommutatorL2`, `LipschitzHilbert_Fourier_LineCommutatorEnergy`, `LipschitzHilbert_Fourier_LineConjugationBound`, `LipschitzHilbert_Fourier_LineConvolutionEnergy`, `LipschitzHilbert_Fourier_LineConvolutionPairing`, `LipschitzHilbert_Fourier_LineCountSlab`, `LipschitzHilbert_Fourier_LineDerivativeCommutatorL2`, `LipschitzHilbert_Fourier_LineDyadicReconstructionEnergy`, `LipschitzHilbert_Fourier_LineFrequencyProjection`, `LipschitzHilbert_Fourier_LineGeometricSchur`, `LipschitzHilbert_Fourier_LineKernelDecay`, `LipschitzHilbert_Fourier_LineKernelScaling`, `LipschitzHilbert_Fourier_LineLocalizedMultiplier`, `LipschitzHilbert_Fourier_LineLowHighCommutator`, `LipschitzHilbert_Fourier_LineLowpassCell`, `LipschitzHilbert_Fourier_LineMollification`, `LipschitzHilbert_Fourier_LineProductSpectrum`, `LipschitzHilbert_Fourier_LineProjectionKernel`, `LipschitzHilbert_Fourier_LineSamplingDecay`, `LipschitzHilbert_Fourier_LineSamplingEnergy`, `LipschitzHilbert_Fourier_LineSamplingGenerator`, `LipschitzHilbert_Fourier_LineSamplingHomeomorph`, `LipschitzHilbert_Fourier_LineSamplingInverse`, `LipschitzHilbert_Fourier_LineSamplingKernelCommutator`, `LipschitzHilbert_Fourier_LineSamplingSchwartz`, `LipschitzHilbert_Fourier_LineSamplingStrongDerivative`, `LipschitzHilbert_Fourier_LocalizedBandStrong`, `LipschitzHilbert_Fourier_MeasureClassKernel`, `LipschitzHilbert_Fourier_NarrowBandCutoff`, `LipschitzHilbert_Fourier_NormalizedBandProjection`, `LipschitzHilbert_Fourier_NormalizedBandSymbol`, `LipschitzHilbert_Fourier_NormalizedConvolutionForm`, `LipschitzHilbert_Fourier_NormalizedSymbolFamily`, `LipschitzHilbert_Fourier_PartitionedFrequencySymbol`, `LipschitzHilbert_Fourier_PlanarSchwartzInversion`, `LipschitzHilbert_Fourier_PlanarSliceFourier`, `LipschitzHilbert_Fourier_PlanarSliceFourierBasic`, `LipschitzHilbert_Fourier_Projection`, `LipschitzHilbert_Fourier_RectangularFrequencyCutoff`, `LipschitzHilbert_Fourier_ReflectedBandProjection`, `LipschitzHilbert_Fourier_RescaledPartitionedSymbol`, `LipschitzHilbert_Fourier_ScalarLineVariation`, `LipschitzHilbert_Fourier_SchwartzConjugation`, `LipschitzHilbert_Fourier_SchwartzGlobalLipschitz`, `LipschitzHilbert_Fourier_SchwartzVerticalProjection`, `LipschitzHilbert_Fourier_SeparatedSymbolFourier`, `LipschitzHilbert_Fourier_SeparatedSymbolOperator`, `LipschitzHilbert_Fourier_ShortVerticalDifference`, `LipschitzHilbert_Fourier_ShortVerticalError`, `LipschitzHilbert_Fourier_SignedAnnularSymbol`, `LipschitzHilbert_Fourier_SimpleFourierPairing`, `LipschitzHilbert_Fourier_SmoothSlopeSymbol`, `LipschitzHilbert_Fourier_SymbolSlice`, `LipschitzHilbert_Fourier_SymbolWeights`, `LipschitzHilbert_Fourier_VariableEndpointKernel`, `LipschitzHilbert_Fourier_VerticalBinCommutator`, `LipschitzHilbert_Fourier_VerticalBinCost`, `LipschitzHilbert_Fourier_VerticalBinKernel`, `LipschitzHilbert_Fourier_VerticalBinLpEnergy`, `LipschitzHilbert_Fourier_VerticalBinPlateau`, `LipschitzHilbert_Fourier_VerticalBinProfile`, `LipschitzHilbert_Fourier_VerticalBinVector`, `LipschitzHilbert_Fourier_VerticalConvolutionL1`, `LipschitzHilbert_Fourier_VerticalConvolutionL2`, `LipschitzHilbert_Fourier_VerticalConvolutionPVLimit`, `LipschitzHilbert_Fourier_VerticalMoment`, `LipschitzHilbert_Fourier_VerticalProjectionDerivative`, `LipschitzHilbert_Fourier_VerticalSamplingCommutator`, `LipschitzHilbert_Fourier_VerticalSamplingDifference`, `LipschitzHilbert_Fourier_VerticalSamplingGeometry`, `LipschitzHilbert_Fourier_VerticalSamplingMihlin`, `LipschitzHilbert_Fourier_VerticalSecantEnergy`, `LipschitzHilbert_Fourier_VerticalWindowRescaling`, `LipschitzHilbert_Fourier_WitnessLineAverage`, `LipschitzHilbert_Geometry_CompactDirectionCutoff`, `LipschitzHilbert_Geometry_ConditionalUnitDirection`, `LipschitzHilbert_Geometry_DirectionChartSampling`, `LipschitzHilbert_Geometry_DirectionDilation`, `LipschitzHilbert_Geometry_FrozenDirection`, `LipschitzHilbert_Geometry_HorizontalStripCover`, `LipschitzHilbert_Geometry_LocalMinimaSelection`, `LipschitzHilbert_Geometry_ProjectionGroupSelection`, `LipschitzHilbert_Geometry_RectangleCoverSelection`, `LipschitzHilbert_Geometry_RectanglePairEnergy`, `LipschitzHilbert_Geometry_SlopeDirection`, `LipschitzHilbert_Geometry_SlopeRectangle`, `LipschitzHilbert_Geometry_SmoothDirectionApproximation`, `LipschitzHilbert_Geometry_SourceShortTreeOverlap`, `LipschitzHilbert_Geometry_UniformNearSelection`, `LipschitzHilbert_Geometry_UnitDirectionCharts`, `LipschitzHilbert_Geometry_VerticalRectangle`, `LipschitzHilbert_Packets_AnalyzingCoefficients`, `LipschitzHilbert_Packets_AnalyzingProfileNormalization`, `LipschitzHilbert_Packets_AnnularPacketGeometry`, `LipschitzHilbert_Packets_FactoredMultiplierPackets`, `LipschitzHilbert_Packets_FiniteNormalizedPacketLattice`, `LipschitzHilbert_Packets_FinitePacketSites`, `LipschitzHilbert_Packets_NormalizedPacketProfiles`, `LipschitzHilbert_Packets_PacketBoxes`, `LipschitzHilbert_Packets_PacketConvolution`, `LipschitzHilbert_Packets_PacketDataJetBudget`, `LipschitzHilbert_Packets_PhysicalPacketSpectrum`, `LipschitzHilbert_Packets_PlanarFrequencyPackets`, `LipschitzHilbert_Packets_SchwartzPacketDecay`, `LipschitzHilbert_Packets_ShortPacketBoxes`, `LipschitzHilbert_Packets_SourceAssignedPacketSum`, `LipschitzHilbert_Packets_SourcePacketSpectrum`, `LipschitzHilbert_Packets_SourceSelectorConcentrationErrorMoments`, `LipschitzHilbert_Packets_SourceSupportedConcentrationCentered`, `LipschitzHilbert_Packets_TopCovariantPacket`, `LipschitzHilbert_Packets_TopWeightedPacket`, `LipschitzHilbert_Packets_UnitPacketSelector`, `LipschitzHilbert_Phase_AngularBoundaryDistance`, `LipschitzHilbert_Phase_DiagonalCarrier`, `LipschitzHilbert_Phase_DiagonalPhaseSelection`, `LipschitzHilbert_Phase_DominantNormalization`, `LipschitzHilbert_Phase_DominantPathComparison`, `LipschitzHilbert_Phase_FiniteInterpolation`, `LipschitzHilbert_Phase_FourthMoment`, `LipschitzHilbert_Phase_FrequencyQuantiles`, `LipschitzHilbert_Phase_GaussianPhaseDamping`, `LipschitzHilbert_Phase_GraphPredictionFactor`, `LipschitzHilbert_Phase_ImprovedFourthMoment`, `LipschitzHilbert_Phase_InterpolationFamily`, `LipschitzHilbert_Phase_PhaseCombinatorics`, `LipschitzHilbert_Phase_PhaseSelection`, `LipschitzHilbert_Phase_PlanarSliceFourierAngular`, `LipschitzHilbert_Phase_PredictionCells`, `LipschitzHilbert_Phase_PredictionNormalization`, `LipschitzHilbert_Phase_Quantiles`, `LipschitzHilbert_Phase_ScalarBandDiagonal`, `LipschitzHilbert_Phase_ScalarPhase`, `LipschitzHilbert_Phase_SimplexTubeInterpolation`, `LipschitzHilbert_Phase_SourcePredictionMotion`, `LipschitzHilbert_Trees_EventMass`, `LipschitzHilbert_Trees_FixedPathAverage`, `LipschitzHilbert_Trees_GeometricBoundaryDepth`, `LipschitzHilbert_Trees_HierarchyWeights`, `LipschitzHilbert_Trees_LineSamplingL2Path`, `LipschitzHilbert_Trees_LineSamplingPath`, `LipschitzHilbert_Trees_PathCoefficient`, `LipschitzHilbert_Trees_PathDrops`, `LipschitzHilbert_Trees_SlopePartitionGrid`, `LipschitzHilbert_Trees_SourceBoundedDuality`, `LipschitzHilbert_Trees_SourceBoxReproduction`, `LipschitzHilbert_Trees_SourceBoxSupremum`, `LipschitzHilbert_Trees_SourceCoordinateSpectrum`, `LipschitzHilbert_Trees_SourceGoodPathSet`, `LipschitzHilbert_Trees_SourceKernelShells`, `LipschitzHilbert_Trees_SourceLpExhaustion`, `LipschitzHilbert_Trees_SourceMaskMotion`, `LipschitzHilbert_Trees_SourceModelThresholdScale`, `LipschitzHilbert_Trees_SourcePhysicalCoefficient`, `LipschitzHilbert_Trees_SourcePlanarPlancherel`, `LipschitzHilbert_Trees_SourcePlanarPolynomial`, `LipschitzHilbert_Trees_SourceResidualBlockGeometry`, `LipschitzHilbert_Trees_SourceReverseWeights`, `LipschitzHilbert_Trees_SourceShiftSimplex`, `LipschitzHilbert_Trees_SourceSlopeLabels`, `LipschitzHilbert_Trees_SourceSpatialSubdivision`, `LipschitzHilbert_Trees_SourceSpatialTreePieces`, `LipschitzHilbert_Trees_SourceThresholdWeights`, `LipschitzHilbert_Trees_SourceTiledLineIntegral`, `LipschitzHilbert_Trees_SourceTreeCells`, `LipschitzHilbert_Trees_SourceVectorSlices`, `LipschitzHilbert_Trees_SourceVerticalDemodulation`, `LipschitzHilbert_Trees_SourceWeightedTreeEnergy`, `LipschitzHilbert_Trees_SourceWhitneySummation`, `LipschitzHilbert_Trees_UnaryEnergy`, `LipschitzHilbert_Trees_UnaryPropagation`, `LipschitzHilbert_Trees_UnaryRunCharging`, `LipschitzHilbert_Trees_UnaryRuns`, `LipschitzHilbert_Trees_UnarySegmentation`.
--
--   **Imports.** It imports the published bundle `Def_LipschitzHilbert`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ090A002`; the statements `OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported`, `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing`, `OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set`, `OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery`, `OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy`, `OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding`, `OAI.LipschitzHilbert.PacketRepresentation.lineConjugation_derivative_bound`, `OAI.LipschitzHilbert.PacketRepresentation.lineSamplingGenerator_commutator_bound`, `OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported` and `OAI.LipschitzHilbert.eventually_source_grid_parameters`; the proof of `OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding`.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The coordinate map `(x,y) ↦ (x,y+s*x)`, with its explicit inverse. -/
def slopeShear (s : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun z := (z.1, z.2 + s * z.1)
  invFun z := (z.1, z.2 - s * z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add (measurable_const.mul measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (measurable_const.mul measurable_fst))

theorem slopeShear_measurePreserving (s : ℝ) :
    MeasurePreserving (slopeShear s) (volume.prod volume) (volume.prod volume) := by
  change MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + s * z.1)) _ _
  exact (MeasurePreserving.id volume).skew_product
    (measurable_snd.add (measurable_const.mul measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (s * x))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

def lineShift (s t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + t, z.2 + s * t)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

def planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.mulRight₀ a⁻¹ (inv_ne_zero ha)).prodCongr
    (MeasurableEquiv.mulRight₀ b⁻¹ (inv_ne_zero hb))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact top shape from (src-5) and its seventh-power decay
outside the mask's near region. -/

noncomputable section

namespace LipschitzHilbert

def topShape (K D x y : ℝ) : ℝ :=
  (2:ℝ)^D*(1+(|x|+|y|)/K)^(-D)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThresholdWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical density-size weight has summable decay on both sides
of the unit scale, with the quarter-power density gain. -/
noncomputable section
namespace LipschitzHilbert

def ordinaryThresholdWeight (gamma eta : ℝ) : ℝ :=
  min gamma (2*eta) * Real.sqrt eta * (1+eta^(-(1/20:ℝ))) / eta

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_MeasureClassKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable cubic separation of dyadic measure classes, with a finite
convolution bound uniform in the number and range of classes. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def measureClassKernel (k : ℤ) : ℝ := (((k.natAbs:ℝ)+1)^3)⁻¹

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeasureClassLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic restricted estimate is dominated by the summable
kernel of the actual dyadic support-measure classes. -/
noncomputable section
namespace LipschitzHilbert

def measureClassLogConstant : ℝ := (2+1/Real.log 2)^3

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicMeasureClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support-measure class is chosen from the actual positive
measure by the integer floor of its base-two logarithm. -/
noncomputable section
namespace LipschitzHilbert

def dyadicMeasureClass (m : ℝ) : ℤ := ⌊Real.log m/Real.log 2⌋

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteRestrictedStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-amplitude restricted-to-strong estimate from Section 2.
The matrix entries are the restricted bilinear pairings. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def restrictedStrongConstant : ℝ :=
  1+32*measureClassLogConstant*(∑' k, measureClassKernel k)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual disjoint amplitude levels and their square-energy budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

def amplitudeLevel (f : X → E) (i : ℤ) : Set X :=
  {x | (2:ℝ)^(i-1)<‖f x‖ ∧ ‖f x‖≤(2:ℝ)^i}

theorem amplitudeLevel_measurable {f : X → E} (hf : Measurable (fun x => ‖f x‖)) (i : ℤ) :
    MeasurableSet (amplitudeLevel f i) :=
  (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)

omit [MeasurableSpace X] in
theorem amplitudeLevel_disjoint (f : X → E) : Pairwise (fun i j => Disjoint (amplitudeLevel f i) (amplitudeLevel f j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : (2:ℝ)^i≤(2:ℝ)^(j-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hxi.2.trans hp)) hxj.1
  · have hp : (2:ℝ)^j≤(2:ℝ)^(i-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hxj.2.trans hp)) hxi.1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RetainedAmplitudeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained pair sum loses only one logarithmic factor, as in the
source amplitude reduction. This concerns the actual measurable levels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def retainedAmplitudeCost (C0 L : ℝ) : ℝ :=
  4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt (4*C0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeAllWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All finite collections of actual amplitude levels split into the
retained logarithmic cost and the two exponentially small mass tails. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

def amplitudeTailCost (Q L : ℝ) : ℝ :=
  (8+2*(2/(1-(Real.sqrt 2)⁻¹)))*Q*Real.exp (-L/8)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted-to-strong estimate for the actual finite amplitude
approximations of Hilbert-valued functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def amplitudePiece (f : X → EuclideanSpace ℂ κ) (i : ℤ) : X → EuclideanSpace ℂ κ :=
  (2:ℝ)^(-i) • (amplitudeLevel f i).indicator f

def amplitudeApprox (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) : X → EuclideanSpace ℂ κ :=
  ∑ i∈I, (2:ℝ)^i • amplitudePiece f i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite amplitude approximations converge in squared L2 energy.
The cutoff is the actual disjoint union of its amplitude levels. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] in
theorem amplitude_scaled_piece (f : X → EuclideanSpace ℂ κ) (i : ℤ) :
    (2:ℝ)^i • amplitudePiece f i=(amplitudeLevel f i).indicator f := by
  funext x
  simp only [amplitudePiece,Pi.smul_apply,smul_smul]
  rw [←zpow_add₀ (by norm_num : (2:ℝ)≠0),add_neg_cancel,zpow_zero,one_smul]

omit [MeasurableSpace X] in
theorem amplitudeApprox_eq_indicator (f : X → EuclideanSpace ℂ κ) (I : Finset ℤ) :
    amplitudeApprox f I=(⋃ i∈I, amplitudeLevel f i).indicator f := by
  funext x
  simp only [amplitudeApprox,amplitude_scaled_piece,Finset.sum_apply]
  exact (Finset.indicator_biUnion_apply I (amplitudeLevel f)
    (fun i _ j _ hij => amplitudeLevel_disjoint f hij) x).symm

theorem amplitudeApprox_memLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (I : Finset ℤ) : MemLp (amplitudeApprox f I) 2 μ := by
  rw [amplitudeApprox_eq_indicator]
  exact hf2.indicator (Finset.measurableSet_biUnion _ (fun i _ => amplitudeLevel_measurable hf.norm i))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AmplitudeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same normalized amplitude pieces in the actual L2 quotient,
including null levels and exact finite reconstruction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudePiece_memLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ) : MemLp (amplitudePiece f i) 2 μ :=
  (hf2.indicator (amplitudeLevel_measurable hf.norm i)).const_smul _

def amplitudeLpPiece (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ) : Lp (EuclideanSpace ℂ κ) 2 μ :=
  (amplitudePiece_memLp μ hf hf2 i).toLp (amplitudePiece f i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BinaryDensityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite binary subdivision used for the far-group mass estimate.
A bad child is bounded using its good parent; good children are subdivided
until the terminal scale. -/
noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

def binaryChildCenter (c l : ℝ) (b : Bool) : ℝ :=
  if b then c+l/4 else c-l/4

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_Quantiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite quantiles for the fourth-moment gap

The lower and upper quantile choices in the proof of `phase:quantile-gap`, §7.
Weights are listed in increasing frequency order. No uniform measure on the
frequency list is assumed.
-/

open scoped BigOperators

namespace LipschitzHilbert

def prefixMass (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, w i

/-- The mass of a closed frequency interval. -/
noncomputable def intervalMass {ι : Type*} [Fintype ι] (w frequency : ι → ℝ)
    (a b : ℝ) : ℝ := by
  classical
  exact ∑ i, if a ≤ frequency i ∧ frequency i ≤ b then w i else 0

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FrequencyQuantiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quarter-tail quantiles in a finite ordered frequency list. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- Extend finite weights by zero, only to use natural-number prefix sums. -/
def extendWeights {N : ℕ} (x : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N then x ⟨i, hi⟩ else 0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_Hellinger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite probability estimate in the phase argument

This is the Hellinger-affinity calculation in §7, proof of `phase:quantile-gap`,
of *A uniform Hilbert transform estimate for Lipschitz directions*.
The finite probability calculation is proved directly.
-/

open scoped BigOperators

namespace LipschitzHilbert

/-- Hellinger affinity of finite probability weights. -/
noncomputable def affinity {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i) * Real.sqrt (q i)

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseCombinatorics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-phase resonance combinatorics

These are the elementary finite combinatorial ingredients of §7,
Lemma `phase:quantile-gap`, of *A uniform Hilbert transform estimate for
Lipschitz directions*. The frequency separation is quantitative; no
assumption about additive independence is made.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

def Separated (frequency : ι → ℝ) (gap : ℝ) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → gap ≤ |frequency i - frequency j|

def Resonant (frequency : ι → ℝ) (gap : ℝ) (i j k l : ι) : Prop :=
  |frequency i + frequency j - frequency k - frequency l| < gap / 4

abbrev Quadruple (ι : Type*) := ι × ι × ι × ι

def swapPairs : Quadruple ι ≃ Quadruple ι where
  toFun q := (q.2.2.1, q.2.2.2, q.1, q.2.1)
  invFun q := (q.2.2.1, q.2.2.2, q.1, q.2.1)
  left_inv := by rintro ⟨i, j, k, l⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

def swapLast : Quadruple ι ≃ Quadruple ι where
  toFun q := (q.1, q.2.1, q.2.2.2, q.2.2.1)
  invFun q := (q.1, q.2.1, q.2.2.2, q.2.2.1)
  left_inv := by rintro ⟨i, j, k, l⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

/-- The first of the four triple-coordinate subprobability weights. -/
def marginal (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) (q : Quadruple ι) : ℝ :=
  if Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2 then
    x q.1 * x q.2.1 * x q.2.2.1 else 0

def geometricTerm (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (q : Quadruple ι) : ℝ :=
  Real.sqrt
    (Real.sqrt (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) *
      Real.sqrt (marginal frequency gap x (swapLast q) *
        marginal frequency gap x ((swapPairs.trans swapLast) q)))

/-- The ordinary fourth-moment quantity in the manuscript. -/
def resonanceSum [Fintype ι] (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ q : Quadruple ι, geometricTerm frequency gap x q

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection of the near-resonant quadruple measure

The quantile-gap argument in §7 projects the triple weight on quadruples
to coordinates `(i,k,l)`. Unique completion makes the Hellinger affinity
of the projected measures exactly the affinity before projection.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*}

abbrev Triple (ι : Type*) := ι × ι × ι

def insertSecond : (Triple ι × ι) ≃ Quadruple ι where
  toFun q := (q.1.1, q.2, q.1.2.1, q.1.2.2)
  invFun q := ((q.1, q.2.2.1, q.2.2.2), q.2.1)
  left_inv := by rintro ⟨⟨i, k, l⟩, j⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

def projectedMass [Fintype ι] (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (q : Triple ι) : ℝ :=
  ∑ j, marginal frequency gap x (q.1, j, q.2.1, q.2.2)

def independentMass (x : ι → ℝ) (q : Triple ι) : ℝ := x q.1 * x q.2.1 * x q.2.2

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_EventMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The quantile event has a positive deficit

Finite sums implement the event calculation in the proof of
`phase:quantile-gap`. The only geometric condition is the explicitly
proved fact that a resonant completion of the event lies below its
chosen central interval.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

def rectangularEvent (I K L : Finset ι) : Finset (Triple ι) := I ×ˢ (K ×ˢ L)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourth moments of separated finite Fourier sums

The exact finite expansion and Fourier-support reduction used in §7,
proof of Proposition `phase:finite-fourier`. The annihilation hypothesis
is a property of the averaging probability measure, not a new axiom.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

def character (frequency t : ℝ) : ℂ := Complex.exp ((frequency * t : ℝ) * Complex.I)

theorem norm_character (frequency t : ℝ) : ‖character frequency t‖ = 1 := by
  simp [character, Complex.norm_exp]

def finiteFourierSum (frequency : ι → ℝ) (coefficient : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, coefficient i * character (frequency i) t

def coefficientProduct (a : ι → ℂ) (q : Quadruple ι) : ℂ :=
  a q.1 * a q.2.1 * conj (a q.2.2.1) * conj (a q.2.2.2)

def frequencyDifference (frequency : ι → ℝ) (q : Quadruple ι) : ℝ :=
  frequency q.1 + frequency q.2.1 - frequency q.2.2.1 - frequency q.2.2.2

def fourierMoment (ν : Measure ℝ) (s : ℝ) : ℂ := ∫ t, character s t ∂ν

/-- A measure with Fourier support in the open interval `(-gap/4,gap/4)`
annihilates all the moments specified in this condition. -/
def FourierGap (ν : Measure ℝ) (gap : ℝ) : Prop :=
  ∀ s : ℝ, gap / 4 ≤ |s| → fourierMoment ν s = 0

def coefficientMass (a : ι → ℂ) (i : ι) : ℝ := ‖a i‖ ^ (4 / 3 : ℝ)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

/-- The manuscript's absolute phase constant `2⁻⁶⁰`. -/
def phaseConstant : ℝ := 1 / 1152921504606846976

/-- The manuscript's threshold `2⁻¹⁰` for a dominant coefficient. -/
def atomThreshold : ℝ := 1 / 1024

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity of finite sequence norms and the small-remainder estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

/-- A sequence norm is written as a real power of its finite power sum. -/
def sequenceNorm (a : ι → ℂ) (r : ℝ) : ℝ := (∑ i, ‖a i‖ ^ r) ^ (1 / r)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of a dominant Fourier carrier in §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

abbrev RemainderIndex (i₀ : ι) := {i : ι // i ≠ i₀}

def remainderFrequency (frequency : ι → ℝ) (i₀ : ι) (i : RemainderIndex i₀) : ℝ :=
  frequency i - frequency i₀

def remainderCoefficient (a : ι → ℂ) (i₀ : ι) (i : RemainderIndex i₀) : ℂ :=
  a i / a i₀

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ImprovedFourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved fourth moment: assembly of the quantitative gap and
the dominant-coefficient alternative from §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

def phaseParameter (D : ℝ) : ℝ := phaseConstant / Real.log (2 * D)

def fourthExponent (D : ℝ) : ℝ := 4 / (3 - phaseParameter D)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoundedDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the interpolated simple-test pairing estimate to a bounded
canonical dual test. Only finite measures and bounded functions are needed. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

def canonicalDual (F : ℝ → ℂ) (p : ℝ) (x : ℝ) : ℂ :=
  conj (F x) * (‖F x‖ ^ (p - 2) : ℝ)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlaneCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure-preserving bridge from the manuscript's real coordinate
pairs to the Euclidean plane used by the published maximal estimate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def planeCoordinates : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem planeCoordinates_apply (z : ℝ × ℝ) :
    planeCoordinates z = WithLp.toLp 2 ![z.1,z.2] := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeOrthonormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthonormal long and transverse axes of an actual slope box. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def slopeAxisVectors (s : ℝ) : Fin 2 → Plane :=
  ![WithLp.toLp 2 ![1/Real.sqrt (1+s^2), s/Real.sqrt (1+s^2)],
    WithLp.toLp 2 ![-s/Real.sqrt (1+s^2), 1/Real.sqrt (1+s^2)]]

theorem slopeAxisVectors_orthonormal (s : ℝ) : Orthonormal ℝ (slopeAxisVectors s) := by
  have hpos : 0 < 1+s^2 := by positivity
  have hq : Real.sqrt (1+s^2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hq2 := Real.sq_sqrt hpos.le
  rw [orthonormal_iff_ite]
  intro i j
  change (∑ k, slopeAxisVectors s j k * slopeAxisVectors s i k) = _
  fin_cases i <;> fin_cases j <;>
    simp [slopeAxisVectors, Fin.sum_univ_two] <;>
    field_simp [hq] <;> nlinarith

def slopeAxes (s : ℝ) : OrthonormalBasis (Fin 2) ℝ Plane :=
  OrthonormalBasis.mk (slopeAxisVectors_orthonormal s)
    ((slopeAxisVectors_orthonormal s).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [Plane])).ge

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SlopeDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normalization of slope directions and the exact
uncertainty-arc condition needed by the Lacey--Li rectangle input. -/

noncomputable section
open scoped BigOperators NNReal
namespace LipschitzHilbert

def slopeDirection (s : ℝ) : Plane := slopeAxes s 0

theorem plane_norm_le_coordinate_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := EuclideanSpace.real_norm_sq_eq z
  simp only [Fin.sum_univ_two] at h
  apply (sq_le_sq₀ (norm_nonneg z) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [h]
  nlinarith [sq_abs (z 0), sq_abs (z 1),
    mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlaneSlopeLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the Euclidean-plane Lipschitz field to the product-coordinate
metric used by the geometric witness and line-counting arguments. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem planeCoordinates_lipschitz : LipschitzWith 2 planeCoordinates := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := plane_norm_le_coordinate_sum (planeCoordinates z-planeCoordinates w)
  simp only [planeCoordinates_apply,PiLp.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  rw [dist_eq_norm]
  apply h.trans
  change |z.1-w.1|+|z.2-w.2| ≤ (2:ℝ)*dist z w
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  linarith [le_max_left |z.1-w.1| |z.2-w.2|,le_max_right |z.1-w.1| |z.2-w.2|]

theorem product_slope_lipschitz (u : Plane → ℝ) {K : ℝ≥0} (hu : LipschitzWith K u) :
    LipschitzWith (2*K) (fun z : ℝ × ℝ => u (planeCoordinates z)) := by
  simpa only [mul_comm,Function.comp_def] using hu.comp planeCoordinates_lipschitz

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous packet identity in §2, with the actual convolution
kernels and the exact area normalization. Absolute integrability follows
from L1 kernels and input and a bounded measurable test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def analyzingWave (area : ℝ) (K : ℝ × ℝ → ℂ) (z y : ℝ × ℝ) : ℂ :=
  (area : ℂ) * conj (K (z-y))

def synthesisWave (area : ℝ) (K : ℝ × ℝ → ℂ) (z x : ℝ × ℝ) : ℂ :=
  (area : ℂ) * K (x-z)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FrozenSlopeMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The multiplier identity freezes the direction at the output point.
It is proved by Fubini for actual integrable time and frequency data. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def slopeKernelOperator (k : ℝ → ℂ) (u : ℝ×ℝ → ℝ) (f : ℝ×ℝ → ℂ)
    (x : ℝ×ℝ) : ℂ :=
  ∫ t, k t*f (x.1-t,x.2-t*u x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CoordinateFourierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by the line coordinate preserves Fourier support for
Schwartz functions. This is the first step in polynomial localization of
the annular packet variation estimate. -/

noncomputable section

open MeasureTheory Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

def coordinateProduct (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive polynomial weights used to localize annular packets on a
reference line. Their construction and Fourier support preservation are
proved here for the actual Schwartz functions. -/

noncomputable section

open Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

def centeredCoordinateProduct (a : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  coordinateProduct f + (-a : ℂ) • f

def quadraticLocalization (a r : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f + (((r ^ 2)⁻¹ : ℝ) : ℂ) • centeredCoordinateProduct a (centeredCoordinateProduct a f)

def polynomialWeight (a r : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  (1 + (x - a) ^ 2 / r ^ 2) ^ q

def polynomialLocalization (a r : ℝ) : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, f => f
  | q + 1, f => quadraticLocalization a r (polynomialLocalization a r q f)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSliceFourierBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-Lebesgue Fourier transforms and transverse partial transforms
of general planar Schwartz functions. The phase is `exp(-2πi(xξ+yη))`. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem planar_shear_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s : ℝ) :
    Integrable (fun z : ℝ × ℝ => f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  exact (slopeShear_measurePreserving s).integrable_comp_of_integrable f.integrable

theorem planar_slice_integrand_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * ω)) •
      f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  apply (planar_shear_integrable f s).norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSliceFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier support of affine-line restrictions

Fubini and the area-preserving shear identify the transverse Fourier
transform of a slice coefficient with the planar transform on the fiber
`ξ+sη=ω`. One-dimensional Fourier inversion then proves exact vanishing
when this fiber misses the planar spectrum. No tensor representation is used.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem planar_phase_integrable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (s ω η : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * ω + z.2 * η)) •
      f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  apply (planar_shear_integrable f s).norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PlanarSliceFourierAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def angularFourier (g : ℝ → ℂ) (ω : ℝ) : ℂ := 𝓕 g (ω / (2 * Real.pi))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPlancherel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-coordinate Plancherel and the common-frequency witness
needed for the actual planar packet Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

abbrev HilbertPlane := WithLp 2 (ℝ×ℝ)

def liftPlanar (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap HilbertPlane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) f

theorem integral_hilbertPlane {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : HilbertPlane → V) :
    (∫ x, F x)=(∫ z : ℝ×ℝ, F (WithLp.toLp 2 z) ∂volume.prod volume) := by
  exact ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ×ℝ)).measurableEmbedding F).symm

/-- Lift a planar Schwartz function to the Hilbert norm on the same coordinates. -/
def hilbertPlanarSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ :=
  liftPlanar f

theorem hilbertPlanarSchwartz_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    hilbertPlanarSchwartz f (WithLp.toLp 2 z)=f z := rfl

theorem integral_hilbertPlanar_bridge {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : WithLp 2 (ℝ×ℝ) → V) :
    (∫ x, F x)=(∫ z : ℝ×ℝ, F (WithLp.toLp 2 z) ∂volume.prod volume) :=
  integral_hilbertPlane F

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

/-- The planar transform remains Schwartz, with the product norm. -/
def planarFourierSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm (𝓕 (hilbertPlanarSchwartz f))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact symbols of finite dilated time-kernel sums. No bound or limit
on the number of scales is used in this identity. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def scaledTimeKernel (k : ℝ → ℂ) (l : ℝ) (t : ℝ) : ℂ :=
  (l⁻¹ : ℂ)*k (t/l)

theorem scaledTimeKernel_integrable (k : ℝ → ℂ) (hk : Integrable k)
    (l : ℝ) (hl : l≠0) : Integrable (scaledTimeKernel k l) := by
  have h := (hk.comp_mul_right' (inv_ne_zero hl)).const_mul (l⁻¹ : ℂ)
  apply h.congr
  filter_upwards [] with t
  change (l⁻¹ : ℂ)*k (t*l⁻¹)=scaledTimeKernel k l t
  rw [scaledTimeKernel, div_eq_mul_inv]

theorem scaledTimeKernel_fourier (k : ℝ → ℂ) (l : ℝ) (hl : 0<l) (omega : ℝ) :
    𝓕 (scaledTimeKernel k l) omega=𝓕 k (l*omega) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [Real.inner_apply, scaledTimeKernel, Circle.smul_def, smul_eq_mul]
  have hp (t : ℝ) : -(t*omega)=-((t/l)*(l*omega)) := by field_simp
  simp_rw [hp]
  calc
    _ = (l⁻¹ : ℂ)*∫ t, (Real.fourierChar (-((t/l)*(l*omega))) : ℂ)*k (t/l) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = (l⁻¹ : ℂ)*(l • ∫ t, (Real.fourierChar (-(t*(l*omega))) : ℂ)*k t) := by
      rw [Measure.integral_comp_div (fun t => (Real.fourierChar (-(t*(l*omega))) : ℂ)*k t) l,
        abs_of_pos hl]
    _ = _ := by
      rw [Complex.real_smul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast hl.ne' : (l:ℂ)≠0), one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def symbolX (l xi eta theta : ℝ) : ℝ := l*(xi+theta*eta)
def symbolY (W eta center : ℝ) : ℝ := W*(eta-center)
def symbolU (l w u theta : ℝ) : ℝ := (u-theta)/(w/l)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation of the normalized (X,Y,U) symbol by Fourier inversion.
The two frequency coordinates and the selector coordinate are separated
inside an absolutely convergent integral. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

abbrev SymbolSpace := EuclideanSpace ℝ (Fin 3)

def symbolPoint (X Y U : ℝ) : SymbolSpace := WithLp.toLp 2 ![X,Y,U]

def frequencyCharacter (nu : SymbolSpace) (X Y : ℝ) : ℂ :=
  (Real.fourierChar (nu 0*X) : ℂ)*(Real.fourierChar (nu 1*Y) : ℂ)

def selectorCharacter (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (Real.fourierChar (nu 2*U) : ℂ)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable fixed polynomial weights for the separated symbol.
The same weight is allocated to the two waves and to the selector,
leaving an integrable outside coefficient. Only a fixed seminorm is used. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def symbolWeight (q : ℕ) (nu : SymbolSpace) : ℝ := ((1+‖nu‖)^q)⁻¹

def symbolCoefficientBound (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) : ℝ :=
  2^(4*q) * (Finset.Iic (4*q,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 S) + 1

def weightedSelector (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (𝓕 S nu / ((symbolWeight q nu : ℝ):ℂ)^3)*selectorCharacter nu U

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SymbolSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting one fixed Schwartz symbol to the two scale parameters.
The restriction does not enlarge any Schwartz seminorm. -/
noncomputable section
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

abbrev MasterSymbolSpace := SymbolSpace × (ℝ × ℝ)

def symbolInclusion : SymbolSpace →L[ℝ] MasterSymbolSpace :=
  ContinuousLinearMap.inl ℝ SymbolSpace (ℝ × ℝ)

theorem symbolSlice_temperate (p : ℝ × ℝ) :
    Function.HasTemperateGrowth (fun q : SymbolSpace => (q,p)) := by
  have h := symbolInclusion.hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const (E := SymbolSpace) (0,p))
  change Function.HasTemperateGrowth (fun q => symbolInclusion q+(0,p)) at h
  simpa only [Pi.add_apply, symbolInclusion, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    add_zero, zero_add] using h

theorem symbolSlice_antilipschitz (p : ℝ × ℝ) :
    AntilipschitzWith 1 (fun q : SymbolSpace => (q,p)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, Prod.dist_eq]
  exact le_max_left _ _

def symbolSlice (F : SchwartzMap MasterSymbolSpace ℂ) (p : ℝ × ℝ) :
    SchwartzMap SymbolSpace ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (symbolSlice_temperate p)
    (symbolSlice_antilipschitz p) F

@[simp] theorem symbolSlice_apply (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (q : SymbolSpace) : symbolSlice F p q=F (q,p) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single compactly supported master symbol for the normalized
annular multipliers. Its slices have uniform Fourier coefficient bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

def masterArgument (z : MasterSymbolSpace) : ℝ :=
  z.1 0+(z.2.1+z.2.2*z.1 1)*z.1 2

theorem masterArgument_temperate : Function.HasTemperateGrowth masterArgument := by
  let P : MasterSymbolSpace →L[ℝ] SymbolSpace := ContinuousLinearMap.fst ℝ _ _
  let Q : MasterSymbolSpace →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.snd ℝ _ _
  let X := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).comp P
  let Y := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).comp P
  let U := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).comp P
  let V := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp Q
  let T := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp Q
  have h := X.hasTemperateGrowth.add
    ((V.hasTemperateGrowth.add (T.hasTemperateGrowth.mul Y.hasTemperateGrowth)).mul U.hasTemperateGrowth)
  change Function.HasTemperateGrowth (fun z => X z+(V z+T z*Y z)*U z) at h
  exact h

def masterCutoff (R : ℝ) (hR : 0<R) : SchwartzMap MasterSymbolSpace ℂ :=
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  (b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

def masterSymbol (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R) :
    SchwartzMap MasterSymbolSpace ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z => psi (masterArgument z)) (masterCutoff R hR)

def normalizedSchwartzSymbol (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t : ℝ) : SchwartzMap SymbolSpace ℂ := symbolSlice (masterSymbol psi R hR) (v,t)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth annular selector. Multiplying the separated selector
by this cutoff gives the required support away from the reference slope. -/
noncomputable section
open scoped ContDiff FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def selectorInner (a : ℝ) (ha : 0<a) : ContDiffBump (0 : ℝ) :=
  ⟨a/2,a,by positivity,by linarith⟩

def selectorOuter (b : ℝ) (hb : 0<b) : ContDiffBump (0 : ℝ) :=
  ⟨b,2*b,hb,by linarith⟩

def annularCutoff (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℝ :=
  ((selectorOuter b hb).hasCompactSupport.mul_right
    (f' := fun U => 1-selectorInner a ha U)).toSchwartzMap
      ((selectorOuter b hb).contDiff.mul
        (contDiff_const.sub (selectorInner a ha).contDiff))

def localizedSelector (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (chi U : ℂ)*weightedSelector S q nu U

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SmoothSlopeSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth extension of the slope denominator gives the full normalized
symbol, including its slope partition and vertical frequency window. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

def positiveDenominator (c s : ℝ) : ℝ :=
  c/2+Real.smoothTransition ((s-c/2)/(c/2))*(s-c/2)

theorem positiveDenominator_lower (c : ℝ) (hc : 0 < c) (s : ℝ) :
    c/2≤positiveDenominator c s := by
  unfold positiveDenominator
  by_cases hs : s ≤ c/2
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hs) (by positivity)), zero_mul, add_zero]
  · exact le_add_of_nonneg_right
      (mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (le_of_not_ge hs)))

theorem positiveDenominator_contDiff (c : ℝ) : ContDiff ℝ ∞ (positiveDenominator c) := by
  unfold positiveDenominator
  fun_prop

def masterVertical (z : MasterSymbolSpace) : ℝ := z.2.1+z.2.2*z.1 1

theorem masterVertical_contDiff : ContDiff ℝ ∞ masterVertical := by
  unfold masterVertical
  fun_prop

def masterSlopeArgument (c : ℝ) (z : MasterSymbolSpace) : ℝ :=
  -z.1 0/positiveDenominator c (masterVertical z)

theorem masterSlopeArgument_contDiff (c : ℝ) (hc : 0 < c) :
    ContDiff ℝ ∞ (masterSlopeArgument c) := by
  apply ContDiff.div (by fun_prop) ((positiveDenominator_contDiff c).comp masterVertical_contDiff)
  intro z
  exact ne_of_gt ((by positivity : (0:ℝ) < c/2).trans_le (positiveDenominator_lower c hc (masterVertical z)))

theorem masterCutoff_hasCompactSupport (R : ℝ) (hR : 0<R) :
    HasCompactSupport (masterCutoff R hR : MasterSymbolSpace → ℂ) := by
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  exact b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)

def partitionedMasterSymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) : SchwartzMap MasterSymbolSpace ℂ :=
  let g := fun z : MasterSymbolSpace =>
    psi (masterArgument z)*rho (masterSlopeArgument c z)*beta (z.1 1)
  ((masterCutoff_hasCompactSupport R hR).mul_right (f' := g)).toSchwartzMap
    (((masterCutoff R hR).smooth ⊤).mul
      (((psi.smooth ⊤).comp masterArgument_temperate.1).mul
        ((rho.smooth ⊤).comp (masterSlopeArgument_contDiff c hc)) |>.mul (by fun_prop)))

def partitionedSymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0<R) (v t : ℝ) : SchwartzMap SymbolSpace ℂ :=
  symbolSlice (partitionedMasterSymbol psi rho beta c hc R hR) (v,t)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RescaledPartitionedSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope partition is rescaled together with the angular variable,
so its argument remains the original frequency slope divided by w/l. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def realDilation (H : ℝ) (hH : H≠0) : ℝ ≃L[ℝ] ℝ :=
  { LinearEquiv.smulOfNeZero ℝ ℝ H hH with
    continuous_toFun := by change Continuous (fun x : ℝ => H*x); fun_prop
    continuous_invFun := by change Continuous (fun x : ℝ => H⁻¹*x); fun_prop }

def dilatedSlopeWindow (rho : SchwartzMap ℝ ℂ) (H : ℝ) (hH : H≠0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilation H hH) rho

theorem dilatedSlopeWindow_apply (rho : SchwartzMap ℝ ℂ) (H : ℝ) (hH : H≠0) (x : ℝ) :
    dilatedSlopeWindow rho H hH x=rho (H*x) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete compact smooth partition on an arithmetic slope lattice.
The finite sum is exactly one on its prescribed interval. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def slopePartitionReal (x : ℝ) : ℝ := Real.smoothTransition (x+1)-Real.smoothTransition x

theorem slopePartitionReal_eq_zero (x : ℝ) (hx : x≤-1 ∨ 1≤x) : slopePartitionReal x=0 := by
  rcases hx with hx | hx
  · rw [slopePartitionReal,Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]
  · rw [slopePartitionReal,Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le hx,sub_self]

def slopePartition : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (slopePartitionReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
    intro x hx
    have hxx : x≤-1 ∨ 1≤x := by
      by_cases h : -1≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx1 => hx ⟨h,hx1⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,slopePartitionReal_eq_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) slopePartitionReal
    unfold slopePartitionReal
    fun_prop)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed real smooth bin profile whose squared translates sum to one.
The trigonometric construction avoids a variable normalization denominator. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def binSquareStep (x : ℝ) : ℝ := (Real.sin (Real.pi/2*Real.smoothTransition x))^2

def verticalBinProfileReal (x : ℝ) : ℝ :=
  Real.sin (Real.pi/2*Real.smoothTransition (x+1))*Real.cos (Real.pi/2*Real.smoothTransition x)

theorem verticalBinProfileReal_zero (x : ℝ) (hx : x≤-1 ∨ 1≤x) : verticalBinProfileReal x=0 := by
  rcases hx with hx | hx
  · simp [verticalBinProfileReal,Real.smoothTransition.zero_of_nonpos (show x+1≤0 by linarith)]
  · simp [verticalBinProfileReal,Real.smoothTransition.one_of_one_le hx]

def verticalBinProfile : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (verticalBinProfileReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
    intro x hx
    have hxx : x≤-1 ∨ 1≤x := by
      by_cases h : -1≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx1 => hx ⟨h,hx1⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,verticalBinProfileReal_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinProfileReal
    unfold verticalBinProfileReal
    fun_prop)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteVerticalBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite real square partition of a positive vertical band.
Only bins meeting the original band are retained. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def verticalBinCenter (K : ℕ) (W : ℝ) (n : ℕ) : ℝ := ((n:ℝ)-K)/W

def verticalBinWindow (K : ℕ) (W : ℝ) (n : ℕ) (eta : ℝ) : ℂ :=
  verticalBinProfile (W*(eta-verticalBinCenter K W n))

def verticalBinLabels (K : ℕ) (w W c C : ℝ) : Finset ℕ :=
  (Finset.range (2*K+1)).filter (fun n =>
    c-w/W≤w*verticalBinCenter K W n ∧ w*verticalBinCenter K W n≤C+w/W)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed enlarged vertical cutoff equals one on every bin profile.
The finite bin partition is exact throughout the prescribed annulus. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def verticalBinPlateauReal (x : ℝ) : ℝ :=
  Real.smoothTransition (x+2)*Real.smoothTransition (2-x)

theorem verticalBinPlateauReal_zero (x : ℝ) (hx : x≤-2 ∨ 2≤x) : verticalBinPlateauReal x=0 := by
  rcases hx with hx | hx
  · simp [verticalBinPlateauReal,Real.smoothTransition.zero_of_nonpos (show x+2≤0 by linarith)]
  · simp [verticalBinPlateauReal,Real.smoothTransition.zero_of_nonpos (show 2-x≤0 by linarith)]

def verticalBinPlateau : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (verticalBinPlateauReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have hxx : x≤-2 ∨ 2≤x := by
      by_cases h : -2≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx2 => hx ⟨h,hx2⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,verticalBinPlateauReal_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinPlateauReal
    unfold verticalBinPlateauReal
    fun_prop)

theorem verticalBinPlateau_one (x : ℝ) (hx : |x|≤1) : verticalBinPlateau x=1 := by
  have hb := abs_le.mp hx
  change (verticalBinPlateauReal x:ℂ)=1
  simp [verticalBinPlateauReal,Real.smoothTransition.one_of_one_le (show 1≤x+2 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤2-x by linarith)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def modulatedTimeKernel (K : ℝ → ℂ) (W center : ℝ) (t : ℝ) : ℂ :=
  Real.fourierChar (center*t) • scaledTimeKernel K W t

theorem modulatedTimeKernel_integrable (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (modulatedTimeKernel K W center) := by
  have hi := scaledTimeKernel_integrable K K.integrable W hW.ne'
  apply hi.norm.mono'
    ((show Continuous (fun t : ℝ => Real.fourierChar (center*t)) by fun_prop).aestronglyMeasurable.smul
      hi.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => le_of_eq (Circle.norm_smul _ _))

def verticalProfileKernel (q : SchwartzMap ℝ ℂ) (W center : ℝ) : ℝ → ℂ :=
  modulatedTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W center

def verticalConvolution (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, K t*f (z.1,z.2-t)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def finiteTimeKernel (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) (t : ℝ) : ℂ :=
  ∑ j : Fin N, scaledTimeKernel k (topLength/(2:ℝ)^j.val) t

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedCauchySchwarz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted scalar Cauchy--Schwarz bound used for vertical convolution. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem weighted_integral_cauchySchwarz {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w g : X → ℝ) (hwm : Measurable w) (hgm : Measurable g)
    (hw : ∀ x, 0≤w x) (hg : ∀ x, 0≤g x)
    (hwi : Integrable w mu) (henergy : Integrable (fun x => w x*g x^2) mu) :
    Integrable (fun x => w x*g x) mu ∧
      (∫ x, w x*g x ∂mu)^2≤(∫ x, w x ∂mu)*(∫ x, w x*g x^2 ∂mu) := by
  let a := fun x => Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)*g x
  have ha_sq (x) : a x^2=w x := Real.sq_sqrt (hw x)
  have hb_sq (x) : b x^2=w x*g x^2 := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (hw x)]
  have ha : MemLp a 2 mu := (memLp_two_iff_integrable_sq (f:=a)
    (hwm.sqrt.aestronglyMeasurable)).2 (by simpa only [ha_sq] using hwi)
  have hb : MemLp b 2 mu := (memLp_two_iff_integrable_sq (f:=b)
    ((hwm.sqrt.mul hgm).aestronglyMeasurable)).2 (by simpa only [hb_sq] using henergy)
  have heq (x) : a x*b x=w x*g x := by
    dsimp [a,b]
    rw [←mul_assoc,Real.mul_self_sqrt (hw x)]
  have hi : Integrable (fun x => w x*g x) mu := by
    have hi0 := ha.integrable_mul hb
    change Integrable (fun x => a x*b x) mu at hi0
    simpa only [heq] using hi0
  refine ⟨hi,?_⟩
  have hcs : (∫ x, w x*g x ∂mu)≤
      Real.sqrt (∫ x, w x ∂mu)*Real.sqrt (∫ x, w x*g x^2 ∂mu) := by
    simpa only [heq,Real.rpow_two,ha_sq,hb_sq,←Real.sqrt_eq_rpow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg (f:=a) (g:=b) Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg (w x)))
        (Filter.Eventually.of_forall (fun x => mul_nonneg (Real.sqrt_nonneg (w x)) (hg x)))
        (by simpa using ha) (by simpa using hb)
  have hs := pow_le_pow_left₀ (integral_nonneg fun x => mul_nonneg (hw x) (hg x)) hcs 2
  rwa [mul_pow,Real.sq_sqrt (integral_nonneg hw),
    Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg (g x)))] at hs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution acts on actual measurable planar functions.
Its L1 and uniform bounds are independent of bin width and carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalTranslation (t : ℝ) : (ℝ×ℝ) ≃ᵐ (ℝ×ℝ) where
  toFun z := (z.1,z.2-t)
  invFun z := (z.1,z.2+t)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.sub measurable_const)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.add measurable_const)

theorem verticalConvolution_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (f : ℝ×ℝ → ℂ) (hf : Measurable f) : Measurable (verticalConvolution K f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ => K p.2*f (p.1.1,p.1.2-p.2)) := by
    exact (hK.comp measurable_snd).mul (hf.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical convolution energy bound for measurable L2 functions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_pointwise_energy (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (z : ℝ×ℝ)
    (he : Integrable (fun t => ‖K t‖*‖f (z.1,z.2-t)‖^2)) :
    ‖verticalConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) := by
  obtain ⟨hi,hsq⟩ := weighted_integral_cauchySchwarz volume
    (fun t => ‖K t‖) (fun t => ‖f (z.1,z.2-t)‖)
    hKm.norm (hfm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm he
  have hn : ‖verticalConvolution K f z‖≤∫ t, ‖K t‖*‖f (z.1,z.2-t)‖ := by
    exact norm_integral_le_of_norm_le hi
      (Filter.Eventually.of_forall (fun t => le_of_eq (norm_mul _ _)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTimeAverageEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating a quadratic short-time error costs the first absolute
kernel moment. This avoids a factor from the number of time scales. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortTimeQuotient (F : ℝ×(ℝ×ℝ) → ℂ) (p : ℝ×(ℝ×ℝ)) : ℂ :=
  if |p.1|≤1/4 then (p.1⁻¹ : ℂ)*F p else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SeparatedSymbolOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini separates the normalized symbol inside the actual planar
frequency integral. The direction parameter is frozen only at its output. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def modulatedFrequency (F : ℝ×ℝ → ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) (omega : ℝ×ℝ) : ℂ :=
  frequencyCharacter nu (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*F omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShearedLatticePeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact periodization over the translated sheared box lattice used
in the continuous packet representation. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace LipschitzHilbert.PacketRepresentation

def latticeHom (l W theta : ℝ) : (ℤ × ℤ) →+ (ℝ × ℝ) where
  toFun n := ((n.1:ℝ)*l, theta*(n.1:ℝ)*l+(n.2:ℝ)*W)
  map_zero' := by simp
  map_add' n m := by ext <;> simp <;> ring

def latticeCell (l W theta : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc 0 l ∧ x.2-theta*x.1 ∈ Ioc 0 W}

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FactoredMultiplierPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factored frequency multiplier is exactly the normalized average
of its actual analyzing and synthesizing convolution packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert

def lowerHilbertPlanarSchwartz (F : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm F

theorem hilbertPlanar_lower (F : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
    hilbertPlanarSchwartz (lowerHilbertPlanarSchwartz F)=F := by
  ext x
  rfl

def planarSchwartzConvolution (K f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  lowerHilbertPlanarSchwartz (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (hilbertPlanarSchwartz f) (hilbertPlanarSchwartz K))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarFrequencyPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def planarInverseSchwartz (F : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  lowerHilbertPlanarSchwartz (𝓕⁻ (hilbertPlanarSchwartz F))

def modulatedFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ) (a b c : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun omega : ℝ×ℝ =>
    (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)) F

def horizontalFrequencyKernel (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l theta : ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz ((symbolWeight q nu:ℂ) •
    modulatedFrequencyWindow A (nu 0*l) (nu 0*l*theta) 0)

def verticalFrequencyKernel (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (W center : ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz ((symbolWeight q nu:ℂ) •
    modulatedFrequencyWindow B 0 (nu 1*W) (-(nu 1*W*center)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzVerticalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfile_temperate (q : SchwartzMap ℝ ℂ) (W center : ℝ) :
    Function.HasTemperateGrowth (fun omega : ℝ×ℝ => q (W*(omega.2-center))) := by
  have hs : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact q.hasTemperateGrowth.comp (by fun_prop)

def schwartzVerticalProjection (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz (SchwartzMap.smulLeftCLM ℂ
    (fun omega : ℝ×ℝ => q (W*(omega.2-center))) (planarFourierSchwartz f))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSecantEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical fundamental theorem of calculus in the quadratic form
used to compare the two orders of convolution and sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSchwartzDeriv (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  (SchwartzMap.evalCLM ℝ (ℝ×ℝ) ℂ (0,1)) (SchwartzMap.fderivCLM ℝ (ℝ×ℝ) ℂ f)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short sampling maps and the interpolation between the two orders of
vertical convolution and directional sampling. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSampling (u : (ℝ×ℝ) → ℝ) (t a b : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1-a,z.2-b-t*u z)

theorem verticalSampling_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (t a b : ℝ) :
    Measurable (verticalSampling u t a b) := by
  unfold verticalSampling
  fun_prop

theorem verticalSampling_antilipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t a b : ℝ) (ht : |t|≤1/4) : AntilipschitzWith 2 (verticalSampling u t a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have hu' := hu.dist_le_mul z w
  rw [Real.dist_eq] at hu'
  have hx : |z.1-w.1|≤dist (verticalSampling u t a b z) (verticalSampling u t a b w) := by
    have h := le_max_left |z.1-w.1| |(z.2-b-t*u z)-(w.2-b-t*u w)|
    simpa only [verticalSampling,Prod.dist_eq,Real.dist_eq,sub_sub_sub_cancel_right] using h
  have hy : |z.2-w.2|≤dist (verticalSampling u t a b z) (verticalSampling u t a b w)+
      |t| *(2*dist z w) := by
    have hid : z.2-w.2=((z.2-b-t*u z)-(w.2-b-t*u w))+t*(u z-u w) := by ring
    calc
      _ = |((z.2-b-t*u z)-(w.2-b-t*u w))+t*(u z-u w)| := congrArg abs hid
      _ ≤ |(z.2-b-t*u z)-(w.2-b-t*u w)| +|t| *|u z-u w| := by
        simpa only [abs_mul] using abs_add_le ((z.2-b-t*u z)-(w.2-b-t*u w)) (t*(u z-u w))
      _ ≤ dist (verticalSampling u t a b z) (verticalSampling u t a b w)+|t| *(2*dist z w) := by
        apply add_le_add
        · exact le_max_right _ _
        · exact mul_le_mul_of_nonneg_left hu' (abs_nonneg t)
  have hd : dist z w≤dist (verticalSampling u t a b z) (verticalSampling u t a b w)+
      |t| *(2*dist z w) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact max_le (hx.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg t)
      (mul_nonneg (by norm_num) (dist_nonneg (x:=z) (y:=w)))))) hy
  change dist z w≤2*dist (verticalSampling u t a b z) (verticalSampling u t a b w)
  nlinarith [dist_nonneg (x:=z) (y:=w)]

def verticalBlend (u : (ℝ×ℝ) → ℝ) (s theta : ℝ) (z : ℝ×ℝ) : ℝ :=
  (1-theta)*u z+theta*u (verticalTranslation s z)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise quadratic comparison of the two sampling orders. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalSamplingDifference (f : SchwartzMap (ℝ×ℝ) ℂ) (u : (ℝ×ℝ) → ℝ)
    (t s : ℝ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-s-t*u (verticalTranslation s z))-
    f (z.1-t,z.2-s-t*u z)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bin/sampling commutator is the integral of the actual sampling-order difference. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def sampledFunction (u : (ℝ×ℝ) → ℝ) (t : ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-t*u z)

def verticalSamplingCommutator (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (t : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  verticalConvolution K (sampledFunction u t f) z-
    sampledFunction u t (verticalConvolution K f) z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bin commutator on a vertical frequency band. Its constant
depends only on the fixed profile; its scale dependence is `t² (W R)²`. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalProfileCommutatorConstant (q : SchwartzMap ℝ ℂ) : ℝ :=
  16*(2*Real.pi)^2*(∫ s, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖)*
    (∫ s, s^2*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteBinCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated bin commutator for the actual finite dyadic time kernel.
The bound is uniform in the number of scales and in the bin carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def finiteBinError (k q : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
    verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-time frozen-direction operator and the exact reason it may
replace the full kernel in a pairing on a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortSlopeOperator (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then K t*f (z.1-t,z.2-t*u z) else 0

theorem shortSlopeOperator_measurable (K : ℝ → ℂ) (hKm : Measurable K)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) :
    Measurable (shortSlopeOperator K u f) := by
  have hs : MeasurableSet {p : (ℝ×ℝ)×ℝ | |p.2|≤1/4} := by
    have hc : Continuous (fun p : (ℝ×ℝ)×ℝ => |p.2|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      K p.2*f (p.1.1-p.2,p.1.2-p.2*u p.1)) := by fun_prop
  exact (hm.ite hs measurable_const).stronglyMeasurable.integral_prod_right'.measurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the estimated time average with the actual commutator of
the vertical bin and the horizontally localized operator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortTimeKernel (K : ℝ → ℂ) (t : ℝ) : ℂ := if |t|≤1/4 then K t else 0

theorem shortTimeKernel_integrable (K : ℝ → ℂ) (hK : Integrable K) :
    Integrable (shortTimeKernel K) := by
  have hc : Continuous (fun t : ℝ => |t|) := by fun_prop
  exact hK.indicator (isClosed_le hc continuous_const).measurableSet

theorem shortSlopeOperator_eq_kernel (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) :
    shortSlopeOperator K u f=slopeKernelOperator (shortTimeKernel K) u f := by
  funext z
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [shortTimeKernel]
  split_ifs <;> simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def timeErrorEnvelope (r t : ℝ) : ℝ := r/(r^2+t^2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicKernelTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact telescoping identity behind the finite Hilbert time-kernel
decomposition. The cutoff profile will be constructed independently. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def profileKernelDifference (a : ℝ → ℂ) (r R t : ℝ) : ℂ :=
  (a (t/r)-a (t/R))/(t : ℂ)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductSlopePrincipalValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise principal values for smooth functions in the product-plane
coordinates used by the actual band operators. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def productSlopeSample (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) : ℝ×ℝ :=
  (z.1-t,z.2-t*u z)

def productSymmetricTruncation (u : (ℝ×ℝ) → ℝ) (epsilon R : ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t in epsilon..R, t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))

def productSlopePrincipalValue (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  let g := fun t : ℝ => f (productSlopeSample u t z)-f (productSlopeSample u (-t) z)
  ∫ t in (0:ℝ)..R, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

theorem productSymmetricTruncation_tendsto (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (z : ℝ×ℝ) :
    Tendsto (fun epsilon : ℝ => productSymmetricTruncation u epsilon R f z)
      (𝓝[>] 0) (𝓝 (productSlopePrincipalValue u R f z)) := by
  let g := fun t : ℝ => f (productSlopeSample u t z)-f (productSlopeSample u (-t) z)
  have hg : Differentiable ℝ g := by
    dsimp only [g,productSlopeSample]
    fun_prop
  have hg0 : g 0=0 := by simp [g,productSlopeSample]
  let reg := Function.update (fun t : ℝ => t⁻¹ • g t) 0 (deriv g 0)
  have hreg : Continuous reg := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t=0
    · subst t
      apply continuousAt_update_same.mpr
      simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
    · apply (continuousAt_update_of_ne ht).mpr
      exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt
  have hcont : Continuous (fun epsilon : ℝ => ∫ t in epsilon..R, reg t) := by
    have hc := (intervalIntegral.continuous_primitive (μ:=volume)
      (fun l r => hreg.intervalIntegrable l r) R).neg
    have heq : (fun epsilon : ℝ => ∫ t in epsilon..R, reg t)=
        (fun epsilon : ℝ => -(∫ t in R..epsilon, reg t)) := by
      funext epsilon
      exact intervalIntegral.integral_symm R epsilon
    rw [heq]
    exact hc
  have heq : (fun epsilon : ℝ => productSymmetricTruncation u epsilon R f z)=ᶠ[𝓝[>] 0]
      (fun epsilon => ∫ t in epsilon..R, reg t) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds]
      with epsilon he heR
    change 0<epsilon at he
    unfold productSymmetricTruncation
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le heR.le] at ht
    have ht0 : t≠0 := (he.trans_le ht.1).ne'
    exact (Function.update_of_ne ht0 (deriv g 0) (fun t : ℝ => t⁻¹ • g t)).symm
  exact (hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds).congr' heq.symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FrozenDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frozen-direction sampling

The sampling maps and positive-time representation of the short Hilbert transform
in §1 of *A uniform Hilbert transform estimate for Lipschitz directions*.
The direction in these definitions is evaluated at the output point.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace LipschitzHilbert

/-- The usual reciprocal-Lipschitz normalization of a vector field. -/
def rescaleField (L : ℝ) (v : DirectionPlane → DirectionPlane) :
    DirectionPlane → DirectionPlane := fun x => v (L⁻¹ • x)

def rescaleFunction (L : ℝ) (f : DirectionPlane → ℂ) :
    DirectionPlane → ℂ := fun x => f (L⁻¹ • x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_UnitDirectionCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite collection of orthogonal charts for a unit direction field.
The clipped slope is defined on the whole plane. On its orientation patch
it agrees exactly with the ratio of the two coordinates. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

def horizontalUnit : Plane := EuclideanSpace.single 0 1

def directionChart (d : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  (ℝ ∙ (d-horizontalUnit))ᗮ.reflection

def chartField (d : Plane) (v : Plane → Plane) : Plane → Plane :=
  fun x => directionChart d (v ((directionChart d).symm x))

def chartDenominator (v : Plane → Plane) (x : Plane) : ℝ := max (1/2) (v x 0)

def rawChartSlope (v : Plane → Plane) (x : Plane) : ℝ :=
  v x 1 / chartDenominator v x

def clippedChartSlope (v : Plane → Plane) (x : Plane) : ℝ :=
  max (-(1/4)) (min (1/4) (rawChartSlope v x))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DirectionChartSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact changes of coordinates and time in the directional integral. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def planeCoordinatesLinear : (ℝ×ℝ) ≃ₗ[ℝ] Plane where
  toEquiv := planeCoordinates.toEquiv
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl

def planeCoordinatesContinuous : (ℝ×ℝ) ≃L[ℝ] Plane :=
  planeCoordinatesLinear.toContinuousLinearEquiv

@[simp] theorem planeCoordinatesContinuous_apply (z : ℝ×ℝ) :
    planeCoordinatesContinuous z=planeCoordinates z := rfl

@[simp] theorem planeCoordinatesContinuous_symm_apply (z : Plane) :
    planeCoordinatesContinuous.symm z=planeCoordinates.symm z := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ChartPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal chart and product coordinates preserve the input L2
norm. The slope and endpoint factors satisfy global quantitative bounds. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

def chartCoordinateMap (d : Plane) : (ℝ×ℝ) ≃L[ℝ] Plane :=
  planeCoordinatesContinuous.trans (directionChart d).symm.toContinuousLinearEquiv

def chartSchwartz (d : Plane) (f : SchwartzMap Plane ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (chartCoordinateMap d) f

@[simp] theorem chartSchwartz_apply (d : Plane) (f : SchwartzMap Plane ℂ) (z : ℝ×ℝ) :
    chartSchwartz d f z=f ((directionChart d).symm (planeCoordinates z)) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelDifferencePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel L1 error controls the actual localized bilinear form by the
smaller of the input and test masses. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slope_integrand_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Integrable (fun t => K t*f (z.1-t,z.2-t*u z)) := by
  apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
  · exact hK.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollificationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed shrinking positive mollifier family. Its a.e. convergence
comes from the existing Lebesgue differentiation theorem. -/
noncomputable section
open MeasureTheory Filter Function
open scoped Convolution Topology Pointwise
namespace LipschitzHilbert.PacketRepresentation

def testMollifier (n : ℕ) : ContDiffBump (0 : ℝ×ℝ) where
  rIn := (1/((n:ℝ)+1))/2
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0<1/((n:ℝ)+1) := by positivity
    linarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed normalization of the original vertical cutoff controls its
L1, L2 and uniform sizes without changing its frequency band or strip. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalProjectionCost (p : SchwartzMap ℝ ℂ) : ℝ :=
  1+∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖

def normalizedBandProjection (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  ((verticalProjectionCost p)⁻¹ : ℂ) • schwartzVerticalProjection p w 0 f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex conjugation reflects the Fourier support of an actual
Schwartz function, and preserves its L2 norm and pointwise size. -/
noncomputable section
open MeasureTheory Function
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def schwartzConj (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] theorem schwartzConj_apply (f : SchwartzMap E ℂ) (x : E) : schwartzConj f x=conj (f x) := rfl

@[simp] theorem schwartzConj_involutive (f : SchwartzMap E ℂ) : schwartzConj (schwartzConj f)=f := by
  ext x
  simp only [schwartzConj_apply,starRingEnd_apply,star_star]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReflectedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Negative vertical bands are conjugates of positive vertical bands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def conjugateReflectedCutoff (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  schwartzConj (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) p)

@[simp] theorem conjugateReflectedCutoff_apply (p : SchwartzMap ℝ ℂ) (s : ℝ) :
    conjugateReflectedCutoff p s=conj (p (-s)) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularCutoffConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit real annular cutoffs and the low-pass difference underlying
the geometric frequency partition. All supports stay inside fixed bands. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyLowBump : ContDiffBump (0:ℝ) where
  rIn := 1
  rOut := 13/12
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def reassemblyLow : SchwartzMap ℝ ℂ :=
  (reassemblyLowBump.hasCompactSupport.toSchwartzMap reassemblyLowBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem reassemblyLow_apply (s : ℝ) : reassemblyLow s=(reassemblyLowBump s : ℂ) := rfl

def reassemblyOuterBump : ContDiffBump (3/2:ℝ) where
  rIn := 3/8
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def reassemblyOuter : SchwartzMap ℝ ℂ :=
  (reassemblyOuterBump.hasCompactSupport.toSchwartzMap reassemblyOuterBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem reassemblyOuter_apply (s : ℝ) : reassemblyOuter s=(reassemblyOuterBump s : ℂ) := rfl

def reassemblyDifference (s : ℝ) : ℂ := reassemblyLow ((16/27)*s)-reassemblyLow ((8/9)*s)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPositiveCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive half of the geometric low-pass difference is Schwartz
and is exactly covered by a fixed admissible enlarged cutoff. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyDifferenceSchwartz : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (16/27) (by norm_num)-
    dilatedSlopeWindow reassemblyLow (8/9) (by norm_num)

@[simp] theorem reassemblyDifferenceSchwartz_apply (s : ℝ) :
    reassemblyDifferenceSchwartz s=reassemblyDifference s := rfl

def reassemblyPositive : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ reassemblyOuter reassemblyDifferenceSchwartz

@[simp] theorem reassemblyPositive_apply (s : ℝ) :
    reassemblyPositive s=reassemblyOuter s*reassemblyDifference s := by
  rw [reassemblyPositive,SchwartzMap.smulLeftCLM_apply_apply reassemblyOuter.hasTemperateGrowth,
    reassemblyDifferenceSchwartz_apply,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine binary low-pass difference for the dyadic commutator
proof, with its scale-independent Fourier square bound. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def dyadicDifference : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (1/2) (by norm_num)-reassemblyLow

@[simp] theorem dyadicDifference_apply (x : ℝ) :
    dyadicDifference x=reassemblyLow (x/2)-reassemblyLow x := by
  simp only [dyadicDifference,sub_apply,dilatedSlopeWindow_apply]
  congr 2
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-dimensional convolution energy bound for measurable L2 functions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineConvolution (K f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, K t*f (x-t)

theorem lineTranslation_measurePreserving (t : ℝ) :
    MeasurePreserving (fun x : ℝ => x-t) volume volume :=
  measurePreserving_sub_right volume t

theorem lineConvolution_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (f : ℝ → ℂ) (hf : Measurable f) : Measurable (lineConvolution K f) := by
  have hm : Measurable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    (hK.comp measurable_snd).mul (hf.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable


theorem lineConvolution_energy_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^2)
      (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^2) := by
    exact (hKm.comp measurable_fst).norm.mul ((hfm.comp (by fun_prop)).norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 2≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^2‖ ∂volume)=
        ‖K t‖*(∫ z, ‖f z‖^2 ∂volume) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^2) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_pointwise_energy (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f) (z : ℝ)
    (he : Integrable (fun t => ‖K t‖*‖f (z-t)‖^2)) :
    ‖lineConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) := by
  obtain ⟨hi,hsq⟩ := weighted_integral_cauchySchwarz volume
    (fun t => ‖K t‖) (fun t => ‖f (z-t)‖)
    hKm.norm (hfm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm he
  have hn : ‖lineConvolution K f z‖≤∫ t, ‖K t‖*‖f (z-t)‖ := by
    exact norm_integral_le_of_norm_le hi
      (Filter.Eventually.of_forall (fun t => le_of_eq (norm_mul _ _)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

theorem lineConvolution_energy_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    MemLp (lineConvolution K f) 2 volume ∧
      (∫ z, ‖lineConvolution K f z‖^2 ∂volume)≤
        (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂volume) := by
  have hi := lineConvolution_energy_joint_integrable K hK hKm f hfm hf
  have hm := lineConvolution_measurable K hKm f hfm
  have hp : ∀ᵐ z ∂volume, ‖lineConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) := by
    filter_upwards [hi.prod_left_ae] with z hz
    exact lineConvolution_pointwise_energy K hK hKm f hfm z hz
  have hdom : Integrable (fun z => (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2))
      volume := hi.integral_prod_right.const_mul _
  have he : Integrable (fun z => ‖lineConvolution K f z‖^2) volume := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) ∂volume :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂volume) := by
      rw [integral_const_mul]
      have hs := integral_integral_swap
        (f:=fun (z : ℝ) (t : ℝ) => ‖K t‖*‖f (z-t)‖^2) hi.swap
      rw [hs]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^2) _]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineFrequencyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth frequency projections on the line and their finite
square-function bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzProjection (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow q W hW) (𝓕 f))

def lineSchwartzProjectionLM (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap.comp
    ((SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow q W hW)).toLinearMap.comp
      (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap)

def lineProjectionToL2 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp (lineSchwartzProjectionLM q W hW)

def lineL2Projection (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineProjectionToL2 q W hW).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line Fourier projection is the actual convolution with its
inverse-Fourier kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineProjectionKernel (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (dilatedSlopeWindow q W hW)

theorem lineConvolution_integrand_of_bounded (K f : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (x : ℝ) :
    Integrable (fun t => K t*f (x-t)) := by
  apply (hK.norm.mul_const B).mono'
    (hK.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖K t*f (x-t)‖≤‖K t‖*B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual line projection kernel has the expected physical scale,
including its exact first absolute moment. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def scaledSchwartzKernel (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) : SchwartzMap ℝ ℂ :=
  (W:ℂ)⁻¹ • dilatedSlopeWindow (𝓕⁻ q) W⁻¹ (inv_ne_zero hW.ne')

theorem scaledSchwartzKernel_apply (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (x : ℝ) :
    scaledSchwartzKernel q W hW x=scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W x := by
  simp only [scaledSchwartzKernel,smul_apply,smul_eq_mul,dilatedSlopeWindow_apply,scaledTimeKernel]
  congr 2
  ring

theorem lineProjectionKernel_eq_scaled (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    lineProjectionKernel q W hW.ne'=scaledSchwartzKernel q W hW := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineProjectionKernel q W hW.ne')) eta=(𝓕 (scaledSchwartzKernel q W hW)) eta
  simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply]
  have he : (scaledSchwartzKernel q W hW : ℝ → ℂ)=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W := funext (scaledSchwartzKernel_apply q W hW)
  rw [SchwartzMap.fourier_coe,he,scaledTimeKernel_fourier _ W hW]
  have hq : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q :=
    FourierTransform.fourier_fourierInv_eq q
  exact (congrArg (fun p : SchwartzMap ℝ ℂ => p (W*eta)) hq).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularResolutionSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete symmetric finite annular partition converges to one away
from the zero vertical frequency. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def reassemblyScale (N n : ℕ) : ℝ := (2/3:ℝ)^N*(3/2:ℝ)^n

theorem reassemblyScale_pos (N n : ℕ) : 0 < reassemblyScale N n := by
  unfold reassemblyScale
  positivity

def reassemblySymbol (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n∈Finset.range (2*N+1), reassemblyDifference (reassemblyScale N n*s)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortL2Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preliminary L2 realization of the short-time operator. Its
logarithmic kernel norm is used only for continuity and density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_schwartz_add (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (f+g : SchwartzMap (ℝ×ℝ) ℂ) z=
      shortSlopeOperator K u f z+shortSlopeOperator K u g z := by
  simp only [shortSlopeOperator_eq_kernel,slopeKernelOperator,add_apply,mul_add]
  exact integral_add (slope_integrand_integrable _ (shortTimeKernel_integrable K hK) u f z)
    (slope_integrand_integrable _ (shortTimeKernel_integrable K hK) u g z)

theorem shortSlopeOperator_schwartz_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=c*shortSlopeOperator K u f z := by
  simp only [shortSlopeOperator_eq_kernel,slopeKernelOperator,smul_apply,smul_eq_mul]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation is an isometric real-linear involution of complex L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

def l2Conj (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 mu

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_L2Indicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable cutoffs as contractions on the actual complex L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

def l2IndicatorLM (mu : Measure X) (S : Set X) (hS : MeasurableSet S) :
    Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun f := ((Lp.memLp f).indicator hS).toLp (S.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (f+g)).indicator hS).coeFn_toLp,
      ((Lp.memLp f).indicator hS).coeFn_toLp,
      ((Lp.memLp g).indicator hS).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add (((Lp.memLp f).indicator hS).toLp _) (((Lp.memLp g).indicator hS).toLp _)]
      with z hz hf hg hadd hout
    rw [hz,hout]
    simp only [Pi.add_apply,hf,hg]
    by_cases h : z∈S
    · simp only [Set.indicator_of_mem h,hadd,Pi.add_apply]
    · simp only [Set.indicator_of_notMem h,add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • f)).indicator hS).coeFn_toLp,
      ((Lp.memLp f).indicator hS).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (((Lp.memLp f).indicator hS).toLp _)] with z hz hf hc hout
    simp only [RingHom.id_apply]
    rw [hz,hout]
    simp only [Pi.smul_apply,hf]
    by_cases h : z∈S
    · simp only [Set.indicator_of_mem h,hc,Pi.smul_apply]
    · simp only [Set.indicator_of_notMem h,smul_zero]

theorem l2IndicatorLM_norm (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : ‖l2IndicatorLM mu S hS f‖≤‖f‖ := by
  change ‖((Lp.memLp f).indicator hS).toLp (S.indicator f)‖≤‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_indicator_le f)

def l2Indicator (mu : Measure X) (S : Set X) (hS : MeasurableSet S) :
    Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (l2IndicatorLM mu S hS).mkContinuous 1 (fun f => by simpa only [one_mul] using l2IndicatorLM_norm mu S hS f)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComplexVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realification preserves the cubic variation and the terminal L² norm
of the complex Hilbert-valued packet sums. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

def complexRealify {κ : Type*} [Fintype κ] (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℝ (κ × Fin 2) :=
  WithLp.toLp 2 (fun i => if i.2 = 0 then (v i.1).re else (v i.1).im)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NestedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Products of nested conditional-average factors

Finite measurable partitions model the nested mesh inside one fixed root cell.
Each factor is constant on the next partition and has average at most one on
every current cell. The product estimate below is an actual integral estimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- The accumulated factor viewed as a function on its current partition. -/
def nestedProductProfile (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) : ℕ → κ → ℝ
  | 0, _ => 1
  | n + 1, i => nestedProductProfile R g n (R n i) * g n i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAverageComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual annular packet errors without a scale-count loss. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

def fullBandSum {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) : ℂ := ∑ j, f j x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScalarLineVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex form of the actual-grid variation comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

def scalarVector (z : ℂ) : EuclideanSpace ℂ Unit := WithLp.toLp 2 (fun _ => z)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted Cauchy–Schwarz step in the local coefficient estimate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

def referenceWeight (a b r W : ℝ) (z : ℝ × ℝ) : ℝ :=
  polynomialWeight a r 1 z.2 * polynomialWeight b W 1 z.1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ParityPartialSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact even/odd decomposition of the dyadic partial sums. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def paddedPacket {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (j : ℕ) : SchwartzMap ℝ ℂ :=
  if h : j < N then f ⟨j,h⟩ else 0

def parityPacket {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) (j : Fin N) : SchwartzMap ℝ ℂ :=
  paddedPacket f (2 * j.val + r)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square comparison for arbitrary fixed positive annular endpoints. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

def annularErrorConstant (a b : ℝ) : ℝ := 4 + 2 * Real.pi * b + 4 * (2 * Real.pi * a)⁻¹

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

def diagonalSynthesis (wave : σ → κ → Ω → ℂ)
    (c : σ → EuclideanSpace ℂ κ) (z : Ω) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ i, c i k * wave i k z)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual center-box assignment on a reference line and exact grouping
of the finite Schwartz synthesis. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem floor_box_distance (u r x : ℝ) (hr : 0 < r) :
    |x - (u + r * (⌊(x - u) / r⌋ : ℤ))| ≤ r := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le ((x - u) / r)) hr.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - u) / r)) hr
  rw [div_mul_cancel₀ _ hr.ne'] at hlo hhi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def packetBoxSynthesis {ι : Type*} [Fintype ι] (index : ι → ℤ × ℤ)
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) : SchwartzMap ℝ ℂ :=
  ∑ i, if index i = b then c i • f i else 0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ShortPacketBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite decomposition of the short-scale synthesis into its actual
center boxes. Empty fibers are retained and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def allPacketBoxes {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (index : ∀ j, ι j → ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.univ.image (fun p : Sigma ι => index p.1 p.2)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The packet spectrum and selector separation in the manuscript,
§2, equations `red:packet-spectra` and `red:selector-assumptions`, give
the actual reference-line annuli used in §5, `conc:main-annuli`.

The only spectral premise is the original planar packet's tilted
wedge and positive vertical band. The same premise suffices for the
first two scaled covariant derivatives. Angular frequencies and
mathlib's cycles-per-unit convention are related explicitly. -/

noncomputable section

open scoped FourierTransform

namespace LipschitzHilbert

theorem source_frequency_annulus
    {ω η s θ ell w cStar cEta CEta cb Cb : ℝ}
    (hell : 0 < ell) (hw : 0 < w) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hwedge : |ω - (s - θ) * η| ≤ cStar / ell)
    (hband : cEta ≤ w * η ∧ w * η ≤ CEta)
    (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell) :
    (cEta * cb - cStar) / ell ≤ |ω| ∧
      |ω| ≤ (CEta * Cb + cStar) / ell := by
  have hη : 0 ≤ η :=
    ((mul_pos_iff_of_pos_left hw).mp (lt_of_lt_of_le hcEta hband.1)).le
  have hlo : cEta * cb ≤ |(s - θ) * η| * ell := by
    rw [abs_mul, abs_of_nonneg hη]
    calc
      cEta * cb = cb * cEta := mul_comm _ _
      _ ≤ cb * (w * η) := mul_le_mul_of_nonneg_left hband.1 hcb
      _ = (cb * w) * η := by ring
      _ ≤ (|s - θ| * ell) * η :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hell).mp hselector.1) hη
      _ = (|s - θ| * η) * ell := by ring
  have hhi : |(s - θ) * η| * ell ≤ CEta * Cb := by
    rw [abs_mul, abs_of_nonneg hη]
    calc
      (|s - θ| * η) * ell = (|s - θ| * ell) * η := by ring
      _ ≤ (Cb * w) * η :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ hell).mp hselector.2) hη
      _ = Cb * (w * η) := by ring
      _ ≤ Cb * CEta := mul_le_mul_of_nonneg_left hband.2 hCb
      _ = CEta * Cb := mul_comm _ _
  have hwedge' : |ω - (s - θ) * η| * ell ≤ cStar :=
    (le_div_iff₀ hell).mp hwedge
  have hlower := abs_sub_abs_le_abs_sub ((s - θ) * η) ω
  rw [abs_sub_comm] at hlower
  have hupper := abs_sub_abs_le_abs_sub ω ((s - θ) * η)
  have hlower' := mul_le_mul_of_nonneg_right hlower hell.le
  have hupper' := mul_le_mul_of_nonneg_right hupper hell.le
  constructor
  · apply (div_le_iff₀ hell).mpr
    nlinarith
  · apply (le_div_iff₀ hell).mpr
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PhysicalPacketSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original physical packet spectrum supplies Fourier cutoffs for
the actual three raw kernels on every affine reference line. The exact
dyadic endpoint identity puts these cutoffs in the form required by
the scaled annular-variation estimate. -/

noncomputable section

open scoped FourierTransform

namespace LipschitzHilbert

/-- Exact rescaling of either annulus endpoint for a dyadic physical
length. The same reference length `R` works for every index. -/
theorem packet_annulus_dyadic_scale (numerator R : ℝ) (j : ℕ) (hR : R ≠ 0) :
    numerator / (2 * Real.pi * (R / (2 : ℝ) ^ j)) =
      (numerator / (2 * Real.pi * R)) * (2 : ℝ) ^ j := by
  have hj : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  field_simp [Real.pi_ne_zero, hR, hj]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SignedAnnularSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All signed finite annular multipliers have the same Mihlin bounds.
The proof uses only the fixed support annulus and its finite overlap. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def signedAnnularSymbol (N : ℕ) (s : ℕ → Bool) : SchwartzMap ℝ ℂ :=
  ∑ n∈Finset.range (2*N+1),
    if s n then dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
    else -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'

def signedAnnularMihlinConstant : ℝ :=
  ∑ r∈Finset.range 5,
    3*(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierKernelFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative first absolute moment from the zeroth and third
L1 derivatives of a Schwartz multiplier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def schwartzDerivative : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, q => q
  | r+1, q => SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalizedMihlinProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform derivative bounds for a rescaled multiplier after restriction
to a fixed annulus. These are the bounds needed for its kernel moment. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def localizedMihlinProfile (m rho : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow m W hW) rho

@[simp] theorem localizedMihlinProfile_apply (m rho : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (x : ℝ) :
    localizedMihlinProfile m rho W hW x=m (W*x)*rho x := by
  rw [localizedMihlinProfile,SchwartzMap.smulLeftCLM_apply_apply
    (dilatedSlopeWindow m W hW).hasTemperateGrowth,dilatedSlopeWindow_apply,smul_eq_mul]

def annularDerivativeBudget (rho : SchwartzMap ℝ ℂ) (r : ℕ) : ℝ :=
  ∑ j∈Finset.range (r+1), (r.choose j:ℝ)*2^j*SchwartzMap.seminorm ℝ 0 (r-j) rho

def localizedKernelFirstMomentConstant (rho : SchwartzMap ℝ ℂ) : ℝ :=
  8*Real.pi*(annularDerivativeBudget rho 0+
    annularDerivativeBudget rho 3/(2*Real.pi)^3)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L2 kernel commutator estimate for multiplication by a bounded
Lipschitz function. The cost is its Lipschitz bound times the first moment. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineMultiplicationCommutator (K b h : ℝ → ℂ) (x : ℝ) : ℂ :=
  b x*lineConvolution K h x-lineConvolution K (fun y => b y*h y) x

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicCommutatorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed enlarged annulus for the low/high part of the commutator.
Its support fits the already proved localized Mihlin kernel estimates. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def dyadicCommutatorCutoff : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (2/3) (by norm_num)-
    dilatedSlopeWindow reassemblyLow 2 (by norm_num)

@[simp] theorem dyadicCommutatorCutoff_apply (x : ℝ) :
    dyadicCommutatorCutoff x=reassemblyLow ((2/3)*x)-reassemblyLow (2*x) := by
  simp only [dyadicCommutatorCutoff,sub_apply,dilatedSlopeWindow_apply]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProductSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier spectrum of an actual Schwartz product, including the
ball and annulus bounds needed in the dyadic commutator decomposition. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzProduct (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem lineSchwartzProduct_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProduct f g x=f x*g x := by
  simp only [lineSchwartzProduct,SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply']

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLocalizedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localized line multipliers and the scale-cancelling first-moment
bound used in the low/high commutator estimate. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def localizedLineSymbol (m : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V) : SchwartzMap ℝ ℂ :=
  localizedMihlinProfile m dyadicCommutatorCutoff V⁻¹ (inv_ne_zero hV.ne')

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed zeroth and second decay bounds for the scaled line kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineKernelDecayConstant (q : SchwartzMap ℝ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (𝓕⁻ q)+SchwartzMap.seminorm ℝ 2 0 (𝓕⁻ q)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowHighCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low/high contribution of the multiplier commutator.
Both localization identities follow from the proved Fourier bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzCommutator (m b h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)-
    lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineGeometricSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual binary scale ratio is a summable row-and-column kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def lineScaleWeight (i j : ℤ) : ℝ := (1/2:ℝ)^(j-i).natAbs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicResolutionSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping and strong pointwise resolution for the binary
low-pass differences used in the commutator decomposition. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def dyadicResolutionScale (N n : ℕ) : ℝ := (1/2:ℝ)^N*(2:ℝ)^n

theorem dyadicResolutionScale_pos (N n : ℕ) : 0<dyadicResolutionScale N n := by
  unfold dyadicResolutionScale
  positivity

def dyadicResolutionSymbol (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.range (2*N+1), dyadicDifference (dyadicResolutionScale N n*x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 resolution by the genuine binary smooth differences. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def dyadicSchwartzSum (N : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ n∈Finset.range (2*N+1), lineSchwartzProjection dyadicDifference (dyadicResolutionScale N n)
    (dyadicResolutionScale_pos N n).ne' f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicReconstructionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic square bounds control the whole Schwartz function,
using the already proved strong binary resolution. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def dyadicResolutionWindow (N : ℕ) : Finset ℤ :=
  (Finset.range (2*N+1)).image (fun n : ℕ => (n:ℤ)-(N:ℤ))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicProjectionCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson condition for the actual binary line projections,
first on intervals and then on the nested dyadic line cells. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def dyadicCarlesonConstant : ℝ :=
  72+4*(∫ t : ℝ, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)^2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

def timeShiftFiltration (ℱ : Filtration ℕ m) (n : ℕ) : Filtration ℕ m where
  seq i := ℱ (n + i)
  mono' := fun _ _ hij => ℱ.mono (Nat.add_le_add_left hij n)
  le' i := ℱ.le (n + i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowpassCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform cellwise bounds for a smooth projection at any fixed ratio
between its physical scale and the cell length. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation

def lineCellMaximalConstant (q : SchwartzMap ℝ ℂ) (ratio : ℝ) : ℝ :=
  60*lineKernelDecayConstant q*(1+1/ratio)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Duality turns the proved smooth Carleson analysis bound into the
actual finite paraproduct synthesis bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def smoothCarlesonDualConstant : ℝ :=
  36*dyadicCarlesonConstant*(lineCellMaximalConstant reassemblyLow (1/128))^2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableCommutatorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full comparable-frequency contribution, with its two product
terms estimated by actual smooth Carleson synthesis. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def comparableCommutatorConstant : ℝ :=
  3*(48*(16384*((∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
    (52*Real.pi/3)))^2+2*smoothCarlesonDualConstant)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LaminarChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterated Carleson sums for a finite laminar family

The family is indexed by occurrences, so equal geometric intervals from
different bins retain their multiplicity. Iterating the actual Carleson
mass bound controls every non-strict nested-chain sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def tupleIntersection (Q : ι → Set X) {n : ℕ} (P : Set X) (a : Fin n → ι) : Set X :=
  P ∩ ⋂ j, Q (a j)

def laminarChainWeight (Q : ι → Set X) (μ : Measure X) :
    (n : ℕ) → Set X → (Fin n → ι) → ℝ
  | 0, P, _ => μ.real P
  | n + 1, P, a => if Q (a 0) ⊆ P then
      laminarChainWeight Q μ n (Q (a 0)) (fun j => a j.succ) else 0

def tupleHeadTailEquiv (n : ℕ) : (Fin (n + 1) → ι) ≃ ι × (Fin n → ι) where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by funext j; refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  right_inv p := by rcases p with ⟨i, a⟩; rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LaminarCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial moments of a finite laminar count

This proves equation `count:moment` of §6. The hypotheses are the actual
Carleson mass bound on the root and selected intervals and the geometric
ordering of intersecting intervals by their scale.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def laminarCount (Q : ι → Set X) (x : X) : ℝ := ∑ i, (Q i).indicator 1 x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountableCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable exhaustion of the Carleson tail

The count is an actual ENNReal sum over occurrences. Every finite subset
has the same exponential tail bound, so continuity from below gives that
bound for the full count without requiring a choice of enumeration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def finiteOccurrenceCount (Q : ι → Set X) (s : Finset ι) (x : X) : ℝ :=
  ∑ i ∈ s, (Q i).indicator (1 : X → ℝ) x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NarrowBandCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nonzero, real and even narrow cutoff for the
p=2 band-to-full reduction. Its positive part is in [1,101/100]. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def narrowBandBump : ContDiffBump (201/200:ℝ) where
  rIn := 1/1000
  rOut := 1/400
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def narrowBandPositive : SchwartzMap ℝ ℂ :=
  (narrowBandBump.hasCompactSupport.toSchwartzMap narrowBandBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem narrowBandPositive_apply (s : ℝ) : narrowBandPositive s=(narrowBandBump s:ℂ) := rfl

def narrowBandProfile : SchwartzMap ℝ ℂ :=
  narrowBandPositive+conjugateReflectedCutoff narrowBandPositive

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteNarrowPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smooth partition over any compact set avoiding zero. Every
piece is absorbed by a positive dilation of the fixed narrow cutoff. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

abbrev NarrowWindow := ℝ × SchwartzMap ℝ ℂ

def narrowPartition : List NarrowWindow → List NarrowWindow
  | [] => []
  | b::bs => b :: (narrowPartition bs).map (fun q =>
      (q.1,q.2-lineSchwartzProduct b.2 q.2))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-family analyzing coefficients are exactly the
original physical packet integrals. Swapping coordinates and applying
the reference slope shear preserves product Lebesgue measure, including
for the totalized Bochner integral without an integrability premise. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

/-- Reference coordinates are ordered `(transverse, horizontal)`. -/
def sourceReferenceToPhysical (t : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodComm.trans (slopeShear t)

@[simp] theorem sourceReferenceToPhysical_apply (t : ℝ) (z : ℝ × ℝ) :
    sourceReferenceToPhysical t z = (z.2, z.1 + t * z.2) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer horizontal moments through vertical averaging. In applications
the first measure is a fixed expanded vertical interval and the second is
the horizontal line interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

def verticalSquareEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V D : Ω → ℝ) : ℝ :=
  2 * ⨍ t, V t^2 + D t^2 ∂μ

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring arbitrary coefficients after a unit sequence-norm estimate. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

def normalizedCoefficient (a : ι → ℂ) (r : ℝ) (i : ι) : ℂ :=
  a i / (sequenceNorm a r : ℂ)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_InterpolationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Analytic families for the finite Fourier interpolation

The magnitude interpolation in §7 keeps each complex phase fixed. Zero
coefficients remain zero. The identities below give exact unit boundary
norms for the coefficient and simple-test-function families.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

def magnitudeFamily (w : ℂ) (A B : ℝ) (z : ℂ) : ℂ :=
  if w = 0 then 0 else
    (w / (‖w‖ : ℂ)) * (‖w‖ : ℂ) ^ ((1 - z) * (A : ℂ) + z * (B : ℂ))

@[simp] theorem magnitudeFamily_zero (A B : ℝ) (z : ℂ) : magnitudeFamily 0 A B z = 0 := by
  simp [magnitudeFamily]

variable {ι : Type*} [Fintype ι]

def coefficientFamily (a : ι → ℂ) (r p₀ p₁ : ℝ) (z : ℂ) (i : ι) : ℂ :=
  magnitudeFamily (a i) (r / p₀) (r / p₁) z

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite bilinear interpolation with constant one

This is the finite simple-function step of §7. The analytic family is
constructed explicitly, and Hadamard's theorem proves the interpolated
pairing estimate from its two endpoint estimates.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePairing (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, K i j * a i * b j

def pairingFamily (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) (z : ℂ) : ℂ :=
  finitePairing K (coefficientFamily a r 1 r₄ z) (coefficientFamily b s 1 (4 / 3) z)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SimpleFourierPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simple tests for Fourier interpolation on the actual averaging measure

A finite measurable profile partitions the real line into its fibers.
Its matrix entries are actual Fourier integrals over those fibers. The
two finite interpolation endpoints follow from positivity and the proved
improved fourth-moment theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def profileMatrix (ν : Measure ℝ) (frequency : ι → ℝ) (φ : ℝ → κ) (i : ι) (j : κ) : ℂ :=
  ∫ t in {u | φ u = j}, character (frequency i) t ∂ν

def fourierInterpolationExponent (D p : ℝ) : ℝ :=
  1 / (1 - (1 + phaseParameter D) / p)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging separated selections

Finite probability laws on retained subsets and the scalar weighted
phase bound from §9, using the retention cancellation of §8.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable (Ω ι : Type*) [Fintype Ω] [Fintype ι]

/-- Finite probability coordinates and their retained subsets. -/
structure FiniteSelectionLaw where
  weight : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1
  retained : Ω → Finset ι

variable {Ω ι}

namespace FiniteSelectionLaw

def marginal (L : FiniteSelectionLaw Ω ι) (i : ι) : ℝ :=
  ∑ ω, if i ∈ L.retained ω then L.weight ω else 0

def selectedCoefficient (L : FiniteSelectionLaw Ω ι) (a : ι → ℂ) (ω : Ω) (i : ι) : ℂ :=
  if i ∈ L.retained ω then a i / (L.marginal i : ℂ) else 0

end FiniteSelectionLaw

def phaseMu (D p : ℝ) : ℝ := (1 + phaseParameter D) / p

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalPhaseSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging diagonal Hilbert-valued phases

The weighted prediction bound of §9 for finite-dimensional Hilbert vectors and
coordinate-dependent frequencies. The retained-set estimate is the proved
constant-one diagonal Fourier gain; the marginal cancellation is exact.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

/-- Coordinatewise modulation by unit characters. -/
def diagonalModulation (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ) (t : ℝ) :
    EuclideanSpace ℂ κ := WithLp.toLp 2 (fun j => a j * character (frequency j) t)

omit [Fintype Ω] [Fintype ι] in
theorem norm_diagonalModulation (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ) (t : ℝ) :
    ‖diagonalModulation frequency a t‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, diagonalModulation,
    norm_mul, norm_character, mul_one]

/-- A diagonal phase sum, represented in the actual Euclidean Hilbert norm. -/
def diagonalFourierSum (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ)
    (t : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j => finiteFourierSum (fun i => frequency i j) (fun i => a i j) t)

namespace FiniteSelectionLaw

def selectedVector (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) : EuclideanSpace ℂ κ :=
  if i ∈ L.retained ω then (L.marginal i : ℂ)⁻¹ • a i else 0

end FiniteSelectionLaw

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DemodulatedVertical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the vertical carrier before applying the interval Sobolev
estimate. The derivative norm is exactly the covariant derivative norm,
independently of the carrier frequencies and Hilbert dimension. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
open PhaseCombinatorics

def demodulatedSignal {κ : Type*} (frequency : κ → ℝ) (f : κ → ℝ → ℂ)
    (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => f k y * character (-frequency k) y)

def covariantSignal {κ : Type*} (frequency : κ → ℝ) (f : κ → ℝ → ℂ)
    (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstExceed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint first-crossing events for a finite scalar process. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def firstExceed {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) : Set X :=
  {x | lambda < U n x ∧ ∀ i < n, U i x ≤ lambda}

def finiteMaxEvent {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) : Set X :=
  {x | ∃ i ≤ N, lambda < U i x}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGoodLambda
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-crossing contraction for a finite martingale with bounded
conditional mean oscillation. This is the finite stopping step in the
John--Nirenberg proof; no exponential-tail theorem is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

def TerminalMeanOscillationBound (F : ℕ → X → ℝ) (ℱ : Filtration ℕ m)
    (μ : Measure X) (N : ℕ) (A : ℝ) : Prop :=
  ∀ n ≤ N, ∀ s, MeasurableSet[ℱ n] s →
    (∫ x in s, |F N x - F n x| ∂μ) ≤ A * μ.real s

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeanOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local mean oscillation estimates used before John--Nirenberg.
The short part is controlled in mean and the long part by its oscillation.
All constants are independent of the dimension of the range. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def integralAverage (μ : Measure X) (f : X → E) : E :=
  (μ.real univ)⁻¹ • ∫ x, f x ∂μ

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopWeightedPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both factors of a fixed top polynomial can be absorbed into the
original packet orders, uniformly in the horizontal reference line. -/

noncomputable section
open scoped BigOperators
open FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

def topWeightedWave (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) : SchwartzMap ℝ ℂ :=
  polynomialLocalization a r q ((polynomialWeight b R q y : ℂ) • f)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopCovariantPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scaled covariant derivative of a top-weighted packet is another
Schwartz packet. Its extra scalar factor is bounded by 8q independently
of the top size and the vertical carrier frequency. -/

noncomputable section
open FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

def topCovariantFactor (b R y : ℝ) (q : ℕ) : ℝ :=
  4*R*deriv (polynomialWeight b R q) y/polynomialWeight b R q y

def topCovariantWave (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) :
    SchwartzMap ℝ ℂ :=
  (topCovariantFactor b R y q:ℂ) • topWeightedWave f a r b R y q +
    topWeightedWave df a r b R y q

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common packet constant for the weighted wave and its constructed
scaled covariant derivative. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

def topPairConstant (C : ℝ) (q : ℕ) : ℝ :=
  (8*(q:ℝ)+1)*(16^q*(1+2*(q:ℝ))*(16^q*C))

def topWeightedPair (f : Fin 2 → SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (i : Fin 2) : SchwartzMap ℝ ℂ :=
  if i=0 then topWeightedWave (f 0) a r b R y q
  else topCovariantWave (f 0) (f 1) a r b R y q

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

def lineMomentBase (C D branching : ℝ) : ℝ :=
  16 * (((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2)))/Real.log (3/2) +
    Real.sqrt D + 1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedMomentIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A spatially varying natural moment order turns uniform local
exponential tails into a summable global exceptional set. -/

noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

def weightedMomentIndex (n : ℕ) (w : ℝ) : ℕ := n + ⌈w⁻¹⌉₊

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product-measure dilation in the horizontal coordinate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def horizontalDilation (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (r*z.1,z.2)
  invFun z := (z.1/r,z.2)
  left_inv z := by ext <;> simp [hr]
  right_inv z := by
    ext
    · dsimp
      field_simp
    · rfl
  measurable_toFun := (measurable_const.mul measurable_fst).prodMk measurable_snd
  measurable_invFun := (measurable_fst.div_const r).prodMk measurable_snd

@[simp] theorem horizontalDilation_apply (r : ℝ) (hr : r ≠ 0) (z : ℝ × ℝ) :
    horizontalDilation r hr z = (r*z.1,z.2) := rfl

/-- The same horizontal scaling in the reference packet convention `(y,x)`. -/
def referenceHorizontalDilation (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1,r*z.2)
  invFun z := (z.1,z.2/r)
  left_inv z := by ext <;> simp [hr]
  right_inv z := by
    ext
    · rfl
    · dsimp
      field_simp
  measurable_toFun := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.div_const r)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopFamilyException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common moment order sums all actual top exceptional sets with
the total top area. This is independent of the number of tops. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

def topExceptionMoment (M J L : ℝ) : ℕ := ⌈(J*L+Real.log M)/Real.log 4⌉₊+1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeTopNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the global lattice neighborhood bound to physical slope
coordinates and the exact top weight, with an exponential area bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

def topAreaPrefactor (K : ℝ) : ℝ := 4*K^2*(4*Real.pi)^2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- All labels whose slope lies in the indicated reference window. -/
def window (labels : Finset ι) (slope : ι → ℝ) (t d radius : ℝ) : Finset ι := by
  classical
  exact labels.filter (fun i => |slope i - t| ≤ radius * d)

/-- Active labels for any number of components. The selector support
is common to the label, so the bound has no component-count factor. -/
def active (labels : Finset ι) {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    (t : ℝ) : Finset ι := by
  classical
  exact labels.filter (fun i => ∃ k, selector i k t ≠ 0)

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceShortTreeOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-tree summation uses actual distance to the Whitney strip,
actual sheared center lattices, and a finite dyadic length sum. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

def stripDistance (c r s : ℝ) : ℝ := max 0 (|s-c|-r/2)

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneySummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the local short-tree bounds over the Whitney partition:
total small-cell length and the large-cell geometric tail. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

def shortWhitneyWeight (L r : ℝ) : ℝ := if r≤L then r else L*(L/r)^2

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceKernelShells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic annuli for a reproducing-kernel bound by actual interval
averages. Closed outer intervals and open inner intervals retain every
boundary point. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def kernelShell (c r : ℝ) : ℕ → Set ℝ
  | 0 => Icc (c-r) (c+r)
  | n+1 => Icc (c-(2:ℝ)^(n+1)*r) (c+(2:ℝ)^(n+1)*r) \
      Ioo (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SchwartzPacketDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Obtain the finite packet decay orders directly from Schwartz
seminorms, including the first two vertical derivatives. -/

noncomputable section
namespace LipschitzHilbert

def schwartzEnvelopeConstant (f : SchwartzMap ℝ ℂ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (polynomialLocalization 0 1 n f)+1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate restrictions of Hilbert-valued planar Schwartz
packets, needed to reproduce non-tensor packet sums. -/
noncomputable section
open scoped NNReal
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem verticalLine_temperate (x : ℝ) :
    Function.HasTemperateGrowth (fun y : ℝ => (x,y)) := by
  let A : ℝ →L[ℝ] (ℝ×ℝ) := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have h := (Function.HasTemperateGrowth.const (E:=ℝ) (x,0)).add A.hasTemperateGrowth
  change Function.HasTemperateGrowth (fun y => (x,0)+A y) at h
  simpa only [A,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,Prod.mk_add_mk,add_zero,zero_add] using h

theorem verticalLine_antilipschitz (x : ℝ) :
    AntilipschitzWith 1 (fun y : ℝ => (x,y)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro y z
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq]
  exact le_max_right _ _

def vectorVerticalSlice (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (x : ℝ) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun y : ℝ => (x,y))
    (verticalLine_temperate x) (verticalLine_antilipschitz x) f

@[simp] theorem vectorVerticalSlice_apply
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x y : ℝ) :
    vectorVerticalSlice f x y=f (x,y) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoxReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reproduction on a physical rectangle. The two spectra are
properties of the actual coordinate restrictions, and all vector
members are controlled by one scalar maximal function. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def coordinateBox (cx cy rx ry : ℝ) : Set (ℝ×ℝ) :=
  {z | |z.1-cx| ≤ rx ∧ |z.2-cy| ≤ ry}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disjoint half-open partition underneath the manuscript's closed
transverse cells. Boundary points are retained exactly once. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceWhitney

def transverseCell (b W : ℝ) (n : ℤ) : Set ℝ :=
  Ico (b+(n:ℝ)*W-W/2) (b+(n:ℝ)*W+W/2)

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCoordinateSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Fourier support of actual planar packets. These lemmas
project the original two-dimensional spectrum without a tensor assumption. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

def planarSwap (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) f

@[simp] theorem planarSwap_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarSwap f z=f z.swap := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint interval selections, including selections depending on a point,
are controlled by one finite cubic variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def intervalPoint {S : ℕ} (a b : Fin S → ℕ) (N j : ℕ) : ℕ :=
  if h : j / 2 < S then if j % 2 = 0 then a ⟨j / 2, h⟩ else b ⟨j / 2, h⟩ else N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted separated synthesis on an actual source top.
The product polynomial is used only as a stronger convenient weight;
its reciprocal has an integral proportional to the top area. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

/-- A convenient product polynomial on the physical top coordinates. -/
def treeProductPolynomial (a b r W t : ℝ) (z : ℝ×ℝ) : ℝ :=
  polynomialWeight a (2*r) 1 z.1 * polynomialWeight b (2*W) 1 (z.2-t*z.1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoxSupremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual suprema of packet values and their energy on disjoint cells.
The supremum includes zero, so an empty packet family contributes zero. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X E ι : Type*} [NormedAddCommGroup E]

def packetNormValues (F : ι → X → E) (Q : Set X) : Set ℝ :=
  {r | r=0 ∨ ∃ a x, x∈Q ∧ r=‖F a x‖}

def packetNormSup (F : ι → X → E) (Q : Set X) : ℝ :=
  sSup (packetNormValues F Q)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse polynomial localization of actual planar vector packets.
Both coordinate frequency cutoffs are retained. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def planarPolynomialLocalization (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  SchwartzMap.smulLeftCLM (EuclideanSpace ℂ κ)
    (fun z : ℝ×ℝ => (polynomialWeight b r q z.2:ℂ)) f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationDisjointExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint intervals fit into a partition of the original finite
horizon. Each interval is collapsed to one jump at its right endpoint;
the gaps contribute additional nonnegative variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def intervalCollapse (a b k : ℕ) : ℕ :=
  if k < b then min k a else k

def disjointCollapse {ι : Type*} [Fintype ι] (a b : ι → ℕ) (k : ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun q : Option ι => q.elim k (fun i => intervalCollapse (a i) (b i) k))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual logarithmic weights and their full-root variation estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def hierarchyLog (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (k : ℕ) : ℂ :=
  ((-a * Real.log (n k) : ℝ) : ℂ) - ∑ i ∈ Finset.range k, z i * (R i : ℂ)

def hierarchyWeight (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (hierarchyLog n R z a k)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SegmentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight variation on a later segment, paid for by full-root mass loss. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def segmentLog (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (start k : ℕ) : ℂ :=
  ((-a * Real.log (n k) : ℝ) : ℂ) - ∑ i ∈ Finset.Ico start k, z i * (R i : ℂ)

def segmentWeight (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (start k : ℕ) : ℂ :=
  Complex.exp (segmentLog n R z a start k)

def boundaryLog (n m : ℕ → ℝ) (i : ℕ) : ℝ := Real.log (m i / n (i + 1))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

def logEnergy (p : ℝ) (x : E) : ℝ := Real.log (1 + ‖x‖ ^ p)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unary residual energies

The amount is the actual `vertexAmount` from §11. Its logarithmic motion
and the small correction `log(1+h/V)` are the analytic ingredients of
the unary-segment telescope in §10, equation `src-28`.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logCorrection (h z : ℝ) : ℝ := Real.log (Real.exp z + h) - z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From probability averages to normalized prediction steps

The probability-mixture transfer, step supremum control, and normalization
costs used in §9. All averages below are actual Bochner integrals.
-/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α : Type*} [MeasurableSpace α]

/-- Supremum on one step cell. -/
def predictionCellSup (B : α → ℝ) (I : Set α) : ℝ := sSup (B '' I)

/-- The normalization denominator from §9. -/
def predictionNormalizer (ν : Measure α) (Bsharp : α → ℝ) : ℝ :=
  max 1 (∫ x, Bsharp x ∂ν)

/-- The normalized step prediction. -/
def normalizedPrediction (ν : Measure α) (Bsharp : α → ℝ) (x : α) : ℝ :=
  Bsharp x / predictionNormalizer ν Bsharp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_PathDrops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic budget for relative drops on an active hierarchy path. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def pathDrop (n : ℕ → ℝ) (i : ℕ) : ℝ := (n i - n (i + 1)) / n i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A positive averaging kernel with compact Fourier support

Square the norm of the Fourier transform of a smooth compactly supported
bump. Plancherel converts its Fourier moments into overlaps of translates
of the bump; disjoint supports therefore give exact annihilation.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

namespace LipschitzHilbert

open PhaseCombinatorics

/-- The nonnegative physical-space averaging density before normalization. -/
def fourierSquare (h : SchwartzMap ℝ ℂ) (t : ℝ) : ℝ := ‖𝓕 h t‖ ^ 2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An actual Fourier-supported averaging probability

Normalize the positive Fourier-square kernel and instantiate its compact
frequency bump. This constructs a probability satisfying `FourierGap` for
every positive gap, rather than assuming existence of an averaging law.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

open PhaseCombinatorics

def fourierAveragingDensity (h : SchwartzMap ℝ ℂ) (t : ℝ) : ℝ :=
  fourierSquare h t / ∫ x, fourierSquare h x

def fourierAveragingMeasure (h : SchwartzMap ℝ ℂ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (fourierAveragingDensity h t))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing a distinguished diagonal carrier

The path-child carrier is a coordinatewise unitary. Removing it leaves the
path vector fixed and subtracts its frequency from every off-path component.
This is the exact transition to the small-drop model in §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

/-- Frequencies after the distinguished child's diagonal carrier is removed. -/
def diagonalRemainderFrequency (frequency : ι → κ → ℝ) (i₀ : ι)
    (i : RemainderIndex i₀) (j : κ) : ℝ := frequency i j - frequency i₀ j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite size-biased random orders

The recursive expectation below chooses the next element proportionally to its
positive weight. This gives the same first-arrival probabilities as independent
exponential clocks, while keeping the probability space entirely finite.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι : Type*} [DecidableEq ι]

def orderMass (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

def orderAverage (w : ι → ℝ) (s : Finset ι) (f : List ι → ℝ) : ℝ :=
  if _hs : s.Nonempty then
    ∑ i : s, w i / orderMass w s *
      orderAverage w (s.erase i.val) (fun l => f (i.val :: l))
  else f []
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem i.property

theorem orderAverage_empty (w : ι → ℝ) (f : List ι → ℝ) :
    orderAverage w ∅ f = f [] := by
  rw [orderAverage]
  simp

omit [DecidableEq ι] in
theorem orderMass_pos (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (hs : s.Nonempty) : 0 < orderMass w s := by
  exact Finset.sum_pos (fun i hi => hw i hi) hs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstArrival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first member of a set in a size-biased random order has the normalized
weights on that set, regardless of the other elements being ordered. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι : Type*} [DecidableEq ι]

def firstFrom (S : Finset ι) : List ι → Option ι
  | [] => none
  | j :: l => if j ∈ S then some j else firstFrom S l

def arrivalEvent (S : Finset ι) (i : ι) (l : List ι) : ℝ :=
  if firstFrom S l = some i then 1 else 0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrderDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite distributions obtained by observing a size-biased random order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]

def orderOutcomeWeight (w : ι → ℝ) (s : Finset ι) (X : List ι → α) (a : α) : ℝ :=
  orderAverage w s (fun l => if X l = a then 1 else 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LocalMinimaSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted independent-set selection by local minima of a size-biased order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def closedNeighborhood (G : ι → ι → Prop) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => j = i ∨ G i j)

theorem mem_closedNeighborhood (G : ι → ι → Prop) (i j : ι) :
    j ∈ closedNeighborhood G i ↔ j = i ∨ G i j := by
  simp [closedNeighborhood]

def localMinima (G : ι → ι → Prop) (l : List ι) : Finset ι :=
  Finset.univ.filter (fun i => firstFrom (closedNeighborhood G i) l = some i)

omit [Fintype ι] in
theorem firstFrom_incompatible (S T : Finset ι) (i j : ι)
    (hiT : i ∈ T) (hjS : j ∈ S) (hij : i ≠ j) (l : List ι)
    (hS : firstFrom S l = some i) (hT : firstFrom T l = some j) : False := by
  induction l with
  | nil => simp [firstFrom] at hS
  | cons k l ih =>
    by_cases hkS : k ∈ S
    · have hki : k = i := by simpa [firstFrom, hkS] using hS
      subst k
      have hij' : i = j := by simpa [firstFrom, hiT] using hT
      exact hij hij'
    · by_cases hkT : k ∈ T
      · have hkj : k = j := by simpa [firstFrom, hkT] using hT
        subst k
        exact hkS hjS
      · apply ih
        · simpa [firstFrom, hkS] using hS
        · simpa [firstFrom, hkT] using hT

theorem localMinima_independent (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i) (l : List ι) :
    (localMinima G l : Set ι).Pairwise (fun i j => ¬G i j) := by
  intro i hi j hj hij hijG
  exact firstFrom_incompatible (closedNeighborhood G i) (closedNeighborhood G j) i j
    ((mem_closedNeighborhood G j i).2 (Or.inr (hG hijG)))
    ((mem_closedNeighborhood G i j).2 (Or.inr hijG)) hij l
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FixedPathAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform averages of the actual graph prediction

The band-limited probability is an explicit mixture. Its graph-prediction
average is at most one by the proved phase gain. Removing the path carrier
then bounds the lower deviation by the off-path coefficient mass, preserving
the relative path drop when passing to the principal probability.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

/-- The actual probability mixture used to approximate cell averages. -/
def predictionMixture (ω τ : Measure ℝ) (η : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - η) • ω + ENNReal.ofReal η • τ

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convolution and the exact averaging mixture

Convolution preserves the proved Fourier gap. A central mass of the kernel
minorizes the uniform law on a smaller interval. The remaining measure is
normalized into the probability used in the prediction-mixture argument.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

/-- The normalized Lebesgue law on a closed interval. Endpoints have zero mass. -/
def intervalProbability (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Icc a b)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable step-supremum prediction factors

Inside one root cell, a finite measurable partition gives an explicit
step supremum. Logarithmic cell oscillation controls its normalization,
producing the actual nonnegative, measurable, average-one factor.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- A finer cell, restricted to the current root region. -/
def predictionCell (I : Set α) (P : α → κ) (i : κ) : Set α := {x | x ∈ I ∧ P x = i}

/-- Actual cell supremums, constant on the finer partition. -/
def predictionStepSup (B : α → ℝ) (I : Set α) (P : α → κ) (x : α) : ℝ :=
  predictionCellSup B (predictionCell I P (P x))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GraphPredictionFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A constructed step factor for the graph prediction

For the fixed snapshot model of §9, combine graph selection, carrier removal,
probability-mixture transfer, finite-cell supremums, and exact normalization.
The resulting factor is an actual measurable step function of average at most
one. Every loss in its comparison retains the off-path mass parameter `u`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]

attribute [local instance] Classical.propDecidable

def predictionCoefficients (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (D p : ℝ) (i : ι) : EuclideanSpace ℂ κ :=
  (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShiftedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

/-- The phase coordinate of a transition in the shared analytic family. -/
def tag (hK : 0 < K) (i : ℕ) : Fin K := ⟨i % K, Nat.mod_lt i hK⟩

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual top mask preserves interval motion.  Only absolute mask
differences occur, so no nonvanishing hypothesis is imposed on the mask. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type} [Fintype κ]

/-- The common diagonal carrier as a complex linear isometry. -/
def diagonalModulationIsometry (frequency : κ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ where
  toFun a := diagonalModulation frequency a t
  map_add' a b := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.add_apply]
    ring
  map_smul' c a := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  norm_map' a := norm_diagonalModulation frequency a t

@[simp]
theorem diagonalModulationIsometry_apply (frequency : κ → ℝ) (t : ℝ)
    (a : EuclideanSpace ℂ κ) :
    diagonalModulationIsometry frequency t a = diagonalModulation frequency a t := rfl

def diagonalModulationRealIsometry (frequency : κ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ κ →ₗᵢ[ℝ] EuclideanSpace ℂ κ where
  toLinearMap := (diagonalModulationIsometry frequency t).toLinearMap.restrictScalars ℝ
  norm_map' a := norm_diagonalModulation frequency a t

@[simp]
theorem diagonalModulationRealIsometry_apply (frequency : κ → ℝ) (t : ℝ)
    (a : EuclideanSpace ℂ κ) :
    diagonalModulationRealIsometry frequency t a = diagonalModulation frequency a t := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass rescaling and block-transition motion for the snapshot prediction.
Every estimate is relative to the positive snapshot masses; no positive
lower cutoff is imposed on a mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def massPowerScale (n c a b : ℝ) : ℝ := n^a*c^b

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_PathCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The dominant-path coefficient from complementary masses

For the path child in §9 the coefficient is
`l^(1-α/p) * r^μ`, where `l=nₐ/n` and `r=nₐ/mₐ`.
Its defect from one and its variation retain the relative path drop.
-/

noncomputable section

namespace LipschitzHilbert

def pathCoefficient (a b l r : ℝ) : ℝ := l ^ a * r ^ b

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform Lipschitz bound for the logarithmic-energy derivative

The dimension-free derivative bound from §9 is proved using the radial
coefficient and its one-dimensional derivative. It supplies the cancellation
between the path numerator and denominator when the path child is dominant.
-/

noncomputable section

namespace LipschitzHilbert

/-- The radial size of the logarithmic-energy gradient. -/
def radialLogSlope (p r : ℝ) : ℝ := p * r ^ (p - 1) / (1 + r ^ p)

/-- The scalar coefficient multiplying the path vector in the derivative. -/
def radialLogCoefficient (p r : ℝ) : ℝ := p * r ^ (p - 2) / (1 + r ^ p)

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of logarithmic energy as an actual bounded linear functional. -/
def logEnergyDerivative (p : ℝ) (x : E) : E →L[ℝ] ℝ :=
  radialLogCoefficient p ‖x‖ • innerSL ℝ x

end Hilbert

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RadialShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial snapshot shrinkage and the balanced prediction comparison

Section 9 shrinks each snapshot amplitude radially by a controlled distance.
The exact norm formula makes its denominator smaller than every nearby moved
denominator. The numerator motion and the logarithmic-energy Lipschitz bound
then give the balanced-case comparison, with its relative path-drop factor.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial truncation by the distance `δ`; its value at the zero vector is zero. -/
def radialShrink (δ : ℝ) (x : E) : E := max (1 - δ / ‖x‖) 0 • x

@[simp] theorem radialShrink_zero (δ : ℝ) : radialShrink δ (0 : E) = 0 := by
  simp [radialShrink]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantPathComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dominant-path logarithmic comparison

The numerator and path denominator are compared together, as in §9,
`pred:path-errors` and equation (src-26). The derivative cancellation is
proved from the actual logarithmic-energy derivative; the residual
child denominator is retained with its exact fractional weight.
-/

noncomputable section

namespace LipschitzHilbert

section Residual

/-- The logarithmic correction from the off-path denominator. -/
def residualLogCorrection (R a : ℝ) : ℝ := a - Real.log (Real.exp a + R)

end Residual

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- The off-path fraction of the complete child denominator. -/
def residualFraction (p R : ℝ) (Y : E) : ℝ := R / (1 + ‖Y‖ ^ p + R)

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pathCancelledLogEnergy (p C : ℝ) (Z V : E) : ℝ :=
  logEnergy p (C • V + Z) - logEnergy p V

end Hilbert

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ScalarPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stability of the removed scalar phase

The dominant-path comparison in §9 removes the scalar phase of its path
weight. Relative motion of a nonzero complex weight gives controlled motion
of that phase, and hence of the rotated off-path vector.
-/

noncomputable section

namespace LipschitzHilbert

/-- The unit complex phase of a weight. -/
def scalarPhase (z : ℂ) : ℂ := NormedSpace.normalize z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnarySegmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopping indices for the greedy unary-segment decomposition. -/

noncomputable section

namespace LipschitzHilbert

/-- A finite partition of a unary run into its actual successive segments. -/
structure UnarySegmentPartition (n : ℕ → ℝ) (start finish : ℕ) where
  blocks : Finset (ℕ × ℕ)
  bounds : ∀ b ∈ blocks, start ≤ b.1 ∧ b.1 < b.2 ∧ b.2 ≤ finish
  cover : ∀ j, start ≤ j → j < finish → ∃ b ∈ blocks, b.1 ≤ j ∧ j < b.2
  ordered : ∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → b.2 ≤ c.1 ∨ c.2 ≤ b.1
  drop_lt_two : ∀ b ∈ blocks, n b.1 - n b.2 < 2
  completed : ∀ b ∈ blocks, b.2 < finish → 1 ≤ n b.1 - n b.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRuns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual consecutive unary runs and their interruption endpoints. -/

noncomputable section

namespace LipschitzHilbert

structure UnaryRunPartition (unary : ℕ → Prop) (start finish : ℕ) where
  runs : Finset (ℕ × ℕ)
  bounds : ∀ r ∈ runs, start ≤ r.1 ∧ r.1 < r.2 ∧ r.2 ≤ finish
  inside : ∀ r ∈ runs, ∀ j, r.1 ≤ j → j < r.2 → unary j
  cover : ∀ j, start ≤ j → j < finish → unary j →
    ∃ r ∈ runs, r.1 ≤ j ∧ j < r.2
  ordered : ∀ r ∈ runs, ∀ s ∈ runs, r ≠ s → r.2 ≤ s.1 ∨ s.2 ≤ r.1
  interruption : ∀ r ∈ runs, r.2 < finish → ¬ unary r.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRunCharging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Charge completed unary segments to themselves and remainders to the
next genuine interruption. The final path remainder is the only exception. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)

abbrev UnaryRunSegment := Σ r : R.runs, (P r).blocks

def unaryRunCharge (i : UnaryRunSegment R P) : Option (ℕ × ℕ) := by
  classical
  exact if i.2.val.2 < i.1.val.2 then some i.2.val else
    if i.1.val.2 < finish then some (i.1.val.2, i.1.val.2 + 1) else none

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact propagation along unary segments

Finite iteration of §10 `res:unary-decomposition`. The residual coefficient
is the actual product of preceding path coefficients. Discarded-top
errors are summed against mass drops rather than the number of tops or
levels, as required in `res:segment-perturbation`.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def unaryPropagator (coeff : ℕ → ℂ) (start finish : ℕ) : ℂ :=
  ∏ j ∈ Finset.Ico start finish, coeff j

@[simp] theorem unaryPropagator_self (coeff : ℕ → ℂ) (start : ℕ) :
    unaryPropagator coeff start start = 1 := by simp [unaryPropagator]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVerticalDemodulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing each vertical bin carrier is an exact pointwise isometry.
Box reproduction can therefore use the narrow demodulated spectra. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def verticalCarrier (nu : ℝ) (z : ℝ×ℝ) : ℂ := Complex.exp ((nu*z.2 : ℝ)*Complex.I)

@[simp] theorem verticalCarrier_norm (nu : ℝ) (z : ℝ×ℝ) : ‖verticalCarrier nu z‖=1 := by
  simp [verticalCarrier,Complex.norm_exp]

def scalarVerticalDemodulation (nu : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (verticalCarrier (-nu)) f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSpatialSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded rectangle splits into uniformly many half-open cells.
Each cell has the exact center bounds used by the ordinary tree estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert

def spatialCellIndex (a L x : ℝ) : ℤ := ⌊(x-a)/L⌋
def spatialCellCenter (a L : ℝ) (i : ℤ) : ℝ := a+((i:ℝ)+1/2)*L

def spatialPacketCell {ι : Type*} (x y : ι → ℝ) (a b L W : ℝ) (q : ι) : ℤ×ℤ :=
  (spatialCellIndex a L (x q),spatialCellIndex b W (y q))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSpatialTreePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite splitting of a selected tree into spatial pieces with
the center bounds required by the ordinary tree theorem. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {ι : Type*}

def spatialTreePiece (S : Finset ι) (x y : ι → ℝ) (a b L W : ℝ) (p : ℤ×ℤ) : Finset ι :=
  S.filter (fun q => spatialPacketCell x y a b L W q=p)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteRemovalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite iteration of proved removal steps, with exact telescoping
packet sums. The step is supplied by the density and size selections. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def finitePacketSum {ι V : Type*} [AddCommMonoid V]
    (v : ι → ℝ×ℝ → V) (S : Finset ι) (z : ℝ×ℝ) : V := ∑ q∈S, v q z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSignedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sign randomization in a Hilbert space, expressed without a
probability space. A bound for every signed sum bounds the square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def finiteSignedSum {n : ℕ} (f : Fin n → E) (s : Fin n → Bool) : E :=
  ∑ i, if s i then f i else -f i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSignedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite randomization for actual measurable functions. Membership in
L2 is recovered from signed sums and is not assumed in advance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}

def signedFunction (f : Fin n → X → ℂ) (s : Fin n → Bool) : X → ℂ :=
  fun x => finiteSignedSum (fun i => f i x) s

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HalfPowerDualTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit dual test for exponent three-halves, with its second,
fourth and third moments. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def halfPowerDualTest (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*g x

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth annular Hilbert multiplier and its cutoff derivative.
All profiles are constructed, rather than supplied as analytic inputs. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertSmoothSign (x : ℝ) : ℝ :=
  Real.smoothTransition (2*x+1)-Real.smoothTransition (1-2*x)

theorem hilbertSmoothSign_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) hilbertSmoothSign := by
  unfold hilbertSmoothSign
  fun_prop

theorem verticalBinPlateauReal_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinPlateauReal := by
  unfold verticalBinPlateauReal
  fun_prop

theorem verticalBinPlateauReal_range (x : ℝ) :
    0≤verticalBinPlateauReal x ∧ verticalBinPlateauReal x≤1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem verticalBinPlateauReal_one (x : ℝ) (hx : |x|≤1) : verticalBinPlateauReal x=1 := by
  have h := verticalBinPlateau_one x hx
  change (verticalBinPlateauReal x:ℂ)=1 at h
  exact_mod_cast h

theorem verticalBinPlateauReal_deriv_zero (x : ℝ) (hx : |x|≤1 ∨ 2≤|x|) :
    deriv verticalBinPlateauReal x=0 := by
  rcases hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [verticalBinPlateauReal_one x hx]
    exact (verticalBinPlateauReal_range y).2
  · have hz : verticalBinPlateauReal x=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hx with hx | hx
      · exact Or.inr hx
      · exact Or.inl (by linarith)
    apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hz]
    exact (verticalBinPlateauReal_range y).1

def hilbertCutoffDerivative : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have ha : 2≤|x| := by
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨h.1.le,h.2.le⟩
    simp only [f,verticalBinPlateauReal_deriv_zero x (Or.inr ha),mul_zero,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    apply hilbertSmoothSign_smooth.mul
    exact (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2)

def hilbertAnnularSymbol : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => -(Real.pi:ℂ)*Complex.I*
    ((hilbertSmoothSign x*(verticalBinPlateauReal x-verticalBinPlateauReal (2*x)) : ℝ) : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have ha : 2≤|x| := by
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨h.1.le,h.2.le⟩
    have hz (s : ℝ) (hs : 2≤|s|) : verticalBinPlateauReal s=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hs with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by linarith)
    have ha2 : 2≤|2*x| := by rw [abs_mul]; norm_num; linarith
    simp only [f,hz x ha,hz (2*x) ha2,sub_self,mul_zero,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply contDiff_const.mul
    apply Complex.ofRealCLM.contDiff.comp
    exact hilbertSmoothSign_smooth.mul (verticalBinPlateauReal_smooth.sub
      (verticalBinPlateauReal_smooth.comp (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => 2*x) by fun_prop))))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual annular inverse Fourier kernel telescopes to a normalized
Schwartz profile. This gives a uniform sharp truncation comparison. -/
noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertTimeKernel : SchwartzMap ℝ ℂ := 𝓕⁻ hilbertAnnularSymbol

def hilbertTimeProfile : SchwartzMap ℝ ℂ := (1/2:ℂ) • (𝓕⁻ hilbertCutoffDerivative)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LayerEnergyMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two layer integrals needed to interpolate the second and fourth
moments to the third moment. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def highLayerEnergy (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if t≤‖f x‖ then ENNReal.ofReal (‖f x‖^2) else 0

def lowLayerEnergy (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if ‖f x‖<t then ENNReal.ofReal (‖f x‖^4) else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingExponentialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variation of differences of exponential endpoint weights. The bound
is polynomial in logarithmic variation; it never exponentiates the size
of a top's logarithmic loss. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def complexSegment (a b : ℂ) (t : ℝ) : ℂ := (1-t) • a + t • b

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MovingSegmentLogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial value and loss budget for the actual moving segment
logarithms. The total cost is paid by the full-root loss, including when
another shift's block begins before the segment. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def segmentCost (n R : ℕ → ℝ) (a Z : ℝ) (j : ℕ) : ℝ :=
  a*Real.log (n j/n (j+1))+Z*R j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductSlopePrincipalValueBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fatou passage from uniform actual sharp truncations to the pointwise
symmetric principal value in product coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def pvInnerRadius (R : ℝ) (n : ℕ) : ℝ := R/((n:ℝ)+2)

theorem pvInnerRadius_pos (R : ℝ) (hR : 0<R) (n : ℕ) : 0<pvInnerRadius R n := by
  unfold pvInnerRadius
  positivity

theorem pvInnerRadius_lt (R : ℝ) (hR : 0<R) (n : ℕ) : pvInnerRadius R n<R := by
  unfold pvInnerRadius
  apply (div_lt_iff₀ (by positivity : 0<(n:ℝ)+2)).mpr
  nlinarith only [Nat.cast_nonneg (α:=ℝ) n,hR]

theorem pvInnerRadius_tendsto (R : ℝ) (hR : 0<R) :
    Tendsto (pvInnerRadius R) atTop (𝓝[>] (0:ℝ)) := by
  have hs := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ) |>.comp (tendsto_add_atTop_nat 1)
  have heq : pvInnerRadius R=(fun n : ℕ => R*((((n+1:ℕ):ℝ)+1)⁻¹)) := by
    funext n
    norm_num [pvInnerRadius,div_eq_mul_inv,Nat.cast_add,add_assoc]
  have hzero : Tendsto (pvInnerRadius R) atTop (𝓝 (0:ℝ)) := by
    rw [heq]
    simpa only [Function.comp_def,one_div,mul_zero] using (tendsto_const_nhds (x:=R)).mul hs
  exact tendsto_nhdsWithin_iff.mpr ⟨hzero,Eventually.of_forall (pvInnerRadius_pos R hR)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NarrowPartitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bound for the fixed narrow cutoff controls a finite partition of any
compact annulus. Its cost is independent of the common frequency dilation. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def narrowPartitionCost (l : List NarrowWindow) : ℝ :=
  (l.map (fun q => verticalProjectionCost q.2)).sum

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedTranslatedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights absorb translations of normalized packet
profiles. The estimates are uniform before all packet locations. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def weightedTranslatedProfile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  symbolWeight q nu • F.compSubConstCLM ℂ a

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_UniformTranslatedProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual profile constant used by the packet estimates is controlled
uniformly for the polynomially weighted translated profiles. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

abbrev PlanarSchwartz := SchwartzMap (ℝ×ℝ) ℂ

def profileVerticalCLM : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  ((SchwartzMap.evalCLM ℂ (ℝ×ℝ) ℂ (0,1)).comp
    (SchwartzMap.fderivCLM ℂ (ℝ×ℝ) ℂ)).restrictScalars ℝ

def profileHorizontalCLM : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  ((SchwartzMap.evalCLM ℂ (ℝ×ℝ) ℂ (1,0)).comp
    (SchwartzMap.fderivCLM ℂ (ℝ×ℝ) ℂ)).restrictScalars ℝ

def profileJetCLM (i : Fin 3) : PlanarSchwartz →L[ℝ] PlanarSchwartz :=
  if i=0 then ContinuousLinearMap.id ℝ _ else if i=1 then profileVerticalCLM
    else profileVerticalCLM.comp profileVerticalCLM

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingProfileNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analyzing wave uses reflection and conjugation together. Its
positive carrier is unchanged, and its normalized profile has the same
uniform weighted-translation bounds as the synthesizing profile. -/
noncomputable section
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def reflectedConjugateProfile (F : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ (E := ℝ×ℝ)) F).postcompCLM Complex.conjCLE.toContinuousLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single Fourier parameter determines both normalized wave profiles.
Their common bound is chosen before all spatial scales and frequency bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def synthesisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace) :
    SchwartzMap (ℝ×ℝ) ℂ := weightedTranslatedProfile F q nu (-nu 0,0)

def analysisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  weightedTranslatedProfile (reflectedConjugateProfile F) q nu (0,nu 1)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NormalizedProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the finite derivative order and Fourier-decay exponent before
any packet lattice. Their fixed profile cost fits the model's logarithmic
budget once the disparity parameter is large enough. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def requiredPacketOrder (D : ℕ) : ℕ := max 207 (6+2*(8*D+1))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzGlobalLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Schwartz function has a global Lipschitz bound from its first
derivative seminorm. This supplies domination in pointwise PV limits. -/
noncomputable section
open scoped NNReal
namespace SchwartzMap
open scoped _root_.SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def globalLipschitzConstant (f : SchwartzMap E ℂ) : ℝ≥0 :=
  ⟨SchwartzMap.seminorm ℝ 0 1 f, apply_nonneg _ _⟩

theorem global_lipschitz (f : SchwartzMap E ℂ) :
    LipschitzWith (_root_.OAI.SchwartzMap.globalLipschitzConstant f) f := by
  apply lipschitzWith_of_nnnorm_fderiv_le f.differentiable
  intro x
  change ‖fderiv ℝ f x‖≤SchwartzMap.seminorm ℝ 0 1 f
  rw [←norm_iteratedFDeriv_one]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f 1 x

end SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductPVPointwiseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise domination of short principal values on globally Lipschitz
inputs. No operator estimate or published input is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem productSlopeSample_symmetric_dist (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (t : ℝ) :
    dist (productSlopeSample u t z) (productSlopeSample u (-t) z)≤2*|t| := by
  rw [Prod.dist_eq]
  apply max_le
  · change |(z.1-t)-(z.1- -t)|≤2*|t|
    have he : (z.1-t)-(z.1- -t)= -2*t := by ring
    rw [he,abs_mul]
    norm_num
  · change |(z.2-t*u z)-(z.2- -t*u z)|≤2*|t|
    have he : (z.2-t*u z)-(z.2- -t*u z)=(-2*t)*u z := by ring
    rw [he,abs_mul,abs_mul]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [abs_nonneg t]

theorem productSymmetricIntegrand_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    ‖t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))‖≤2*(K:ℝ) := by
  have h := (hf.dist_le_mul (productSlopeSample u t z) (productSlopeSample u (-t) z)).trans
    (mul_le_mul_of_nonneg_left (productSlopeSample_symmetric_dist u z hu t) K.coe_nonneg)
  rw [dist_eq_norm] at h
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  by_cases ht : t=0
  · simp [ht]
  · have htpos := abs_pos.mpr ht
    calc
      _ ≤ |t|⁻¹*((K:ℝ)*(2*|t|)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr htpos.le)
      _ = 2*(K:ℝ) := by field_simp

theorem productSymmetricTruncation_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (epsilon R : ℝ) (he : 0≤epsilon) (heR : epsilon≤R) :
    ‖productSymmetricTruncation u epsilon R f z‖≤2*(K:ℝ)*R := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t (_ : t∈Set.uIoc epsilon R) => productSymmetricIntegrand_bound u z hu f hf t)
  rw [abs_of_nonneg (sub_nonneg.mpr heR)] at h
  exact h.trans (by nlinarith [K.coe_nonneg])

theorem productSlopePrincipalValue_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : (ℝ×ℝ) → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfd : Differentiable ℝ f) (R : ℝ) (hR : 0<R) :
    ‖productSlopePrincipalValue u R f z‖≤2*(K:ℝ)*R := by
  apply le_of_tendsto (productSymmetricTruncation_tendsto u f hfd R hR z).norm
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds]
    with epsilon he heR
  exact productSymmetricTruncation_pointwise_bound u z hu f hf epsilon R he.le heR.le

theorem productSchwartzPV_pointwise_bound (u : (ℝ×ℝ) → ℝ) (z : ℝ×ℝ)
    (hu : |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0<R) :
    ‖productSlopePrincipalValue u R f z‖≤2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R :=
  productSlopePrincipalValue_pointwise_bound u z hu f (_root_.OAI.SchwartzMap.global_lipschitz f) f.differentiable R hR

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductPVContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise principal value is continuous for continuous bounded
slope fields. The removable value at time zero is irrelevant to integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def productPVIntegrand (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (z : ℝ×ℝ) (t : ℝ) : ℂ :=
  t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic selection of the relative exit scale for each nonzero interval. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

/-- Relative radii, starting below one half as required by the pathwise argument. -/
def relativeExitScale (m : ℕ) : ℝ := (1/4)*(1/2)^m

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedLogDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing a logarithmic restricted estimate from bounded Schwartz
functions to measurable bounded tests, preserving the support masses. -/
noncomputable section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

def restrictedLogFactor (C a b : ℝ) : ℝ :=
  C*((1+|Real.log (a/b)|)^3)⁻¹*Real.sqrt a*Real.sqrt b

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScalarRestrictedStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex instance of the proved restricted-to-strong
estimate, transported through the one-dimensional orthonormal basis. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

abbrev scalarCoordinate : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_UnitPacketSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact Fourier selectors are normalized to the size and
Lipschitz bounds required by the finite packet model. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def selectorNormalizer (chi : SchwartzMap ℝ ℝ) (C : ℝ) : ℝ :=
  C*(1+SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi)

def unitPacketSelector (chi : SchwartzMap ℝ ℝ) (C : ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  ((selectorNormalizer chi C)⁻¹:ℂ)*localizedSelector chi S q nu U

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScaledUnitSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selectors at angular scale `d`: measurability, unit
size, support away from the label, and the required scaled Lipschitz bound. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def scaledUnitSelector (chi : SchwartzMap ℝ ℝ) (C : ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (d theta s : ℝ) : ℂ :=
  unitPacketSelector chi C S q nu ((s-theta)/d)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceAssignedPacketSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact grouping by an assignment defined only on the selected packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def assignedPacketSet {ι J : Type*} (S : Finset ι) (assigned : S → J) (j : J) : Finset ι :=
  S.filter fun q => ∃ hq : q∈S, assigned ⟨q,hq⟩=j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceModelThresholdScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The size threshold used at each dyadic density level. -/
noncomputable section
namespace LipschitzHilbert

def modelSizeThreshold (energyNorm area : ℝ) (k : ℤ) : ℝ :=
  Real.sqrt ((2:ℝ)^k)*energyNorm/Real.sqrt area

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FinitePacketSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any finite collection in the joint spatial lattice is realized by
finite site fibers. No rectangular truncation or extra packet is added. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {Label : Fin N → Type} (labels : ∀ j, Finset (Label j))

abbrev LatticeSiteIndex := Σ j : Fin N, Σ _l : labels j, ℤ×ℤ

abbrev LatticeRow := Σ j : Fin N, labels j

def latticeSiteProductEquiv : LatticeSiteIndex labels ≃ (LatticeRow labels × (ℤ×ℤ)) where
  toFun := fun s => (⟨s.1,s.2.1⟩,s.2.2)
  invFun := fun s => ⟨s.1.1,⟨s.1.2,s.2⟩⟩
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

theorem siteIndex_injective (j : Fin N) (l : labels j) :
    Function.Injective (fun n : ℤ×ℤ => (⟨j,⟨l,n⟩⟩ : LatticeSiteIndex labels)) := by
  intro a b h
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

def retainedSites (S : Finset (LatticeSiteIndex labels)) (j : Fin N) (l : labels j) :
    Finset (ℤ×ℤ) :=
  S.preimage (fun n => ⟨j,⟨l,n⟩⟩) (siteIndex_injective labels j l).injOn

theorem mem_retainedSites (S : Finset (LatticeSiteIndex labels))
    (j : Fin N) (l : labels j) (n : ℤ×ℤ) :
    n∈retainedSites labels S j l ↔ (⟨j,⟨l,n⟩⟩ : LatticeSiteIndex labels)∈S :=
  Finset.mem_preimage

def retainedSiteEquiv (S : Finset (LatticeSiteIndex labels)) :
    (Σ j : Fin N, Σ l : labels j, retainedSites labels S j l) ≃ S where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1,q.2.2.val⟩⟩,
    (mem_retainedSites labels S q.1 q.2.1 q.2.2.val).mp q.2.2.property⟩
  invFun := fun q => ⟨q.val.1,⟨q.val.2.1,⟨q.val.2.2,
    (mem_retainedSites labels S q.val.1 q.val.2.1 q.val.2.2).mpr q.property⟩⟩⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FiniteNormalizedPacketLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realization of an arbitrary finite part of the translated lattice
by the actual normalized packet data. The site fibers are shared by
all carrier components and add no extra terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
variable (F : SchwartzMap (ℝ×ℝ) ℂ)
  (q : ℕ)
  (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ)
  (order : ℕ)
  (htop : 0<topLength)
  (hwidth : 0<width)
  (hC : 0<C)
  (horder : 3≤order)
  (hratio : 1 ≤ ratioBound)
  (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ)
  (theta : ∀ j, labels j → ℝ)
  (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))

attribute [local instance] Classical.propDecidable

def finiteSiteFiber (j : Fin N) (l : Label j) : Finset (ℤ×ℤ) :=
  if h : l∈labels j then retainedSites labels S j ⟨l,h⟩ else ∅

def finiteSiteFiberEquiv (j : Fin N) (l : labels j) :
    finiteSiteFiber labels S j l.val ≃ retainedSites labels S j l :=
  Equiv.subtypeEquivRight (by
    intro n
    simp [finiteSiteFiber,l.property])

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedConvolutionForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual common finite convolution form, named independently of
its estimate and of the lattice used to average it. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def latticeLength (topLength : ℝ) (labels : ∀ j, Finset (Label j))
    (i : LatticeRow labels) : ℝ := topLength/(2:ℝ)^i.1.val

theorem latticeLength_pos (topLength : ℝ) (htop : 0<topLength)
    (labels : ∀ j, Finset (Label j)) (i : LatticeRow labels) :
    0<latticeLength topLength labels i := div_pos htop (pow_pos (by norm_num) _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnnularPacketGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical choices for the annular multiplier. The enlargement
and compact master radius depend only on its support and on the two
frequency-window widths. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

structure AnnularPacketGeometry (A B c C a M : ℝ) where
  H : ℝ
  R : ℝ
  hA : 0≤A
  hB : 0≤B
  hc : 0 < c
  hC : 0<C
  ha : 0<a
  hM : 0<M
  hH : 1≤H
  hR : 0<R
  narrow : A≤a/4
  size : A+B+(M+A)/(H*c)≤R
  radius : max (H*C) H≤R
  quarter : (3*a/(4*(H*C)))/2≤1/4
  separation : (2*Real.pi*A)/(2*Real.pi*(H*c))<(3*a/(4*(H*C))/2)/4
  coverage : 6*max (2*((M+A)/(H*c)))
    ((2*Real.pi*A)/(2*Real.pi*(H*c))+3*a/(4*(H*C))/2)<1

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ} (p : AnnularPacketGeometry A B c C a M)

def inner : ℝ := 3*a/(4*(p.H*C))
def outer : ℝ := (M+A)/(p.H*c)
theorem H_pos : 0<p.H := zero_lt_one.trans_le p.hH
theorem inner_pos : 0<p.inner := by unfold inner; positivity [p.H_pos,p.hC,p.ha]

end AnnularPacketGeometry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical weights for the bounded-input, unequal-measure estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def reverseThresholdWeight (ratio eta : ℝ) : ℝ :=
  min 1 (Real.sqrt (eta/ratio))*min 1 eta*(1+eta^(-(1/20:ℝ)))/eta

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualBlockGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual blocks contain disjoint bands of packet lengths.
Their cardinality is bounded by the logarithm of the source block width
ratio, rather than by the total number of packet scales. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def residualLengthSet {N : ℕ} (stop : Fin N → ℕ) (lower upper : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => lower ≤ stop j ∧ stop j < upper)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized distance to the nearest boundary is a one-periodic
folded fractional part of the common grid translation. -/

noncomputable section
namespace LipschitzHilbert

def unitBoundaryDistance (u : ℝ) : ℝ := min (Int.fract u) (1-Int.fract u)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_GeometricBoundaryDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact average of the boundary-depth envelope used after telescoping. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

def geometricBoundaryLayer (ε q : ℝ) (j : ℕ) : ℝ → ℝ :=
  (Ioo 0 (ε * q ^ j)).indicator (fun _ => 1)

def geometricBoundaryDepth (ε q b : ℝ) : ℝ :=
  ∑' j : ℕ, geometricBoundaryLayer ε q j b

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WitnessTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving an actual popularity witness to a fixed reference line. -/

noncomputable section

open scoped NNReal

namespace LipschitzHilbert
namespace SlopeBox

/-- The point at horizontal coordinate `w.1` on the reference line through `z`. -/
def referencePoint (s : ℝ) (z w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1, z.2 + s * (w.1 - z.1))

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_WitnessLineAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact transferred witness gives the required popular line bin. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

def linePoint (s : ℝ) (z : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  (x, z.2 + s * (x - z.1))

def lineBinSet (u : ℝ × ℝ → ℝ) (s : ℝ) (z : ℝ × ℝ) (bin : Set ℝ) : Set ℝ :=
  {x | u (linePoint s z x) ∈ bin}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCountSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the line-counting tail across a finite transverse interval. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

def lineCountSlab (N : ℝ × ℝ → ℝ≥0∞) (U V : Set ℝ) (lambda : ℝ) : Set (ℝ × ℝ) :=
  (U ×ˢ V) ∩ {z | ENNReal.ofReal lambda < N (z.2, z.1)}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTiledLineIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the source root-window estimates over the actual half-open tiling
of a line. Local integrability comes from the marked-window theorem; it
is not inferred from a vacuous Bochner-integral inequality. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def sourceLineTile (H : ℝ) (k : ℤ) : Set ℝ := Ico (H*k) (H*((k:ℝ)+1))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationErrorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural moments of the actual labeled positive error on arbitrary
binary intervals. The constant depends on the source size and logarithmic
source sum, never on the number of available slope labels. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

def selectorErrorMomentBase (B : ℝ) : ℝ :=
  16*((4*(2*((1024*Real.pi^2)*B)+(240*Real.pi)*B+1))/Real.log (3/2)+
    (1024*Real.pi^2)*B+1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_RectangularFrequencyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed rectangular plateau supplies both convolution factors in the
finite band representation. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

def unitPlaneBump : ContDiffBump (0 : ℝ×ℝ) := ⟨1,2,by norm_num,by norm_num⟩

def unitPlaneCutoff : SchwartzMap (ℝ×ℝ) ℂ :=
  (unitPlaneBump.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp unitPlaneBump.contDiff)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SlopePartitionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite smooth partition uses the same arithmetic labels as
the packet model; their local multiplicity is uniform in the truncation. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def finiteSlopeLabels (K : ℕ) : Finset ℕ := Finset.range (2*K+1)
def finiteSlopeCenter (K : ℕ) (delta d : ℝ) (n : ℕ) : ℝ := delta*d*((n:ℝ)-K)

def scaledSlopePartition (delta : ℝ) (hd : 0<delta) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow slopePartition delta⁻¹ (inv_ne_zero hd.ne')

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWindowRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarge the vertical reference width together with the auxiliary
angular precision. This leaves the physical multiplier and W/w unchanged. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ}

def enlargeVertical (p : AnnularPacketGeometry A B c C a M) :
    AnnularPacketGeometry A (p.H*B) c C a M where
  H := p.H
  R := p.R+p.H*B
  hA := p.hA
  hB := mul_nonneg p.H_pos.le p.hB
  hc := p.hc
  hC := p.hC
  ha := p.ha
  hM := p.hM
  hH := p.hH
  hR := by linarith [p.hR,mul_nonneg p.H_pos.le p.hB]
  narrow := p.narrow
  size := by linarith [p.size,p.hB]
  radius := p.radius.trans (by linarith [mul_nonneg p.H_pos.le p.hB])
  quarter := p.quarter
  separation := p.separation
  coverage := p.coverage

end AnnularPacketGeometry

def verticallyRescaledWindow (beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow beta H⁻¹ (inv_ne_zero hH.ne')

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedFrequencySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete slope-partitioned frequency symbol is uniformly bounded
and measurable, including at the zero of its vertical denominator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def partitionedFrequencySymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℂ :=
  psi (l*(p.2.1+u p.1*p.2.2))*rho (-symbolX l p.2.1 p.2.2 theta/(w*p.2.2))*
    beta (symbolY W p.2.2 center)

def annularBandSymbol (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℂ :=
  psi (l*(p.2.1+u p.1*p.2.2))*beta (symbolY W p.2.2 center)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGoodPathSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source good set controls the pointwise total bad-top mass.
Its measure estimate follows from the full weighted bad-path integral. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {ι X : Type*} [MeasurableSpace X]

def sourceBadPathMass (tops : Finset ι) (weight : ι → X → ℝ) (bad : ι → Set X) (x : X) : ℝ :=
  ∑ t ∈ tops, (bad t).indicator (weight t) x

def sourceGoodPathSet (base : Set X) (tops : Finset ι) (weight : ι → X → ℝ)
    (bad : ι → Set X) (L : ℝ) : Set X :=
  base ∩ {x | sourceBadPathMass tops weight bad x ≤ Real.exp (-L)}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SimplexTubeInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded analytic tubes preserve a common bound under finite convex
combinations of their real parameters. This is the scalar interpolation
step used for the finitely many shift parameters in manuscript §11. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*}

def phaseTubePoint (a eta : ι → ℝ) : ι → ℂ :=
  fun i => (a i:ℂ)+(eta i:ℂ)*Complex.I

def phaseTubeLine (a b eta : ι → ℝ) (z : ℂ) : ι → ℂ :=
  fun i => (1-z)*(a i:ℂ)+z*(b i:ℂ)+(eta i:ℂ)*Complex.I

def phaseTubeBound (F : (ι → ℂ) → ℂ) (C : ℝ) (a : ι → ℝ) : Prop :=
  ∀ eta, ‖F (phaseTubePoint a eta)‖ ≤ C

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GaussianPhaseDamping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian damping of the finite shift parameters. Its exact norm
removes the crude exp(C√L) growth outside the imaginary ball of radius L². -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

def gaussianPhaseDamping (z : ι → ℂ) : ℂ := Complex.exp (∑ i, z i^2)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonnegative shift simplex and its vertex geometry. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

def sourceShiftSimplex (mu : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = mu}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppedScalarExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar algebra for a stopped path. The terminal coefficient is
retained, so a small positive terminal mass is never replaced by zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def stoppedScalarExpansion (active : ℕ → Prop) (beta terminal : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,j => terminal j
  | n+1,j => if active j then beta j*stoppedScalarExpansion active beta terminal n (j+1)
      else terminal j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Hilbert-valued tests recover the Lp norm on each finite
exhaustion set used in the source interpolation. The canonical test is
constructed explicitly and introduces no dimension-dependent constant. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourceCanonicalDual (F : X → EuclideanSpace ℂ κ) (p : ℝ) (x : X) :
    EuclideanSpace ℂ κ := ((‖F x‖^(p-2):ℝ):ℂ) • F x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLpExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded logarithmic-coefficient exhaustions preserve the uniform
Lp estimate. Integrability of the full power is proved by monotone
Lebesgue integration, before passing back to the real integral. -/

noncomputable section
open MeasureTheory Set Filter
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourceExhaustion (R : X → ℝ) (n : ℕ) : Set X := {x | R x ≤ (n:ℝ)}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataJetBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smaller concentration normalization has a polynomial bound that
does not involve the later mask exponent. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem smallJetRatio_ge_one {L a : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) :
    1 ≤ 4*L^a := by
  have h := Real.one_le_rpow hL ha
  linarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SlopeRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual Euclidean rectangle enclosing a clipped thin slope
parallelogram, with the explicit lengths used in the popular-top proof. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

theorem slope_rectangle_short_le_long (s a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) :
    b/Real.sqrt (1+s^2) ≤
      Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b := by
  have hq : 1 ≤ Real.sqrt (1+s^2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg s])
  have hqpos : 0 < Real.sqrt (1+s^2) := lt_of_lt_of_le zero_lt_one hq
  calc
    b/Real.sqrt (1+s^2) ≤ b := div_le_self hb.le hq
    _ ≤ a := hba
    _ ≤ Real.sqrt (1+s^2)*a := le_mul_of_one_le_left ha.le hq
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_VerticalRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Euclidean enclosures of fat slope parallelograms. The
constant vertical field makes every such enclosure Lacey--Li admissible. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert

def verticalAxes : OrthonormalBasis (Fin 2) ℝ Plane :=
  (slopeAxes 0).reindex (Equiv.swap 0 1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationCentered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def centeredPhaseCutoff_p1 (t : ℝ) (d : Fin N → ℝ) (phase : Fin 3) : Fin N → ℝ :=
  if phase=0 then (fun j => t+d j) else if phase=1 then (fun j => d j-t) else fun _ => 0

def centeredPhaseField_p1 (t : ℝ) (v : ℝ×ℝ → ℝ) (phase : Fin 3) : ℝ×ℝ → ℝ :=
  if phase=0 then (fun z => v (sourceReferenceToPhysical t z))
  else if phase=1 then (fun z => -v (sourceReferenceToPhysical t z)) else fun _ => 0

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bin square-function bound on the actual L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfileKernel_continuous (q : SchwartzMap ℝ ℂ) (W center : ℝ) :
    Continuous (verticalProfileKernel q W center) := by
  unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
  fun_prop


theorem verticalProfileKernel_integrable (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (verticalProfileKernel q W center) :=
  modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite vectors of vertical projections, including their energy,
L1, uniform, and horizontal support bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalBinKernelCost : ℝ := ∫ t : ℝ, ‖(𝓕⁻ verticalBinProfile : SchwartzMap ℝ ℂ) t‖

def verticalBinVector (I : Finset ℕ) (K : ℕ) (W : ℝ) (f : ℝ×ℝ → ℂ)
    (z : ℝ×ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun n : I => verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The number of retained vertical bins has the allowed exponential growth. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalBinVectorCost (w W c C : ℝ) : ℝ :=
  ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)*verticalBinKernelCost

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TotalBinErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Substitution of the manuscript's actual bin count and width into the
total commutator error, followed by its small-time decay. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def totalBinErrorCoefficient (k : SchwartzMap ℝ ℂ) (C : ℝ) : ℝ :=
  (2*C+3)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*C^2)

def totalProjectedBinError (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength w W c C : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∑ n : verticalBinLabels ⌈C*W/w⌉₊ w W c C,
    finiteBinError k verticalBinProfile N topLength W (verticalBinCenter ⌈C*W/w⌉₊ W n) u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n) f) z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalProjectionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical derivative of the actual band projection has L1 and
uniform bounds of order inverse bandwidth. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalDerivativeProfile (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (2*Real.pi*Complex.I : ℂ) • SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => (s:ℂ)) p

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortVerticalDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact vertical FTC for replacing short directional sampling by
horizontal sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortVerticalDifference (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) : ℂ :=
  f (z.1-t,z.2-t*u z)-f (z.1-t,z.2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortVerticalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated very-short-time replacement error, with its exact
first-moment dependence. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortVerticalError (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then K t*shortVerticalDifference f u t z else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpTimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's time and averaging-width choices, with the exact
logarithmic long-time cost used by the sharp truncation argument. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def sharpSourceTime (L : ℝ) : ℝ := Real.exp (-(L^(97/100:ℝ)))
def sharpSourceWidthRatio (L : ℝ) : ℝ := Real.exp (L^(9/10:ℝ))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous short-time operator agrees on every L2 class with
its integral representative. This permits exact support localization. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def shortSample (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (t : ℝ) (z : ℝ×ℝ) : ℂ :=
  if |t|≤1/4 then f (z.1-t,z.2-t*u z) else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothedCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assembled finite commutator bound has one constant, independent
of the coefficient smoothing and the number of input frequency bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def lineLowHighEnergyConstant : ℝ :=
  36*((∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*
    localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2

def lineHighLowEnergyConstant : ℝ :=
  576*((∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(26*Real.pi/3))^2

def lineCommutatorEnergyConstant : ℝ :=
  3*(lineLowHighEnergyConstant+lineHighLowEnergyConstant+49152*comparableCommutatorConstant)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineBoundedCommutatorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a fixed bounded Schwartz coefficient the undifferentiated
commutator is an actual bounded L2 map. This identifies the limits of
the differentiated frequency approximations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineProductLM (b : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ b).toLinearMap

def lineCommutatorLM (m b : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (lineProductLM b).comp (lineSchwartzProjectionLM m 1 (by norm_num))-
    (lineSchwartzProjectionLM m 1 (by norm_num)).comp (lineProductLM b)

def lineCommutatorToL2 (m b : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp (lineCommutatorLM m b)

def lineCommutatorL2 (m b : SchwartzMap ℝ ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCommutatorToL2 m b).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDerivativeCommutatorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differentiated Lipschitz commutator has its actual bounded L2
extension, with the uniform constant proved by dyadic decomposition. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineCommutatorNormConstant : ℝ := Real.sqrt lineCommutatorEnergyConstant

def lineDerivativeCommutatorToL2 (m b : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCommutatorToL2 m b).comp (SchwartzMap.derivCLM ℂ ℂ).toLinearMap

def lineDerivativeCommutatorL2 (m b : SchwartzMap ℝ ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineDerivativeCommutatorToL2 m b).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short-time line sampling map and its inverse. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def lineSampling (u : ℝ → ℝ) (t y : ℝ) : ℝ := y-t*u y

theorem lineSampling_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) : LipschitzWith 2 (lineSampling u t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hu.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  simp only [Real.dist_eq,NNReal.coe_ofNat,lineSampling]
  have he : x-t*u x-(y-t*u y)=(x-y)-t*(u x-u y) := by ring
  rw [he]
  have htri := abs_sub (x-y) (t*(u x-u y))
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg t)
  nlinarith [abs_nonneg (x-y)]

theorem lineSampling_antilipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) : AntilipschitzWith 2 (lineSampling u t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := hu.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  have he : x-y=(lineSampling u t x-lineSampling u t y)+t*(u x-u y) := by
    unfold lineSampling
    ring
  have htri : |x-y|≤|lineSampling u t x-lineSampling u t y|+|t| *|u x-u y| := by
    conv_lhs => rw [he]
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg t)
  nlinarith [abs_nonneg (x-y)]

theorem lineSampling_surjective (u : ℝ → ℝ) (hu : Continuous u) (B : ℝ)
    (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) : Function.Surjective (lineSampling u t) := by
  intro y
  let a := y-|t| *B
  let b := y+|t| *B
  have hab : a≤b := by dsimp [a,b]; nlinarith [abs_nonneg t]
  have hprod (x : ℝ) : -(|t| *B)≤t*u x ∧ t*u x≤|t| *B := by
    have hh := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)
    rw [←abs_mul] at hh
    exact abs_le.mp hh
  have ha : lineSampling u t a≤y := by have := (hprod a).1; dsimp [lineSampling,a]; linarith
  have hb' : y≤lineSampling u t b := by have := (hprod b).2; dsimp [lineSampling,b]; linarith
  have hc : Continuous (lineSampling u t) := continuous_id.sub (continuous_const.mul hu)
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha,hb'⟩
  exact ⟨x,hx⟩

def lineSamplingHomeomorph (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) : ℝ ≃ₜ ℝ :=
  let e := Equiv.ofBijective (lineSampling u t)
    ⟨(lineSampling_antilipschitz u hu t ht).injective,lineSampling_surjective u hu.continuous B hB hb t⟩
  { e with
    continuous_toFun := (lineSampling_lipschitz u hu t ht).continuous
    continuous_invFun := ((lineSampling_antilipschitz u hu t ht).to_rightInverse e.apply_symm_apply).continuous }

theorem lineSamplingHomeomorph_symm_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingHomeomorph u hu B hB hb t ht).symm :=
  (lineSampling_antilipschitz u hu t ht).to_rightInverse
    (lineSamplingHomeomorph u hu B hB hb t ht).apply_symm_apply

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-dimensional composition operators with uniform L2
bounds from the inverse Lipschitz estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem line_map_le_two (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    Measure.map phi volume≤(2:ℝ≥0∞) • (volume : Measure ℝ) := by
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply hm hS,Measure.smul_apply,smul_eq_mul]
  have hh := ha.hausdorffMeasure_preimage_le (d:=1) (by norm_num) S
  simpa only [hausdorffMeasure_real,ENNReal.rpow_one,ENNReal.coe_ofNat] using hh

theorem line_memLp_comp (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume) :
    MemLp (f ∘ phi) 2 volume ∧ (∫ x, ‖f (phi x)‖^2)≤2*(∫ x, ‖f x‖^2) := by
  have hmap := line_map_le_two phi hm ha
  have hi := hf.integrable_norm_pow (by decide : 2≠0)
  have hscaled := hi.smul_measure (by norm_num : (2:ℝ≥0∞)≠⊤)
  have hcomp : Integrable (fun x => ‖f x‖^2) (Measure.map phi volume) := hscaled.mono_measure hmap
  have hint : Integrable ((fun x => ‖f x‖^2) ∘ phi) volume := hcomp.comp_measurable hm
  refine ⟨(memLp_two_iff_integrable_sq_norm (hfm.comp hm).aestronglyMeasurable).mpr hint,?_⟩
  rw [←integral_map hm.aemeasurable hcomp.aestronglyMeasurable]
  have hh := integral_mono_measure hmap (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖) hscaled
  simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using hh

def lineCompositionToL2 (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp (f ∘ phi)
  map_add' f g := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp_add
    (line_memLp_comp phi hm ha g g.continuous.measurable (g.memLp 2 volume)).1
  map_smul' c f := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp_const_smul c

def lineCompositionL2 (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCompositionToL2 phi hm ha).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugation generator for a compact smooth direction.
Its Lipschitz bound is uniform in the short time parameter. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingHomeomorph_symm_contDiff (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    ContDiff ℝ ∞ ((lineSamplingHomeomorph u hu B hB hb t ht).symm : ℝ → ℝ) := by
  let e := lineSamplingHomeomorph u hu B hB hb t ht
  have hd : Differentiable ℝ u := hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hne (x : ℝ) : 1-t*deriv u x≠0 := by
    have hu' : |deriv u x|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
    have hp : |t*deriv u x|≤1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hu' (abs_nonneg t)).trans (by simpa only [mul_one] using ht)
    have hl := (abs_le.mp hp).2
    linarith
  have he' (x : ℝ) : HasDerivAt e (1-t*deriv u x) x :=
    (hasDerivAt_id x).sub ((hd x).hasDerivAt.const_mul t)
  have he : ContDiff ℝ ∞ (e : ℝ → ℝ) := contDiff_id.sub (contDiff_const.mul hc)
  exact e.contDiff_symm_deriv hne he' he

def lineSamplingGenerator (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) : ℝ :=
  -u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y)

theorem lineSamplingGenerator_contDiff (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    ContDiff ℝ ∞ (lineSamplingGenerator u hu B hB hb t ht) :=
  (hc.comp (lineSamplingHomeomorph_symm_contDiff u hu hc B hB hb t ht)).neg

theorem lineSamplingGenerator_compact (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    HasCompactSupport (lineSamplingGenerator u hu B hB hb t ht) :=
  (hcompact.comp_homeomorph (lineSamplingHomeomorph u hu B hB hb t ht).symm).neg

def lineSamplingGeneratorSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) : SchwartzMap ℝ ℂ :=
  ((lineSamplingGenerator_compact u hu hcompact B hB hb t ht).toSchwartzMap
    (lineSamplingGenerator_contDiff u hu hc B hB hb t ht)).postcompCLM Complex.ofRealCLM

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof-independent inverse family, with quantitative continuity in
space and time. These identities are used in the conjugation derivative. -/
noncomputable section
open Function
namespace LipschitzHilbert.PacketRepresentation

def lineSamplingInverse (u : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := invFun (lineSampling u t)

theorem lineSamplingInverse_eq (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    lineSamplingInverse u t=(lineSamplingHomeomorph u hu B hB hb t ht).symm := by
  exact invFun_eq_of_injective_of_rightInverse (lineSampling_antilipschitz u hu t ht).injective
    (lineSamplingHomeomorph u hu B hB hb t ht).apply_symm_apply

theorem lineSampling_inverse_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (y : ℝ) :
    lineSampling u t (lineSamplingInverse u t y)=y :=
  rightInverse_invFun (lineSampling_surjective u hu.continuous B hB hb t) y

theorem lineSamplingInverse_space_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingInverse u t) := by
  rw [lineSamplingInverse_eq u hu B hB hb t ht]
  exact lineSamplingHomeomorph_symm_lipschitz u hu B hB hb t ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual forward and inverse sampling operators on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSampling_temperate (u : ℝ → ℝ) (hc : ContDiff ℝ ∞ u)
    (hcompact : HasCompactSupport u) (t : ℝ) :
    Function.HasTemperateGrowth (lineSampling u t) := by
  have hu := (hcompact.toSchwartzMap hc).hasTemperateGrowth
  exact Function.HasTemperateGrowth.id'.sub ((Function.HasTemperateGrowth.const t).mul hu)

theorem lineSamplingInverse_temperate (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    Function.HasTemperateGrowth (lineSamplingInverse u t) := by
  let b := (lineSamplingGenerator_compact u hu hcompact B hB hb t ht).toSchwartzMap
    (lineSamplingGenerator_contDiff u hu hc B hB hb t ht)
  have heq : lineSamplingInverse u t=fun y => y-t*b y := by
    funext y
    have hh := lineSampling_inverse_apply u hu B hB hb t y
    change lineSamplingInverse u t y-t*u (lineSamplingInverse u t y)=y at hh
    have hb' : b y = -u (lineSamplingInverse u t y) := by
      change -u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y)=_
      rw [lineSamplingInverse_eq u hu B hB hb t ht]
    rw [hb']
    linarith
  rw [heq]
  exact Function.HasTemperateGrowth.id'.sub
    ((Function.HasTemperateGrowth.const t).mul b.hasTemperateGrowth)

theorem lineSamplingInverse_antilipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    AntilipschitzWith 2 (lineSamplingInverse u t) :=
  (lineSampling_lipschitz u hu t ht).to_rightInverse
    (lineSampling_inverse_apply u hu B hB hb t)

def lineSamplingSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (t : ℝ) (ht : |t|≤1/2) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (lineSampling_temperate u hc hcompact t)
    (lineSampling_antilipschitz u hu t ht)

def lineSamplingInverseSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (lineSamplingInverse_temperate u hu hc hcompact B hB hb t ht)
    (lineSamplingInverse_antilipschitz u hu B hB hb t ht)

@[simp] theorem lineSamplingSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingSchwartz u hu hc hcompact t ht f y=f (lineSampling u t y) := rfl

@[simp] theorem lineSamplingInverseSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f y=
      f (lineSamplingInverse u t y) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineSamplingPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total Schwartz paths for short-time sampling. Outside the interval
needed in the proof the paths are extended by the identity. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u)
  (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineDirectionSchwartz : SchwartzMap ℝ ℂ :=
  (hcompact.toSchwartzMap hc).postcompCLM Complex.ofRealCLM

@[simp] theorem lineDirectionSchwartz_apply (y : ℝ) :
    lineDirectionSchwartz u hc hcompact y=(u y:ℂ) := rfl

def lineSamplingPath (s : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  if hs : |s|≤1/2 then lineSamplingSchwartz u hu hc hcompact s hs f else f

def lineSamplingInversePath (s : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  if hs : |s|≤1/2 then lineSamplingInverseSchwartz u hu hc hcompact B hB hb s hs f else f

def lineSamplingTangent (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -lineSchwartzProduct (lineDirectionSchwartz u hc hcompact)
    (lineSamplingSchwartz u hu hc hcompact t ht (schwartzDerivative 1 f))

def lineSamplingInverseTangent (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
    (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingStrongDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 derivatives of the actual sampling paths. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzDerivativeBound (f : SchwartzMap ℝ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (schwartzDerivative 1 f)

theorem lineSchwartzDerivativeBound_nonneg (f : SchwartzMap ℝ ℂ) :
    0≤lineSchwartzDerivativeBound f := apply_nonneg _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineSamplingL2Path
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded L2 sampling paths and their agreement with the Schwartz paths. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineSamplingL2Path (s : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  if hs : |s|≤1/2 then lineCompositionL2 (lineSampling u s)
    (lineSampling_lipschitz u hu s hs).continuous.measurable (lineSampling_antilipschitz u hu s hs)
  else ContinuousLinearMap.id ℂ _

def lineSamplingInverseL2Path (s : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  if hs : |s|≤1/2 then lineCompositionL2 (lineSamplingInverse u s)
    (lineSamplingInverse_space_lipschitz u hu B hB hb s hs).continuous.measurable
    (lineSamplingInverse_antilipschitz u hu B hB hb s hs)
  else ContinuousLinearMap.id ℂ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConjugationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the strong conjugation derivative with a uniform bound. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineConjugationL2 (m : SchwartzMap ℝ ℂ) (s : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineSamplingL2Path u hu s).comp
    ((lineL2Projection m 1 (by norm_num)).comp (lineSamplingInverseL2Path u hu B hB hb s))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable common envelope for bounded displacements of a line
Schwartz function, used to pass to nonsmooth directions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzDecayConstant (f : SchwartzMap ℝ ℂ) : ℝ :=
  4*(Finset.Iic (2,0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_CompactDirectionCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs of bounded Lipschitz directions, normalized to
preserve the exact Lipschitz constant one. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def directionTent (R y : ℝ) : ℝ := max (1-|y|/R) 0

theorem directionTent_nonneg (R y : ℝ) : 0≤directionTent R y := le_max_right _ _

theorem directionTent_le_one (R : ℝ) (hR : 0<R) (y : ℝ) : directionTent R y≤1 := by
  apply max_le
  · have := div_nonneg (abs_nonneg y) hR.le
    linarith
  · norm_num

theorem directionTent_zero (R : ℝ) (hR : 0<R) (y : ℝ) (hy : R≤|y|) :
    directionTent R y=0 := by
  apply max_eq_right
  have hh : 1≤|y|/R := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hy)
  linarith

theorem directionTent_difference (R : ℝ) (hR : 0<R) (x y : ℝ) :
    |directionTent R x-directionTent R y|≤|x-y|/R := by
  have hh := abs_max_sub_max_le_abs (1-|x|/R) (1-|y|/R) 0
  calc
    _ ≤ |(1-|x|/R)-(1-|y|/R)| := hh
    _ = |(|x|-|y|)|/R := by
      rw [show (1-|x|/R)-(1-|y|/R)=-( (|x|-|y|)/R) by ring,abs_neg,abs_div,abs_of_pos hR]
    _ ≤ |x-y|/R := div_le_div_of_nonneg_right (abs_abs_sub_abs_le x y) hR.le

def compactDirectionCutoff (u : ℝ → ℝ) (R : ℝ) (y : ℝ) : ℝ :=
  (R/(R+1))*u y*directionTent R y

theorem compactDirectionCutoff_compact (u : ℝ → ℝ) (R : ℝ) (hR : 0<R) :
    HasCompactSupport (compactDirectionCutoff u R) := by
  apply HasCompactSupport.intro (isCompact_Icc (a:= -R) (b:=R))
  intro y hy
  have habs : R < |y| := lt_of_not_ge (fun hh => hy (abs_le.mp hh))
  simp only [compactDirectionCutoff,directionTent_zero R hR y habs.le,mul_zero]

theorem compactDirectionCutoff_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hb : ∀ x, |u x|≤1) (R : ℝ) (hR : 0<R) :
    LipschitzWith 1 (compactDirectionCutoff u R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |compactDirectionCutoff u R x-compactDirectionCutoff u R y|≤1*|x-y|
  have ha : 0≤R/(R+1) := by positivity
  have hu' : |u x-u y|≤|x-y| := by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hu.dist_le_mul x y
  have he : compactDirectionCutoff u R x-compactDirectionCutoff u R y=
      (R/(R+1))*(u x*(directionTent R x-directionTent R y)+(u x-u y)*directionTent R y) := by
    simp only [compactDirectionCutoff]
    ring
  rw [he,abs_mul,abs_of_nonneg ha]
  calc
    _ ≤ (R/(R+1))*(|u x*(directionTent R x-directionTent R y)|+|(u x-u y)*directionTent R y|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) ha
    _ = (R/(R+1))*(|u x| *|directionTent R x-directionTent R y|+
        |u x-u y| *directionTent R y) := by rw [abs_mul,abs_mul,abs_of_nonneg (directionTent_nonneg R y)]
    _ ≤ (R/(R+1))*(1*(|x-y|/R)+|x-y| *1) := by
      apply mul_le_mul_of_nonneg_left _ ha
      exact add_le_add
        (mul_le_mul (hb x) (directionTent_difference R hR x y) (abs_nonneg _) (by norm_num))
        (mul_le_mul hu' (directionTent_le_one R hR y) (directionTent_nonneg R y) (abs_nonneg _))
    _ = 1*|x-y| := by field_simp [hR.ne',ne_of_gt (show 0<R+1 by linarith)]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive compact mollification on the line preserves the size and
Lipschitz bounds needed for the sampling maps. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution ContDiff
namespace LipschitzHilbert.PacketRepresentation

def lineMollification (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) : SchwartzMap ℝ ℝ :=
  ((phi.hasCompactSupport_normed (μ:=volume)).convolution
    (L:=ContinuousLinearMap.lsmul ℝ ℝ) hcompact).toSchwartzMap
      ((phi.hasCompactSupport_normed (μ:=volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed hf.locallyIntegrable)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SmoothDirectionApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact smooth approximants of a bounded Lipschitz direction. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

def lineDirectionMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1/((n:ℝ)+1))/2
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0<1/((n:ℝ)+1) := by positivity
    linarith

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hb : ∀ x, |u x|≤1)

def smoothDirectionApprox (n : ℕ) : SchwartzMap ℝ ℝ :=
  lineMollification (lineDirectionMollifier n) (compactDirectionCutoff u ((n:ℝ)+1))
    ((compactDirectionCutoff_lipschitz u hu hb ((n:ℝ)+1) (by positivity)).continuous.integrable_of_hasCompactSupport
      (compactDirectionCutoff_compact u ((n:ℝ)+1) (by positivity)))
    (compactDirectionCutoff_compact u ((n:ℝ)+1) (by positivity))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingKernelCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved L2 operator commutator is the actual convolution/sampling
difference, with its squared integral bound. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineSamplingKernelCommutator (m : SchwartzMap ℝ ℂ) (u : ℝ → ℝ) (t : ℝ)
    (f : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  lineConvolution (lineProjectionKernel m 1 (by norm_num))
      (fun z => f (lineSampling u t z)) y-
    lineConvolution (lineProjectionKernel m 1 (by norm_num)) f (lineSampling u t y)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingMihlin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiberwise Mihlin control of the actual planar sampling commutator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def scalarVerticalSlice (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (verticalLine_temperate x) (verticalLine_antilipschitz x) f

@[simp] theorem scalarVerticalSlice_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    scalarVerticalSlice f x y=f (x,y) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionPVLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution commutes with the limit of symmetric truncations
on Schwartz inputs. Domination comes from the global derivative bound and
does not use a full-frequency Hilbert estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def principalValueProfileCommutator (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel q W center) (productSlopePrincipalValue u R f)-
    productSlopePrincipalValue u R (schwartzVerticalProjection q W center f)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SignedPVCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform actual signed-annular principal-value commutators for the
Euclidean Lipschitz slope fields in the target theorem. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def signedPVCommutatorConstant : ℝ :=
  32*lineCommutatorNormConstant*signedAnnularMihlinConstant

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition and multiplier absorption for bounded inputs, before any
L2 membership of the input is known. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_eq_verticalProfile (p : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (lineProjectionKernel p W hW.ne' : ℝ → ℂ)=verticalProfileKernel p W 0 := by
  funext x
  rw [lineProjectionKernel_eq_scaled p W hW,scaledSchwartzKernel_apply]
  simp only [verticalProfileKernel,modulatedTimeKernel,zero_mul,
    Real.fourierChar.map_zero_eq_one,one_smul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedVerticalMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The multiplier is linear in its Schwartz symbol on bounded measurable
inputs. The input need not have finite L2 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_add (p q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    lineProjectionKernel (p+q) W hW=lineProjectionKernel p W hW+lineProjectionKernel q W hW := by
  simp only [lineProjectionKernel,dilatedSlopeWindow,map_add,FourierTransform.fourierInv_add]

theorem lineProjectionKernel_smul (p : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) (c : ℂ) :
    lineProjectionKernel (c • p) W hW=c • lineProjectionKernel p W hW := by
  simp only [lineProjectionKernel,dilatedSlopeWindow,map_smul,FourierTransform.fourierInv_smul]

def boundedVerticalMultiplierLM (W : ℝ) (hW : 0<W) (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) where
  toFun p := verticalConvolution (verticalProfileKernel p W 0) f
  map_add' p q := by
    funext z
    simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,lineProjectionKernel_add]
    change (∫ t, (lineProjectionKernel p W hW.ne' t+lineProjectionKernel q W hW.ne' t)*
      f (z.1,z.2-t))=_
    simp_rw [add_mul]
    exact integral_add
      (lineConvolution_integrand_of_bounded _ _ (lineProjectionKernel p W hW.ne').integrable
        (hfm.comp (by fun_prop)) B (fun y => hf _) z.2)
      (lineConvolution_integrand_of_bounded _ _ (lineProjectionKernel q W hW.ne').integrable
        (hfm.comp (by fun_prop)) B (fun y => hf _) z.2)
  map_smul' c p := by
    funext z
    simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,lineProjectionKernel_smul]
    change (∫ t, (c*lineProjectionKernel p W hW.ne' t)*f (z.1,z.2-t))=
      c*(∫ t, lineProjectionKernel p W hW.ne' t*f (z.1,z.2-t))
    simp_rw [mul_assoc]
    exact integral_const_mul c _

@[simp] theorem boundedVerticalMultiplierLM_apply (W : ℝ) (hW : 0<W) (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) (p : SchwartzMap ℝ ℂ) :
    boundedVerticalMultiplierLM W hW f hfm B hf p=
      verticalConvolution (verticalProfileKernel p W 0) f := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularEnlargement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed symmetric enlarged annular cutoff is one on every nonzero
piece of the concrete annular resolution. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyEnlarged : SchwartzMap ℝ ℂ :=
  reassemblyOuter+conjugateReflectedCutoff reassemblyOuter

@[simp] theorem reassemblyEnlarged_apply (x : ℝ) :
    reassemblyEnlarged x=reassemblyOuter x+reassemblyOuter (-x) := by
  simp only [reassemblyEnlarged,add_apply,conjugateReflectedCutoff_apply,
    reassemblyOuter_apply,Complex.conj_ofReal]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBoundedSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform synthesis of actual annular projections of a bounded function
once those individual projections have finite square energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def annularBoundedComponent (N : ℕ) (F : (ℝ×ℝ) → ℂ) (i : Fin (2*N+1)) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N i) 0) F

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVCommutatorSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed commutator estimate controls the square sum of individual
actual annular PV commutators without assuming a full PV L2 operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def annularProfile (N : ℕ) (i : Fin (2*N+1)) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N i)
    (reassemblyScale_pos N i).ne'

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVFromNarrow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite frequency covering converts the narrow-band
hypothesis into uniform bounds for all dilated annular inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def fixedAnnulus : Set ℝ := {x | 1≤|x| ∧ |x|≤2}

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVPartialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite annular output has a uniform L2 bound, derived directly
from the annular input estimates and actual signed PV commutators. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def annularPVBoundConstant (D : ℝ) : ℝ :=
  Real.sqrt 12*Real.sqrt (2*(signedPVCommutatorConstant^2+12*D^2))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ScalarBandDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar basic and reverse-disparity diagonal bounds, without
projecting the test or imposing a spectrum on amplitude slices. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

def scalarVector (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : EuclideanSpace ℂ Unit :=
  PiLp.single 2 () (f z)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CenteredBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive annular cutoff is exactly a centered cutoff at the same
width, so both scalar endpoint estimates apply to the original input. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

def centeredPositiveCutoff (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  p.compSubConstCLM ℂ (-(3/2:ℝ))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionPowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Markov estimates and the actual large/small amplitude splitting used
for interpolation of line convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def highAmplitude (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := {x | t≤‖f x‖}.indicator f

def lowAmplitude (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := {x | ‖f x‖<t}.indicator f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertFiniteSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth finite Hilbert multiplier has a uniform bound obtained
from an exact telescoping identity, independently of the scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertFrequencySign (x : ℝ) : ℂ := if 0≤x then 1 else -1

def hilbertFiniteSymbol (N : ℕ) (L : ℝ) (hL : 0<L) : SchwartzMap ℝ ℂ :=
  ∑ j : Fin N, dilatedSlopeWindow hilbertAnnularSymbol (L/(2:ℝ)^j.val)
    (ne_of_gt (div_pos hL (pow_pos (by norm_num) j.val)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution duality for an integrable input and a bounded test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def reverseLineConvolution (K g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, K t*g (x+t)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedBandStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strong L2 control of the actual positive-band pairing,
localized in a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def horizontalStrip (l r : ℝ) : Set (ℝ×ℝ) := {z | z.1∈Icc l r}

theorem horizontalStrip_measurable (l r : ℝ) : MeasurableSet (horizontalStrip l r) :=
  measurable_fst (measurableSet_Icc)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VariableEndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable factor between one half and one may change both sharp
endpoints. The resulting kernel error has a uniform integrable majorant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def endpointErrorMajorant (epsilon R t : ℝ) : ℝ :=
  6*timeErrorEnvelope (epsilon/2) t+6*timeErrorEnvelope (R/2) t

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_HorizontalStripCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete partition into horizontal strips; their one-cell
extensions have uniformly bounded overlap and contain short translates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def horizontalCell (d : ℝ) (j : ℤ) : Set ℝ := Ico ((j:ℝ)*d) (((j:ℝ)+1)*d)
def horizontalEnlargement (d : ℝ) (j : ℤ) : Set ℝ := Icc (((j:ℝ)-1)*d) (((j:ℝ)+2)*d)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ConditionalUnitDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 truncation bounds for unit vector fields with a fixed small
Lipschitz constant, obtained by the finite orthogonal direction cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

def chartTruncation (d : Plane) (v : Plane → Plane) (epsilon R : ℝ)
    (f : SchwartzMap Plane ℂ) (x : Plane) : ℂ :=
  let z := planeCoordinates.symm (directionChart d x)
  productSymmetricTruncation
    (fun z => clippedChartSlope (chartField d v) (planeCoordinates z))
    (epsilon*chartDenominator (chartField d v) (planeCoordinates z))
    (R*chartDenominator (chartField d v) (planeCoordinates z)) (chartSchwartz d f) z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DirectionDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal-Lipschitz dilation and its exact L2 scaling in the plane. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem memLp_two_comp_smul_iff (f : Plane → ℂ) (hf : Continuous f)
    (L : ℝ) (hL : L≠0) :
    MemLp (fun x => f (L • x)) 2 volume ↔ MemLp f 2 volume := by
  have hc : Continuous (fun x => f (L • x)) := hf.comp (by fun_prop)
  constructor
  · intro h
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
      ((integrable_comp_smul_iff volume (fun x => ‖f x‖^2) hL).mp
        ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp h))
  · intro h
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      ((integrable_comp_smul_iff volume (fun x => ‖f x‖^2) hL).mpr
        ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp h))

def rescaleSchwartz (L : ℝ) (hL : L≠0) (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ Plane L⁻¹ (inv_ne_zero hL)).toContinuousLinearEquiv f

@[simp] theorem rescaleSchwartz_apply (L : ℝ) (hL : L≠0) (f : SchwartzMap Plane ℂ) (x : Plane) :
    rescaleSchwartz L hL f x=f (L⁻¹ • x) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleCoverSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite selection with the exact length/eccentricity priority in the
Lacey--Li covering algorithm. The removal predicate will be instantiated
by containment in the auxiliary maximal-function level set. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {ι : Type*}

def rectangleRemaining [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i : ι) : Finset ι := by
  classical
  exact stock.filter (fun j => j≠i ∧ ¬blocked (insert i previous) j)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ProjectionGroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite maximal-length grouping of overlapping projected
popularity sets used in the far-angle estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

def projectionBlocked (P : ι → Set ℝ) (s : Finset ι) (j : ι) : Prop :=
  ∃ i ∈ s, (P i ∩ P j).Nonempty

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_UniformNearSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A universal near-angle selected overlap bound, with all directional
and aspect-ratio choices discharged. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

abbrev selectionDilation : ℝ := 265
abbrev selectionThreshold : ℝ≥0∞ := ENNReal.ofReal (1/1048576 : ℝ)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectanglePairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered overlap sums for an actual finite selection list. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

def orderedPairSum (f : ι → ι → ℝ≥0∞) : List ι → ℝ≥0∞
  | [] => 0
  | i::l => (∑ j ∈ l.toFinset, f i j)+orderedPairSum f l

def previousPairSum (f : ι → ι → ℝ≥0∞) (p : Finset ι) (l : List ι) : ℝ≥0∞ :=
  ∑ j ∈ l.toFinset, ∑ i ∈ p, f i j

end LipschitzHilbert

end

end OAI
end


