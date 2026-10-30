-- Prove2me | Definitions.Def_OAIQ090A002
-- name    : OAIQ090A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T19:36:49.243536+00:00
-- url     : https://prove2.me/theorems/71c35572-8b34-4e2e-9b6e-e9d7abffb92c
-- title:
--   Definitions bundle OAIQ090A002 of the split of OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 438 declarations of OpenAI's Lean: 276 definitions, 8 inductive types or structures and 154 theorems. The definitions and types are `OAI.LipschitzHilbert.PacketLatticeData.packetL2`, `OAI.LipschitzHilbert.PacketLatticeData.physicalMaskedBand`, `OAI.LipschitzHilbert.PacketLatticeData.physicalParentStoppedBoundAt`, `OAI.LipschitzHilbert.PacketLatticeData.recordedSizeTests`, `OAI.LipschitzHilbert.PacketLatticeData.referenceAlt`, `OAI.LipschitzHilbert.PacketLatticeData.referenceLabelsEquiv`, `OAI.LipschitzHilbert.PacketLatticeData.referenceSelector`, `OAI.LipschitzHilbert.PacketLatticeData.referenceTreeTop`, `OAI.LipschitzHilbert.PacketLatticeData.selectedCells`, `OAI.LipschitzHilbert.PacketLatticeData.selectedCoefficients`, `OAI.LipschitzHilbert.PacketLatticeData.selectedMultipliers`, `OAI.LipschitzHilbert.PacketLatticeData.selectedPackets`, `OAI.LipschitzHilbert.PacketLatticeData.selectedPhysicalPrefix`, `OAI.LipschitzHilbert.PacketLatticeData.selectedReferenceEquiv`, `OAI.LipschitzHilbert.PacketLatticeData.sizeDeletionRecords`, `OAI.LipschitzHilbert.PacketLatticeData.sizeSelectionRecords`, `OAI.LipschitzHilbert.PacketLatticeData.unsignedSizeTestEnergy`, `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry.numerics`, `OAI.LipschitzHilbert.PacketRepresentation.BandToFullInput`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVComm`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial`, `OAI.LipschitzHilbert.PacketRepresentation.bandL2Operator`, `OAI.LipschitzHilbert.PacketRepresentation.bandL2Pairing`, `OAI.LipschitzHilbert.PacketRepresentation.coefficient`, `OAI.LipschitzHilbert.PacketRepresentation.compactMollification`, `OAI.LipschitzHilbert.PacketRepresentation.comparableDerivativePiece`, `OAI.LipschitzHilbert.PacketRepresentation.convolutionProfile`, `OAI.LipschitzHilbert.PacketRepresentation.dyadicParaproduct`, `OAI.LipschitzHilbert.PacketRepresentation.endpointErrorOperator`, `OAI.LipschitzHilbert.PacketRepresentation.endpointKernelError`, `OAI.LipschitzHilbert.PacketRepresentation.envelopeSeminorm`, `OAI.LipschitzHilbert.PacketRepresentation.finiteDiagonalBandL1`, `OAI.LipschitzHilbert.PacketRepresentation.finiteNormalizedPacketEquiv`, `OAI.LipschitzHilbert.PacketRepresentation.finiteNormalizedPacketLattice`, `OAI.LipschitzHilbert.PacketRepresentation.finitePartitionedBandL1`, `OAI.LipschitzHilbert.PacketRepresentation.highLowPiece`, `OAI.LipschitzHilbert.PacketRepresentation.highLowRow`, `OAI.LipschitzHilbert.PacketRepresentation.horizontalTruncatedHilbert`, `OAI.LipschitzHilbert.PacketRepresentation.kernelConvolution`, `OAI.LipschitzHilbert.PacketRepresentation.kernelPairing` and 244 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LipschitzHilbert_Estimates_BoxVariationWeights`, `LipschitzHilbert_Estimates_ClippedSlopeBox`, `LipschitzHilbert_Estimates_CompactMollification`, `LipschitzHilbert_Estimates_ComparableDerivativeSum`, `LipschitzHilbert_Estimates_FrozenSlopeMultiplier`, `LipschitzHilbert_Estimates_HorizontalHilbertLp`, `LipschitzHilbert_Estimates_OrderDistribution`, `LipschitzHilbert_Estimates_PlanarChangeVariables`, `LipschitzHilbert_Estimates_ProductSlopePrincipalValue`, `LipschitzHilbert_Estimates_ProductSlopePrincipalValueBound`, `LipschitzHilbert_Estimates_RealFiniteVariation`, `LipschitzHilbert_Estimates_ReferenceAnalysis`, `LipschitzHilbert_Estimates_ReferenceChart`, `LipschitzHilbert_Estimates_ReferenceException`, `LipschitzHilbert_Estimates_ReferenceFamilyException`, `LipschitzHilbert_Estimates_ReferenceSynthesis`, `LipschitzHilbert_Estimates_RelativeExitEnergy`, `LipschitzHilbert_Estimates_RelativeMartingaleExits`, `LipschitzHilbert_Estimates_ScalarRestrictedStrong`, `LipschitzHilbert_Estimates_SharpTimeMoment`, `LipschitzHilbert_Estimates_ShearedLatticePeriodization`, `LipschitzHilbert_Estimates_ShiftedBlocks`, `LipschitzHilbert_Estimates_ShortL2Operator`, `LipschitzHilbert_Estimates_ShortSlopeLpRealization`, `LipschitzHilbert_Estimates_ShortSlopeOperator`, `LipschitzHilbert_Estimates_SlopeBoxHorizontalRescale`, `LipschitzHilbert_Estimates_SmoothCarlesonEnergy`, `LipschitzHilbert_Estimates_SmoothCarlesonSynthesis`, `LipschitzHilbert_Estimates_StripSubdivision`, `LipschitzHilbert_Estimates_TopAreaAverage`, `LipschitzHilbert_Estimates_TopDyadicDomination`, `LipschitzHilbert_Estimates_TopWeightIntegral`, `LipschitzHilbert_Estimates_UniformTranslatedProfileBounds`, `LipschitzHilbert_Estimates_VariableEndpointOperator`, `LipschitzHilbert_Estimates_WeightedOrder`, `LipschitzHilbert_Estimates_WeightedReferenceVariation`, `LipschitzHilbert_Estimates_WitnessInterval`, `LipschitzHilbert_Fourier_AnnularBoundedSynthesis`, `LipschitzHilbert_Fourier_AnnularPVCommutatorSquare`, `LipschitzHilbert_Fourier_AnnularPVReconstruction`, `LipschitzHilbert_Fourier_BandL2Pairing`, `LipschitzHilbert_Fourier_BoundedFrequencyMultiplier`, `LipschitzHilbert_Fourier_GlobalAnnularVariation`, `LipschitzHilbert_Fourier_GlobalBandOperator`, `LipschitzHilbert_Fourier_KernelAverageEnergy`, `LipschitzHilbert_Fourier_KernelPairing`, `LipschitzHilbert_Fourier_L1FrequencyMultiplier`, `LipschitzHilbert_Fourier_LineDyadicTelescoping`, `LipschitzHilbert_Fourier_LineHighLowSum`, `LipschitzHilbert_Fourier_LineLowHighSum`, `LipschitzHilbert_Fourier_LineTiling`, `LipschitzHilbert_Fourier_LocalizedBandOperator`, `LipschitzHilbert_Fourier_LocalizedBandStrong`, `LipschitzHilbert_Fourier_NormalizedConvolutionForm`, `LipschitzHilbert_Fourier_NormalizedSymbolFormL1`, `LipschitzHilbert_Fourier_PVCommutatorSymbolLinearity`, `LipschitzHilbert_Fourier_PartitionedAnnularFormL1`, `LipschitzHilbert_Fourier_PartitionedBandFormL1`, `LipschitzHilbert_Fourier_PhysicalPlanarJet`, `LipschitzHilbert_Fourier_PlanarCovariantJet`, `LipschitzHilbert_Fourier_PlanarModulatedJet`, `LipschitzHilbert_Fourier_PlanarPositiveConvolution`, `LipschitzHilbert_Fourier_PlanarSchwartzInversion`, `LipschitzHilbert_Fourier_PlanarSchwartzSlice`, `LipschitzHilbert_Fourier_PlanarSliceFourier`, `LipschitzHilbert_Fourier_PlanarSliceFourierBasic`, `LipschitzHilbert_Fourier_PlanarSliceFourierDerivative`, `LipschitzHilbert_Fourier_ProductPVLinear`, `LipschitzHilbert_Fourier_PublishedBandReductionInput`, `LipschitzHilbert_Fourier_RectangularFrequencyCutoff`, `LipschitzHilbert_Fourier_ReferenceLineCount`, `LipschitzHilbert_Fourier_ScaledFrequencyWindows`, `LipschitzHilbert_Fourier_SchwartzDilation`, `LipschitzHilbert_Fourier_SchwartzVerticalProjection`, `LipschitzHilbert_Fourier_SharpBandMeasurableRestricted`, `LipschitzHilbert_Fourier_SharpKernelComparison`, `LipschitzHilbert_Fourier_SharpKernelSymmetrization`, `LipschitzHilbert_Fourier_SharpVerticalCommutator`, `LipschitzHilbert_Fourier_VerticalBinLpEnergy`, `LipschitzHilbert_Fourier_VerticalBinLpReconstruction`, `LipschitzHilbert_Fourier_VerticalConvolutionL1`, `LipschitzHilbert_Fourier_VerticalConvolutionL2`, `LipschitzHilbert_Fourier_VerticalConvolutionLp`, `LipschitzHilbert_Fourier_VerticalL2Projection`, `LipschitzHilbert_Fourier_VerticalProjectionAlgebra`, `LipschitzHilbert_Fourier_VerticalSamplingGeometry`, `LipschitzHilbert_Geometry_ClippedEnclosure`, `LipschitzHilbert_Geometry_DyadicNearbyInputs`, `LipschitzHilbert_Geometry_FarSlabGeometry`, `LipschitzHilbert_Geometry_FatEnclosure`, `LipschitzHilbert_Geometry_FiniteTransverseDirections`, `LipschitzHilbert_Geometry_LaceyLiSelectionCover`, `LipschitzHilbert_Geometry_LocalMinimaSelection`, `LipschitzHilbert_Geometry_NearRectangleLine`, `LipschitzHilbert_Geometry_NearRectangleSection`, `LipschitzHilbert_Geometry_PacketDataFarGram`, `LipschitzHilbert_Geometry_PacketDataSelectionRecords`, `LipschitzHilbert_Geometry_PacketDataSizeSelectionEnergy`, `LipschitzHilbert_Geometry_PositiveRectangleAuxiliary`, `LipschitzHilbert_Geometry_RectangleArea`, `LipschitzHilbert_Geometry_RectangleCountingEnergy`, `LipschitzHilbert_Geometry_RectangleCoverSelection`, `LipschitzHilbert_Geometry_RectangleDilation`, `LipschitzHilbert_Geometry_RectanglePairEnergy`, `LipschitzHilbert_Geometry_RectangleProjection`, `LipschitzHilbert_Geometry_SelectedFarFamily`, `LipschitzHilbert_Geometry_SlopeRectangle`, `LipschitzHilbert_Geometry_VerticalRectangle`, `LipschitzHilbert_Packets_AnalyzedReplacement`, `LipschitzHilbert_Packets_AnnularPacketGeometry`, `LipschitzHilbert_Packets_ConvolutionPacketProfile`, `LipschitzHilbert_Packets_FiniteNormalizedPacketLattice`, `LipschitzHilbert_Packets_NormalizedPacketLattice`, `LipschitzHilbert_Packets_PacketBoxes`, `LipschitzHilbert_Packets_PacketConvolution`, `LipschitzHilbert_Packets_PacketDataDeletionForest`, `LipschitzHilbert_Packets_PacketDataDensityJetNormalization`, `LipschitzHilbert_Packets_PacketDataJetBudget`, `LipschitzHilbert_Packets_PacketDataMaskedBand`, `LipschitzHilbert_Packets_PacketDataParentStoppedBound`, `LipschitzHilbert_Packets_PacketDataReferenceConditions`, `LipschitzHilbert_Packets_PacketDataReferenceCross`, `LipschitzHilbert_Packets_PacketDataSelectedGeometry`, `LipschitzHilbert_Packets_PacketDataSelectedPackets`, `LipschitzHilbert_Packets_PacketDataSelectedReference`, `LipschitzHilbert_Packets_PacketDataSelectedScale`, `LipschitzHilbert_Packets_PacketDataSelectedSum`, `LipschitzHilbert_Packets_PacketDataSizeTest`, `LipschitzHilbert_Packets_PacketDataStoppingPrefix`, `LipschitzHilbert_Packets_PacketDataTreeSize`, `LipschitzHilbert_Packets_PacketFrequencyInputL1`, `LipschitzHilbert_Packets_PacketReferenceSpectrum`, `LipschitzHilbert_Packets_PhysicalPlanarPacket`, `LipschitzHilbert_Packets_PlanarFrequencyPackets`, `LipschitzHilbert_Packets_PlanarPacketFamily`, `LipschitzHilbert_Packets_ReferencePacketFamily`, `LipschitzHilbert_Packets_ScaledPlanarPacket`, `LipschitzHilbert_Packets_ShortPacketBoxes`, `LipschitzHilbert_Packets_SourceFrozenCellIntegral`, `LipschitzHilbert_Packets_SourceFrozenCoefficientEnergy`, `LipschitzHilbert_Packets_SourceFrozenLongInterval`, `LipschitzHilbert_Packets_SourceLabeledPacketRestriction`, `LipschitzHilbert_Packets_SourceLatticePacket`, `LipschitzHilbert_Packets_SourcePacketDensity`, `LipschitzHilbert_Packets_SourcePacketOwnDensity`, `LipschitzHilbert_Packets_SourcePacketShortSum`, `LipschitzHilbert_Packets_SourcePacketSpectrum`, `LipschitzHilbert_Packets_SourceSelectorConcentrationActive`, `LipschitzHilbert_Packets_SourceSelectorDerivative`, `LipschitzHilbert_Packets_SourceSupportedCovariantRescale`, `LipschitzHilbert_Packets_SourceSupportedLatticeData`, `LipschitzHilbert_Packets_SourceSupportedPacketData`, `LipschitzHilbert_Packets_SourceSupportedRawRescale`, `LipschitzHilbert_Packets_TopRawPacketData`, `LipschitzHilbert_Phase_FiniteDiagonalBandL1`, `LipschitzHilbert_Phase_GraphPredictionFactor`, `LipschitzHilbert_Phase_PlanarSliceFourierAngular`, `LipschitzHilbert_Phase_ScalarBandDiagonal`, `LipschitzHilbert_Phase_SourceAngularFrozenIntegration`, `LipschitzHilbert_Phase_SourceAngularOrdinaryTree`, `LipschitzHilbert_Phase_SourceAngularTreeSplit`, `LipschitzHilbert_Phase_SourceLabeledAngularErrorData`, `LipschitzHilbert_Phase_SourcePredictionValues`, `LipschitzHilbert_Trees_FourGridBandErrors`, `LipschitzHilbert_Trees_SourceAssignedStoppedBound`, `LipschitzHilbert_Trees_SourceCarrierFreeEnvelope`, `LipschitzHilbert_Trees_SourceCenteredCoefficient`, `LipschitzHilbert_Trees_SourceCenteredMaskedVariation`, `LipschitzHilbert_Trees_SourceCenteredSquareBound`, `LipschitzHilbert_Trees_SourceCoordinateSpectrum`, `LipschitzHilbert_Trees_SourceCrossDerivative`, `LipschitzHilbert_Trees_SourceDensityKeepers`, `LipschitzHilbert_Trees_SourceDensitySpatialCost`, `LipschitzHilbert_Trees_SourceInhabitedLabels`, `LipschitzHilbert_Trees_SourceLabeledActiveReference`, `LipschitzHilbert_Trees_SourceLabeledCrossResidual`, `LipschitzHilbert_Trees_SourceLabeledMainSlots`, `LipschitzHilbert_Trees_SourceLabeledMaskedSlots`, `LipschitzHilbert_Trees_SourceLabeledMultiscaleEnergy`, `LipschitzHilbert_Trees_SourceLabeledPositiveSplit`, `LipschitzHilbert_Trees_SourceLabeledRawEnvelope`, `LipschitzHilbert_Trees_SourceLabeledSelectedVariation`, `LipschitzHilbert_Trees_SourceLabeledStoppingVariation`, `LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope`, `LipschitzHilbert_Trees_SourceLabeledVariationSplit`, `LipschitzHilbert_Trees_SourceLatticeGeometry`, `LipschitzHilbert_Trees_SourceLatticeRawData`, `LipschitzHilbert_Trees_SourceLatticeSpectrum`, `LipschitzHilbert_Trees_SourceLengthRestriction`, `LipschitzHilbert_Trees_SourceLongCellMask`, `LipschitzHilbert_Trees_SourceLongPrefixes`, `LipschitzHilbert_Trees_SourceLongTreeSplit`, `LipschitzHilbert_Trees_SourceMarkedIntegral`, `LipschitzHilbert_Trees_SourceMaskGeometry`, `LipschitzHilbert_Trees_SourceMaskedPhysicalMoments`, `LipschitzHilbert_Trees_SourceMaskedSynthesis`, `LipschitzHilbert_Trees_SourceMaskedVariationTail`, `LipschitzHilbert_Trees_SourceOrdinaryTreeEstimate`, `LipschitzHilbert_Trees_SourceParameters`, `LipschitzHilbert_Trees_SourcePhysicalCoefficient`, `LipschitzHilbert_Trees_SourcePhysicalPositiveScale`, `LipschitzHilbert_Trees_SourcePhysicalReferenceSquare`, `LipschitzHilbert_Trees_SourcePlanarKernelBound`, `LipschitzHilbert_Trees_SourcePlanarPlancherel`, `LipschitzHilbert_Trees_SourcePolarizedInterval`, `LipschitzHilbert_Trees_SourceReferenceBounds`, `LipschitzHilbert_Trees_SourceReferenceMainRestriction`, `LipschitzHilbert_Trees_SourceReferenceMask`, `LipschitzHilbert_Trees_SourceReferenceTail`, `LipschitzHilbert_Trees_SourceReproduction`, `LipschitzHilbert_Trees_SourceShearedEnvelopeEnergy`, `LipschitzHilbert_Trees_SourceShortTreeGlobal`, `LipschitzHilbert_Trees_SourceShortTreeIntegral`, `LipschitzHilbert_Trees_SourceSlottedCoefficient`, `LipschitzHilbert_Trees_SourceSlottedLattice`, `LipschitzHilbert_Trees_SourceThresholdSum`, `LipschitzHilbert_Trees_SourceTreeCellDensity`, `LipschitzHilbert_Trees_SourceTreeCellGluing`, `LipschitzHilbert_Trees_SourceTreeCells`, `LipschitzHilbert_Trees_SourceTreeSelectorError`, `LipschitzHilbert_Trees_SourceVectorPolynomial`, `LipschitzHilbert_Trees_SourceVectorSlices`, `LipschitzHilbert_Trees_SourceVerticalDemodulation`, `LipschitzHilbert_Trees_SourceWeightedEnvelopeKernel`, `LipschitzHilbert_Trees_SourceWeightedTreeMajorant`, `LipschitzHilbert_Trees_SourceWeightedTreeMaximal`, `LipschitzHilbert_Trees_SourceWhitneyGluing`, `LipschitzHilbert_Trees_SourceWhitneyIntervals`.
--
--   **Imports.** It imports the published bundle `Def_LipschitzHilbert`; the bundles `OAIQ090A000` and `OAIQ090A001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral`, `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion`, `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion`, `OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step`, `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log`, `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound`, `OAI.LipschitzHilbert.PacketRepresentation.band_projected_high`, `OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation`, `OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1`, `OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1`, `OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse`, `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal`, `OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments`, `OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments`, `OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path` and `OAI.LipschitzHilbert.exists_source_supported_grid_prediction`; the proofs of `OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral`, `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion`, `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_marked_path_bound`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square`, `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing`, `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing`, `OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step`, `OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound`, `OAI.LipschitzHilbert.PacketLatticeData.exists_universal_ordinary_model_estimate`, `OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set`, `OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery`, `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log`, `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound`, `OAI.LipschitzHilbert.PacketRepresentation.band_projected_high`, `OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy`, `OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation`, `OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1`, `OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1`, `OAI.LipschitzHilbert.PacketRepresentation.lineConjugation_derivative_bound`, `OAI.LipschitzHilbert.PacketRepresentation.lineSamplingGenerator_commutator_bound`, `OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse`, `OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported`, `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail`, `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_selector_error_family_concentration_of_supported`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate`, `OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal`, `OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments`, `OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments`, `OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path`, `OAI.LipschitzHilbert.eventually_source_grid_parameters`, `OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal`, `OAI.LipschitzHilbert.exists_source_supported_grid_prediction`, `OAI.LipschitzHilbert.laceyLiInput_proved`, `OAI.LipschitzHilbert.main`, `OAI.LipschitzHilbert.main_of_three_published_inputs`, `OAI.LipschitzHilbert.uniform_truncation` and `OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs`.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

def tiledLineGrid (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) : FiniteLineGrid where
  branching := G
  branching_pos := hG
  origin := origin + k * H
  width := H
  width_pos := hH
  depth := N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FourGridBandErrors
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radix-four meshes and the geometric error bound for each band. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def bandErrorAt (g : FiniteLineGrid) (f : ℝ → ℂ) (level i j : ℕ) (x : ℝ) : ℂ :=
  (if j < i then f x else 0) - g.scalarAverage g.lineMeasure f level x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exhaust the line by growing roots while keeping the comparison mesh
fixed. The annular variation constant is independent of the root size. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

def expandingGrid (N M : ℕ) : FiniteLineGrid where
  branching := 4
  branching_pos := by norm_num
  origin := -((4 : ℝ) ^ M) / 2
  width := (4 : ℝ) ^ M
  width_pos := by positivity
  depth := M + N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxVariationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable weights for the fixed-box variation estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def boxVariationWeight (p : ℤ × ℤ) : ℝ :=
  lineEnvelope 0 1 1 p.1 * lineEnvelope 0 1 1 p.2

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

namespace SlopeBox

/-- Normalized top coordinates, using first a translation, then the slope
shear, then the two independent dilations. -/
def normalizedCoordinates (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) : ℝ × ℝ :=
  planeDivide (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
    (slopeShear (-T.slope) (z - (T.x, T.y)))

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopDyadicDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic dilation domination for the actual decaying top weights. The
base dilation may be larger than the weight radius, as required when the
popular-rectangle argument first clips to the localization strip. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert
namespace SlopeBox

def radialDilation (T : SlopeBox) (R : ℝ) : Set (ℝ × ℝ) := {z | T.radius z ≤ R}

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact area of the orthogonal rectangles in the published input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def orthogonalCoordinates (R : Rectangle) : Plane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.subRight R.center).trans
    (R.axes.measurableEquiv.trans planeCoordinates.symm)

end LipschitzHilbert.Rectangle

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

def slopeRectangle (c : ℝ × ℝ) (s a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) : Rectangle where
  center := planeCoordinates c
  axes := slopeAxes s
  long := Real.sqrt (1+s^2)*a+|s|/Real.sqrt (1+s^2)*b
  short := b/Real.sqrt (1+s^2)
  short_pos := div_pos hb (Real.sqrt_pos.mpr (by positivity))
  short_le_long := slope_rectangle_short_le_long s a b ha hb hba

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ClippedSlopeBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal clipping before Euclidean enclosure. The width of the
clipped interval is bounded by both the testing strip and the original
dilation; no large horizontal dilation enters the long-side restriction. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.SlopeBox

def clipLeft (T : SlopeBox) (D l : ℝ) : ℝ := max l (T.x-D*T.length)
def clipRight (T : SlopeBox) (D r : ℝ) : ℝ := min r (T.x+D*T.length)
def clipLength (T : SlopeBox) (D l r : ℝ) : ℝ := T.clipRight D r-T.clipLeft D l

def clipCenter (T : SlopeBox) (D l r : ℝ) : ℝ × ℝ :=
  let x := (T.clipLeft D l+T.clipRight D r)/2
  (x,T.y+T.slope*(x-T.x))

end LipschitzHilbert.SlopeBox

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

def kernelConvolution (K f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  convolution f K (ContinuousLinearMap.mul ℝ ℂ) planeMeasure

def coefficient (f : ℝ × ℝ → ℂ) (area : ℝ) (K : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  ∫ y, f y * conj (analyzingWave area K z y) ∂planeMeasure

def packetProduct (KA KB f b g : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) : ℂ :=
  coefficient f area KB z *
    ∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure

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

def planarInverse (F : ℝ×ℝ → ℂ) (x : ℝ×ℝ) : ℂ :=
  ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) • F omega ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz restrictions to affine reference lines. This applies
to general two-variable packets, with no tensor factorization. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem planarSchwartzSlice_vertical_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ) (b s x : ℝ) :
    HasDerivAt (fun y => planarSchwartzSlice f y s x)
      (fderiv ℝ f (x,b+s*x) (0,1)) b := by
  have hline : HasDerivAt (fun y : ℝ => (x,y+s*x)) (0,1) b := by
    simpa only [add_zero,id_eq] using (hasDerivAt_const b x).prodMk
      ((hasDerivAt_id b).add_const (s*x))
  exact (f.hasFDerivAt (x,b+s*x)).comp_hasDerivAt b hline

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarCovariantJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first two covariant vertical derivatives of a general planar
Schwartz packet, restricted to a reference line. -/

noncomputable section
namespace LipschitzHilbert

def planarCovariantDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) (frequency : ℝ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  planarVerticalDerivative f-((frequency:ℂ)*Complex.I) • f

theorem planarCovariantDerivative_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale b s x : ℝ) :
    (scale:ℂ)*(deriv (fun y => planarSchwartzSlice f y s x) b-
      (frequency:ℂ)*Complex.I*planarSchwartzSlice f b s x) =
      planarSchwartzSlice ((scale:ℂ) • planarCovariantDerivative f frequency) b s x := by
  rw [(planarSchwartzSlice_vertical_hasDerivAt f b s x).deriv]
  simp only [planarSchwartzSlice_apply,smul_apply,smul_eq_mul,
    planarCovariantDerivative,sub_apply,planarVerticalDerivative_apply]

def planarCovariantJet (f : SchwartzMap (ℝ × ℝ) ℂ) (frequency scale : ℝ)
    (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then (scale:ℂ) • planarCovariantDerivative f frequency else
    (scale:ℂ) • planarCovariantDerivative ((scale:ℂ) • planarCovariantDerivative f frequency) frequency

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

def planarSliceFourier (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b : ℝ) : ℂ :=
  𝓕 (planarSchwartzSlice f b s) ω

theorem planarSliceFourier_eq (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b : ℝ) :
    planarSliceFourier f s ω b =
      ∫ x, Real.fourierChar (-(x * ω)) • f (x, b + s * x) := by
  simp only [planarSliceFourier, SchwartzMap.fourier_coe, Real.fourier_eq,
    Real.inner_apply, planarSchwartzSlice_apply]

theorem planarSliceFourier_integrable (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Integrable (planarSliceFourier f s ω) := by
  have h := (planar_slice_integrand_integrable f s ω).integral_prod_right
  rw [funext (planarSliceFourier_eq f s ω)]
  exact h

theorem planar_slice_uniform_bound (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω b x : ℝ) :
    ‖Real.fourierChar (-(x * ω)) • f (x, b + s * x)‖ ≤
      planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x := by
  rw [Circle.norm_smul]
  apply (planar_schwartz_envelope f 1 (x, b + s * x)).trans
  have hline : lineEnvelope 0 1 1 (b + s * x) ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      (lineEnvelope_antitone 0 1 (b + s * x) (show 0 ≤ 1 by omega))
  calc
    _ = (planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x) *
        lineEnvelope 0 1 1 (b + s * x) := by ring
    _ ≤ _ := mul_le_of_le_one_right
      (mul_nonneg (planarEnvelopeConstant_pos f 1).le (lineEnvelope_nonneg 0 1 1 x)) hline

theorem planarSliceFourier_continuous (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω : ℝ) :
    Continuous (planarSliceFourier f s ω) := by
  simp only [funext (planarSliceFourier_eq f s ω)]
  apply continuous_of_dominated
    (bound := fun x => planarEnvelopeConstant f 1 * lineEnvelope 0 1 1 x)
  · intro b
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall (planar_slice_uniform_bound f s ω b)
  · exact (integrable_lineEnvelope_one 0 1 (by norm_num)).const_mul _
  · exact Filter.Eventually.of_forall (fun x =>
      continuous_const.smul (f.continuous.comp (by fun_prop)))

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

theorem planarSliceFourier_fourier (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω η : ℝ) :
    𝓕 (planarSliceFourier f s ω) η = planarFourier f (ω - s * η, η) := by
  rw [Real.fourier_eq]
  simp only [Real.inner_apply]
  have hinter (b : ℝ) : Real.fourierChar (-(b * η)) • planarSliceFourier f s ω b =
      ∫ x, Real.fourierChar (-(x * ω + b * η)) • f (x, b + s * x) := by
    rw [planarSliceFourier_eq]
    change (Real.fourierChar (-(b * η)) : ℂ) •
      (∫ x, Real.fourierChar (-(x * ω)) • f (x, b + s * x)) = _
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    change Real.fourierChar (-(b * η)) •
      (Real.fourierChar (-(x * ω)) • f (x, b + s * x)) = _
    rw [← mul_smul, ← Real.fourierChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hinter]
  rw [← integral_prod_symm _ (planar_phase_integrable f s ω η)]
  have hshear := (slopeShear_measurePreserving s).integral_comp
    (slopeShear s).measurableEmbedding
    (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * (ω - s * η) + z.2 * η)) • f z)
  calc
    _ = ∫ z, Real.fourierChar (-((slopeShear s z).1 * (ω - s * η) +
        (slopeShear s z).2 * η)) • f (slopeShear s z) ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      change Real.fourierChar (-(z.1 * ω + z.2 * η)) • f (z.1, z.2 + s * z.1) =
        Real.fourierChar (-(z.1 * (ω - s * η) + (z.2 + s * z.1) * η)) •
          f (z.1, z.2 + s * z.1)
      congr 2
      ring
    _ = _ := hshear

/-- A frequency fiber missing the planar spectrum gives exact vanishing
of every affine slice Fourier coefficient at that frequency. -/
theorem planarSchwartzSlice_fourier_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (b s ω : ℝ) (hfiber : ∀ η, planarFourier f (ω - s * η, η) = 0) :
    𝓕 (planarSchwartzSlice f b s) ω = 0 := by
  have hzero : 𝓕 (planarSliceFourier f s ω) = (0 : ℝ → ℂ) := by
    funext η
    simp only [planarSliceFourier_fourier, hfiber, Pi.zero_apply]
  have h := (planarSliceFourier_continuous f s ω).fourierInv_fourier_eq
    (planarSliceFourier_integrable f s ω) (by rw [hzero]; exact integrable_zero _ _ _)
  have hb := congrFun h b
  rw [hzero] at hb
  simpa only [Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero,
    planarSliceFourier] using hb.symm

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

theorem planarSchwartzSlice_angularFourier_eq_zero
    (f : SchwartzMap (ℝ × ℝ) ℂ) (b s ω : ℝ)
    (hfiber : ∀ η, planarAngularFourier f (ω - s * η, η) = 0) :
    angularFourier (planarSchwartzSlice f b s) ω = 0 := by
  apply planarSchwartzSlice_fourier_eq_zero
  intro η
  have h := hfiber ((2 * Real.pi) * η)
  have hξ : (ω - s * ((2 * Real.pi) * η)) / (2 * Real.pi) =
      ω / (2 * Real.pi) - s * η := by field_simp [Real.pi_ne_zero]
  have hη : (2 * Real.pi * η) / (2 * Real.pi) = η := by field_simp [Real.pi_ne_zero]
  simpa only [planarAngularFourier, hξ, hη] using h

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

theorem fourier_liftPlanar (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    𝓕 (liftPlanar f) (WithLp.toLp 2 z)=planarFourier f z := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq,integral_hilbertPlane]
  unfold planarFourier
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [WithLp.prod_inner_apply,Real.inner_apply,liftPlanar,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply]
  rfl

theorem fourier_hilbertPlanar_bridge (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    𝓕 (hilbertPlanarSchwartz f) (WithLp.toLp 2 z)=planarFourier f z :=
  fourier_liftPlanar f z

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

theorem planarFourierSchwartz_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarFourierSchwartz f z=planarFourier f z :=
  fourier_hilbertPlanar_bridge f z

theorem planarFourier_inversion (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    PacketRepresentation.planarInverse (planarFourier f) x=f x := by
  have hinv : (𝓕⁻ (𝓕 (hilbertPlanarSchwartz f) : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
      SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ)=hilbertPlanarSchwartz f :=
    FourierTransform.fourierInv_fourier_eq _
  have h := congrArg (fun g : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ => g (WithLp.toLp 2 x)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, integral_hilbertPlanar_bridge] at h
  simpa only [WithLp.prod_inner_apply, Real.inner_apply, fourier_hilbertPlanar_bridge,
    hilbertPlanarSchwartz_apply, PacketRepresentation.planarInverse, mul_comm] using h

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

theorem verticalTranslation_measurePreserving (t : ℝ) :
    MeasurePreserving (verticalTranslation t) planeMeasure planeMeasure := by
  change MeasurePreserving (fun z : ℝ×ℝ => (z.1,z.2-t)) _ _
  have hm := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right volume (-t))
  have heq : Prod.map (id : ℝ → ℝ) (fun x => x + -t)=
      (fun z : ℝ×ℝ => (z.1,z.2-t)) := by
    funext z
    cases z
    rfl
  rw [heq] at hm
  exact hm

theorem integral_verticalTranslation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (f : ℝ×ℝ → V) :
    (∫ z, f (z.1,z.2-t) ∂planeMeasure)=∫ z, f z ∂planeMeasure :=
  (verticalTranslation_measurePreserving t).integral_comp' f

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

theorem verticalConvolution_energy_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖f (p.2.1,p.2.2-p.1)‖^2)
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖f (p.2.1,p.2.2-p.1)‖^2) := by
    exact (hKm.comp measurable_fst).norm.mul ((hfm.comp (by fun_prop)).norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 2≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z.1,z.2-t)‖^2‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖^2)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_energy_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (verticalConvolution K f) 2 planeMeasure ∧
      (∫ z, ‖verticalConvolution K f z‖^2 ∂planeMeasure)≤
        (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hi := verticalConvolution_energy_joint_integrable K hK hKm f hfm hf
  have hm := verticalConvolution_measurable K hKm f hfm
  have hp : ∀ᵐ z ∂planeMeasure, ‖verticalConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) := by
    filter_upwards [hi.prod_left_ae] with z hz
    exact verticalConvolution_pointwise_energy K hK hKm f hfm z hz
  have hdom : Integrable (fun z => (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2))
      planeMeasure := hi.integral_prod_right.const_mul _
  have he : Integrable (fun z => ‖verticalConvolution K f z‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      have hs := integral_integral_swap
        (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖K t‖*‖f (z.1,z.2-t)‖^2) hi.swap
      rw [hs]
      simp_rw [integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖^2)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelAverageEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An energy bound for a time average of a uniformly bounded family.
This is used with the time-normalized sampling commutator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelAverage_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (_hB : 0≤B) (hF : ∀ t, MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B) :
    MemLp (fun z => ∫ t, K t*F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖∫ t, K t*F (t,z)‖^2 ∂planeMeasure)≤(∫ t, ‖K t‖)^2*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖F p‖^2
  have hHm : Measurable H := (hKm.comp measurable_fst).norm.mul (hFm.norm.pow_const 2)
  have hH0 (p) : 0≤H p := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hF t).integrable_norm_pow (by decide : 2≠0)).const_mul ‖K t‖
    · apply (hK.norm.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖H (t,z)‖ ∂planeMeasure‖≤‖K t‖*B
      simp only [Real.norm_of_nonneg (hH0 _)]
      rw [Real.norm_of_nonneg (integral_nonneg (fun z => hH0 (t,z)))]
      change (∫ z, ‖K t‖*‖F (t,z)‖^2 ∂planeMeasure)≤_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (henergy t) (norm_nonneg _)
  have hm : Measurable (fun z => ∫ t, K t*F (t,z)) :=
    ((hKm.comp measurable_fst).mul hFm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖∫ t, K t*F (t,z)‖^2≤
      (∫ t, ‖K t‖)*(∫ t, H (t,z)) := by
    filter_upwards [hi.prod_left_ae] with z hz
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume
      (fun t => ‖K t‖) (fun t => ‖F (t,z)‖) hKm.norm
      (hFm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) hK.norm hz
    have hn : ‖∫ t, K t*F (t,z)‖≤∫ t, ‖K t‖*‖F (t,z)‖ :=
      norm_integral_le_of_norm_le hprod
        (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hi.integral_prod_right.const_mul (∫ t, ‖K t‖)
  have he : Integrable (fun z => ‖∫ t, K t*F (t,z)‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  have htotal : (∫ t, ∫ z, H (t,z) ∂planeMeasure)≤(∫ t, ‖K t‖)*B := by
    rw [←integral_mul_const]
    apply integral_mono hi.integral_prod_left (hK.norm.mul_const B)
    intro t
    change (∫ z, ‖K t‖*‖F (t,z)‖^2 ∂planeMeasure)≤_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (henergy t) (norm_nonneg _)
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, H (t,z)) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)*(∫ t, ∫ z, H (t,z) ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ t, ‖K t‖)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => H (t,z)) hi.swap)
    _ ≤ (∫ t, ‖K t‖)*((∫ t, ‖K t‖)*B) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSliceFourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation of a general planar Schwartz function has
the Fourier multiplier `2π i η`. Consequently every scaled covariant
vertical jet used in the packet construction preserves spectral zeros.
The proof uses one-dimensional differentiation and product Fubini, so
it does not impose a tensor decomposition on the planar packet. -/

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

def verticalSchwartzSlice (f : SchwartzMap (ℝ × ℝ) ℂ) (x : ℝ) :
    SchwartzMap ℝ ℂ :=
  planarSchwartzSlice (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) f) x 0

theorem verticalSchwartzSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (x y : ℝ) : verticalSchwartzSlice f x y = f (x, y) := by
  change f (x + 0 * y, y) = f (x, y)
  simp

theorem verticalSchwartzSlice_deriv (f : SchwartzMap (ℝ × ℝ) ℂ)
    (x : ℝ) : deriv (verticalSchwartzSlice f x) =
      (verticalSchwartzSlice (planarVerticalDerivative f) x : ℝ → ℂ) := by
  funext y
  have hline : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (f.hasFDerivAt (x, y)).comp_hasDerivAt y hline
  change HasDerivAt (fun t => f (x, t)) (fderiv ℝ f (x, y) (0, 1)) y at h
  have hslice : (verticalSchwartzSlice f x : ℝ → ℂ) = fun t => f (x, t) :=
    funext (verticalSchwartzSlice_apply f x)
  rw [hslice, h.deriv, verticalSchwartzSlice_apply, planarVerticalDerivative_apply]

theorem verticalSchwartzSlice_fourier_deriv
    (f : SchwartzMap (ℝ × ℝ) ℂ) (x η : ℝ) :
    𝓕 (verticalSchwartzSlice (planarVerticalDerivative f) x) η =
      (2 * Real.pi * Complex.I * η) * 𝓕 (verticalSchwartzSlice f x) η := by
  have hi : Integrable (deriv (verticalSchwartzSlice f x)) := by
    rw [verticalSchwartzSlice_deriv]
    exact (verticalSchwartzSlice (planarVerticalDerivative f) x).integrable
  have h := congrFun (Real.fourier_deriv (verticalSchwartzSlice f x).integrable
    (verticalSchwartzSlice f x).differentiable hi) η
  rw [verticalSchwartzSlice_deriv] at h
  simpa only [SchwartzMap.fourier_coe, smul_eq_mul] using h

theorem planarFourier_eq_vertical_integral
    (f : SchwartzMap (ℝ × ℝ) ℂ) (ξ η : ℝ) :
    planarFourier f (ξ, η) = ∫ x,
      Real.fourierChar (-(x * ξ)) • 𝓕 (verticalSchwartzSlice f x) η := by
  unfold planarFourier
  rw [integral_prod _ (planarFourier_integrand_integrable f (ξ, η))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [Real.inner_apply, verticalSchwartzSlice_apply]
  change (∫ y, Real.fourierChar (-(x * ξ + y * η)) • f (x, y)) =
    (Real.fourierChar (-(x * ξ)) : ℂ) •
      (∫ y, Real.fourierChar (-(y * η)) • f (x, y))
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  change Real.fourierChar (-(x * ξ + y * η)) • f (x, y) =
    Real.fourierChar (-(x * ξ)) • (Real.fourierChar (-(y * η)) • f (x, y))
  rw [← mul_smul, ← Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

/-- The exact vertical-derivative multiplier for the product-Lebesgue
Fourier transform, with mathlib's `2π` convention. -/
theorem planarFourier_verticalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (ξ η : ℝ) :
    planarFourier (planarVerticalDerivative f) (ξ, η) =
      (2 * Real.pi * Complex.I * η) * planarFourier f (ξ, η) := by
  rw [planarFourier_eq_vertical_integral, planarFourier_eq_vertical_integral]
  simp_rw [verticalSchwartzSlice_fourier_deriv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

theorem planarFourier_sub (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency : ℝ × ℝ) :
    planarFourier (f - g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarFourier f frequency - planarFourier g frequency := by
  unfold planarFourier
  simp only [sub_apply, smul_sub]
  exact integral_sub (planarFourier_integrand_integrable f frequency)
    (planarFourier_integrand_integrable g frequency)

theorem planarFourier_covariantDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency ξ η : ℝ) :
    planarFourier (planarCovariantDerivative f frequency) (ξ, η) =
      (2 * Real.pi * Complex.I * η - (frequency : ℂ) * Complex.I) *
        planarFourier f (ξ, η) := by
  rw [planarCovariantDerivative, planarFourier_sub, planarFourier_smul,
    planarFourier_verticalDerivative]
  ring

/-- All three scaled covariant jets retain every spectral zero of the
original general planar Schwartz packet. -/
theorem planarFourier_covariantJet_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale : ℝ) (i : Fin 3) (ξ η : ℝ)
    (hzero : planarFourier f (ξ, η) = 0) :
    planarFourier (planarCovariantJet f frequency scale i) (ξ, η) = 0 := by
  fin_cases i
  · exact hzero
  · change planarFourier ((scale : ℂ) • planarCovariantDerivative f frequency :
      SchwartzMap (ℝ × ℝ) ℂ) (ξ, η) = 0
    rw [planarFourier_smul, planarFourier_covariantDerivative, hzero, mul_zero, mul_zero]
  · change planarFourier ((scale : ℂ) • planarCovariantDerivative
      ((scale : ℂ) • planarCovariantDerivative f frequency) frequency :
      SchwartzMap (ℝ × ℝ) ℂ) (ξ, η) = 0
    rw [planarFourier_smul, planarFourier_covariantDerivative, planarFourier_smul,
      planarFourier_covariantDerivative, hzero, mul_zero, mul_zero, mul_zero, mul_zero]

theorem planarAngularFourier_covariantJet_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale : ℝ) (i : Fin 3) (ξ η : ℝ)
    (hzero : planarAngularFourier f (ξ, η) = 0) :
    planarAngularFourier (planarCovariantJet f frequency scale i) (ξ, η) = 0 :=
  planarFourier_covariantJet_eq_zero f frequency scale i _ _ hzero

end LipschitzHilbert

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

def latticeAverage (l W theta : ℝ) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (l*W))⁻¹ • planeMeasure.restrict (latticeCell l W theta)

end LipschitzHilbert.PacketRepresentation

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

theorem planarInverseSchwartz_fourier (F : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (planarInverseSchwartz F) omega=F omega := by
  rw [← fourier_hilbertPlanar_bridge, planarInverseSchwartz, hilbertPlanar_lower,
    FourierTransform.fourier_fourierInv_eq, hilbertPlanarSchwartz_apply]

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

theorem schwartzVerticalProjection_fourier (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzVerticalProjection q W center f) omega=
      q (W*(omega.2-center))*planarFourier f omega := by
  rw [schwartzVerticalProjection,planarInverseSchwartz_fourier,
    SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

theorem planar_schwartz_ext_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (h : ∀ omega, planarFourier f omega=planarFourier g omega) : f=g := by
  ext z
  rw [←planarFourier_inversion f z,←planarFourier_inversion g z]
  exact congrArg (fun F => planarInverse F z) (funext h)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarChangeVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative change of variables for the short Lipschitz sampling maps.
The product plane uses its original sup norm and product Lebesgue measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem planar_map_le_four (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) :
    Measure.map phi planeMeasure≤(4:ℝ≥0∞) • planeMeasure := by
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply hm hS,Measure.smul_apply,smul_eq_mul]
  have h := ha.hausdorffMeasure_preimage_le (d:=2) (by norm_num) S
  norm_num only [hausdorffMeasure_prod_real,Measure.volume_eq_prod,ENNReal.rpow_two,
    ENNReal.coe_ofNat,show (2:ℝ≥0∞)^2=4 by norm_num] at h
  exact h

theorem planar_integral_comp_le_four (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (g : (ℝ×ℝ) → ℝ) (hg : Integrable g planeMeasure)
    (hgn : ∀ z, 0≤g z) :
    Integrable (g ∘ phi) planeMeasure ∧
      (∫ z, g (phi z) ∂planeMeasure)≤4*∫ z, g z ∂planeMeasure := by
  have hmap := planar_map_le_four phi hm ha
  have hi : Integrable g (Measure.map phi planeMeasure) :=
    (hg.smul_measure (by norm_num : (4:ℝ≥0∞)≠⊤)).mono_measure hmap
  refine ⟨hi.comp_measurable hm,?_⟩
  rw [←integral_map hm.aemeasurable hi.aestronglyMeasurable]
  have h := integral_mono_measure hmap (Filter.Eventually.of_forall hgn)
    (hg.smul_measure (by norm_num : (4:ℝ≥0∞)≠⊤))
  simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using h

theorem planar_memLp_comp_bound (phi : (ℝ×ℝ) → (ℝ×ℝ)) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (f ∘ phi) 2 planeMeasure ∧
      (∫ z, ‖f (phi z)‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_comp_le_four phi hm ha (fun z => ‖f z‖^2)
    (hf.integrable_norm_pow (by decide : 2≠0)) (fun z => sq_nonneg _)
  exact ⟨(memLp_two_iff_integrable_sq_norm (hfm.comp hm).aestronglyMeasurable).2 h.1,h.2⟩

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

theorem verticalSampling_energy (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t a b : ℝ) (ht : |t|≤1/4) (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (f ∘ verticalSampling u t a b) 2 planeMeasure ∧
      (∫ z, ‖f (verticalSampling u t a b z)‖^2 ∂planeMeasure)≤4*∫ z, ‖f z‖^2 ∂planeMeasure :=
  planar_memLp_comp_bound _ (verticalSampling_measurable u hu.continuous.measurable t a b)
    (verticalSampling_antilipschitz u hu t a b ht) f hfm hf

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

theorem shortSlopeOperator_energy (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    MemLp (shortSlopeOperator K u f) 2 planeMeasure ∧
      (∫ z, ‖shortSlopeOperator K u f z‖^2 ∂planeMeasure)≤
        4*(∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let F := fun p : ℝ×(ℝ×ℝ) =>
    if |p.1|≤1/4 then f (p.2.1-p.1,p.2.2-p.1*u p.2) else 0
  have hum := hu.continuous.measurable
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    have hc : Continuous (fun p : ℝ×(ℝ×ℝ) => |p.1|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  have hFm : Measurable F := (hfm.comp (by fun_prop)).ite hs measurable_const
  have henergy (t : ℝ) : MemLp (fun z => F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤4*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
    by_cases ht : |t|≤1/4
    · simpa only [F,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
        verticalSampling_energy u hu t t 0 ht f hfm hf
    · simp only [F,ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      exact ⟨MemLp.zero',by positivity⟩
  have h := kernelAverage_energy K hKm hK F hFm (4*∫ z, ‖f z‖^2 ∂planeMeasure)
    (by positivity) (fun t => (henergy t).1) (fun t => (henergy t).2)
  have heq (z : ℝ×ℝ) : (∫ t, K t*F (t,z))=shortSlopeOperator K u f z := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [F]
    split_ifs <;> simp
  simp only [heq] at h
  refine ⟨h.1,h.2.trans_eq ?_⟩
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and kernel linearity of the actual scalar pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def kernelPairing (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) : ℂ :=
  ∫ z, slopeKernelOperator K u f z*star (g z) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive compact mollifiers preserve the unit bound and give actual
Schwartz approximants for compactly supported measurable tests. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution Pointwise
namespace LipschitzHilbert.PacketRepresentation

def compactMollification (phi : ContDiffBump (0 : ℝ×ℝ))
    (f : (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  ((phi.hasCompactSupport_normed (μ:=planeMeasure)).convolution (L:=ContinuousLinearMap.lsmul ℝ ℝ)
    hc).toSchwartzMap
      ((phi.hasCompactSupport_normed (μ:=planeMeasure)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed hf.locallyIntegrable)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory

namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_measurable (r R : ℝ) : Measurable (sharpTimeKernel r R) := by
  unfold sharpTimeKernel
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedFrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded measurable frequency symbol can be paired with an L1 test
function. This justifies finite recombination before the uniform estimates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def variableFrequencyMultiplier (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
    (m (z,omega)*planarFourier f omega) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1FrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable frequency envelopes justify multipliers and finite
recombination for L1 inputs, including discontinuous amplitude slices. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def variableFrequencyMultiplierL1 (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
    (m (z,omega)*planarFourier f omega) ∂planeMeasure

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

theorem shortSchwartz_memLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (shortSlopeOperator K u f) 2 planeMeasure :=
  (shortSlopeOperator_energy K hKm hK u hu f f.continuous.measurable (f.memLp 2 planeMeasure)).1

def shortSchwartzToL2 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] Lp ℂ 2 planeMeasure where
  toFun f := (shortSchwartz_memLp K hKm hK u hu f).toLp (shortSlopeOperator K u f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(shortSchwartz_memLp K hKm hK u hu (f+g)).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu f).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu g).coeFn_toLp,
      Lp.coeFn_add ((shortSchwartz_memLp K hKm hK u hu f).toLp _) ((shortSchwartz_memLp K hKm hK u hu g).toLp _)]
      with z hz hfz hgz hadd
    rw [hz,hadd]
    simp only [Pi.add_apply,hfz,hgz]
    exact shortSlopeOperator_schwartz_add K hK u f g z
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(shortSchwartz_memLp K hKm hK u hu (c • f)).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu f).coeFn_toLp,
      Lp.coeFn_smul c ((shortSchwartz_memLp K hKm hK u hu f).toLp _)] with z hz hfz hsmul
    simp only [RingHom.id_apply]
    rw [hz,hsmul]
    simp only [Pi.smul_apply,smul_eq_mul,hfz]
    exact shortSlopeOperator_schwartz_smul K u f c z

def shortL2Operator (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (shortSchwartzToL2 K hKm hK u hu).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ScaledPlanarPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General planar Schwartz profiles in the physical packet coordinates.
The affine restriction retains Schwartz regularity and the carrier is
removed exactly by vertical covariant differentiation. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem modulatedPlanarSlice_vertical_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => modulatedPlanarSlice f a cy l W delta frequency t hl x)
      (((frequency:ℂ)*Complex.I)*modulatedPlanarSlice f a cy l W delta frequency y hl x +
        Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)*
          ((1/W:ℝ):ℂ)*planarVerticalDerivative f ((x-a)/l,(y-cy+delta*(x-a))/W)) y := by
  have hg : HasDerivAt (fun t : ℝ => ((x-a)/l,(t-cy+delta*(x-a))/W)) (0,1/W) y := by
    simpa only [sub_zero, add_zero, one_div, id_eq] using (hasDerivAt_const y ((x-a)/l)).prodMk
      ((((hasDerivAt_id y).sub_const cy).add_const (delta*(x-a))).div_const W)
  have hf := (f.hasFDerivAt ((x-a)/l,(y-cy+delta*(x-a))/W)).comp_hasDerivAt y hg
  have hc := (((((hasDerivAt_id y).sub_const cy).add_const
    (delta*(x-a))).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  have h := hc.mul hf
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · beta_reduce
    exact modulatedPlanarSlice_apply f a cy l W delta frequency t hl x
  · rw [modulatedPlanarSlice_apply, planarVerticalDerivative_apply]
    have hv : (0,1/W) = (1/W:ℝ) • ((0,1):ℝ × ℝ) := by simp
    rw [hv, map_smul]
    simp only [Complex.real_smul, Function.comp_apply, id_eq]
    push_cast
    ring

theorem modulatedPlanarSlice_covariant (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarSlice f a cy l W delta frequency t hl x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl x) =
      modulatedPlanarSlice (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
        a cy l W delta frequency y hl x := by
  rw [(modulatedPlanarSlice_vertical_hasDerivAt f a cy l W delta frequency y hl x).deriv]
  simp only [modulatedPlanarSlice_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarModulatedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual raw kernels for a general planar packet. The
covariant derivative differentiates its normalized vertical profile. -/

noncomputable section
namespace LipschitzHilbert

theorem modulatedPlanarJet_covariant_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl 0 x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarJet f a cy l W delta frequency scale y hl 0 x) =
      modulatedPlanarJet f a cy l W delta frequency scale y hl 1 x := by
  simpa [modulatedPlanarJet,planarProfileJet] using
    modulatedPlanarSlice_covariant f a cy l W delta frequency scale y hl x

theorem modulatedPlanarJet_covariant_one (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl 1 x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarJet f a cy l W delta frequency scale y hl 1 x) =
      modulatedPlanarJet f a cy l W delta frequency scale y hl 2 x := by
  simpa [modulatedPlanarJet,planarProfileJet] using
    modulatedPlanarSlice_covariant (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
      a cy l W delta frequency scale y hl x

theorem modulatedPlanarJet_differentiable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) (x : ℝ) :
    DifferentiableAt ℝ (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl i x) y :=
  (modulatedPlanarSlice_vertical_hasDerivAt _ a cy l W delta frequency y hl x).differentiableAt

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PhysicalPlanarPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full two-dimensional Schwartz packet and its exact affine-line
restriction. This connects physical spectra to the constructed raw waves. -/

noncomputable section
namespace LipschitzHilbert

theorem physicalPlanarPacket_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency c s : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    planarSchwartzSlice (physicalPlanarPacket f a b l W θ frequency hl hW) c s =
      modulatedPlanarSlice f a (b-s*a) l W (s-θ) frequency c hl := by
  ext x
  rw [planarSchwartzSlice_apply,physicalPlanarPacket_apply,modulatedPlanarSlice_apply]
  have hphase : (c+s*x-b)-θ*(x-a) = c-(b-s*a)+(s-θ)*(x-a) := by ring
  rw [hphase]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PhysicalPlanarJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical covariant derivatives coincide with the three raw
kernels, so their spectral support can be inherited from the full packet. -/

noncomputable section
namespace LipschitzHilbert

theorem physicalPlanarPacket_covariant (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    (scale:ℂ) • planarCovariantDerivative (physicalPlanarPacket f a b l W θ frequency hl hW) frequency =
      physicalPlanarPacket (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
        a b l W θ frequency hl hW := by
  ext z
  rcases z with ⟨x,y⟩
  let P := physicalPlanarPacket f a b l W θ frequency hl hW
  have hs (t : ℝ) : planarSchwartzSlice P t 0 =
      modulatedPlanarSlice f a b l W (-θ) frequency t hl := by
    simpa only [zero_mul,sub_zero,zero_sub] using
      physicalPlanarPacket_slice f a b l W θ frequency t 0 hl hW
  have hfun : (fun t => planarSchwartzSlice P t 0 x) =
      (fun t => modulatedPlanarSlice f a b l W (-θ) frequency t hl x) := by
    funext t
    rw [hs t]
  have h := planarCovariantDerivative_slice P frequency scale y 0 x
  rw [hfun,hs y] at h
  have hc := modulatedPlanarSlice_covariant f a b l W (-θ) frequency scale y hl x
  have he := h.symm.trans hc
  have hs' := physicalPlanarPacket_slice (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
    a b l W θ frequency y 0 hl hW
  have ht := congrArg (fun g : SchwartzMap ℝ ℂ => g x) hs'
  simp only [zero_mul,sub_zero,zero_sub,planarSchwartzSlice_apply,add_zero] at ht he
  exact he.trans ht.symm

theorem physicalPlanarPacket_jet (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (i : Fin 3) :
    planarCovariantJet (physicalPlanarPacket f a b l W θ frequency hl hW) frequency scale i =
      physicalPlanarPacket (planarProfileJet f (scale/W) i) a b l W θ frequency hl hW := by
  fin_cases i
  · simp [planarCovariantJet,planarProfileJet]
  · simpa [planarCovariantJet,planarProfileJet] using
      physicalPlanarPacket_covariant f a b l W θ frequency scale hl hW
  · change (scale:ℂ) • planarCovariantDerivative
      ((scale:ℂ) • planarCovariantDerivative
        (physicalPlanarPacket f a b l W θ frequency hl hW) frequency) frequency = _
    rw [physicalPlanarPacket_covariant,physicalPlanarPacket_covariant]
    rfl

theorem physicalPlanarPacket_jet_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale c s : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (i : Fin 3) :
    planarSchwartzSlice
      (planarCovariantJet (physicalPlanarPacket f a b l W θ frequency hl hW) frequency scale i) c s =
      modulatedPlanarJet f a (b-s*a) l W (s-θ) frequency scale c hl i := by
  rw [physicalPlanarPacket_jet,physicalPlanarPacket_slice]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ReferencePacketFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite packet data in one reference box. Coefficients are
left arbitrary for the weighted synthesis and subsequent duality argument. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

structure ReferencePacketFamily (N : ℕ) (κ : Type*) (ι : Fin N → Type*)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  centerX : ℝ
  centerZ : ℝ
  radius : ℝ
  width : ℝ
  constant : ℝ
  radius_pos : 0 < radius
  width_pos : 0 < width
  length : Fin N → ℝ
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, ∀ _ : ι j, length j ≤ radius
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  center_x : ∀ j i, |baseX + length j * (site j i).1 - centerX| ≤ radius
  center_z : ∀ j i, |baseZ + width * (site j i).2 - centerZ| ≤ width
  wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  wave_bound : ∀ j i k y x, ‖wave j i k y x‖ ≤ constant *
    (lineEnvelope (baseX + length j * (site j i).1) (length j) 3 x *
     lineEnvelope (baseZ + width * (site j i).2) width 3 y)

namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
  [Fintype κ] [∀ j, Fintype (ι j)]

def packets (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) (j : Fin N) (k : κ) :
    SchwartzMap ℝ ℂ := packetSynthesis (fun i => c j i k) (fun i => P.wave j i k y)

def coefficientEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : ℝ :=
  ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedReferenceVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomially weighted maximal-synthesis estimate about an arbitrary
reference box, conditional only on the published scalar Lépingle input. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def transverseEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) : ℝ :=
  ∑ j, P.length j * ∑ i, ‖c j i‖^2 *
    lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y

def weightedVariationEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
    ∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
      ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable planar synthesis, threshold selection, and the weighted
variation integral in the reference chart (transverse, longitudinal). -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def scaleSynthesis (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (j : Fin N) (z : ℝ × ℝ) :
    EuclideanSpace ℂ κ := WithLp.toLp 2 (fun k => P.packets c z.1 j k z.2)

def variation (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ × ℝ) : ℝ :=
  cubicVariation (fun n => hilbertPartialBandSum (P.packets c z.1) n z.2) N

def thresholdSynthesis (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (z : ℝ × ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, if v z ≤ d j then P.scaleSynthesis c j z else 0

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selected analyzing integrals on the reference chart. Integrability
is obtained from the two-coordinate packet envelope and a bounded test. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def selectedWave (P : ReferencePacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d s.1 then P.wave s.1 s.2 k z.1 z.2 else 0

def mainCoefficient (P : ReferencePacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (i : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
    (P.selectedWave d v) g ⟨j,i⟩

end ReferencePacketFamily
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

theorem packetBoxIndex_horizontal (u y r W x z : ℝ) (hr : 0 < r) :
    |x - (u + r * (packetBoxIndex u y r W x z).1)| ≤ r :=
  floor_box_distance u r x hr

theorem packetBoxIndex_vertical (u y r W x z : ℝ) (hW : 0 < W) :
    |z - (y + W * (packetBoxIndex u y r W x z).2)| ≤ W :=
  floor_box_distance y W z hW

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ShortPacketBoxes
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

def shortBoxSynthesis {σ : Type*} {ι : σ → Type*} [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) (j : σ) :
    SchwartzMap ℝ ℂ :=
  packetSynthesis (fun i : ShortBoxFiber len index r b j => c j i)
    (fun i => f j i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar dyadic packet family and its restriction to an actual
short-packet center box. This restriction carries no coefficient budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def boxIndex (P : PlanarPacketFamily N κ ι) (u y r : ℝ) : ∀ j, ι j → ℤ × ℤ :=
  centerBoxIndex P.centerX P.centerZ u y r P.width

abbrev BoxFiber (P : PlanarPacketFamily N κ ι) (u y r : ℝ) (b : ℤ × ℤ) :=
  ShortBoxFiber P.length (P.boxIndex u y r) r b

def referenceBox (P : PlanarPacketFamily N κ ι) (u y r : ℝ) (hr : 0 < r)
    (b : ℤ × ℤ) : ReferencePacketFamily N κ (P.BoxFiber u y r b) where
  baseX := P.baseX
  baseZ := P.baseZ
  centerX := u+r*b.1
  centerZ := y+P.width*b.2
  radius := r
  width := P.width
  constant := P.constant
  radius_pos := hr
  width_pos := P.width_pos
  length := P.length
  length_pos := P.length_pos
  length_le := fun _ i => i.property.1
  site := fun j i => P.site j i.val
  site_injective := fun j => (P.site_injective j).comp Subtype.val_injective
  center_x := by
    intro j i
    have h := packetBoxIndex_horizontal u y r P.width (P.centerX j i) (P.centerZ j i) hr
    have hi := congrArg Prod.fst i.property.2
    change (packetBoxIndex u y r P.width (P.centerX j i) (P.centerZ j i)).1 = b.1 at hi
    rw [hi] at h
    exact h
  center_z := by
    intro j i
    have h := packetBoxIndex_vertical u y r P.width (P.centerX j i) (P.centerZ j i) P.width_pos
    have hi := congrArg Prod.snd i.property.2
    change (packetBoxIndex u y r P.width (P.centerX j i) (P.centerZ j i)).2 = b.2 at hi
    rw [hi] at h
    exact h
  wave := fun j i k => P.wave j i k
  wave_bound := fun j i k y x => P.wave_bound j i k y x

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLatticePacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual general planar packets on translated sheared lattices form
the canonical planar packet family. Only the bookkeeping sites are
quantized: the raw waves retain their original centers and profiles. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

/-- The center drift is `theta-t`, whereas the modulation along the
reference line has shear `t-theta`. This identifies every actual raw
jet with the corresponding restriction of the physical planar packet. -/
theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (u : ι j) (k : κ)
    (y t : ℝ) :
    P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (physicalPlanarPacket (P.profile j u k)
        (P.actualX j u) (P.actualZ j u + t * P.actualX j u)
        (P.length j) P.width (t + P.rowSlope j) (P.frequency k)
        (P.length_pos j).ne' P.width_pos.ne') (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j u k) (P.actualX j u)
    (P.actualZ j u + t * P.actualX j u) (P.length j) P.width
    (t + P.rowSlope j) (P.frequency k) P.scale y t
    (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j u + t * P.actualX j u - t * P.actualX j u = P.actualZ j u := by
    ring
  have hd : t - (t + P.rowSlope j) = -P.rowSlope j := by ring
  simpa only [hc, hd, raw] using h.symm

end SourceLatticePacket

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

section Packet

variable (f : SchwartzMap (ℝ × ℝ) ℂ)
  (b s θ ell w cStar cEta CEta cb Cb : ℝ)
  (hell : 0 < ell) (hw : 0 < w) (hcEta : 0 < cEta)
  (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
  (hspectrum : ∀ ξ η, planarAngularFourier f (ξ, η) ≠ 0 →
    |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta)
  (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- Exact angular-frequency annulus for an actual affine-line slice. -/
theorem sourcePacket_angular_annulus {ω : ℝ}
    (hω : angularFourier (planarSchwartzSlice f b s) ω ≠ 0) :
    (cEta * cb - cStar) / ell ≤ |ω| ∧
      |ω| ≤ (CEta * Cb + cStar) / ell := by
  by_contra hbound
  apply hω
  apply planarSchwartzSlice_angularFourier_eq_zero
  intro η
  by_contra hnonzero
  have hs := hspectrum (ω - s * η) η hnonzero
  have hwedge : |ω - (s - θ) * η| ≤ cStar / ell := by
    convert hs.1 using 2
    all_goals try with_reducible_and_instances rfl
    ring
  exact hbound (source_frequency_annulus hell hw hcEta hcb hCb hwedge hs.2 hselector)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- The same annulus, with endpoints converted to mathlib's Fourier
transform convention by division by `2π`. -/
theorem sourcePacket_fourier_annulus {ξ : ℝ}
    (hξ : 𝓕 (planarSchwartzSlice f b s) ξ ≠ 0) :
    (cEta * cb - cStar) / (2 * Real.pi * ell) ≤ |ξ| ∧
      |ξ| ≤ (CEta * Cb + cStar) / (2 * Real.pi * ell) := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hcancel : (2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by
    field_simp [Real.pi_ne_zero]
  have hangular : angularFourier (planarSchwartzSlice f b s) (2 * Real.pi * ξ) ≠ 0 := by
    simpa only [SchwartzMap.fourier_coe, angularFourier, hcancel] using hξ
  have h := sourcePacket_angular_annulus f b s θ ell w cStar cEta CEta cb Cb
    hell hw hcEta hcb hCb hspectrum hselector hangular
  simp only [abs_mul, abs_of_pos hπ] at h
  constructor
  · have hl : ((cEta * cb - cStar) / ell) / (2 * Real.pi) ≤ |ξ| :=
      (div_le_iff₀ hπ).mpr (by nlinarith [h.1])
    simpa only [div_div, mul_comm ell (2 * Real.pi)] using hl
  · have hu : |ξ| ≤ ((CEta * Cb + cStar) / ell) / (2 * Real.pi) :=
      (le_div_iff₀ hπ).mpr (by nlinarith [h.2])
    simpa only [div_div, mul_comm ell (2 * Real.pi)] using hu

include hspectrum in
theorem sourcePacket_jet_spectrum (frequency scale : ℝ) (i : Fin 3) :
    ∀ ξ η, planarAngularFourier (planarCovariantJet f frequency scale i) (ξ, η) ≠ 0 →
      |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta := by
  intro ξ η hnonzero
  apply hspectrum ξ η
  intro hzero
  exact hnonzero (planarAngularFourier_covariantJet_eq_zero
    f frequency scale i ξ η hzero)

include hell hw hcEta hcb hCb hspectrum hselector in
/-- All three covariant jets lie in the same actual line annulus;
there is no separate spectral assumption on either derivative. -/
theorem sourcePacket_jet_fourier_annulus (frequency scale : ℝ) (i : Fin 3) {ξ : ℝ}
    (hξ : 𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ ≠ 0) :
    (cEta * cb - cStar) / (2 * Real.pi * ell) ≤ |ξ| ∧
      |ξ| ≤ (CEta * Cb + cStar) / (2 * Real.pi * ell) :=
  sourcePacket_fourier_annulus (planarCovariantJet f frequency scale i)
    b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb
    (sourcePacket_jet_spectrum f θ ell w cStar cEta CEta hspectrum frequency scale i)
    hselector hξ

include hell hw hcEta hcb hCb hspectrum hselector in
theorem sourcePacket_jet_fourier_cutoffs (frequency scale : ℝ) (i : Fin 3) :
    (∀ ξ, |ξ| < (cEta * cb - cStar) / (2 * Real.pi * ell) →
      𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ = 0) ∧
    (∀ ξ, (CEta * Cb + cStar) / (2 * Real.pi * ell) < |ξ| →
      𝓕 (planarSchwartzSlice (planarCovariantJet f frequency scale i) b s) ξ = 0) := by
  constructor
  · intro ξ hξ
    by_contra hnonzero
    exact (not_le_of_gt hξ) (sourcePacket_jet_fourier_annulus
      f b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb hspectrum hselector
      frequency scale i hnonzero).1
  · intro ξ hξ
    by_contra hnonzero
    exact (not_le_of_gt hξ) (sourcePacket_jet_fourier_annulus
      f b s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb hspectrum hselector
      frequency scale i hnonzero).2

end Packet

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original physical spectrum controls all raw kernels on an
actual translated, sheared source lattice. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalPacket (t : ℝ) (j : Fin N) (u : ι j) (k : κ) : SchwartzMap (ℝ × ℝ) ℂ :=
  physicalPlanarPacket (P.profile j u k) (P.actualX j u)
    (P.actualZ j u+t*P.actualX j u) (P.length j) P.width
    (t+P.rowSlope j) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

theorem raw_fourier_cutoffs (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hspectrum : ∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η) ≠ 0 →
      |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧
        cEta ≤ w*η ∧ w*η ≤ CEta)
    (hselector : ∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j| ∧
      |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ ξ, |ξ| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |ξ| →
      𝓕 (P.raw i j u k y) ξ = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector j u
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb (hspectrum j u k) hsel
    (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  exact h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalL2Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical Schwartz multiplier extends to L2. This
preliminary bound supplies continuity for restricted-test approximation. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def schwartzVerticalProjectionLM (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ×ℝ) ℂ where
  toFun := schwartzVerticalProjection p w 0
  map_add' f g := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_add]
    ring
  map_smul' c f := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_smul,RingHom.id_apply]
    ring

def verticalSchwartzToL2 (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] Lp ℂ 2 planeMeasure :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap.comp (schwartzVerticalProjectionLM p w)

def verticalL2Projection (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (verticalSchwartzToL2 p w).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalProjectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Addition and exact absorption of vertical multipliers on Schwartz
functions and their continuous L2 realizations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_add_profile (p q : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (p+q) w 0 f=
      schwartzVerticalProjection p w 0 f+schwartzVerticalProjection q w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,planarFourier_add,add_apply,add_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAreaAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized intersection averages and top-area weights. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.SlopeBox

def dilationAverage (T : SlopeBox) (D : ℝ) (Q : Set (ℝ × ℝ)) : ℝ :=
  (volume.prod volume).real (Q ∩ T.radialDilation D)/(8*D^2*T.length*T.width)

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityKeepers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing-length selection of the actual spatial and angular density
tests. Keeper witnesses are disjoint even when their spatial boxes overlap. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

def densityTest (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (T : SlopeBox)
    (omega : Set ℝ) (K : ℝ) : Set (ℝ×ℝ) :=
  E ∩ densitySpatialBox T K ∩ u ⁻¹' omega

def densityConflict {ι : Type*} (T : ι → SlopeBox) (omega : ι → Set ℝ)
    (K : ℝ) (i j : ι) : Prop :=
  (densitySpatialBox (T i) K ∩ densitySpatialBox (T j) K).Nonempty ∧
    (omega i ∩ omega j).Nonempty

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensitySpatialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The number of translated ordinary trees in a density keeper has the
small power loss needed for summing the dyadic density thresholds. -/
noncomputable section
namespace LipschitzHilbert

def densitySpatialCount (eta : ℝ) : ℕ := ⌈5*densityRadius eta⌉₊

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThresholdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over any finite family of dyadic density thresholds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def ordinaryThresholdEnvelope (k : ℤ) : ℝ := ordinaryThresholdRatio^k.natAbs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableDerivativeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative part of the comparable-frequency commutator sums
uniformly, including arbitrarily low output frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def comparableDerivativePiece (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  schwartzDerivative 1 (lineSchwartzCommutator m
    (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b) (H k))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpTimeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sharply truncated Hilbert kernel has first absolute moment at most
twice its outer radius, independently of the inner truncation. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_first_moment (r R : ℝ) (hr : 0 < r) (hR : 0<R) :
    Integrable (fun t => |t| *‖sharpTimeKernel r R t‖) ∧
      (∫ t, |t| *‖sharpTimeKernel r R t‖)≤2*R := by
  let q := (Icc (-R) R).indicator (fun _ : ℝ => (1:ℝ))
  have hq : Integrable q := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp))
  have hm : Measurable (fun t => |t| *‖sharpTimeKernel r R t‖) :=
    (show Measurable (fun t : ℝ => |t|) from by fun_prop).mul (sharpTimeKernel_measurable r R).norm
  have hb (t : ℝ) : |t| *‖sharpTimeKernel r R t‖≤q t := by
    by_cases ht : r< |t| ∧ |t|<R
    · have hn : t≠0 := abs_pos.mp (hr.trans ht.1)
      have hmem : t∈Icc (-R) R := abs_le.mp ht.2.le
      simp only [sharpTimeKernel,ite_eq_left ht,q,indicator_of_mem hmem,norm_inv,
        Complex.norm_real,Real.norm_eq_abs,mul_inv_cancel₀ (abs_ne_zero.mpr hn),le_refl]
    · simp only [sharpTimeKernel,ite_eq_right ht,norm_zero,mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  have hi := hq.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact hb t)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, q t := integral_mono hi hq hb
    _ = 2*R := by
      rw [integral_indicator_const 1 measurableSet_Icc]
      simp only [measureReal_def,Real.volume_Icc,smul_eq_mul,mul_one]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_integrable (r R : ℝ) (hr : 0 < r) (hR : 0<R) :
    Integrable (sharpTimeKernel r R) := by
  have hi := (sharpTimeKernel_first_moment r R hr hR).1.const_mul r⁻¹
  apply hi.mono' (sharpTimeKernel_measurable r R).aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : r< |t| ∧ |t|<R
  · have h1 : 1 ≤ r⁻¹*|t| := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (one_le_div hr).2 ht.1.le
    calc
      _ = 1*‖sharpTimeKernel r R t‖ := (one_mul _).symm
      _ ≤ (r⁻¹*|t|)*‖sharpTimeKernel r R t‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring
  · simp only [sharpTimeKernel,ite_eq_right ht,norm_zero,mul_zero,le_refl]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini transfers the precisely stated one-dimensional Hilbert input
to the horizontal remainder on the actual plane. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def horizontalTruncatedHilbert (r R : ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) f z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedOrder
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

theorem orderAverage_nonempty (w : ι → ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : List ι → ℝ) :
    orderAverage w s f = ∑ i : s, w i / orderMass w s *
      orderAverage w (s.erase i.val) (fun l => f (i.val :: l)) := by
  rw [orderAverage, dite_eq_left hs]

theorem orderAverage_nonnegative (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (f : List ι → ℝ) (hf : ∀ l, 0 ≤ f l) :
    0 ≤ orderAverage w s f := by
  induction s using Finset.strongInductionOn generalizing f with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (div_nonneg (hw i i.property).le (orderMass_pos w s hw hs).le)
      exact ih _ (Finset.erase_ssubset i.property)
        (fun j hj => hw j (Finset.mem_of_mem_erase hj)) _ (fun l => hf _)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [orderAverage_empty] using hf []

theorem orderAverage_const (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (c : ℝ) : orderAverage w s (fun _ => c) = c := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      have hrec (i : s) : orderAverage w (s.erase i.val) (fun _ => c) = c :=
        ih _ (Finset.erase_ssubset i.property)
          (fun j hj => hw j (Finset.mem_of_mem_erase hj))
      simp_rw [hrec]
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have hsum : (∑ i : s, w i) = orderMass w s := Finset.sum_coe_sort s w
      rw [hsum, div_self (orderMass_pos w s hw hs).ne', one_mul]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact orderAverage_empty _ _

theorem orderAverage_sum {κ : Type*} (w : ι → ℝ) (s : Finset ι)
    (t : Finset κ) (f : κ → List ι → ℝ) :
    orderAverage w s (fun l => ∑ k ∈ t, f k l) =
      ∑ k ∈ t, orderAverage w s (f k) := by
  induction s using Finset.strongInductionOn generalizing f with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · rw [orderAverage_nonempty w s hs]
      have hrec (i : s) :
          orderAverage w (s.erase i.val) (fun l => ∑ k ∈ t, f k (i.val :: l)) =
            ∑ k ∈ t, orderAverage w (s.erase i.val) (fun l => f k (i.val :: l)) :=
        ih _ (Finset.erase_ssubset i.property) _
      simp_rw [hrec]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact (orderAverage_nonempty w s hs (f k)).symm
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simp only [orderAverage_empty]

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

omit [Fintype α] in
theorem orderOutcomeWeight_nonnegative (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) (a : α) :
    0 ≤ orderOutcomeWeight w s X a := by
  apply orderAverage_nonnegative w s hw
  intro l
  split_ifs <;> norm_num

theorem orderOutcomeWeight_total (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) :
    ∑ a, orderOutcomeWeight w s X a = 1 := by
  unfold orderOutcomeWeight
  rw [← orderAverage_sum]
  have heq : (fun l => ∑ a : α, if X l = a then (1 : ℝ) else 0) = fun _ => 1 := by
    funext l
    simp
  rw [heq, orderAverage_const w s hw]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sharp kernel integral is exactly the positive-time
symmetric quotient, including its sign and both endpoints. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation

theorem sharpKernel_symmetrize (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t, sharpTimeKernel epsilon R t*F t)=
      ∫ t in epsilon..R, (t:ℂ)⁻¹*(F t-F (-t)) := by
  let G := fun t : ℝ => (t:ℂ)⁻¹*F t
  let H := fun t : ℝ => (t:ℂ)⁻¹*F (-t)
  have hinv : ContinuousOn (fun t : ℝ => (t:ℂ)⁻¹) (uIcc epsilon R) := by
    apply (Complex.continuous_ofReal.continuousOn).inv₀
    intro t ht
    rw [uIcc_of_le heR] at ht
    exact_mod_cast (he.trans_le ht.1).ne'
  have hG : IntervalIntegrable G volume epsilon R :=
    (hinv.mul hF.continuousOn).intervalIntegrable
  have hH : IntervalIntegrable H volume epsilon R :=
    (hinv.mul (hF.comp continuous_neg).continuousOn).intervalIntegrable
  let A := (Ioo epsilon R).indicator G
  let B := (Ioo epsilon R).indicator H
  have hA : Integrable A := (integrable_indicator_iff measurableSet_Ioo).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le heR).mp hG)
  have hB : Integrable B := (integrable_indicator_iff measurableSet_Ioo).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le heR).mp hH)
  have hAI : (∫ t, A t)=∫ t in epsilon..R, G t := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le heR]
  have hBI : (∫ t, B t)=∫ t in epsilon..R, H t := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le heR]
  have heq (t : ℝ) : sharpTimeKernel epsilon R t*F t=A t-B (-t) := by
    by_cases ht : 0≤t
    · have hn : -t∉Ioo epsilon R := by intro h; linarith only [h.1,he,ht]
      rw [show B (-t)=0 from Set.indicator_of_notMem hn H,sub_zero]
      by_cases hm : t∈Ioo epsilon R
      · have hc : epsilon < |t| ∧ |t|<R := by simpa only [abs_of_nonneg ht,mem_Ioo] using hm
        rw [show A t=G t from Set.indicator_of_mem hm G]
        simp only [sharpTimeKernel,ite_eq_left hc,G]
      · have hc : ¬(epsilon < |t| ∧ |t|<R) := by simpa only [abs_of_nonneg ht,mem_Ioo] using hm
        rw [show A t=0 from Set.indicator_of_notMem hm G]
        simp only [sharpTimeKernel,ite_eq_right hc,zero_mul]
    · have ht' : t<0 := lt_of_not_ge ht
      have hn : t∉Ioo epsilon R := by intro h; linarith only [h.1,he,ht']
      rw [show A t=0 from Set.indicator_of_notMem hn G]
      by_cases hm : -t∈Ioo epsilon R
      · have hc : epsilon < |t| ∧ |t|<R := by simpa only [abs_of_neg ht',mem_Ioo] using hm
        rw [show B (-t)=H (-t) from Set.indicator_of_mem hm H]
        simp only [sharpTimeKernel,ite_eq_left hc,H,neg_neg,Complex.ofReal_neg,inv_neg,neg_mul,zero_sub]
      · have hc : ¬(epsilon < |t| ∧ |t|<R) := by simpa only [abs_of_neg ht',mem_Ioo] using hm
        rw [show B (-t)=0 from Set.indicator_of_notMem hm H]
        simp only [sharpTimeKernel,ite_eq_right hc,zero_mul,sub_zero]
  simp_rw [heq]
  rw [integral_sub hA hB.comp_neg]
  have hneg : (∫ t, B (-t))=∫ t, B t := by simpa using Measure.integral_comp_mul_left B (-1)
  rw [hneg,hAI,hBI,←intervalIntegral.integral_sub hG hH]
  apply intervalIntegral.integral_congr
  intro t _
  change (t:ℂ)⁻¹*F t-(t:ℂ)⁻¹*F (-t)=(t:ℂ)⁻¹*(F t-F (-t))
  ring

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

theorem sharpSlope_eq_productSymmetric (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Continuous f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (z : ℝ×ℝ) :
    slopeKernelOperator (sharpTimeKernel epsilon R) u f z=productSymmetricTruncation u epsilon R f z := by
  have h := sharpKernel_symmetrize epsilon R he heR (fun t => f (productSlopeSample u t z))
    (hf.comp (by unfold productSlopeSample; fun_prop))
  simpa only [slopeKernelOperator,productSlopeSample,productSymmetricTruncation,
    Complex.real_smul,Complex.ofReal_inv] using h

theorem sharp_shortTimeKernel (epsilon R : ℝ) (hR : R≤1/4) :
    shortTimeKernel (sharpTimeKernel epsilon R)=sharpTimeKernel epsilon R := by
  funext t
  unfold shortTimeKernel
  by_cases ht : |t|≤1/4
  · rw [ite_eq_left ht]
  · rw [ite_eq_right ht]
    symm
    unfold sharpTimeKernel
    rw [ite_eq_right (by intro h; exact ht (h.2.le.trans hR))]

theorem shortSharp_eq_productSymmetric (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (hf : Continuous f) (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (hR : R≤1/4)
    (z : ℝ×ℝ) : shortSlopeOperator (sharpTimeKernel epsilon R) u f z=
      productSymmetricTruncation u epsilon R f z := by
  rw [shortSlopeOperator_eq_kernel,sharp_shortTimeKernel epsilon R hR]
  exact sharpSlope_eq_productSymmetric u f hf epsilon R he heR z

end LipschitzHilbert.PacketRepresentation

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

theorem shortSharp_tendsto_productSlopePrincipalValue (u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (z : ℝ×ℝ) :
    Tendsto (fun n => shortSlopeOperator (sharpTimeKernel (pvInnerRadius R n) R) u f z)
      atTop (𝓝 (productSlopePrincipalValue u R f z)) := by
  have h := (productSymmetricTruncation_tendsto u f hf R hR z).comp (pvInnerRadius_tendsto R hR)
  apply h.congr'
  filter_upwards [] with n
  exact (shortSharp_eq_productSymmetric u f hf.continuous _ R (pvInnerRadius_pos R hR n)
    (pvInnerRadius_lt R hR n).le hRsmall z).symm

theorem productSlopePrincipalValue_measurable (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f : (ℝ×ℝ) → ℂ) (hf : Differentiable ℝ f) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4) :
    Measurable (productSlopePrincipalValue u R f) := by
  apply measurable_of_tendsto_metrizable
    (fun n => shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R) u hu f hf.continuous.measurable)
  exact tendsto_pi_nhds.mpr (shortSharp_tendsto_productSlopePrincipalValue u f hf R hR hRsmall)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeMartingaleExits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative exits for the finite scalar specialization of Zorin-Kranich,
Bernoulli 26 (2020), Definition 2.1. The running radius is measured from
the initial value; the terminal time is one step beyond the path in use. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

variable {Ω : Type*}

def runningOscillation (F : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  finiteMaxSignal (fun k y => F k y-F 0 y) n x

def relativeNextExit (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (σ : Ω → ℕ) : Ω → ℕ :=
  hittingBtwn (fun n x => ‖F n x-stoppedProcess F (fun y => (σ y:WithTop ℕ)) n x‖-
    a*runningOscillation F n x) (Ioi 0) 0 H

def relativeExitTimes (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | i+1 => relativeNextExit F a H (relativeExitTimes F a H i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RelativeExitEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable quadratic energies of the relative sampled martingales. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

def relativeExitEnergy (F : ℕ → Ω → ℝ) (a : ℝ) (H : ℕ) (x : Ω) : ℝ :=
  ∑ j : Fin H, ‖F (relativeExitTimes F a H (j.val+1) x) x-
    F (relativeExitTimes F a H j.val x) x‖^2

def weightedRelativeExitEnergy (F : ℕ → Ω → ℝ) (H : ℕ) (x : Ω) : ℝ :=
  ∑' m, relativeExitScale m*relativeExitEnergy F (relativeExitScale m) H x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RealFiniteVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued finite variation and cancellation of the running radius
in the pathwise relative-exit estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

abbrev realVariationCube (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  finiteCubicVariation (fun n => F n x) N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WitnessInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete interval carries each transferred compact witness. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def witnessInterval (T : SlopeBox) (P : ℝ) : Set ℝ :=
  Icc (T.x - P * T.length) (T.x + P * T.length)

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Area-preserving reference-line coordinates for a top. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.SlopeBox

def referenceChart (T : SlopeBox) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1, z.2 + (T.y + T.slope * (z.1 - T.x)))
  invFun z := (z.1, z.2 - (T.y + T.slope * (z.1 - T.x)))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1, z.2 + (T.y + T.slope * (z.1 - T.x))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1, z.2 - (T.y + T.slope * (z.1 - T.x))))
    fun_prop

def referenceRectangle (T : SlopeBox) (K : ℝ) : Set (ℝ × ℝ) :=
  T.witnessInterval K ×ˢ Icc (-K * T.width) (K * T.width)

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable planar exceptional set attached to one reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def referenceException (T : SlopeBox) (N : ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) : Set (ℝ × ℝ) :=
  T.referenceChart '' LipschitzHilbert.lineCountSlab N (T.witnessInterval K)
    (Icc (-K * T.width) (K * T.width)) lambda

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReferenceLineCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One list-independent angular count and exceptional set per reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def referenceSlope (R : SlopeBox) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u (R.referenceChart (p.2, p.1))

def ReferencePopularCount (R : SlopeBox) (u : ℝ × ℝ → ℝ) (c P θ : ℝ) (M : ℕ)
    (N : ℝ × ℝ → ℝ≥0∞) : Prop :=
  ∀ (p : ℝ × ℝ) (bins : Finset (AngularBins.Bin M)),
    (∀ b ∈ bins, ∃ a d : ℝ, a < d ∧ d - a ≤ 2 * P * R.length ∧ p.2 ∈ Icc a d ∧
      θ * (d - a) ≤ ∫ x in Icc a d,
        AngularBins.binFunction R.slope c (R.referenceSlope u) b (p.1, x)) →
    (bins.card : ℝ≥0∞) ≤ N p

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceFamilyException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The common counting exceptional set

One count is chosen for each reference top, independently of every
separated list. Their finite union has the total-top-area budget of §6.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def referenceFamilyException {ι : Type*} (T : ι → SlopeBox)
    (N : ι → ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i, (T i).referenceException (N i) K lambda

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScalarRestrictedStrong
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

def scalarLift (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] HilbertLp (κ:=Fin 1) mu :=
  (scalarCoordinate.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).compLpL 2 mu

def scalarDrop (mu : Measure X) : HilbertLp (κ:=Fin 1) mu →L[ℝ] Lp ℂ 2 mu :=
  (scalarCoordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).compLpL 2 mu

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

def block (σ : Fin K) (j : ℕ) : Finset ℕ :=
  Finset.Ico (endpoint σ j) (endpoint σ (j + 1))

def lastTransition (σ : Fin K) (j : ℕ) : ℕ := endpoint σ (j + 1) - 1

@[simp] theorem lastTransition_eq (σ : Fin K) (j : ℕ) :
    lastTransition σ j = σ.val + j * K := by
  unfold lastTransition
  rw [endpoint_succ]
  omega

@[simp] theorem tag_val (hK : 0 < K) (i : ℕ) : (tag hK i).val = i % K := rfl

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeLpRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual integral realization of the continuous L2 short-time map. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def shortSlopeLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1.toLp
    (shortSlopeOperator K u f)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxHorizontalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance of the physical slope boxes under horizontal dilation. -/

noncomputable section
namespace LipschitzHilbert.SlopeBox

def horizontalRescale (T : SlopeBox) (r : ℝ) (hr : 0 < r) : SlopeBox where
  x := T.x/r
  y := T.y
  slope := r*T.slope
  length := T.length/r
  width := T.width
  length_pos := div_pos T.length_pos hr
  width_pos := T.width_pos

theorem horizontalRescale_intercept (T : SlopeBox) (r : ℝ) (hr : 0 < r) :
    (T.horizontalRescale r hr).y - (T.horizontalRescale r hr).slope*(T.horizontalRescale r hr).x =
      T.y-T.slope*T.x := by
  change T.y-(r*T.slope)*(T.x/r) = _
  field_simp

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson estimate in real squared L2 energy, for the
actual high/low convolution products. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def smoothDyadicProduct (f : ℝ → ℂ) (h : SchwartzMap ℝ ℂ)
    (ratio : ℝ) (hratio : 0 < ratio) (k : ℤ) (x : ℝ) : ℂ :=
  lineConvolution (lineProjectionKernel dyadicDifference (scale k) (scale_pos _).ne') f x*
    lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
      (mul_pos hratio (scale_pos _)).ne') h x

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
open DyadicLineGrid

def dyadicParaproduct (I : Finset ℤ) (b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ k∈I, lineSchwartzProduct
    (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b) (H k)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleCountingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact first and second moments of finite rectangle counts, in the
normalization of Lacey--Li's covering lemma (3.1)--(3.2). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {ι : Type*}

def rectangleCount (R : ι → Rectangle) (s : Finset ι) (x : Plane) : ℝ≥0∞ :=
  ∑ i∈s, (R i).carrier.indicator (fun _ => (1:ℝ≥0∞)) x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rectangle dilations and containment of intersecting rectangles
with controlled relative angle, as used in Lacey--Li (3.4). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.Rectangle

def dilate (R : Rectangle) (a : ℝ) (ha : 0<a) : Rectangle where
  center := R.center
  axes := R.axes
  long := a*R.long
  short := a*R.short
  short_pos := mul_pos ha R.short_pos
  short_le_long := mul_le_mul_of_nonneg_left R.short_le_long ha.le

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PositiveRectangleAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise monotone positive-integral auxiliary maximal functions for
finite rectangle selection. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

def positiveChartLine (e : Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  positiveHorizontal (f ∘ e.symm) (e x)

def positivePlaneSquare (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  squareSup (f ∘ planeCoordinates) (planeCoordinates.symm x)

variable {ι : Type*} [Fintype ι]

def positiveAuxiliary (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  positivePlaneSquare f x ⊔ Finset.univ.sup (fun i => positiveChartLine (e i) f x)

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

def rectanglePriority (R : ι → Rectangle) (i j : ι) : Prop :=
  (R j).long≤(R i).long ∧
    ((R j).long=(R i).long → (R i).short/(R i).long≤(R j).short/(R j).long)

inductive RectangleCoverRun [DecidableEq ι] (R : ι → Rectangle) (blocked : Finset ι → ι → Prop) :
    Finset ι → Finset ι → List ι → Prop
  | stop (previous : Finset ι) : RectangleCoverRun R blocked previous ∅ []
  | step (previous stock : Finset ι) (i : ι) (tail : List ι)
      (hi : i∈stock) (hpriority : ∀ j∈stock, rectanglePriority R i j)
      (hallowed : ¬blocked previous i)
      (htail : RectangleCoverRun R blocked (insert i previous)
        (rectangleRemaining blocked previous stock i) tail) :
      RectangleCoverRun R blocked previous stock (i::tail)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiSelectionCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual discarded-family covering estimate in the Lacey--Li
selection algorithm. The remaining energy estimate is geometric. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

def maximalBlocked (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (s : Finset ι) (i : ι) : Prop :=
  (R i).carrier ⊆ {x | η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) s) x}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearRectangleSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transverse section bound for intersecting rectangles. This is the
area-to-line reduction behind the near-angle part of Lacey--Li (3.5). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def nearSection (R S : Rectangle) (x : Plane) (B : ℝ) : Set ℝ :=
  Icc (-S.short/2) (S.short/2) ∩
    Icc ((S.orthogonalCoordinates x).2-B*R.short) ((S.orthogonalCoordinates x).2+B*R.short)

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearRectangleLine
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection of a transverse rectangle section onto an actual line.
The dilation is explicit, and no geometric covering hypothesis is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def projectionTime (S : Rectangle) (x w : Plane) (u : ℝ) : ℝ :=
  (u-(S.orthogonalCoordinates x).2) / S.axes.repr w 1

def nearLineParameters (R S : Rectangle) (x w : Plane) (B : ℝ) : Set ℝ :=
  (fun t => (S.orthogonalCoordinates x).2+t*S.axes.repr w 1) ⁻¹' nearSection R S x B

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteTransverseDirections
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite family of transverse directions. Compactness supplies
a universal net, independent of the rectangles later selected. -/
noncomputable section
open Set MeasureTheory Metric
namespace LipschitzHilbert.Rectangle

def transverseFrame (R : Rectangle) : Rectangle where
  center := 0
  axes := R.axes.reindex (Equiv.swap 0 1)
  long := 1
  short := 1
  short_pos := zero_lt_one
  short_le_long := le_rfl

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate projections and exact change of orthogonal
coordinates for the popularity packing in Lacey--Li (3.11). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.Rectangle

def coordinateProjection (S : Rectangle) (E : Set Plane) : Set ℝ :=
  (fun x => (S.orthogonalCoordinates x).1) '' E

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarSlabGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local strips in the reference coordinates, and the coordinate bounds
needed to compare their overlap with a transverse line through a small
selected rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def stripSlab (S : Rectangle) (c l : ℝ) : Set Plane :=
  S.orthogonalCoordinates ⁻¹'
    (Icc (c-l/2) (c+l/2) ×ˢ Icc (-S.short/2) (S.short/2))

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StripSubdivision
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact binary subdivision of the reference strips. Shared boundary
fibers have zero planar measure, so closed strip masses add exactly. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LipschitzHilbert

def stripMass {ι : Type*} (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_UniformTranslatedProfileBounds
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual profile constant used by the packet estimates is controlled
uniformly for the polynomially weighted translated profiles. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def envelopeSeminorm (n : ℕ) : Seminorm ℝ PlanarSchwartz :=
  (SchwartzMap.seminorm ℝ 0 0).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun z : ℝ×ℝ => (planarPolynomialWeight n z:ℂ))).restrictScalars ℝ).toLinearMap

def profileControlSeminorm (n : ℕ) : Seminorm ℝ PlanarSchwartz :=
  ∑ i : Fin 3, (
    (envelopeSeminorm n).comp (profileJetCLM i).toLinearMap+
    (envelopeSeminorm n).comp (profileHorizontalCLM.comp (profileJetCLM i)).toLinearMap+
    (envelopeSeminorm n).comp (profileVerticalCLM.comp (profileJetCLM i)).toLinearMap)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariableEndpointOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 control of the error caused by measurable changes of both
time endpoints, with no regularity assumption on the endpoint factor. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def endpointKernelError (epsilon R : ℝ) (a : (ℝ×ℝ) → ℝ)
    (p : ℝ×(ℝ×ℝ)) : ℂ :=
  sharpTimeKernel (epsilon*a p.2) (R*a p.2) p.1-sharpTimeKernel epsilon R p.1

def endpointErrorOperator (epsilon R : ℝ) (a u : (ℝ×ℝ) → ℝ)
    (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, endpointKernelError epsilon R a (t,z)*shortSample u f t z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ProductPVLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual product-coordinate principal value is linear on Schwartz
inputs, before any boundedness theorem is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem productPV_schwartz_add (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (f g : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R (f+g : SchwartzMap (ℝ×ℝ) ℂ) z=
      productSlopePrincipalValue u R f z+productSlopePrincipalValue u R g z := by
  apply tendsto_nhds_unique (shortSharp_tendsto_productSlopePrincipalValue u (f+g)
    (f+g).differentiable R hR hRs z)
  apply ((shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRs z).add
    (shortSharp_tendsto_productSlopePrincipalValue u g g.differentiable R hR hRs z)).congr'
  exact Eventually.of_forall fun n => (shortSlopeOperator_schwartz_add _
    (sharpTimeKernel_integrable _ R (pvInnerRadius_pos R hR n) hR) u f g z).symm

theorem productPV_schwartz_smul (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (c : ℂ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=
      c*productSlopePrincipalValue u R f z := by
  apply tendsto_nhds_unique (shortSharp_tendsto_productSlopePrincipalValue u (c • f)
    (c • f).differentiable R hR hRs z)
  apply ((shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRs z).const_mul c).congr'
  exact Eventually.of_forall fun _ => (shortSlopeOperator_schwartz_smul _ u f c z).symm

def productPVSchwartzLM (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R) (hRs : R≤1/4) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) where
  toFun := fun f => productSlopePrincipalValue u R f
  map_add' f g := funext (productPV_schwartz_add u R hR hRs f g)
  map_smul' c f := funext (productPV_schwartz_smul u R hR hRs c f)

@[simp] theorem productPVSchwartzLM_apply (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    productPVSchwartzLM u R hR hRs f=productSlopePrincipalValue u R f := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution on the L2 quotient, with its actual integral representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalConvolutionLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1.toLp
    (verticalConvolution K f)

end LipschitzHilbert.PacketRepresentation

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

def verticalBinLp (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  verticalConvolutionLp (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconstruction of a vertical frequency band for arbitrary L2 inputs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def verticalProfileLp (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  verticalConvolutionLp (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBoundedSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

theorem finiteFunctionSum_memLp {n : ℕ} (f : Fin n → (ℝ×ℝ) → ℂ)
    (h : ∀ i, MemLp (f i) 2 planeMeasure) :
    MemLp (fun z => ∑ i, f i z) 2 planeMeasure := by
  simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun i _ => h i)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpVerticalCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical-profile commutator has a bound independent of the
inner cutoff. Its principal-time integral has the same bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpVerticalCommutator (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel q W center)
    (shortSlopeOperator (sharpTimeKernel epsilon R) u f)-
  shortSlopeOperator (sharpTimeKernel epsilon R) u
    (verticalConvolution (verticalProfileKernel q W center) f)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inhomogeneous coefficient reconstruction: the low-frequency
part is retained, and the finite high-frequency tail telescopes. -/
noncomputable section
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lineDyadic (f : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f

def lineLowpass (f : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProjection reassemblyLow (scale k) (scale_pos k).ne' f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite high/low sum: geometric Schur summation inside
each high-frequency output annulus, then finite Fourier overlap. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def highLowPiece (m b h : SchwartzMap ℝ ℂ) (i j : ℤ) : SchwartzMap ℝ ℂ :=
  if i+5≤j then
    lineSchwartzCommutator m (lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne' b)
      (schwartzDerivative 1 (lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h))
  else 0

def highLowRow (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) : SchwartzMap ℝ ℂ :=
  ∑ j∈J, highLowPiece m b h i j

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowHighSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete low/high commutator sum has a bound independent of
both the number and the location of the retained dyadic frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lowHighPiece (m b h : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzCommutator m
    (lineSchwartzProjection reassemblyLow (16*scale k) (by have := scale_pos k; positivity) b)
    (schwartzDerivative 1 (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' h))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DyadicNearbyInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine nearby dyadic input frequencies form an actual Schwartz
family with uniform spectral and square-energy bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def nearbyInputPiece (h : SchwartzMap ℝ ℂ) (i j : ℤ) : SchwartzMap ℝ ℂ :=
  if i-4≤j ∧ j≤ i+4 then lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h else 0

def nearbyInput (J : Finset ℤ) (h : SchwartzMap ℝ ℂ) (i : ℤ) : SchwartzMap ℝ ℂ :=
  ∑ j∈J, nearbyInputPiece h i j

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal dilation for Schwartz packets, including the Fourier
and measure factors needed to normalize different top lengths. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert

theorem schwartzDilation_fourier (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (ξ : ℝ) :
    𝓕 (schwartzDilation f r hr) ξ = |r⁻¹| • 𝓕 f (ξ/r) := by
  simp only [SchwartzMap.fourier_coe,Real.fourier_real_eq,schwartzDilation_apply]
  have hphase (x : ℝ) : -(r*x*(ξ/r)) = -(x*ξ) := by field_simp
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => Real.fourierChar (-(x*(ξ/r))) • f x) r
  simpa only [hphase] using h

theorem schwartzDilation_low (f : SchwartzMap ℝ ℂ) (r a : ℝ) (hr : 0 < r)
    (h : ∀ ξ, |ξ| < a/r → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < a) :
    𝓕 (schwartzDilation f r hr.ne') ξ = 0 := by
  rw [schwartzDilation_fourier,h (ξ/r),smul_zero]
  rw [abs_div,abs_of_pos hr]
  exact (div_lt_div_iff_of_pos_right hr).mpr hξ

theorem schwartzDilation_high (f : SchwartzMap ℝ ℂ) (r b : ℝ) (hr : 0 < r)
    (h : ∀ ξ, b/r < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : b < |ξ|) :
    𝓕 (schwartzDilation f r hr.ne') ξ = 0 := by
  rw [schwartzDilation_fourier,h (ξ/r),smul_zero]
  rw [abs_div,abs_of_pos hr]
  exact (div_lt_div_iff_of_pos_right hr).mpr hξ

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz reproducing kernels for the long-tree frequency
rectangles. A smooth compact-frequency cutoff is constructed, rather
than adding a reproduction hypothesis to the tree estimate. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution
namespace LipschitzHilbert

/-- The normalized spatial dilation has the correct scale and mass
factor for frequency cutoffs at scale `1/r`. -/
def scaledReproducingKernel (K : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0 < r) :
    SchwartzMap ℝ ℂ := r⁻¹ • schwartzDilation K r⁻¹ (inv_ne_zero hr.ne')

@[simp] theorem scaledReproducingKernel_apply (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0 < r) (x : ℝ) :
    scaledReproducingKernel K r hr x=(r⁻¹:ℂ)*K (x/r) := by
  simp only [scaledReproducingKernel,smul_apply,schwartzDilation_apply,
    Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
  rw [mul_comm r⁻¹ x]

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

def vectorHorizontalSlice (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (y : ℝ) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => (x,y+0*x))
    (affineLine_temperate y 0) (affineLine_antilipschitz y 0) f

@[simp] theorem vectorHorizontalSlice_apply
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y x : ℝ) :
    vectorHorizontalSlice f y x=f (x,y) := by
  change f (x,y+0*x)=f (x,y)
  simp only [zero_mul,add_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PVCommutatorSymbolLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity in the frequency symbol for the actual PV commutator,
without assuming boundedness of the full principal-value operator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def schwartzVerticalProfileLM (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap (ℝ×ℝ) ℂ where
  toFun p := schwartzVerticalProjection p W 0 f
  map_add' p q := schwartzVerticalProjection_add_profile p q W f
  map_smul' c p := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_smul,smul_apply,
      smul_eq_mul,RingHom.id_apply]
    ring

@[simp] theorem schwartzVerticalProfileLM_apply (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (p : SchwartzMap ℝ ℂ) :
    schwartzVerticalProfileLM W f p=schwartzVerticalProjection p W 0 f := rfl

def pvCommutatorSymbolLM (W : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) :=
  boundedVerticalMultiplierLM W hW (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u hum f f.differentiable R hR hRs)
    (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z (hub z) f R hR)-
  (productPVSchwartzLM u R hR hRs).comp (schwartzVerticalProfileLM W f)

@[simp] theorem pvCommutatorSymbolLM_apply (W : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (p : SchwartzMap ℝ ℂ) :
    pvCommutatorSymbolLM W hW u hum hub R hR hRs f p=
      principalValueProfileCommutator p W 0 R u f := rfl

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

def annularPVComm (N : ℕ) (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (i : Fin (2*N+1)) : (ℝ×ℝ) → ℂ :=
  principalValueProfileCommutator (annularProfile N i) 1 0 R u f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite annular convolutions converge pointwise to the
actual principal value. No L2 estimate for that principal value is used. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def annularPVPartial (N : ℕ) (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  ∑ n∈Finset.range (2*N+1), verticalConvolution
    (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N n) 0)
    (productSlopePrincipalValue u R f)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandL2Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous L2 realization of the actual short-time band pairing. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def bandL2Operator (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (shortL2Operator K hKm hK u hu).comp (verticalL2Projection p w)

def bandL2Pairing (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  (isBoundedBilinearMap_inner (𝕜:=ℂ)).toContinuousLinearMap.flip.comp
    ((bandL2Operator K hKm hK u hu p w).restrictScalars ℝ)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal Whitney cells for the ordinary tree estimate. An allowed
cell has no tile of shorter length whose center meets its triple. A
maximal allowed cell obtains its concrete witness from its parent. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
attribute [local instance] Classical.propDecidable

theorem point_center_bound (k j : ℤ) {z : ℝ} (hz : z ∈ cell 0 k j) :
    |z-center k j| ≤ scale k/2 := by
  have hr : left 0 k (j+1)=left 0 k j+scale k := by
    simp only [left,Int.cast_add,Int.cast_one]
    ring
  change left 0 k j ≤ z ∧ z < left 0 k (j+1) at hz
  rw [hr] at hz
  unfold center
  exact abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem scale_mono {k l : ℤ} (hkl : k ≤ l) : scale k ≤ scale l :=
  zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkl

/-- A finite family of positive tile lengths has a common strictly smaller scale. -/
theorem exists_small_scale {ι : Type*} (tiles : Finset ι) (ell : ι → ℝ)
    (hpos : ∀ i ∈ tiles, 0 < ell i) :
    ∃ k : ℤ, ∀ i ∈ tiles, scale k < ell i := by
  classical
  induction tiles using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i tiles hi ih =>
    obtain ⟨k,hk⟩ := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    obtain ⟨l,hl,_⟩ := exists_mem_Ioc_zpow
      (hpos i (Finset.mem_insert_self i tiles)) (by norm_num : (1:ℝ) < 2)
    refine ⟨min k l,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (scale_mono (min_le_right k l)).trans_lt hl
    · exact (scale_mono (min_le_left k l)).trans_lt (hk j hj)

/-- Every real point lies in a maximal allowed interval. The upper scale
is obtained from one actual tile, rather than an assumed global cutoff. -/
theorem exists_whitney_cover {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (hne : tiles.Nonempty) (hpos : ∀ i ∈ tiles, 0 < ell i) (z : ℝ) :
    ∃ k j, Whitney tiles x ell k j ∧ z ∈ cell 0 k j := by
  obtain ⟨k,hk⟩ := exists_small_scale tiles ell hpos
  obtain ⟨i,hi⟩ := hne
  obtain ⟨l,_,hl⟩ := exists_mem_Ico_zpow
    (show 0 < max (ell i) |x i-z| + 1 by
      have := le_max_right (ell i) |x i-z|
      linarith [abs_nonneg (x i-z)]) (by norm_num : (1:ℝ) < 2)
  let top := max k (l+1)
  have hbig : max (ell i) |x i-z| < scale top := by
    exact (lt_trans (by linarith) hl).trans_le (scale_mono (le_max_right k (l+1)))
  have htop : ¬Allowed tiles x ell top (index 0 top z) := by
    intro h
    have ha := h i hi ((le_max_left (ell i) |x i-z|).trans hbig.le)
    have hd := point_center_bound top (index 0 top z) (mem_index_cell 0 top z)
    have ht := abs_sub_le (x i) z (center top (index 0 top z))
    have hz := (le_max_right (ell i) |x i-z|).trans hbig.le
    linarith only [ha,hd,ht,hz]
  have hstart : Allowed tiles x ell k (index 0 k z) := by
    intro j hj hlen
    exact False.elim ((hk j hj).not_ge hlen)
  obtain ⟨m,j,hm,hsub⟩ := exists_maximalBad (le_max_left k (l+1)) hstart
  have hz := hsub (mem_index_cell 0 k z)
  refine ⟨m,j,⟨hm.2.1,?_⟩,hz⟩
  have hmt : m < top := by
    apply lt_of_le_of_ne hm.1
    intro he
    apply htop
    have hz' : z ∈ cell 0 top j := by simpa only [he] using hz
    rw [index_eq_of_mem hz']
    simpa only [he] using hm.2.1
  exact hm.2.2 (m+1) (parent 0 m j) (by omega) (by omega)
    (cell_subset_parent 0 m j)

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

/-- Every original item occurs in exactly one slot. -/
def slotItemsEquiv (j : Fin N) :
    (Σ b : Fin B, P.SlotItem hcard b j) ≃ Σ l : P.labels j, Item j l where
  toFun p := p.2.1
  invFun p := ⟨P.slotEmbedding hcard j p.1, ⟨p, rfl⟩⟩
  left_inv := by
    rintro ⟨b, ⟨p, hp⟩⟩
    cases hp
    rfl
  right_inv := fun _ => rfl

end SourceLabeledLattice

end LipschitzHilbert

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

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def physicalSelectedWave (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d q.1 then P.physicalPacket t q.1 q.2 k z else 0

def physicalCoefficient (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) :
    EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume)
    (fun q : Σ j, ι j => P.length q.1 * P.width)
    (P.physicalSelectedWave t d v) g ⟨j, u⟩

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacement synthesis packets retain the local budget of the actual
integral-defined analyzing coefficients. The same coefficient budget applies to top weights and covariant
derivative packets. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert.PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def analyzedReplacement (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ)
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant/P.length j)*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y))
    (C : ℝ) (hC : 0 < C) (wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (hb : ∀ j i k x, ‖wave j i k x‖ ≤ C*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y))
    (hdb : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤ (C/P.length j)*
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
        lineEnvelope (P.centerZ j i) P.width 2 y)) : LinePacketFamily N κ ι :=
  (P.analyzedLine d v hv g hg hg1 y hderiv).replaceWaves C hC wave hb hdb

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopRawPacketData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local packet data used by the top concentration argument. Every field
is a raw kernel, geometry, regularity, or Fourier-support condition; no
concentration or coefficient-budget assumption is included. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def topPacketAmplitude (P : PlanarPacketFamily N κ ι) (Ab Am : ℝ) (D : ℕ) : ℝ :=
  let C := topPairConstant P.constant (8*D+1)
  P.coefficientScale*256^(8*D+1)*
    (24*lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) 2)

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual-center localization supplies the top geometry after snapping.
The full one-mesh displacement is retained in each hypothesis. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem family_centerX_error (j : Fin N) (u : ι j) :
    |P.actualX j u-P.family.centerX j u| ≤ P.length j := by
  simpa only [actualX,family_centerX,snappedSite] using
    snappedLatticeSite_horizontal (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) (P.length_pos j) (P.site j u)

theorem family_centerZ_error (j : Fin N) (u : ι j) :
    |P.actualZ j u-P.family.centerZ j u| ≤ P.width := by
  simpa only [actualZ,family_centerZ,snappedSite] using
    snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)

theorem family_centerX_local (j : Fin N) (u : ι j) (x R : ℝ)
    (hloc : |P.actualX j u-x|+P.length j ≤ R) :
    |P.family.centerX j u-x| ≤ R := by
  calc
    _ ≤ |P.family.centerX j u-P.actualX j u|+|P.actualX j u-x| := abs_sub_le _ _ _
    _ ≤ P.length j+|P.actualX j u-x| := by
      gcongr
      simpa only [abs_sub_comm] using P.family_centerX_error j u
    _ ≤ R := by linarith

theorem family_centerZ_local (j : Fin N) (u : ι j) (y R : ℝ)
    (hloc : |P.actualZ j u-y|+P.width ≤ R) :
    |P.family.centerZ j u-y| ≤ R := by
  calc
    _ ≤ |P.family.centerZ j u-P.actualZ j u|+|P.actualZ j u-y| := abs_sub_le _ _ _
    _ ≤ P.width+|P.actualZ j u-y| := by
      gcongr
      simpa only [abs_sub_comm] using P.family_centerZ_error j u
    _ ≤ R := by linarith

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeRawData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the top concentration data from actual source packets.
The premises describe physical spectrum, actual centers and fixed-order
profile bounds; neither concentration nor a coefficient budget is assumed. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

structure SourceLatticeSpectralData (P : SourceLatticePacket N κ ι) where
  referenceSlope : ℝ
  w : ℝ
  cStar : ℝ
  cEta : ℝ
  CEta : ℝ
  cb : ℝ
  Cb : ℝ
  w_pos : 0 < w
  cEta_pos : 0 < cEta
  cb_nonneg : 0 ≤ cb
  Cb_nonneg : 0 ≤ Cb
  spectrum : ∀ j u k ξ η,
    planarAngularFourier (P.physicalPacket referenceSlope j u k) (ξ,η) ≠ 0 →
      |ξ+(referenceSlope+P.rowSlope j)*η| ≤ cStar/P.length j ∧
        cEta ≤ w*η ∧ w*η ≤ CEta
  selector : ∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j| ∧
    |P.rowSlope j| ≤ Cb*w/P.length j

namespace SourceLatticeSpectralData
variable {P : SourceLatticePacket N κ ι}

def lo (S : SourceLatticeSpectralData P) : ℝ := (S.cEta*S.cb-S.cStar)/(2*Real.pi)
def hi (S : SourceLatticeSpectralData P) : ℝ := (S.CEta*S.Cb+S.cStar)/(2*Real.pi)

theorem raw_cutoffs (S : SourceLatticeSpectralData P)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ ξ, |ξ| < (S.lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (S.hi/P.topLength)*(2:ℝ)^j.val < |ξ| → 𝓕 (P.raw i j u k y) ξ = 0) :=
  P.raw_fourier_cutoffs S.referenceSlope S.w S.cStar S.cEta S.CEta S.cb S.Cb
    S.w_pos S.cEta_pos S.cb_nonneg S.Cb_nonneg S.spectrum S.selector i j u k y

end SourceLatticeSpectralData

namespace SourceLatticePacket
variable (P : SourceLatticePacket N κ ι)

theorem raw_top_bound (D : ℕ) (horder : 3+2*(8*D+1) ≤ P.order)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant*
      (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) x *
        lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
  apply (P.raw_bound i j u k y x).trans
  rw [family_centerX,family_centerZ]
  apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_antitone _ _ _ (by omega)) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

theorem raw_top_derivative_bound (D : ℕ) (horder : 3+2*(8*D+1) ≤ P.order)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.constant/P.length j)*
      (lineEnvelope (P.family.centerX j u) (P.length j) (3+2*(8*D+1)) x *
        lineEnvelope (P.family.centerZ j u) P.width (2+2*(8*D+1)) y) := by
  apply (P.raw_derivative_bound i j u k y x).trans
  rw [family_centerX,family_centerZ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_antitone _ _ _ (by omega)) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolarizedInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cross-profile source intervals and their four self-family
representation. Every coefficient is the original selected integral. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

def rawInterval (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  planarPacketInterval coeff (fun j u k t s => P.raw i j u k t s) lower upper x y

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

def slottedAlt (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ := alt j p.1.1 p.1.2 k

include hAlt in
theorem slottedAlt_bound (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) :
    planarProfileConstant (P.slottedAlt hcard alt b j p k)
        (2 * (P.slotted hcard b).order) ≤ (P.slotted hcard b).profileBound :=
  hAlt j p.1.1 p.1.2 k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSizeSelectionEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint recorded tests and the exact energy bookkeeping for the
finite signed size-selection run. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def recordedSizeTests (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => P.sizeTestPackets negative w cb cell grid R T ::
      recordedSizeTests negative w cb A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeTest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unsigned size tests for unrestricted packet families. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def unsignedSizeTestEnergy (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox) : ℝ :=
  ∑ q∈R, if P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
    cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| then
    ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketReferenceSpectrum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted family passes its original spectra to every local
reference lattice without enlarging either frequency strip. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

/-- The local family carries the original selector as a function of the
physical direction. Only its label type changes. -/
def referenceSelector (b : ∀ j, P.labels j → κ → ℝ → ℂ) :
    ∀ j, (Q).labels j → κ → ℝ → ℂ :=
  fun j l => b j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarPositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive planar kernel in coordinates (x,Y), and its exact
factorization into the two line convolutions used for concentration. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

def planarPositiveConvolution (l W : ℝ) (f : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, (lineKernel l (x-z.1) * lineKernel W (y-z.2)) * f z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

def branchingNat (L : ℝ) : ℕ := (2 ^ stepExponent L) ^ blockCount L

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCarrierFreeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive error envelope must not inherit the large carrier bound
of the wide reference cone. The exact raw norm is independent of it. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

/-- The absolute raw-envelope constant contains no frequency or carrier. -/
def absoluteConstant (P : SourceLatticePacket N κ ι) : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem absoluteConstant_pos : 0 < P.absoluteConstant := by
  have hR : 0 < P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  have hB := P.profileBound_pos
  unfold absoluteConstant
  positivity

theorem snappedSite_injective (j : Fin N) (l : P.labels j) :
    Function.Injective (P.snappedSite j l) :=
  (snappedLatticeSite_injective _ _ _ _ _).comp (P.site_injective j l)

theorem raw_swapped_joint_measurable (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) :
    Measurable (fun z : ℝ×ℝ => P.raw i j l u k z.2 z.1) := by
  have hm : Measurable (fun z : ℝ×ℝ => P.raw i j l u k z.1 z.2) :=
    (modulatedPlanarJet_continuous (P.profile j l u k) (P.actualX j l u) (P.actualZ j l u)
      (P.length j) P.width (-P.rowSlope j l) (P.frequency k) P.scale
      (P.length_pos j).ne' i).measurable
  intro s hs
  change MeasurableSet (Prod.swap ⁻¹' ((fun z : ℝ×ℝ => P.raw i j l u k z.1 z.2) ⁻¹' s))
  exact (measurable_swap : Measurable (Prod.swap : ℝ×ℝ → ℝ×ℝ)) (hm hs)

theorem raw_absolute_envelope (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ ((2^P.order*P.profileBound)*P.ratioBound^2)*
      (lineEnvelope (P.actualX j l u) (P.length j) P.order x*
        lineEnvelope (P.actualZ j l u) P.width P.order y) := by
  let C := P.ratioBound^2*P.profileBound
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) P.profileBound_pos.le
  have hprofile : ∀ z, ‖planarProfileJet (P.profile j l u k) (P.scale/P.width) i z‖ ≤ C*
      (lineEnvelope 0 1 (2*P.order) z.1*lineEnvelope 0 1 (2*P.order) z.2) := by
    intro z
    exact (planar_profile_envelope (P.profile j l u k) (2*P.order) (P.scale/P.width)
      P.ratioBound P.ratioBound_ge_one P.scale_bound i z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (P.profile_bound j l u k) (sq_nonneg _))
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have hshear : |(-P.rowSlope j l)*P.length j/P.width| ≤ 1 := by
    simpa only [length,neg_mul,neg_div,abs_neg] using P.shear_bound j l
  have h := modulatedPlanarSlice_envelope (planarProfileJet (P.profile j l u k) (P.scale/P.width) i)
    (P.actualX j l u) (P.actualZ j l u) (P.length j) P.width (-P.rowSlope j l) (P.frequency k)
    y C (P.length_pos j).ne' P.order hC hshear hprofile x
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [raw,modulatedPlanarJet,div_eq_mul_inv,C])
  ring

theorem raw_absolute_tileEnvelope (horder : 6 ≤ P.order) (i : Fin 3)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    ‖P.raw i j l u k z.2 z.1‖ ≤ P.absoluteConstant*
      tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 z := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) z.1 z.2 (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [← pow_add]
    congr 1
    omega
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have hs' := mul_le_mul_of_nonneg_left hs hA
  rw [hp] at hs'
  have hraw := (P.raw_absolute_envelope i j l u k z.2 z.1).trans hs'
  apply hraw.trans
  change ((2^P.order*P.profileBound)*P.ratioBound^2)*
    (3^(2*P.order)*(lineEnvelope _ _ P.order z.1*lineEnvelope _ _ P.order z.2)) ≤ _
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceLabeledAngularErrorData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def angularErrorFamily :
    LabeledAngularErrorFamily N (fun j => P.labels j) κ (fun j l => Item j l) where
  topLength := P.topLength
  width := P.width
  angleBase := a
  referenceSlope := t
  smallRatio := c
  wideConstant := Cwide
  exponent := E
  wideExponent := J
  packetBound := P.absoluteConstant
  multiplierBound := M
  multiplierLip := Lip
  radius := radius
  radiusBound := K
  multiplicity := H
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  angleBase_pos := ha
  smallRatio_pos := hc
  smallRatio_le := hc1
  wideConstant_le := hC
  wideRatio_ge := hwide
  packetBound_nonneg := P.absoluteConstant_pos.le
  multiplierBound_nonneg := hM
  multiplierLip_nonneg := hLip
  radius_le := hradius
  direction := fun z => v (slopeShear t z)
  direction_measurable := hv.comp (slopeShear t).measurable
  test := fun z => g (slopeShear t z)
  test_measurable := hg.comp (slopeShear t).measurable
  test_bound := fun _ => hg1 _
  originX := fun _ _ => 0
  originY := fun _ _ => 0
  slope := fun j l => t+P.rowSlope j l
  localMultiplicity := hlocal
  site := P.snappedSite
  site_injective := P.snappedSite_injective
  multiplier := b
  multiplier_measurable := hb
  multiplier_bounded := hbM
  multiplier_support := hsupport
  multiplier_near := hnear
  multiplier_far := hfar
  wave := fun j l u k z => P.raw 0 j l u k z.2 z.1
  wave_measurable := fun j l u k => P.raw_swapped_joint_measurable 0 j l u k
  wave_bound := by
    intro j l u k z
    simpa only [zero_add,length] using P.raw_absolute_tileEnvelope horder 0 j l u k z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected tree from an unrestricted packet lattice has a genuine
bounded reference lattice. Only the selected packets are present, and
their original physical waves are preserved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)

theorem selectedItem_mem (j : Fin N) (l : P.selectedLabels S j) (u : P.SelectedItem S j l) :
    (⟨j,⟨P.selectedOriginalLabel S j l,u.val⟩⟩ : P.PacketIndex)∈S := by
  obtain ⟨h,hu⟩ := u.property
  exact hu

variable (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)

local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedReferenceEquiv : (Q).PacketIndex ≃ S where
  toFun := fun q => ⟨⟨q.1,⟨P.selectedOriginalLabel S q.1 q.2.1,q.2.2.val⟩⟩,
    P.selectedItem_mem S q.1 q.2.1 q.2.2⟩
  invFun := fun q => ⟨q.val.1,⟨
    ⟨q.val.2.1.val,Finset.mem_filter.mpr ⟨q.val.2.1.property,
      ⟨q.val.2.1.property,q.val.2.2,q.property⟩⟩⟩,
    ⟨q.val.2.2,⟨q.val.2.1.property,q.property⟩⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMultiscaleEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finitely labeled family inherits multiscale synthesis
through its exact slot partition. The only additional factor is the
explicit fixed label bound, with no scale or vector-dimension loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def physicalLabeledSynthesis (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, planarFixedSynthesis (fun p : Σ l : P.labels j, Item j l => c j p.1 p.2)
    (fun p k => P.physicalPacket t j p.1 p.2 k) z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted interval-maximal synthesis on actual separated
source trees, conditional only on the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert


namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def physicalTreePartial (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis (c j) (P.physicalPacket t j) z) n

def physicalTreeVariation (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  cubicVariation (fun n => P.physicalTreePartial t c n z) N

def physicalTreeMaximal (P : SourceLatticePacket N κ ι) (t : ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

end SourceLatticePacket


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

def physicalTreeMaximal (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A symmetric reference cutoff is exactly three one-sided cutoffs,
including its boundary. No level-set nullity is required. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalCenteredWave (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) : ℂ :=
  if |v z-t| ≤ d q.1 then P.physicalPacket s q.1 q.2 k z else 0

def physicalCenteredCoefficient (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (u : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun q : Σ j, ι j => P.length q.1*P.width)
    (P.physicalCenteredWave s t d v) g ⟨j,u⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual top masks restricted to the affine reference line. The
bandwidth and derivative costs retain the exact top length and slope. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.SlopeBox

def maskLineA (T : SlopeBox) (L A : ℝ) : ℝ := (1/T.length)/L^A
def maskLineB (T : SlopeBox) (L A : ℝ) : ℝ := (-T.x/T.length)/L^A
def maskLineC (T : SlopeBox) (L A t : ℝ) : ℝ := ((t-T.slope)/T.width)/L^A
def maskLineD (T : SlopeBox) (L A y : ℝ) : ℝ := ((y-T.y+T.slope*T.x)/T.width)/L^A

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smallness of the actual top-mask derivative and Fourier radius
follows from packet shortness and the fixed narrow cone. All scale
parameters cancel before choosing the large manuscript parameter. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SlopeBox

theorem maskLineRate_packet_le (T : SlopeBox) (L A t ell cone : ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hshort : ell ≤ T.length)
    (hcone : |t-T.slope| ≤ cone*T.width/ell) :
    2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|) ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell := by
  have hx : 1/T.length ≤ 1/ell := one_div_le_one_div_of_le hell hshort
  have hy : |t-T.slope|/T.width ≤ cone/ell := by
    apply (div_le_iff₀ T.width_pos).mpr
    convert hcone using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsum : 1/T.length+|t-T.slope|/T.width ≤ (1+cone)/ell := by
    calc
      _ ≤ 1/ell+cone/ell := add_le_add hx hy
      _ = _ := by ring
  unfold maskLineA maskLineC
  rw [abs_div,abs_div,abs_div,abs_div,abs_one,
    abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    abs_of_pos (Real.rpow_pos_of_pos hL A)]
  calc
    _ = (2*(⌈L⌉₊:ℝ)/L^A)*(1/T.length+|t-T.slope|/T.width) := by ring
    _ ≤ (2*(⌈L⌉₊:ℝ)/L^A)*((1+cone)/ell) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A single scalar choice gives both derivative control and the
half-annulus margin, uniformly over top lengths and packet scales. -/
theorem scaled_maskLine_bounds (T : SlopeBox) (L A t ell cone r lo : ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hr : 0 < r) (hshort : ell ≤ T.length)
    (hcone : |t-T.slope| ≤ cone*T.width/ell)
    (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo)) :
    2*(⌈L⌉₊:ℝ)*(|r*T.maskLineA L A|+|r*T.maskLineC L A t|) ≤ 1/(ell/r) ∧
    (2*(⌈L⌉₊:ℝ))*((|r*T.maskLineA L A|+|r*T.maskLineC L A t|)/(2*Real.pi)) ≤
      (lo/2)/(ell/r) := by
  have hrate := T.maskLineRate_packet_le L A t ell cone hL hell hshort hcone
  have heq : 2*(⌈L⌉₊:ℝ)*(|r*T.maskLineA L A|+|r*T.maskLineC L A t|) =
      r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) := by
    rw [abs_mul,abs_mul,abs_of_pos hr]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hrate hr.le
  have hfirst : r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) ≤ r/ell := by
    calc
      _ ≤ r*((2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell) := hscaled
      _ ≤ r*(1/ell) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hsmall.trans (min_le_left _ _)) hell.le) hr.le
      _ = _ := by ring
  have hsecond : r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) ≤
      r*(Real.pi*lo)/ell := by
    calc
      _ ≤ r*((2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell) := hscaled
      _ ≤ r*((Real.pi*lo)/ell) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hsmall.trans (min_le_right _ _)) hell.le) hr.le
      _ = _ := by ring
  constructor
  · rw [heq]
    convert hfirst using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [hr.ne',hell.ne']
  · have h := (div_le_div_of_nonneg_right hsecond (by positivity : 0 ≤ 2*Real.pi))
    rw [← heq] at h
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp [hr.ne',hell.ne',Real.pi_ne_zero])

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square and cubic-variation moments for the actual normalized
reference collection. Its root window need only contain retained
lengths, so the short-packet restriction introduces no larger window. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

def referenceSquareMomentCost (B : ℝ) (grid : FiniteLineGrid) (p : ℝ) : ℝ≥0∞ :=
  (2:ℝ≥0∞)^(p/2)*(7*ENNReal.ofReal (((p/2)*(((grid.branching:ℝ)+2)*
    (2*LinePacketFamily.squareMeanConstant B+48*(4*Real.pi)^4))/Real.log (3/2))^(p/2))+
    (ENNReal.ofReal (LinePacketFamily.squareMeanConstant B))^(p/2))

def referenceVariationMomentCost (M C B : ℝ) (grid : FiniteLineGrid) (p : ℝ) : ℝ≥0∞ :=
  (2:ℝ≥0∞)^p*(7*ENNReal.ofReal ((p*(((grid.branching:ℝ)+2)*
    (2*Real.sqrt (M*C^2*B+1)+4*(C*(4*Real.pi)^2)))/Real.log (3/2))^p)+
    (ENNReal.ofReal (Real.sqrt (M*C^2*B+1)))^p)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked reference family synthesizes the original physical top
mask and alternate packet. Its analyzing coefficient is unchanged, so
the normalization is the original `constant * pi^2`, not its doubled
synthesis-envelope constant. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem mixedReferenceLine_length (y : ℝ) (j : Fin N) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).length j =
      P.length j/P.topLength := by
  change (P.topLength/P.topLength)/(2:ℝ)^j.val =
    (P.topLength/(2:ℝ)^j.val)/P.topLength
  ring

variable (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

theorem normalized_mask_rate
    (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    ∀ j u (_k : κ), 2*(⌈L⌉₊:ℝ)*
      (|P.topLength*(T j u).maskLineA L A|+
       |P.topLength*(T j u).maskLineC L A t|) ≤
      1/(P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).length j := by
  intro j u k
  rw [abs_mul,abs_mul,abs_of_pos P.topLength_pos,
    P.mixedReferenceLine_length c hc alt hAlt d v hv g hg hg1]
  calc
    _ = P.topLength*(2*(⌈L⌉₊:ℝ)*
        (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|)) := by ring
    _ ≤ P.topLength*(1/P.length j) :=
      mul_le_mul_of_nonneg_left (hrate j u) P.topLength_pos.le
    _ = 1/(P.length j/P.topLength) := by simp [div_eq_mul_inv,mul_comm]

/-- The actual top mask is applied only to the synthesis wave. -/
def maskedMixedReferenceLine
    (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    LinePacketFamily N κ ι :=
  (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).sincMasked ⌈L⌉₊
    (fun j u _ => P.topLength*(T j u).maskLineA L A)
    (fun j u _ => (T j u).maskLineB L A)
    (fun j u _ => P.topLength*(T j u).maskLineC L A t)
    (fun j u _ => (T j u).maskLineD L A y)
    (P.normalized_mask_rate c hc alt hAlt d v hv g hg hg1 T L A t y hrate)

variable (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
  (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)

/-- The exact physical band, with the original analyzing coefficient,
the physical top mask, and the original alternate synthesis packet. -/
def maskedMixedReferenceBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k *
      ((T j u).mask L A (x,y+t*x):ℂ)*(P.withProfile alt hAlt).raw 0 j u k y x)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedPhysicalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical shortness and the narrow reference cone discharge the
mask-rate hypotheses. The resulting masked mixed moments use the
original integral coefficients and actual top masks. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem physicalReferenceMaskRate (P : SourceLatticePacket N κ ι)
    (T : ∀ j, ι j → SlopeBox) (L A t cone lo : ℝ) (hL : 0 < L)
    (hshort : ∀ j u, P.length j ≤ (T j u).length)
    (hcone : ∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j)
    (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo)) :
    ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j := by
  intro j u
  simpa only [one_mul,div_one] using
    ((T j u).scaled_maskLine_bounds L A t (P.length j) cone 1 lo
      hL (P.length_pos j) zero_lt_one (hshort j u) (hcone j u) hsmall).1

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural-order forms of the exact reference moments. The moment grid
may have fixed binary branching, independent of the source angular step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SourceLatticePacket

def referenceSquareMomentBase (B : ℝ) (grid : FiniteLineGrid) : ℝ :=
  16*((((grid.branching:ℝ)+2)*(2*LinePacketFamily.squareMeanConstant B+
    48*(4*Real.pi)^4))/Real.log (3/2)+LinePacketFamily.squareMeanConstant B+1)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedVariationTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked reference variation tail in original physical variables.
The interval may have any origin and any positive length containing the
retained packet lengths. Neither its scale nor its origin enters the
relative exceptional-measure constant. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

def physicalMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCoefficient t d v g j u k)*
      ((T j u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x))

def physicalMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => P.physicalMaskedBand c alt hAlt d v g T L A t y j x)) N

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredMaskedVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric frozen coefficients in the actual masked synthesis.
The exact three-cutoff identity gives a fixed three-event loss, with no
assumption about the measure of selector boundary sets. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

def physicalCenteredMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCenteredCoefficient t t d v g j u k)*
      ((T j u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x))

def physicalCenteredMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x)) N

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise norms of actual vector packets are controlled by the
same positive main and error envelopes used in the reference tails. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def rawPacketValue (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l)
    (c : EuclideanSpace ℂ κ) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c k*P.raw i j l u k y x)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledPositiveSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source coefficient supplies the positive per-length
main/error bound for every residual subset, with original synthesis waves. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalErrorScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ l : P.labels j, ∑ u : Item j l, ‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
    tileEnvelope (P.length j*(P.snappedSite j l u).1)
      (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalPositiveScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact positive envelopes of the original physical coefficients.
The symmetric cutoff is controlled by the three actual one-sided
reference families, with no exceptional boundary convention. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def positiveEnvelope (j : Fin N) (u : ι j) (y x : ℝ) : ℝ :=
  lineEnvelope (P.length j*(P.snappedSite j u).1) (P.length j) 3 x*
    lineEnvelope (P.width*(P.snappedSite j u).2) P.width 2 y

def physicalPositiveScale (s : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ u, ‖P.physicalCoefficient s d v g j u‖*P.positiveEnvelope j u y x

def physicalCenteredPositiveScale (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ u, ‖P.physicalCenteredCoefficient s t d v g j u‖*P.positiveEnvelope j u y x

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalReferenceSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical positive main square is exactly the normalized
reference square function times its coefficient normalization. This
connects the symmetric frozen main term to three proved line estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalReferenceLine (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ) : LinePacketFamily N κ ι :=
  P.referenceAnalyzedLine d (fun z => v (sourceReferenceToPhysical t z))
    (hv.comp (sourceReferenceToPhysical t).measurable)
    (fun z => g (sourceReferenceToPhysical t z))
    (hg.comp (sourceReferenceToPhysical t).measurable) (fun _ => hg1 _) y

def physicalReferenceSquare (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) : ℝ :=
  (P.physicalReferenceLine t d v hv g hg hg1 y).squareFunction (x/P.topLength)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredSquareBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical centered main square is controlled by three
reference squares. The resulting exceptional-set inclusion is exact. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalCenteredSquare (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) : ℝ :=
  Real.sqrt (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive frozen main sum in the original labeled collection
is exactly the sum of the centered positive scales in its fixed slots.
The physical packets, coefficients and snapped envelopes are unchanged. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

def frozenSlot (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1) (s : Fin B) :
    SourceLatticePacket N κ (P.SlotItem hcard s) :=
  (P.slotted hcard s).frozenProfile (fun j p k => b j p.1.1 k t)
    (fun j p k => hb j p.1.1 k)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMaskedSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Masked centered synthesis in the original labeled family is the
exact sum of its fixed-slot syntheses. In particular the cubic variation
is controlled by the actual centered masked variations already bounded
on physical intervals. No total-label factor occurs. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalCenteredMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

def physicalCenteredMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x)) N

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
  (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)

/-- The slot functions use the original alternate packet and original
mask at each retained item. -/
def slotCenteredMaskedBand (s : Fin B) (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  (P.slotted hcard s).physicalCenteredMaskedBand
    (fun j p k => b j p.1.1 k t)
    (P.slottedAlt hcard alt s) (P.slottedAlt_bound hcard alt hAlt s)
    (fun j => a*(2:ℝ)^j.val) v g
    (fun j p => T j p.1.1 p.1.2) L A t y j x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalErrorMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalAngularErrorCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LocalMinimaSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

def localMinimaOutcome (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i) (l : List ι) :
    IndependentSelection G := ⟨localMinima G l, localMinima_independent G hG l⟩

def localMinimaLaw (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    PhaseCombinatorics.FiniteSelectionLaw (IndependentSelection G) ι where
  weight := orderOutcomeWeight w Finset.univ (localMinimaOutcome G hG)
  nonnegative := orderOutcomeWeight_nonnegative w Finset.univ (fun i _ => hw i) _
  total := orderOutcomeWeight_total w Finset.univ (fun i _ => hw i) _
  retained := Subtype.val

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

def graphPredictionValue (frequency : ι → κ → ℝ) (l : ι → ℝ)
    (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ) (D p t : ℝ) : ℝ :=
  energyRatio p (1 + ∑ i, l i * ‖X i‖ ^ p)
    (diagonalFourierSum frequency (predictionCoefficients l X lambda D p) t)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCrossDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unconditional horizontal derivative estimate for actual cross-profile
top sums. The lower length cutoff gives the reciprocal scale factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def crossDerivativeConstant (P : SourceLatticePacket N κ ι) (D : ℕ) : ℝ :=
  (P.constant*Real.pi^2)*(4*((16^(8*D+1)*(16^(8*D+1)*P.constant))*(4*Real.pi)^2))


end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLengthRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting to an interval of original packet lengths preserves all
interval concentration bounds. The resulting coefficients are explicit
zero extensions of the original analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def restrictCoefficient (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  if lower ≤ j.val ∧ j.val < upper then coeff j l u else 0

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source node ratio and its snapshot graph predictor, with the original
child amplitudes and masses kept explicit. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The same snapshot, with only its prescribed diagonal carriers moving. -/
def sourceSnapshotPrediction (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) : ℝ :=
  energyRatio p (1+∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
    (∑ i, (((c i/n)^(1-μ):ℝ):ℂ) •
      (lam i • diagonalModulation (frequency i) ((c i)^(μ-1) • A i) b))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledStoppingVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def physicalMaskedValue (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    ((T q.1 q.2.1 q.2.2).mask L A z:ℂ)*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

def physicalStoppingPrefix (stop : Fin N → ℕ) (z : ℝ×ℝ) : ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLabeledPacketRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The restricted packet type is precisely the selected finite set. -/
def restrictedPacketEquiv (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).PacketIndex ≃ Q where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1,q.2.2.val⟩⟩,by
    obtain ⟨h,hm⟩ := q.2.2.property
    exact hm⟩
  invFun := fun q => ⟨q.val.1,⟨q.val.2.1,⟨q.val.2.2,⟨q.val.2.1.property,q.property⟩⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarKernelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product reproducing-kernel majorants are controlled by the actual
strong maximal construction on the plane. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
open DyadicLineGrid

def normalizedLineEnvelope (c r x : ℝ) : ℝ := r⁻¹*lineEnvelope c r 1 x

def verticalKernelAverage (U : ℝ×ℝ → ℝ) (c r x : ℝ) : ℝ :=
  ∫ y, normalizedLineEnvelope c r y*U (x,y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCellDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density factor for a long-tree cell. A literal admissible test
controls the measure of its angularly restricted cell, with polynomial
loss in the transverse cell index. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

namespace SourceWhitney
open DyadicLineGrid

/-- Horizontal Whitney strip crossed with one transverse cell in the
reference coordinates of a tree. -/
def treeCell (slope y W : ℝ) (k j n : ℤ) : Set (ℝ×ℝ) :=
  {z | z.1∈cell 0 k j ∧ |(z.2-slope*z.1)-y-(n:ℝ)*W|≤W/2}

end SourceWhitney
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
open DyadicLineGrid

def partitionCell (b W : ℝ) (p : (ℤ×ℤ)×ℤ) : Set (ℝ×ℝ) :=
  cell 0 p.1.1 p.1.2 ×ˢ transverseCell b W p.2

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

def planarVerticalSlice (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  planarSchwartzSlice (planarSwap f) x 0

@[simp] theorem planarVerticalSlice_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    planarVerticalSlice f x y=f (x,y) := by
  simp only [planarVerticalSlice,planarSchwartzSlice_apply,planarSwap_apply,zero_mul,add_zero,
    Prod.swap_prod_mk]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongPrefixes
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long packets form a literal prefix in scale. Every truncated
interval of that prefix has the proved coordinate cutoffs and is bounded
pointwise by the original tree maximum. -/
noncomputable section
open FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longPrefix (r : ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => 32*r<P.length j)).sup (fun j => j.val+1)

def physicalLongIntervalSchwartz (t r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (lo hi : ℕ) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  P.physicalTreePartialSchwartz t c (min hi (P.longPrefix r))-
    P.physicalTreePartialSchwartz t c (min lo (P.longPrefix r))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenLongInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hard angular cutoff in the frozen long-tree expression selects
one exact interval of the original scale indices. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def angularStart (w d : ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => w/P.length j<d)).sup (fun j => j.val+1)

def frozenLongValue (t r w s : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    EuclideanSpace ℂ κ :=
  ∑ j : Fin N, if 32*r<P.length j ∧ |s-t|≤w/P.length j then
    planarFixedSynthesis (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
      (fun a k => P.physicalPacket t j a.1 a.2 k) z else 0

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial localization preserves the actual coordinate frequency
cutoffs of Hilbert-valued Schwartz packets. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

def vectorPolynomialLocalization (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) : SchwartzMap ℝ (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => polynomialLocalization a r q (f.postcompCLM (vectorCoordinate k)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenCellIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen long sums are measurable, have finite cell suprema,
and integrate against the original common angular-support mask. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

namespace SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longCellSup (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (b : ℝ) (p : (ℤ×ℤ)×ℤ) : ℝ :=
  packetNormSup (fun a : ℕ×ℕ => P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2)
    (coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*P.width)
      (DyadicLineGrid.scale p.1.1/2) (P.width/2))

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMainRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def referenceCondition (oldSlope newSlope referenceLength cone w : ℝ)
    (j : Fin N) (l : P.labels j) : Prop :=
  P.length j ≤ referenceLength ∧
    |oldSlope+P.rowSlope j l-newSlope| ≤ cone*w/P.length j

def referenceLabelsEquiv (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    P.referenceLabels oldSlope newSlope referenceLength cone w j ≃
      {l : P.labels j // P.referenceCondition oldSlope newSlope referenceLength cone w j l} where
  toFun := fun l => ⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,by
    obtain ⟨h,hlen,hangle⟩ := (Finset.mem_filter.mp l.property).2
    exact ⟨hlen,hangle⟩⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr
    ⟨l.val.property,⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary density attached to literal source packets. A keeper in the
packet's original angular cell automatically meets the reference-cone
condition used by the phase-averaging argument. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def densityTile (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) : OrdinaryDensityTile where
  center := (P.actualX q.1 q.2.1 q.2.2,
    P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2)
  level := q.1.val
  cell := cell q.1 q.2.1

def ordinaryDensity (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (q : P.PacketIndex) : ℝ :=
  (P.densityTile oldSlope cell q).density P.topLength w P.width tau grid E u

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue stripwise estimates over the actual countable Whitney partition.
Finite-subfamily bounds imply integrability and the same global bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)

variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

include hne hpos in
theorem exists_cellIndex (z : ℝ) :
    ∃ i : CellIndex tiles x ell, z∈cell 0 i.val.1 i.val.2 := by
  obtain ⟨k,j,hj,hz⟩ := exists_whitney_cover tiles x ell hne hpos z
  exact ⟨⟨(k,j),hj⟩,hz⟩

/-- The unique maximal allowed dyadic cell containing a given point. -/
def indexAt (z : ℝ) : CellIndex tiles x ell :=
  Classical.choose (exists_cellIndex tiles x ell hne hpos z)

def strip (E : Set (ℝ×ℝ)) (i : CellIndex tiles x ell) : Set (ℝ×ℝ) :=
  E∩Prod.fst ⁻¹' cell 0 i.val.1 i.val.2

variable {V : Type*}

/-- Evaluate the local function belonging to the unique Whitney strip. -/
def paste (F : CellIndex tiles x ell → ℝ×ℝ → V) (z : ℝ×ℝ) : V :=
  F (indexAt tiles x ell hne hpos z.1) z

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongCellMask
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-witness density test supplies the common mask and
mass bounds on the disjoint cells used in long-tree integration. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def HasLongPacket (i : P.DensityWhitneyCell) : Prop :=
  ∃ q : P.PacketIndex, 32*DyadicLineGrid.scale i.val.1<P.length q.1

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMajorant
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual polynomially weighted tree maximum is a bounded
measurable majorant. Its L2 energy is inherited from the stronger product
weight, without adding a maximal-function premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def transverseTreeMajorant (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCellGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable gluing on the actual horizontal Whitney cells and
half-open transverse cells. A finite rectangle bound suffices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

abbrev ProductCellIndex := CellIndex tiles x ell × ℤ

def productCell (b W : ℝ) (i : ProductCellIndex tiles x ell) : Set (ℝ×ℝ) :=
  partitionCell b W (i.1.val,i.2)

end LipschitzHilbert.SourceWhitney

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
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

def verticalDemodulation (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => SchwartzMap.smulLeftCLM ℂ (verticalCarrier (-nu k))
    (f.postcompCLM (vectorCoordinate k)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularFrozenIntegration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frozen long-tree integration keeps angular and spatial widths
separate. Carrier removal supplies uniform reproduction on spatial cells. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable


def frozenWhitneyLocalAtWidth (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  (E∩u ⁻¹' Omega i).indicator
    (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w (u z) c z) z


def frozenTreeValueAtWidth (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) (P.frozenWhitneyLocalAtWidth w c E u Omega)


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketOwnDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Own-box density tests for the literal source packets, and the resulting
short-packet bound on every horizontal Whitney strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The actual spatial rectangle and direction of a source packet. -/
def ownBox (oldSlope : ℝ) (q : P.PacketIndex) : SlopeBox where
  x := P.actualX q.1 q.2.1 q.2.2
  y := P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2
  slope := oldSlope+P.rowSlope q.1 q.2.1
  length := P.length q.1
  width := P.width
  length_pos := P.length_pos q.1
  width_pos := P.width_pos

/-- The ordinary density includes each packet's own rectangle. -/
def ownDensityTest (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ)
    (grid : ℤ) (w tau : ℝ) (q : P.PacketIndex)
    (hlen : P.length q.1≤tau)
    (hslope : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    OrdinaryDensityTest P.topLength w P.width tau grid (P.densityTile oldSlope cell q) where
  top := P.ownBox oldSlope q
  level := q.1.val
  cell := cell q.1 q.2.1
  length_eq := by simp only [ownBox,length,DyadicLineGrid.scale,zpow_natCast]
  width_eq := rfl
  length_le := hlen
  tile_length_le := by
    simpa only [densityTile,ownBox,length,DyadicLineGrid.scale,zpow_natCast] using le_refl (P.length q.1)
  center_mem := by
    simp only [densitySpatialBox,densityTile,ownBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
    exact ⟨mul_nonneg (by norm_num) (P.length_pos q.1).le,
      mul_nonneg (by norm_num) P.width_pos.le⟩
  slope_mem_tile := hslope
  slope_mem_self := hslope

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketShortSum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-tree lattice sums for the literal labeled source family.
The Whitney separation is derived from the actual packet centers. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

abbrev whitneyAllowed (k m : ℤ) : Prop :=
  Allowed (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) k m

def shortKernel (k m : ℤ) (q : P.PacketIndex) : ℝ :=
  (1+(stripDistance (center k m) (DyadicLineGrid.scale k) (P.actualX q.1 q.2.1 q.2.2)/P.length q.1)^2)⁻¹^2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortTreeIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete finite-strip short-tree estimate for the original packet
integrals. All density tests, lattice sums and Whitney budgets are actual. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Original packet with its coefficient and original selector. -/
def ordinaryPacketValue (P : SourceLabeledLattice N κ Label Item) (oldSlope : ℝ)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (q : P.PacketIndex) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun a => coefficient q a*selector q.1 q.2.1 a (u z)*
    P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a z)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShortTreeGlobal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original short-tree sum on the full Whitney partition, with
integrability and a uniform size-density-area bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

abbrev WhitneyCell (P : SourceLabeledLattice N κ Label Item) :=
  CellIndex (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)

def shortLocalValue (P : SourceLabeledLattice N κ Label Item) (oldSlope CW : ℝ)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.WhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale i.val.1 then
    P.ordinaryPacketValue oldSlope coefficient selector u q z else 0

theorem packet_univ_nonempty (P : SourceLabeledLattice N κ Label Item)
    (hne : Nonempty P.PacketIndex) : (Finset.univ : Finset P.PacketIndex).Nonempty := by
  obtain ⟨q⟩ := hne
  exact ⟨q,Finset.mem_univ q⟩

def shortTreeValue (P : SourceLabeledLattice N κ Label Item) (hne : Nonempty P.PacketIndex)
    (oldSlope CW : ℝ) (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) : ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1)
    (P.shortLocalValue oldSlope CW coefficient selector u)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeSelectorError
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-tree freezing error is a summable dyadic error, with
its original angular indicator retained on both terms. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Arbitrary coordinate multipliers on the actual raw packets. -/
def rawSelectorTreeValue (i : Fin 3)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (y x : ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    WithLp.toLp 2 (fun k => c j l u k * beta j l k * P.raw i j l u k y x)

/-- The original physical packet sum, before restriction to its common
angular-support set. -/
def physicalTreeSelectorValue (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    WithLp.toLp 2 (fun k => c j l u k * beta j l k * P.physicalPacket t j l u k z)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongTreeSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original long sum, its frozen coefficients, and the literal
selector error. No support property is imposed on the frozen sum. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longCoefficient (r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (v : Item j l) : EuclideanSpace ℂ κ :=
  if 32*r<P.length j then c j l v else 0

def frozenSelectorCoefficient
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (j : Fin N) (l : P.labels j) (v : Item j l) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c j l v k*selector j l k 0)

def longOriginalLocal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  P.physicalTreeSelectorValue 0 (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (fun j l k => selector j l k (u z)) z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularTreeSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact short/frozen/error identity with an independent angular
cutoff, and the corresponding integrated selector error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longErrorLocalAtWidth (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  P.longOriginalLocal c selector u i z-
    P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w (u z)
      (P.frozenSelectorCoefficient c selector) z


def longErrorTreeValueAtWidth (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1)
    (fun i => (E∩u ⁻¹' Omega i).indicator (P.longErrorLocalAtWidth w c selector u i))


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceOrdinaryTreeEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary size-density tree estimate for the actual selected
packet sum. Scalar Lépingle is the sole published analytic premise here. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def ordinaryTreeConstant (P : SourceLabeledLattice N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip : ℝ) : ℝ :=
  27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound+
  Real.sqrt (C*(B:ℝ))*P.absoluteConstant+
  32^106*(B:ℝ)*P.absoluteConstant*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
    (32*2^203)*9*transverseTailConstant

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularOrdinaryTree
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary size-density tree bound with separate angular width
and spatial width. Constants are uniform in their ratio and in the
number of vertical frequency bins. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The separated portion of the original coefficient family, as in
Eq. (size) of the manuscript. -/
def angularSeparatedTreeEnergy (P : SourceLabeledLattice N κ Label Item) (cb w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) : ℝ :=
  ∑ j, ∑ l : P.labels j, ∑ v : Item j l,
    if cb*w/P.length j≤|P.rowSlope j l| then
      ‖c j l v‖^2*P.length j*P.width else 0


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected reference family retains the original density tests
and spectra. No bound on the unselected slopes is involved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)
  (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedCells (cell : ∀ j, P.labels j → ℤ) : ∀ j, (Q).labels j → ℤ :=
  fun j l => cell j (P.selectedOriginalLabel S j l)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (S : Finset P.PacketIndex) (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedCoefficients (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∀ j (l : (Q).labels j), P.SelectedItem S j l → EuclideanSpace ℂ κ :=
  fun j l u => c j (P.selectedOriginalLabel S j l) u.val

def selectedMultipliers (beta : ∀ j, P.labels j → κ → ℂ) :
    ∀ j, (Q).labels j → κ → ℂ := fun j l => beta j (P.selectedOriginalLabel S j l)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTreeSize
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unsigned size test supplies the separated energy of
a spatial piece in arbitrary reference coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceTreeTop (t a b : ℝ) : SlopeBox where
  x := a
  y := b+t*a
  slope := t
  length := P.topLength
  width := P.width
  length_pos := P.topLength_pos
  width_pos := P.width_pos

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSelectionRecords
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paired tops and their actual recorded test packets. Chronological
nondeletion is a conclusion of the finite stopping run. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeSelectionRecords (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (SlopeBox × Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => (T,P.sizeTestPackets negative w cb cell grid R T) ::
      sizeSelectionRecords negative w cb A cell grid
        (R\P.sizeDeletePackets w A cell grid R T) tops

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedPackets
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The union of the actual recorded separated tests. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def selectedPackets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (initial : Finset P.PacketIndex) (tops : List SlopeBox) : Finset P.PacketIndex :=
  (P.sizeSelectionRecords negative w cb A cell grid initial tops).toFinset.biUnion Prod.snd

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDeletionForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full trees removed by the size-selection loop, including the
nonseparated packets deleted with each recorded top. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def sizeDeletionRecords (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (SlopeBox × Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => (T,P.sizeDeletePackets w A cell grid R T) ::
      sizeDeletionRecords w A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tile envelopes are controlled by the actual strong maximal
function. Only one quadratic top weight in each coordinate is needed. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def topReciprocalWeight (a b L W : ℝ) (z : ℝ×ℝ) : ℝ :=
  lineEnvelope a L 1 z.1*lineEnvelope b W 1 z.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShearedEnvelopeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted envelope estimate in the physical coordinates of an
arbitrary reference slope. The shear preserves product Lebesgue measure. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def shearedTileEnvelope (cx cy ell W t : ℝ) (n : ℕ) (z : ℝ×ℝ) : ℝ :=
  tileEnvelope cx (cy-t*cx) ell W n (z.1,z.2-t*z.1)

def shearedTopReciprocal (a b L W t : ℝ) (z : ℝ×ℝ) : ℝ :=
  topReciprocalWeight a (b-t*a) L W (z.1,z.2-t*z.1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataFarGram
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distant-scale Gram contribution of an actual selected tree is
bounded by the short-packet envelope paired with its interval maximum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem packetVector_memLp
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (q : P.PacketIndex) :
    MemLp (P.packetVector c q) 2 (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).const_mul _

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedScale
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparable-scale Gram control for an arbitrary selected packet
set, using its actual masked coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- The L2 packet vector, with its coefficient already included. -/
def packetL2 (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) : Lp (EuclideanSpace ℂ κ) 2 ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
  (P.packetVector_memLp c q).toLp (P.packetVector c q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ConvolutionPacketProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Schwartz profiles for the actual convolution packets,
with arbitrary prescribed vertical carrier. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def convolutionProfile (K : SchwartzMap (ℝ×ℝ) ℂ) (l W theta nu : ℝ)
    (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  (l*W:ℂ) • scalarVerticalDemodulation (nu*W)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W theta hl hW).symm K)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledFrequencyWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency windows obtained from a fixed normalized packet profile.
The normalization is exact and removes all spatial scale parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def normalizedSpatialKernel (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  ((l*W:ℂ)⁻¹) • physicalPlanarPacket F 0 0 l W theta carrier hl hW

def scaledFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarFourierSchwartz (normalizedSpatialKernel F l W theta carrier hl hW)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_NormalizedPacketLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Fourier-separated synthesis profiles on arbitrary finite
translated lattices. The slopes have no global shear restriction. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order) ≤ C)

/-- All carrier components share each actual site. The profile bound
comes from the single normalized profile, independently of these data. -/
def normalizedPacketLattice : PacketLatticeData N κ Label Item where
  topLength := topLength
  width := width
  scale := scale
  ratioBound := ratioBound
  profileBound := C
  order := order
  topLength_pos := htop
  width_pos := hwidth
  profileBound_pos := hC
  order_ge_three := horder
  ratioBound_ge_one := hratio
  scale_bound := hscale
  labels := labels
  originX := originX
  originZ := originZ
  rowSlope := theta
  frequency := fun k => 2*Real.pi*center k
  site := site
  site_injective := hinj
  profile := fun _ _ _ _ => synthesisProfile F q nu
  profile_bound := fun _ _ _ _ => hprofile

local notation "P" => normalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile

def normalizedAnalysisFamily (G : SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ j (l : (P).labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ :=
  fun _ _ _ _ => analysisProfile G q nu

theorem normalizedAnalysisFamily_bound (G : SchwartzMap (ℝ×ℝ) ℂ)
    (hG : planarProfileConstant (analysisProfile G q nu) (2*order) ≤ C) :
    ∀ j (l : (P).labels j) (u : Item j l) k,
      planarProfileConstant (normalizedAnalysisFamily F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G
          j l u k) (2*(P).order) ≤ (P).profileBound := by
  intro j l u k
  exact hG

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_FiniteNormalizedPacketLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
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
variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1 ≤ ratioBound) (hscale : |scale/width| ≤ ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)

attribute [local instance] Classical.propDecidable

def finiteNormalizedPacketLattice : PacketLatticeData N κ Label
    (fun j l => finiteSiteFiber labels S j l) :=
  normalizedPacketLattice F q nu topLength width scale ratioBound C order
    htop hwidth hC horder hratio hscale labels (fun j l => (origin j l).1)
    (fun j l => (origin j l).2) theta center (fun _ _ n => n.val)
    (fun _ _ => Subtype.val_injective) hprofile

local notation "P" => finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels origin theta center S hprofile

def finiteNormalizedPacketEquiv : (P).PacketIndex ≃ S :=
  (Equiv.sigmaCongrRight (fun j => Equiv.sigmaCongrRight
    (fun l : labels j => finiteSiteFiberEquiv labels S j l))).trans
      (retainedSiteEquiv labels S)

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

def latticeFrequencyWindow (chi : SchwartzMap (ℝ×ℝ) ℂ) (topLength width : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (i : LatticeRow labels) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  scaledFrequencyWindow (planarInverseSchwartz chi) (latticeLength topLength labels i)
    width (theta i.1 i.2) (2*Real.pi*center k)
    (latticeLength_pos topLength htop labels i).ne' hwidth.ne'

def normalizedConvolutionSum (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (topLength width : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (b : ∀ j, labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z, b i.1 i.2 k (u z)*
    kernelConvolution
      (horizontalFrequencyKernel (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k)
        nu q (latticeLength topLength labels i) (theta i.1 i.2))
      (kernelConvolution
        (verticalFrequencyKernel (latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k)
          nu q width (center k)) (fun x => f x k)) z*star (g z k) ∂volume.prod volume

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

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ} (p : AnnularPacketGeometry A B c C a M)

def numerics : PacketLatticeData.OrdinaryModelNumerics
    (2*Real.pi*A) (2*Real.pi*(p.H*c)) (p.inner/2) (2*p.outer) :=
  Classical.choice (PacketLatticeData.exists_ordinary_model_numerics _ _ _ _
    (by positivity [p.hA]) (by positivity [p.H_pos,p.hc])
    (by positivity [p.inner_pos]) p.separation)

end AnnularPacketGeometry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenCoefficientEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bessel duality for the original physical packets with fixed selector
values. Both the synthesis and analyzing energies use the actual packet
area. The constant is independent of vector dimension and scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

def physicalFrozenCoefficient (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (beta : P.PacketIndex → κ → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun p : P.PacketIndex => P.length p.1*P.width)
    (fun p k z => beta p k * P.physicalPacket t p.1 p.2.1 p.2.2 k z) g q

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCrossResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross-profile residual squares: analyze against the original packets,
synthesize the alternate packets, and keep the same original main/error
reference quantities. No alternate analyzing coefficient is substituted. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

def physicalCrossPacketValue (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (i : Fin 3) (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  (P.withProfile alt hAlt).rawPacketValue i q.1 q.2.1 q.2.2
    (P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2) (z.2-t*z.1) z.1


end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal derivative estimate uses the coefficient norm bound
for the original smooth selector. It supplies the horizontal term in the
motion and prediction estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def boundedSelectedTopSum (P : SourceLatticePacket N κ ι)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound) (s : Finset (Fin N))
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (x y : ℝ) : EuclideanSpace ℂ κ :=
  ∑ j ∈ s, vectorPacketSynthesis (coeff j)
    (fun u k => (P.withProfile alt hAlt).raw 0 j u k y) x


end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked predictors are patched cellwise, then integrated in reverse
geometric order. Their logarithmic errors are summed in the original
forward angular order and paid by the actual first mass crossing. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def reverseMarkedError (g : FiniteLineGrid) (level : ℕ → ℕ) (count : ℕ)
    (marked : ℕ → ℕ → Prop) (error : ℕ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  g.markedError (level (ShiftedBlocks.reverseIndex count j)) (marked j) (error j)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveReference
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow main reference family retains only labels active at the
frozen direction. Inactive labels contribute exactly zero, so neither
the square nor the masked variation needs spectral assumptions there. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

theorem frozenActiveLabel_nonzero (j : Fin N) (l : P.frozenActiveLabels t b j) :
    ∃ k, b j (P.frozenActiveOriginalLabel t b j l) k t ≠ 0 := by
  obtain ⟨h,k,hk⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) = P.frozenActiveOriginalLabel t b j l := Subtype.ext rfl
  exact ⟨k,by simpa only [heq] using hk⟩

def frozenActiveSelector : ∀ j, (P.frozenActiveFamily t b).labels j → κ → ℝ → ℂ :=
  fun j l => b j (P.frozenActiveOriginalLabel t b j l)

def frozenActiveLabelsEquiv (j : Fin N) : P.frozenActiveLabels t b j ≃
    {l : P.labels j // ∃ k, b j l k t ≠ 0} where
  toFun := fun l => ⟨P.frozenActiveOriginalLabel t b j l,P.frozenActiveLabel_nonzero t b j l⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr ⟨l.val.property,
    ⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationActive
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only frozen-active labels enter the centered main term. Their actual
angular separation bounds the modulation parameter, independently of
the wide cone used for the positive angular error. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

theorem frozenActive_carrier_bound (w F Cb : ℝ) (hw : 0 < w)
    (hF : 0 ≤ F) (_hCb : 0 ≤ Cb) (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : P.frozenActiveLabels t b j) (k : κ) :
    |P.frequency k*P.rowSlope j (P.frozenActiveOriginalLabel t b j l)*P.length j| ≤ F*Cb := by
  have hs := hangle j _ (P.frozenActiveLabel_nonzero t b j l)
  rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j)]
  calc
    _ ≤ (F/w)*(Cb*w/P.length j)*P.length j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hfreq k) hs (abs_nonneg _) (div_nonneg hF hw.le)) (P.length_pos j).le
    _ = F*Cb := by field_simp [hw.ne',(P.length_pos j).ne']

/-- Changing a bound field changes no packet; the centered family uses
the narrow modulation bound supplied by active labels. -/
def activeMainFamily (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
    (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j) :
    SourceLabeledLattice N κ Label Item :=
  { P.frozenActiveFamily t b with
    carrierBound := F*Cb
    carrierBound_nonneg := mul_nonneg hF hCb
    carrier_bound := P.frozenActive_carrier_bound t b w F Cb hw hF hCb hfreq hangle }

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedPacketData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw packet data with length control only on actual retained items. No
concentration conclusion is included in these structures. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
structure SupportedTopRawPacketData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (P : PlanarPacketFamily N κ ι) (lo hi : ℝ) (T : SlopeBox) (K : ℝ) (D : ℕ) where
  raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  frequency : κ → ℝ
  length_le : ∀ j (_u : ι j), P.length j ≤ K*T.length
  width_le : P.width ≤ K*T.width
  centerX_le : ∀ j u, |P.centerX j u-T.x| ≤ K*T.length
  centerZ_le : ∀ j u, |P.centerZ j u-(T.y-T.slope*T.x)| ≤ K*T.width
  wave_eq : ∀ j u k y, raw 0 j u k y = P.wave j u k y
  bound : ∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  derivative_bound : ∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  low : ∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) ξ = 0
  high : ∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (raw i j u k y) ξ = 0
  covariant : ∀ y j u k x, (4*(K*T.width):ℂ)*
    (deriv (fun t => raw 0 j u k t x) y -
      (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x
  continuous : ∀ i j u k, Continuous (fun z : ℝ × ℝ => raw i j u k z.1 z.2)
  differentiable : ∀ j u k x y, DifferentiableAt ℝ (fun t => raw 0 j u k t x) y

structure SupportedTopCovariantData {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] {P : PlanarPacketFamily N κ ι}
    {lo hi : ℝ} {T : SlopeBox} {K : ℝ} {D : ℕ}
    (data : SupportedTopRawPacketData P lo hi T K D) where
  second : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  bound : ∀ y j u k x, ‖second j u k y x‖ ≤ P.constant*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  derivative_bound : ∀ y j u k x, ‖deriv (second j u k y) x‖ ≤ (P.constant/P.length j)*
    (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x *
      lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)
  low : ∀ y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (second j u k y) ξ = 0
  high : ∀ y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (second j u k y) ξ = 0
  covariant : ∀ y j u k x, (4*(K*T.width):ℂ)*
    (deriv (fun t => data.raw 1 j u k t x) y -
      (data.frequency k:ℂ)*Complex.I*data.raw 1 j u k y x) = second j u k y x
  continuous : ∀ j u k, Continuous (fun z : ℝ × ℝ => second j u k z.1 z.2)
  differentiable : ∀ j u k x y, DifferentiableAt ℝ (fun t => data.raw 1 j u k t x) y
structure SourceSupportedLatticeTopGeometry {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
    (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : ∀ j (_u : ι j), P.length j ≤ K*T.length
  width_le : P.width ≤ K*T.width
  centerX_le : ∀ j u, |P.actualX j u-T.x|+P.length j ≤ K*T.length
  centerZ_le : ∀ j u, |P.actualZ j u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width
  order_le : 3+2*(8*D+1) ≤ P.order
  scale_eq : P.scale = 4*(K*T.width)

structure SourceSupportedLabeledTopGeometry {N : ℕ} {κ : Type} {Label : Fin N → Type}
    {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item) (T : SlopeBox) (K : ℝ) (D : ℕ) : Prop where
  length_le : ∀ j (l : P.labels j) (_u : Item j l), P.length j ≤ K * T.length
  width_le : P.width ≤ K * T.width
  centerX_le : ∀ j l u, |P.actualX j l u - T.x| + P.length j ≤ K * T.length
  centerZ_le : ∀ j l u,
    |P.actualZ j l u - (T.y - T.slope * T.x)| + P.width ≤ K * T.width
  order_le : 3 + 2 * (8 * D + 1) ≤ P.order
  scale_eq : P.scale = 4 * (K * T.width)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLatticeData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct supported raw data from the original physical packet spectrum
and center bounds; empty scales impose no top-length condition. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
def supportedTopRawData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceSupportedLatticeTopGeometry P T K D) :
    SupportedTopRawPacketData P.family (S.lo/P.topLength) (S.hi/P.topLength) T K D where
  raw := fun i => P.raw (i.castLE (by decide))
  frequency := P.frequency
  length_le := G.length_le
  width_le := G.width_le
  centerX_le := fun j u => P.family_centerX_local j u T.x (K*T.length) (G.centerX_le j u)
  centerZ_le := fun j u => P.family_centerZ_local j u (T.y-T.slope*T.x)
    (K*T.width) (G.centerZ_le j u)
  wave_eq := fun _ _ _ _ => rfl
  bound := fun i y j u k x => P.raw_top_bound D G.order_le _ j u k y x
  derivative_bound := fun i y j u k x => P.raw_top_derivative_bound D G.order_le _ j u k y x
  low := fun i y j u k => (S.raw_cutoffs _ j u k y).1
  high := fun i y j u k => (S.raw_cutoffs _ j u k y).2
  covariant := by
    intro y j u k x
    have hs := congrArg Complex.ofReal G.scale_eq
    push_cast at hs
    rw [← hs]
    exact modulatedPlanarJet_covariant_zero (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x
  continuous := by
    intro i j u k
    exact modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale (P.length_pos j).ne' _
  differentiable := by
    intro j u k x y
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' 0 x

def supportedTopCovariantData (S : SourceLatticeSpectralData P) (T : SlopeBox) (K : ℝ) (D : ℕ)
    (G : SourceSupportedLatticeTopGeometry P T K D) : SupportedTopCovariantData (P.supportedTopRawData S T K D G) where
  second := P.raw 2
  bound := fun y j u k x => P.raw_top_bound D G.order_le 2 j u k y x
  derivative_bound := fun y j u k x => P.raw_top_derivative_bound D G.order_le 2 j u k y x
  low := fun y j u k => (S.raw_cutoffs 2 j u k y).1
  high := fun y j u k => (S.raw_cutoffs 2 j u k y).2
  covariant := by
    intro y j u k x
    have hs := congrArg Complex.ofReal G.scale_eq
    push_cast at hs
    rw [← hs]
    exact modulatedPlanarJet_covariant_one (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x
  continuous := by
    intro j u k
    exact modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale (P.length_pos j).ne' 2
  differentiable := by
    intro j u k x y
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' 1 x

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceInhabitedLabels
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing labels with no items preserves every packet and every
source band. Only genuinely populated assigned fibers enter label counts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def inhabitedItemsEquiv (j : Fin N) :
    (Σ l : P.inhabitedLabels j, Item j l) ≃ Σ l : P.labels j, Item j l where
  toFun := fun p => ⟨P.inhabitedOriginalLabel j p.1,p.2⟩
  invFun := fun p => ⟨⟨p.1.val,Finset.mem_filter.mpr ⟨p.1.property,⟨p.2⟩⟩⟩,p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported assigned-top estimates apply to the original individual
physical packets. These identities retain their analyzing coefficients,
alternate profiles, stopping levels, masks and source transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The common-type recentered family used in the actual top envelopes. -/
def assignedReferenceFamily (top : τ) :
    SourceLabeledLattice N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) :=
  (P.assignedTopFamily packets assigned top).referenceFamily oldSlope (T top).slope
    (R top) cone w F hw hcone hF hwide hfrequency

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

def assignedReferenceOriginalLabel (top : τ) (j : Fin N) (l : (Q top).labels j) : P.labels j :=
  ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
    oldSlope (T top).slope (R top) cone w j l).val.2

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

def assignedReferenceAlternate (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j (orig top j l) u.val k

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

def assignedReferenceSelector (top : τ) (j : Fin N) (l : (Q top).labels j) : κ → ℝ → ℂ :=
  b j (orig top j l)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketFrequencyInputL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency input and exact separated convolution identities for L1
data, including the amplitude slices of the bin decomposition. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def packetFrequencyInputL1 (A B : SchwartzMap (ℝ×ℝ) ℂ) (f : ℝ×ℝ → ℂ) : ℝ×ℝ → ℂ :=
  fun omega => A omega*B omega*planarFourier f omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedSymbolFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite normalized symbol form equals the common
weighted average of the actual normalized convolution forms. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def normalizedSymbolSumL1 (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (chi : SchwartzMap ℝ ℝ) (topLength width w : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ)
    (u : ℝ×ℝ → ℝ) (f : κ → ℝ×ℝ → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (chi (symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)):ℂ)*
      (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
        (S i k (symbolPoint (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2))
          (symbolY width omega.2 (center k))
          (symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)))*
        (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
          latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
          planarFourier (f k) omega)) ∂planeMeasure)*star (g z k) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedAnnularFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite representation including the manuscript slope partition
and the vertical bin window. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def partitionedAnnularSumL1 (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (psi (latticeLength topLength labels i*(omega.1+u z*omega.2))*
        rho (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))*
        beta (symbolY width omega.2 (center k))*
        (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
          latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
          planarFourier (f k) omega)) ∂planeMeasure)*star (g z k) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

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

def rectangularFrequencyCutoff (A B : ℝ) (hA : 0<A) (hB : 0<B) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (packetCoordinates (A/2) (B/2) 0 (by positivity) (by positivity)) unitPlaneCutoff

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PartitionedBandFormL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the two auxiliary frequency plateaus from the actual
partitioned multiplier. They equal one on its contributing frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def finitePartitionedBandL1 (psi rho beta : SchwartzMap ℝ ℂ)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (psi (latticeLength topLength labels i*(omega.1+u z*omega.2))*
        rho (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))*
        beta (symbolY width omega.2 (center k))*planarFourier (f k) omega) ∂planeMeasure)*
      star (g z k) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteDiagonalBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic slope partition recombines exactly into the finite
vector-valued diagonal band operator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def finiteDiagonalBandL1 {N : ℕ} {κ : Type} [Fintype κ]
    (psi beta : SchwartzMap ℝ ℂ) (topLength width : ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ j : Fin N, ∑ k, ∫ z, variableFrequencyMultiplierL1
    (annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) width (center k) u) (f k) z*
    star (g z k) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceLabelsEquiv (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    P.referenceLabels oldSlope newSlope referenceLength cone w j ≃
      {l : P.labels j // P.referenceCondition oldSlope newSlope referenceLength cone w j l} where
  toFun := fun l => ⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,by
    obtain ⟨h,hlen,hangle⟩ := (Finset.mem_filter.mp l.property).2
    exact ⟨hlen,hangle⟩⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr
    ⟨l.val.property,⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSelectedVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def selectedPhysicalPrefix (Q : Finset P.PacketIndex) (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical length bands of unrestricted masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalMultiplierCoefficient t b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceCross
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local reference restriction preserves the actual two-profile packet
operator, including its masked analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

abbrev referenceAlt
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ j (l : (Q).labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ :=
  fun j l => alt j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)

theorem referenceAlt_bound
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (j : Fin N) (l : (Q).labels j) (a : Item j l) (k : κ) :
    planarProfileConstant
      (P.referenceAlt oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency alt j l a k)
        (2*(Q).order)≤(Q).profileBound :=
  hAlt j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) a k

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataStoppingPrefix
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def selectedPhysicalPrefix (Q : Finset P.PacketIndex) (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentStoppedBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parent-cone version of the stopped physical path estimate.
 The two literal physical reference events discharge the square and
variation inputs of the stopped path estimate. The propagated unary
residual and mass power estimates follow from the active mass path itself.
The remaining local hypotheses concern marking and off-child amplitudes. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

/-- The exact physical stopped-path statement at one manuscript scale.
-/
def physicalParentStoppedBoundAt (q D Cmass qoff A_M L : ℝ) (Klocal Hlocal : ℕ) : Prop :=
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ Klocal) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) Hlocal) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s w R C F : ℝ) (hw : 0 < w) (hR : 0 < R),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    ∀ (top : τ), top ∈ tops → precision top = w/R →
    ∀ (hcone : 0 ≤ C+(SourceParameters.branching L)^2) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (hparentCone : 0 ≤ C+(SourceParameters.branching L)^3)
      (hparentWide : (C+(SourceParameters.branching L)^3)*w ≤ P.width),
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (Z Nmass α μ : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (∀ k, ‖phase k‖ ≤ Z) → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 → Real.sqrt L*μ = α-1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R (slope top) (C+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^3) w F
      hw hparentCone hF hparentWide hfrequency
    let origSquare := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) (2*q+11) →
    let n := grid.shiftedPathMass tops slope precision cut weight shift top z
    let finish := firstMassStop n count (L^A_M)
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let level := ShiftedBlocks.endpoint shift
    let transition := grid.sourceTransition tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) phase z
    let base := grid.sourcePacketBase tops slope precision cut weight assigned
      (fun u => stop u.1) (value z) a z
    let W := fun j => grid.packetAmplitude
      (packets.filter fun u => assigned u ∉ grid.cellTops tops slope precision cut
        (level (j+1)) (grid.index (level (j+1)) (slope top)))
      (fun u => slope (assigned u)) (fun u => stop u.1) base transition
      (level j) (grid.index (level j) (slope top))
    let amp := grid.sourceShiftedPathAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) value phase a shift top z
    ∀ (H : ℕ) (marked : ℕ → Prop) (Cex : ℝ), level count ≤ H → 0 ≤ Cex →
      Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
      (∀ j < count, marked j → L^A_M < n j) →
      (∀ j < finish, marked j → (1/4:ℝ) ≤ n j-n (j+1)) →
      (∀ j < finish, ¬marked j → n j-n (j+1) < 1 →
        ‖W j‖ ≤ (L^qoff*Real.exp (-L*Real.log L))*(n j-n (j+1))) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ L^A_M) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ L^A_M+1) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, if marked j then
          grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top z j else 1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataJetBudget
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
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

@[simp] theorem withJetControl_referenceEnvelopeConstant
    (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio) :
    (P.withJetControl scale ratio hratio hscale).referenceEnvelopeConstant =
      ((2^P.order*P.profileBound)*ratio^2)*3^(2*P.order) := rfl

theorem smallJetScale_control (P : PacketLatticeData N κ Label Item)
    {L a width : ℝ} (hL : 0 < L) (hw : 0 ≤ width) (hwidth : width ≤ P.width) :
    |(4*(L^a*width))/P.width| ≤ 4*L^a := by
  have hr : 0 ≤ L^a := Real.rpow_nonneg hL.le _
  rw [abs_of_nonneg (div_nonneg (by positivity) P.width_pos.le)]
  apply (div_le_iff₀ P.width_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hwidth (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hr)]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityJetNormalization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The late mask normalization preserves the actual density forest,
physical packet sums and masks. Its analytic constant has an explicit
polynomial bound after the mask exponent has been chosen. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

@[simp] theorem withJetControl_physicalMaskedValue
    (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (q : P.PacketIndex) :
    (P.withJetControl scale ratio hratio hscale).physicalMaskedValue alt hAlt t b v f T L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

end LipschitzHilbert.PacketLatticeData

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

def verticalRectangle (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) : Rectangle where
  center := planeCoordinates c
  axes := verticalAxes
  long := b+|s| * a
  short := a
  short_pos := ha
  short_le_long := hab.trans (le_add_of_nonneg_right (by positivity))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FatEnclosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fat clipped tops have vertical enclosing rectangles. Lacey--Li for
the constant vertical field handles them without a length restriction. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

def fatEnclosure (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width) : Rectangle :=
  verticalRectangle (T.clipCenter D l r) T.slope (T.clipLength D l r) (2*D*T.width) ha hfat

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ClippedEnclosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The thin enclosing rectangle for an actual horizontally clipped top
box. The long side is controlled by the testing strip before the published
length restriction is invoked. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

def thinEnclosure (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r) : Rectangle :=
  slopeRectangle (T.clipCenter D l r) T.slope (T.clipLength D l r) (2*D*T.width)
    ha (by have := T.width_pos; positivity) hthin

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedRawRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the physical horizontal scale of raw packet data. All
kernel, derivative and spectral conditions are transported explicitly. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SupportedTopRawPacketData
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
  {P : PlanarPacketFamily N κ ι} {lo hi K : ℝ} {T : SlopeBox} {D : ℕ}

def horizontalRescale (r : ℝ) (hr : 0 < r)
    (data : SupportedTopRawPacketData P (lo/r) (hi/r) T K D) :
    SupportedTopRawPacketData (P.horizontalRescale r hr) lo hi (T.horizontalRescale r hr) K D where
  raw := fun i j u k y => schwartzDilation (data.raw i j u k y) r hr.ne'
  frequency := data.frequency
  length_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_length]
    change P.length j/r ≤ K*(T.length/r)
    simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hr).mpr (data.length_le j u)
  width_le := data.width_le
  centerX_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_centerX]
    change |P.centerX j u/r-T.x/r| ≤ K*(T.length/r)
    rw [← sub_div,abs_div,abs_of_pos hr]
    simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hr).mpr (data.centerX_le j u)
  centerZ_le := by
    intro j u
    rw [PlanarPacketFamily.horizontalRescale_centerZ,SlopeBox.horizontalRescale_intercept]
    exact data.centerZ_le j u
  wave_eq := by
    intro j u k y
    apply congrArg (fun f : SchwartzMap ℝ ℂ => schwartzDilation f r hr.ne')
    exact data.wave_eq j u k y
  bound := by
    intro i y j u k x
    rw [schwartzDilation_apply,PlanarPacketFamily.horizontalRescale_centerX,
      PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
      lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact data.bound i y j u k (r*x)
  derivative_bound := by
    intro i y j u k x
    rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
      PlanarPacketFamily.horizontalRescale_centerZ,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    have h := mul_le_mul_of_nonneg_left (data.derivative_bound i y j u k (r*x)) hr.le
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [(P.length_pos j).ne',hr.ne']
    dsimp only [PlanarPacketFamily.horizontalRescale]
    ring
  low := by
    intro i y j u k ξ hξ
    apply schwartzDilation_low (data.raw i j u k y) r (lo*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply data.low i y j u k η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  high := by
    intro i y j u k ξ hξ
    apply schwartzDilation_high (data.raw i j u k y) r (hi*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply data.high i y j u k η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  covariant := by
    intro y j u k x
    exact data.covariant y j u k (r*x)
  continuous := by
    intro i j u k
    change Continuous (fun z : ℝ × ℝ => data.raw i j u k z.1 (r*z.2))
    exact (data.continuous i j u k).comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  differentiable := by
    intro j u k x y
    exact data.differentiable j u k (r*x) y

end SupportedTopRawPacketData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedCovariantRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second covariant kernel obeys the same horizontal transport. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert
namespace SupportedTopCovariantData
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
  {P : PlanarPacketFamily N κ ι} {lo hi K : ℝ} {T : SlopeBox} {D : ℕ}

def horizontalRescale (r : ℝ) (hr : 0 < r)
    {data : SupportedTopRawPacketData P (lo/r) (hi/r) T K D} (second : SupportedTopCovariantData data) :
    SupportedTopCovariantData (data.horizontalRescale r hr) where
  second := fun j u k y => schwartzDilation (second.second j u k y) r hr.ne'
  bound := by
    intro y j u k x
    rw [schwartzDilation_apply,PlanarPacketFamily.horizontalRescale_centerX,
      PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
      lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact second.bound y j u k (r*x)
  derivative_bound := by
    intro y j u k x
    rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
      PlanarPacketFamily.horizontalRescale_centerZ,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    have h := mul_le_mul_of_nonneg_left (second.derivative_bound y j u k (r*x)) hr.le
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [(P.length_pos j).ne',hr.ne']
    dsimp only [PlanarPacketFamily.horizontalRescale]
    ring
  low := by
    intro y j u k ξ hξ
    apply schwartzDilation_low (second.second j u k y) r (lo*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply second.low y j u k η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  high := by
    intro y j u k ξ hξ
    apply schwartzDilation_high (second.second j u k y) r (hi*(2:ℝ)^j.val) hr _ ξ hξ
    intro η hη
    apply second.high y j u k η
    convert hη using 1
    all_goals try with_reducible_and_instances rfl
    ring
  covariant := by
    intro y j u k x
    exact second.covariant y j u k (r*x)
  continuous := by
    intro j u k
    change Continuous (fun z : ℝ × ℝ => second.second j u k z.1 (r*z.2))
    exact (second.continuous j u k).comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  differentiable := by
    intro j u k x y
    exact second.differentiable j u k (r*x) y

end SupportedTopCovariantData
end LipschitzHilbert

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

def scalarBandForm (psi beta : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f g : (ℝ×ℝ) → ℂ) : ℂ :=
  ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
    (annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) W center u) f z*star (g z) ∂planeMeasure

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandMeasurableRestricted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sharp band logarithmic estimate for bounded measurable
L2 tests. The slight strip margin is used only for smooth approximation. -/
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpBandL2Pairing (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  bandL2Pairing (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w

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

def stripL2Cutoff (l r : ℝ) : Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  l2Indicator planeMeasure (horizontalStrip l r) (horizontalStrip_measurable l r)

def localizedSharpBandPairing (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  (sharpBandL2Pairing epsilon R he hR field hfield p w).bilinearComp
    ((stripL2Cutoff l r).restrictScalars ℝ) ((stripL2Cutoff l r).restrictScalars ℝ)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedBandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The localized positive-band Hilbert operator has a uniform L2 norm,
independent of its sharp inner endpoint and vertical frequency width. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def localizedSharpBandOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (stripL2Cutoff l r).comp
    ((bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w).comp (stripL2Cutoff l r))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalBandOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global positive and negative vertical-band bounds at one absolute
short scale, conditional on martingale variation, the directional
maximal estimate, and the horizontal Hilbert estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpBandOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PublishedBandReductionInput
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The precise published band-to-full input

Di Plinio, Guo, Thiele and Zorin-Kranich, *Square functions for bi-Lipschitz
maps and directional operators*, J. Funct. Anal. 275 (2018), 2015--2058,
DOI 10.1016/j.jfa.2018.07.005, author version arXiv:1706.07111,
Corollary 1.4, p₀=2 (printed p. 2), following Corollary 1.3.

We use only its conclusion for the fixed real, even, nonnegative and
nonzero narrow cutoff. Its frequency
support is ±[1,101/100]. This is the inverse Fourier transform of the
paper's Ψ, up to the harmless scalar normalization in the reproducing
formula. We require the hypothesis for all positive widths, which is
stronger than the paper's requirement 0<t<t₀.

The proposition below records the rescaled specialization at R<=1/10000:
set (x,y)=R(X,Y). The resulting field is u(RX,RY), whose vertical
Lipschitz constant is at most R, hence at most 1/100. The width changes
from w to w/R and the same two-dimensional L2 scaling occurs on both
sides. Our sampling uses a minus sign instead of the paper's plus sign;
the symmetric principal values differ by an overall minus sign.

-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def BandToFullInput : Prop :=
  ∀ B : ℝ, 0<B → ∃ C : ℝ, 0<C ∧
    ∀ R : ℝ, 0<R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
      (∀ w : ℝ, 0<w → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
          (schwartzVerticalProjection narrowBandProfile w 0 f)) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
          (schwartzVerticalProjection narrowBandProfile w 0 f)) 2 planeMeasure≤
            ENNReal.ofReal (B*‖f.toLp 2 planeMeasure‖)) →
      ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
          ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SelectedFarFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite far family inside an actual selection run. These data will
be obtained from the projected-popularity grouping; the local estimates
below use no further geometric assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert

structure SelectedFarFamily (ι : Type*) [DecidableEq ι] where
  n : ℕ
  directions : Fin n → Rectangle
  direction_net : ∀ T : Rectangle, ∃ i, dist ((directions i).axes 0) (T.axes 1) < 1/4
  rectangles : ι → Rectangle
  previous : Finset ι
  stock : Finset ι
  selected : List ι
  run : RectangleCoverRun rectangles
    (maximalBlocked (fun i => (directions i).orthogonalCoordinates) rectangles
      selectionDilation (by norm_num) selectionThreshold) previous stock selected
  members : Finset ι
  members_selected : members ⊆ selected.toFinset
  reference : ι
  reference_previous : reference ∈ previous
  angle : ℝ
  angle_pos : 0 < angle
  angle_small : angle ≤ 1/20
  lengths : ∀ j ∈ members, (rectangles j).long ≤ (rectangles reference).long
  intersects : ∀ j ∈ members, ((rectangles reference).carrier ∩ (rectangles j).carrier).Nonempty
  far : ∀ j ∈ members, 64*(rectangles j).short <
    (rectangles j).long*dist ((rectangles reference).axes 0) ((rectangles j).axes 0)
  angle_upper : ∀ j ∈ members, dist ((rectangles reference).axes 0) ((rectangles j).axes 0) ≤ 2*angle
  angle_lower : ∀ j ∈ members, angle/2 ≤ dist ((rectangles reference).axes 0) ((rectangles j).axes 0)

namespace SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

abbrev refRect (F : SelectedFarFamily ι) : Rectangle := F.rectangles F.reference

def longMembers (F : SelectedFarFamily ι) (l : ℝ) : Finset ι :=
  F.members.filter (fun j => 8*l ≤ (F.rectangles j).long)

def comparableMembers (F : SelectedFarFamily ι) (l : ℝ) : Finset ι :=
  F.members.filter (fun j => l ≤ (F.rectangles j).long ∧ (F.rectangles j).long ≤ 16*l)

end SelectedFarFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectanglePairEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

def overlapPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  volume ((R i).carrier ∩ (R j).carrier)

def nearPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  if (R j).long*dist ((R i).axes 0) ((R j).axes 0) ≤ 64*(R j).short then overlapPair R i j else 0

def farPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  if 64*(R j).short < (R j).long*dist ((R i).axes 0) ((R j).axes 0) then overlapPair R i j else 0

end LipschitzHilbert

end

end OAI
end


