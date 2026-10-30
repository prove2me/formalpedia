-- Prove2me | Definitions.Def_OAIQ088F002
-- name    : OAIQ088F002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:41:58.210217+00:00
-- url     : https://prove2.me/theorems/06b8115f-a1f7-4df2-a101-70d84ff1a2dc
-- title:
--   Definitions bundle OAIQ088F002 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 457 declarations of OpenAI's Lean: 352 definitions, 7 inductive types or structures, 15 instances and 83 theorems. The definitions and types are `OAI.Falconer.MaskJetIndex.jetEvaluation`, `OAI.Falconer.PreparedOriginalPair`, `OAI.Falconer.ProfileEndpointBound`, `OAI.Falconer.ProjectedStartingPair.relation`, `OAI.Falconer.PublishedFrostmanAboveHalf`, `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedHeavyHyperplanes`, `OAI.Falconer.PublishedPlanarFurstenberg`, `OAI.Falconer.PublishedQuadraticStationary`, `OAI.Falconer.PublishedRadialMoment`, `OAI.Falconer.QuarterPencilData`, `OAI.Falconer.RegularRefinementData`, `OAI.Falconer.Regularization.ScalarBranchingLevel`, `OAI.Falconer.Regularization.ScalarChildChoice`, `OAI.Falconer.Regularization.ScalarPathLevel`, `OAI.Falconer.Regularization.blockBin`, `OAI.Falconer.Regularization.blockLabel`, `OAI.Falconer.Regularization.blockLogProduct`, `OAI.Falconer.Regularization.blockProduct`, `OAI.Falconer.Regularization.blockSlope`, `OAI.Falconer.Regularization.cellScaleMap`, `OAI.Falconer.Regularization.cellsMeetingBall`, `OAI.Falconer.Regularization.classLeaves`, `OAI.Falconer.Regularization.classMeasure`, `OAI.Falconer.Regularization.classPairWeight`, `OAI.Falconer.Regularization.extendLabel`, `OAI.Falconer.Regularization.labeledChildren`, `OAI.Falconer.Regularization.leafUnion`, `OAI.Falconer.Regularization.normalizedClass`, `OAI.Falconer.Regularization.prefixChildren`, `OAI.Falconer.Regularization.prefixFiber`, `OAI.Falconer.Regularization.radialClassBallBound`, `OAI.Falconer.Regularization.regularizationIndex`, `OAI.Falconer.Regularization.regularizationLabel`, `OAI.Falconer.Regularization.regularizationLeaves`, `OAI.Falconer.Regularization.regularizationPairDistance`, `OAI.Falconer.Regularization.regularizationPairExceptional`, `OAI.Falconer.Regularization.regularizationPairMask`, `OAI.Falconer.Regularization.regularizationSet`, `OAI.Falconer.Regularization.regularizationTestBad` and 319 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory, in whole or in part: `Falconer_Angular_AngularGainFinite`, `Falconer_Angular_AngularGrid`, `Falconer_Angular_AngularSamples`, `Falconer_Angular_BadDirectionEnvelope`, `Falconer_Angular_CapNet`, `Falconer_Angular_CappedActiveCover`, `Falconer_Angular_CubeCapacity`, `Falconer_Angular_DyadicCapTerms`, `Falconer_Angular_EvenStartingCaps`, `Falconer_Angular_FourPointCaps`, `Falconer_Angular_GnomonicCap`, `Falconer_Angular_GnomonicChart`, `Falconer_Angular_GnomonicCone`, `Falconer_Angular_GnomonicPairGram`, `Falconer_Angular_GnomonicPrunedLaw`, `Falconer_Angular_GnomonicTripleAngle`, `Falconer_Angular_MultiscaleCapMass`, `Falconer_Angular_NorthRotation`, `Falconer_Angular_OuterAngularBound`, `Falconer_Angular_PublishedGnomonic`, `Falconer_Angular_SphereCapBound`, `Falconer_Angular_SphereCapBox`, `Falconer_Angular_SphereInverse`, `Falconer_Angular_SphereModel`, `Falconer_Angular_SphereRotations`, `Falconer_Estimates_AllDimensionalRegularizationLabels`, `Falconer_Estimates_AllTestsRestoration`, `Falconer_Estimates_AnchoredPairFailure`, `Falconer_Estimates_BadTripleRelation`, `Falconer_Estimates_CoarsePlanarRounding`, `Falconer_Estimates_CommonTubeKernel`, `Falconer_Estimates_ComparableBands`, `Falconer_Estimates_ConeSections`, `Falconer_Estimates_DescriptorEnvelope`, `Falconer_Estimates_DescriptorScaledKernel`, `Falconer_Estimates_DescriptorTestBad`, `Falconer_Estimates_EnergySplitting`, `Falconer_Estimates_FarRegionSplit`, `Falconer_Estimates_FilteredLimit`, `Falconer_Estimates_FinePacketCounts`, `Falconer_Estimates_FiniteAnchorLabels`, `Falconer_Estimates_FiniteEnergyRegularity`, `Falconer_Estimates_FourPointPartition`, `Falconer_Estimates_LocalCellLines`, `Falconer_Estimates_LocalPacketRows`, `Falconer_Estimates_OffPoleAmbient`, `Falconer_Estimates_OriginalPairFilter`, `Falconer_Estimates_OuterRootGain`, `Falconer_Estimates_PacketCentering`, `Falconer_Estimates_Packing`, `Falconer_Estimates_PairExceptional`, `Falconer_Estimates_PlanarQuarter`, `Falconer_Estimates_PlanarSampling`, `Falconer_Estimates_PlanarSelectedGain`, `Falconer_Estimates_PlanarSquash`, `Falconer_Estimates_PolicyLowBand`, `Falconer_Estimates_PrefixCounting`, `Falconer_Estimates_PreparedPair`, `Falconer_Estimates_ProjectedPacketRows`, `Falconer_Estimates_QuadraticDifferential`, `Falconer_Estimates_QuarterEndpointMap`, `Falconer_Estimates_RegularOuterMask`, `Falconer_Estimates_RegularRefinementData`, `Falconer_Estimates_RegularRoot`, `Falconer_Estimates_RegularizationClasses`, `Falconer_Estimates_RegularizationPairMask`, `Falconer_Estimates_RegularizationProperties`, `Falconer_Estimates_RegularizationSelection`, `Falconer_Estimates_RegularizationTestBad`, `Falconer_Estimates_RegularizationVariation`, `Falconer_Estimates_RescaledConditional`, `Falconer_Estimates_RetainedPairs`, `Falconer_Estimates_RotatedInverse`, `Falconer_Estimates_RotatedInverseExpansion`, `Falconer_Estimates_RotatedTubeData`, `Falconer_Estimates_RotatedWeightedInverse`, `Falconer_Estimates_ScalarBunchClusterTree`, `Falconer_Estimates_ScalarChildChoice`, `Falconer_Estimates_ScalarClusterPathTree`, `Falconer_Estimates_ScalarPathCenters`, `Falconer_Estimates_ScalarPathLevel`, `Falconer_Estimates_ScalarPathNodes`, `Falconer_Estimates_ScalarPointPaths`, `Falconer_Estimates_ScalarRounding`, `Falconer_Estimates_ScalarSelectedForks`, `Falconer_Estimates_ScaledInverseRemainder`, `Falconer_Estimates_ScaledWeightedInverse`, `Falconer_Estimates_SpatialAnnulusKernel`, `Falconer_Estimates_SpatialEndpointFamily`, `Falconer_Estimates_SuffixGrouping`, `Falconer_Estimates_TripleColumns`, `Falconer_Estimates_TroublesomePair`, `Falconer_Estimates_TubePacketDilation`, `Falconer_Estimates_TubeSecondMoment`, `Falconer_Estimates_ValidDescriptors`, `Falconer_Estimates_WeightedInverse`, `Falconer_Fourier_AllDimensionalSpatialFourierSeparation`, `Falconer_Fourier_BaseJetAmplitude`, `Falconer_Fourier_BumpDerivatives`, `Falconer_Fourier_CellSymbols`, `Falconer_Fourier_CompactFourierBound`, `Falconer_Fourier_ComplexMaskJets`, `Falconer_Fourier_ConeIntegration`, `Falconer_Fourier_EuclideanSmoothConvolution`, `Falconer_Fourier_InverseJetShell`, `Falconer_Fourier_InverseJetValues`, `Falconer_Fourier_JetDerivativeBounds`, `Falconer_Fourier_JetStateEnvelope`, `Falconer_Fourier_JointStationaryGeometry`, `Falconer_Fourier_PoleCutoffs`, `Falconer_Fourier_PoleStationarySupport`, `Falconer_Fourier_PublishedQuadraticStationary`, `Falconer_Fourier_QuadraticStationary`, `Falconer_Fourier_RotatedInverseSymbols`, `Falconer_Fourier_ScaledInverseIntegration`, `Falconer_Fourier_SignedStationary`, `Falconer_Fourier_StationaryTransport`, `Falconer_Geometry_BoundedProjectionCoordinates`, `Falconer_Geometry_ChartCoordinates`, `Falconer_Geometry_CubeBallPacking`, `Falconer_Geometry_EuclideanCross`, `Falconer_Geometry_EuclideanLpTrace`, `Falconer_Geometry_EuclideanMollifier`, `Falconer_Geometry_EuclideanRieszEnergy`, `Falconer_Geometry_GeneralGridRounding`, `Falconer_Geometry_GeneralTransverseGrid`, `Falconer_Geometry_GridProjectionTransfer`, `Falconer_Geometry_IntegerFivePaths`, `Falconer_Geometry_IntegerFourPaths`, `Falconer_Geometry_NormalizedInverseFactors`, `Falconer_Geometry_PlanarChartRepair`, `Falconer_Geometry_PlanarProjectionCoordinates`, `Falconer_Geometry_PlanarScalarGrid`, `Falconer_Geometry_PlanarSlopeBalls`, `Falconer_Geometry_PointBallCounts`, `Falconer_Geometry_ProjectionCells`, `Falconer_Geometry_ProjectionCoordinateBalls`, `Falconer_Geometry_ProjectionCube`, `Falconer_Geometry_ProjectionKernel`, `Falconer_Geometry_ProjectionLaw`, `Falconer_Geometry_ProjectionRows`, `Falconer_Geometry_RoundedProjectionCoordinates`, `Falconer_Geometry_SamplingGrid`, `Falconer_Geometry_ScalarForkGeometry`, `Falconer_Geometry_SeededSeparation`, `Falconer_Geometry_SelectedChartRelation`, `Falconer_Geometry_SimilarityGeometry`, `Falconer_Geometry_SmallChartCube`, `Falconer_Geometry_SurfaceTestNorm`, `Falconer_Geometry_TransverseGridCoordinates`, `Falconer_Geometry_TripleGridRounding`, `Falconer_Geometry_TwoProjectionFrame`, `Falconer_Geometry_TwoProjectionPiecePair`, `Falconer_Geometry_TwoProjectionPieces`, `Falconer_Graphs_CommonRowNormalization`, `Falconer_Graphs_DyadicGraph`, `Falconer_Graphs_EligibleDyadicGraph`, `Falconer_Graphs_GraphDegrees`, `Falconer_Graphs_NearGraph`, `Falconer_Graphs_ProfileGraph`, `Falconer_Incidence_BlockLeafCounts`, `Falconer_Incidence_BlockProfileCells`, `Falconer_Incidence_BlockRegularization`, `Falconer_Incidence_CoarsePencilWeights`, `Falconer_Incidence_GridCount`, `Falconer_Incidence_LeafMassBins`, `Falconer_Incidence_NormalizedProductPencils`, `Falconer_Incidence_PencilFiberEnergy`, `Falconer_Incidence_PublishedFurstenberg`, `Falconer_Incidence_QuarterPencils`, `Falconer_Incidence_RegularClassRadialIncidence`, `Falconer_Incidence_RegularEnergyPencils`, `Falconer_Incidence_RoundedRowPencils`, `Falconer_Incidence_SquashedPencils`, `Falconer_Incidence_WeightedLoomisBase`, `Falconer_Measures_FarOriginalSupport`, `Falconer_Measures_FrequencyMeasure`, `Falconer_Measures_ProductPartitionMask`, `Falconer_Measures_ScalarPrefixPruning`, `Falconer_Measures_ScalarProductBalls`, `Falconer_Measures_StartingMeasures`, `Falconer_Measures_SupportPairFilter`, `Falconer_Radial_AffineSlabCluster`, `Falconer_Radial_AffineSubspaceFrostman`, `Falconer_Radial_CoarsePlateDirections`, `Falconer_Radial_CoarsePlateFilter`, `Falconer_Radial_EuclideanRadialDensity`, `Falconer_Radial_FarRadialKernel`, `Falconer_Radial_FinitePlateException`, `Falconer_Radial_HeavyPlateCells`, `Falconer_Radial_HyperplaneEnergy`, `Falconer_Radial_HyperplaneFiber`, `Falconer_Radial_HyperplaneFourier`, `Falconer_Radial_HyperplaneFrame`, `Falconer_Radial_LatePlateTail`, `Falconer_Radial_LocalRadialPruning`, `Falconer_Radial_MultilevelRadialPruning`, `Falconer_Radial_PublishedHeavyPlates`, `Falconer_Radial_PublishedRadialMoment`, `Falconer_Radial_RadialBadWitness`, `Falconer_Radial_RadialCollisionMass`, `Falconer_Radial_RadialMoments`, `Falconer_Radial_RadialPairSeparation`, `Falconer_Radial_RadialPairSwap`, `Falconer_Radial_RadialSphereLaw`, `Falconer_Radial_RadialTupleTransversality`, `Falconer_Radial_SignedRadialKernel`, `Falconer_Radial_SingleStationaryRadial`, `Falconer_Radial_SphereSlab`, `Falconer_Radial_StationaryRadialSum`, `Falconer_Recursion_AnchoredTriplePotential`, `Falconer_Recursion_FiniteCountingPotential`, `Falconer_Recursion_FiniteProjectionPotential`, `Falconer_Recursion_FrequencyIntervals`, `Falconer_Recursion_IntermediateProfiles`, `Falconer_Recursion_ProfileBalls`, `Falconer_Recursion_ProfileCompactness`, `Falconer_Recursion_ProfileEndpointBound`, `Falconer_Recursion_ProfileGrid`, `Falconer_Recursion_ProfileInterpolation`, `Falconer_Recursion_ProfileNear`, `Falconer_Recursion_ProfileUniformLimit`, `Falconer_Recursion_ReachedStateRecursion`, `Falconer_Recursion_RetainedProfileBounds`, `Falconer_Recursion_ScalarBranchingLevel`, `Falconer_Recursion_UnitProfiles`, `Falconer_Shells_ClassPairDistance`, `Falconer_Shells_DistanceInverse`, `Falconer_Shells_FilteredEndpointDistance`, `Falconer_Shells_FrequencyShell`, `Falconer_Shells_PartitionEndpointDistance`, `Falconer_Shells_PositiveRestriction`, `Falconer_Shells_RotatedInverseShell`, `Falconer_Shells_SpatialSharedShell`, `Falconer_Shells_TwoProfileInverseShell`, `Falconer_Slicing_AffineSliceCoordinates`, `Falconer_Slicing_EndpointSliceCosts`, `Falconer_Slicing_GaussianActiveCount`, `Falconer_Slicing_GaussianActiveCover`, `Falconer_Slicing_GaussianActiveRelation`, `Falconer_Slicing_GaussianAmplification`, `Falconer_Slicing_GaussianBox`, `Falconer_Slicing_GaussianChartPairAverage`, `Falconer_Slicing_GaussianChartTripleAverage`, `Falconer_Slicing_GaussianCloseMass`, `Falconer_Slicing_GaussianControlledRows`, `Falconer_Slicing_GaussianConvolution`, `Falconer_Slicing_GaussianDamping`, `Falconer_Slicing_GaussianFourier`, `Falconer_Slicing_GaussianLebesgue`, `Falconer_Slicing_GaussianMultiband`, `Falconer_Slicing_GaussianPointBand`, `Falconer_Slicing_GaussianPointClose`, `Falconer_Slicing_GaussianPointMass`, `Falconer_Slicing_GaussianPrunedIncidence`, `Falconer_Slicing_GaussianPrunedPair`, `Falconer_Slicing_GaussianPruningSets`, `Falconer_Slicing_GaussianRows`, `Falconer_Slicing_GaussianSlabBox`, `Falconer_Slicing_GaussianSliceMean`, `Falconer_Slicing_GaussianSliceMoment`, `Falconer_Slicing_GaussianSpanRows`, `Falconer_Slicing_GnomonicSliceLaw`, `Falconer_Slicing_HyperplaneSlice`, `Falconer_Slicing_HyperplaneSliceEnergy`, `Falconer_Slicing_PlanarSliceGeometry`, `Falconer_Slicing_SlabSliceAverage`, `Falconer_Slicing_SliceCoordinates`, `Falconer_Slicing_SliceGeometry`.
--
--   **Imports.** It imports the bundles `OAIQ088F000` and `OAIQ088F001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ088F004`; the statements `OAI_Falconer_CapAvailable_nonendpoint_improve`, `OAI_Falconer_Regularization_endpoint_contact_gain`, `OAI_Falconer_Regularization_eventual_source_family`, `OAI.Falconer.Regularization.exists_regularization_scalar_shell`, `OAI_Falconer_Regularization_nonendpoint_contact_gain`, `OAI.Falconer.Regularization.nonendpoint_one_scale_gain`, `OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning`, `OAI_Falconer_Regularization_planar_profile_scale_selection`, `OAI_Falconer_Regularization_radial_regular_classes`, `OAI_Falconer_Regularization_scalar_bunch_cluster_projection_gain`, `OAI_Falconer_Regularization_scalar_porous_log_growth`, `OAI_Falconer_Regularization_scalar_projection_growth_of_sumset`, `OAI.Falconer.Regularization.scalar_weak_block_projection`, `OAI_Falconer_Regularization_single_class_radial_gain`, `OAI_Falconer_Regularization_source_classes_uniform_contact`, `OAI_Falconer_Regularization_uniform_parallel_exceptional`, `OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound`, `OAI_Falconer_Regularization_uniform_regularization_variation`, `OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition`, `OAI_Falconer_block_cell_normal_power`, `OAI.Falconer.block_cell_power`, `OAI.Falconer.bounded_chart_regular_fine_gain`, `OAI_Falconer_centered_packet_gain_from_local_pencils`, `OAI_Falconer_coarse_packet_gain`, `OAI_Falconer_coarse_plate_preparation`, `OAI_Falconer_common_unbalanced_regular_reference`, `OAI.Falconer.controlled_dyadic_angular_gain`, `OAI.Falconer.controlled_endpoint_angular_gain`, `OAI.Falconer.coordinate_graph_obstruction`, `OAI_Falconer_discarded_cap_term_bound`, `OAI_Falconer_displacement_inverse_expansion`, `OAI_Falconer_dyadic_localization_error`, `OAI.Falconer.dyadic_original_slice_costs`, `OAI.Falconer.dyadic_original_slice_selection`, `OAI.Falconer.dyadic_profile_graph_energy_step`, `OAI.Falconer.endpoint_original_middle_pruning`, `OAI.Falconer.endpoint_spherical_preparation`, `OAI_Falconer_even_prepared_original_pair`, `OAI.Falconer.exists_far_data_bound`, `OAI.Falconer.exists_far_data_stationary_band`, `OAI.Falconer.exists_flexible_graph_child`, `OAI_Falconer_exists_jetState_graph_step`, `OAI_Falconer_exists_jetState_noncomparable_original_pointwise`, `OAI_Falconer_exists_outer_policy_graph_step`, `OAI_Falconer_exists_policy_far_recurrence`, `OAI_Falconer_exists_policy_graph_recurrence_at`, `OAI_Falconer_exists_policy_positive_band_bound`, `OAI.Falconer.exists_policy_positive_common_budgets`, `OAI_Falconer_exists_policy_positive_suffix_recurrence`, `OAI.Falconer.exists_policy_prefix_common_budgets`, `OAI.Falconer.exists_policy_recursion_bounds`, `OAI_Falconer_exists_policy_root_bounds`, `OAI.Falconer.exists_policy_scalar_conversion`, `OAI.Falconer.exists_regular_class_shell`, `OAI.Falconer.exists_rotated_masked_fourier_inverse_order`, `OAI_Falconer_exists_two_profile_graph_step`, `OAI.Falconer.exists_two_profile_masked_shell_order`, `OAI.Falconer.exists_uniform_outer_angular_decay`, `OAI.Falconer.finite_euclidean_radial_testNorm_moment`, `OAI.Falconer.frozen_coarse_packet_impossible`, `OAI_Falconer_full_chart_regular_fine_gain`, `OAI_Falconer_general_regular_coarse_cover_alternative`, `OAI_Falconer_geometric_regular_fiber`, `OAI_Falconer_large_pencil_growth`, `OAI_Falconer_mainTarget_of_five_published_inputs`, `OAI.Falconer.mainTarget_of_three_published_inputs`, `OAI_Falconer_mainTarget_of_two_published_inputs`, `OAI.Falconer.prepared_pair_of_lower_dimensions`, `OAI.Falconer.prepared_pair_positive_distance`, `OAI_Falconer_profileEndpointBound_ordered_power`, `OAI.Falconer.publishedPlanarFurstenberg_proved`, `OAI_Falconer_regular_fine_gain`, `OAI_Falconer_regular_refinement_preparation`, `OAI.Falconer.rounded_profile_endpoint_gain`, `OAI.Falconer.scalar_shell_of_two_profile_inverse`, `OAI_Falconer_sphere_offPole_decay`, `OAI.Falconer.sphere_stationary_expansion`, `OAI_Falconer_sphere_stationary_expansion_unscaled`, `OAI_Falconer_thin_tube_upgrade`, `OAI_Falconer_uniform_profile_endpoint_gain`, `OAI_Falconer_uniform_scale_combination`, `OAI_Falconer_uniform_small_cover_pencils`, `OAI_Falconer_unit_pair_positive_distance` and `OAI_Falconer_wide_product_incidence`; the proofs of `OAI_Falconer_CapAvailable_nonendpoint_improve`, `OAI.Falconer.Regularization.endpoint_one_scale_gain`, `OAI_Falconer_Regularization_endpoint_two_sided_one_scale`, `OAI_Falconer_Regularization_eventual_source_family`, `OAI.Falconer.Regularization.exists_regularization_scalar_shell`, `OAI.Falconer.Regularization.nonendpoint_one_scale_gain`, `OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning`, `OAI_Falconer_Regularization_planar_profile_scale_selection`, `OAI_Falconer_Regularization_radial_regular_classes`, `OAI_Falconer_Regularization_scalar_bounded_projection`, `OAI_Falconer_Regularization_scalar_bunch_cluster_projection_gain`, `OAI.Falconer.Regularization.scalar_dyadic_projection`, `OAI_Falconer_Regularization_scalar_porous_log_growth`, `OAI_Falconer_Regularization_scalar_projection_growth_of_sumset`, `OAI.Falconer.Regularization.scalar_weak_block_projection`, `OAI_Falconer_Regularization_source_classes_uniform_contact`, `OAI_Falconer_Regularization_uniform_parallel_exceptional`, `OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound`, `OAI_Falconer_Regularization_uniform_regularization_variation`, `OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition`, `OAI.Falconer.block_cell_power`, `OAI.Falconer.bounded_chart_regular_fine_gain`, `OAI.Falconer.centered_packet_product_power`, `OAI_Falconer_coarse_packet_gain`, `OAI_Falconer_common_unbalanced_regular_reference`, `OAI.Falconer.controlled_dyadic_angular_gain`, `OAI.Falconer.controlled_endpoint_angular_gain`, `OAI.Falconer.coordinate_graph_obstruction`, `OAI_Falconer_discarded_cap_term_bound`, `OAI_Falconer_displacement_inverse_expansion`, `OAI_Falconer_dyadic_localization_error`, `OAI.Falconer.dyadic_original_slice_costs`, `OAI.Falconer.dyadic_original_slice_selection`, `OAI.Falconer.dyadic_profile_graph_energy_step`, `OAI.Falconer.endpoint_original_middle_pruning`, `OAI.Falconer.endpoint_spherical_preparation`, `OAI_Falconer_eventually_initial_plate_loss`, `OAI.Falconer.exists_far_data_bound`, `OAI.Falconer.exists_far_data_stationary_band`, `OAI.Falconer.exists_flexible_graph_child`, `OAI_Falconer_exists_jetState_far_tested_integral`, `OAI_Falconer_exists_jetState_graph_step`, `OAI_Falconer_exists_jetState_noncomparable_original_pointwise`, `OAI_Falconer_exists_outer_policy_graph_step`, `OAI_Falconer_exists_policy_far_recurrence`, `OAI_Falconer_exists_policy_graph_recurrence_at`, `OAI.Falconer.exists_policy_positive_common_budgets`, `OAI_Falconer_exists_policy_positive_suffix_recurrence`, `OAI.Falconer.exists_policy_prefix_common_budgets`, `OAI.Falconer.exists_policy_recursion_bounds`, `OAI_Falconer_exists_policy_root_bounds`, `OAI.Falconer.exists_policy_scalar_conversion`, `OAI.Falconer.exists_regular_class_shell`, `OAI.Falconer.exists_rotated_masked_fourier_inverse_order`, `OAI_Falconer_exists_two_profile_graph_step`, `OAI.Falconer.exists_two_profile_masked_shell_order`, `OAI.Falconer.exists_uniform_outer_angular_decay`, `OAI.Falconer.falconer_distance_conjecture`, `OAI.Falconer.finite_euclidean_radial_testNorm_moment`, `OAI.Falconer.frozen_coarse_packet_impossible`, `OAI_Falconer_gaussian_controlled_pruning_ledger`, `OAI_Falconer_gaussian_select_polynomial_costs`, `OAI_Falconer_gaussian_select_polynomial_slice`, `OAI_Falconer_geometric_regular_fiber`, `OAI_Falconer_large_pencil_growth`, `OAI.Falconer.mainTarget_of_three_published_inputs`, `OAI_Falconer_mainTarget_of_two_published_inputs`, `OAI.Falconer.prepared_pair_of_lower_dimensions`, `OAI.Falconer.prepared_pair_positive_distance`, `OAI.Falconer.publishedPlanarFurstenberg_proved`, `OAI.Falconer.rounded_profile_endpoint_gain`, `OAI.Falconer.scalar_shell_of_two_profile_inverse`, `OAI.Falconer.small_chart_weak_radial`, `OAI_Falconer_sphere_offPole_decay`, `OAI.Falconer.sphere_stationary_expansion`, `OAI_Falconer_sphere_stationary_expansion_unscaled`, `OAI_Falconer_thin_tube_upgrade`, `OAI_Falconer_uniform_profile_endpoint_gain` and `OAI_Falconer_uniform_small_cover_pencils`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F000
import Definitions.Def_OAIQ088F001

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PublishedFurstenberg
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published planar incidence input

Orponen–Shmerkin–Wang, *Kaufman and Falconer estimates for radial projections
and a continuum version of Beck's theorem*, Geom. Funct. Anal. 34 (2024),
Definitions 2.5–2.6 and Theorem 2.7 (arXiv:2209.00348), following
Orponen–Shmerkin, Duke Math. J. 172 (2023), Theorem 1.3 and Remark 1.4.

The proposition below is the separated finite-set specialization in one
bounded, nonvertical line chart needed by `ang:planar-measures`. Only
`0 < b ≤ 1/2` and `b < f < 1` are retained. The chart identifies a line
with its slope and intercept. Equivalence with the published line metric
and replacement of covering counts by cardinalities cost fixed constants;
the epsilon and the small-scale threshold below are chosen after these
constants, not identified with the published theorem's original epsilon.

This is an explicit proposition to be supplied as a hypothesis. It is not
a global axiom, and no proof of this published theorem is claimed here.
-/

namespace Falconer

/-- Exactly the range of the published planar Furstenberg estimate needed
by the higher-dimensional slicing argument, in a bounded line chart. -/
def PublishedPlanarFurstenberg : Prop := by
  classical
  exact ∀ b f : ℝ, 0 < b → b ≤ 1 / 2 → b < f → f < 1 →
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ ^ (-ε)) P →
    ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
        FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b (δ ^ (-ε)) (T x) ∧
        ∀ l ∈ T x, TubeIncident δ x l) →
      δ ^ (-2 * b - ε) ≤ ((P.biUnion T).card : ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGainFinite
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite labelled incidence obstruction

The sampling argument in `ang:planar-measures` ends with finite point
and line families. Their counting contradiction follows
from the precise published Furstenberg input. All line families must use
a common separated grid before cardinalities replace covering numbers.
Direction labels remain distinct throughout the upper counting estimate.
-/

namespace Falconer
open Set
open scoped BigOperators

/-- Choose the grid slope first, then the grid intercept nearest the exact
line through the point. Every constructed line remains incident. -/
noncomputable def roundedIncidentLine (δ : ℝ) (x : Space 2) (m : ℝ) : Space 2 :=
  WithLp.toLp 2 ![lineGridRound δ m,
    lineGridRound δ (x 1 - lineGridRound δ m * x 0)]

@[simp] theorem roundedIncidentLine_fst (δ : ℝ) (x : Space 2) (m : ℝ) :
    roundedIncidentLine δ x m 0 = lineGridRound δ m := rfl

@[simp] theorem roundedIncidentLine_snd (δ : ℝ) (x : Space 2) (m : ℝ) :
    roundedIncidentLine δ x m 1 =
      lineGridRound δ (x 1 - lineGridRound δ m * x 0) := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common line grid for the planar incidence obstruction

Each original strip gives a bounded list of common-grid line parameters.
The list is attached to its original direction label. Rounding therefore
turns the manuscript's covering-number upper bound into the cardinality
upper bound needed by `published_furstenberg_labelled_obstruction`.
-/

namespace Falconer
open Set

noncomputable def gridLine (δ : ℝ) (p : ℤ × ℤ) : Space 2 :=
  WithLp.toLp 2 ![δ * (p.1 : ℝ), δ * (p.2 : ℝ)]

@[simp] theorem gridLine_fst (δ : ℝ) (p : ℤ × ℤ) :
    gridLine δ p 0 = δ * (p.1 : ℝ) := rfl

@[simp] theorem gridLine_snd (δ : ℝ) (p : ℤ × ℤ) :
    gridLine δ p 1 = δ * (p.2 : ℝ) := rfl

/-- The bounded candidate intercept list for one strip, retaining its
original slope label even if other labels have the same rounded slope. -/
noncomputable def roundedStripCandidates (δ m a : ℝ) (L : ℕ) : Finset (Space 2) :=
  (Finset.Icc (round (a / δ) - (L : ℤ)) (round (a / δ) + (L : ℤ))).image
    (fun j => gridLine δ (round (m / δ), j))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularSamples
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite sampled direction families

Ball counts for the sampled direction labels control both multiplicities
and normalized ball counts of the rounded incident line families. The
estimates below retain the original labels, including repeated directions.
-/

namespace Falconer
open Set
open scoped BigOperators

noncomputable def roundedLineFamily {ι : Type*} [DecidableEq ι]
    (δ : ℝ) (x : Space 2) (m : ι → ℝ) (S : Finset ι) : Finset (Space 2) :=
  S.image (fun i => roundedIncidentLine δ x (m i))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereModel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Euclidean sphere and its surface measure

The surface measure is induced by polar coordinates of Euclidean
Lebesgue measure.
-/

namespace Falconer
open Set MeasureTheory

instance sphereMeasure_finite (d : ℕ) : IsFiniteMeasure (sphereMeasure d) := by
  unfold sphereMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Grid centers with mesh `s⁻¹`. A common fixed translation cancels in all
pair differences and so does not enter the counting argument. -/
noncomputable def scaledGridPoint {d : ℕ} (s : ℝ) (z : Fin d → ℤ) : Space d :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / s)

@[simp] theorem scaledGridPoint_apply {d : ℕ} (s : ℝ) (z : Fin d → ℤ) (i : Fin d) :
    scaledGridPoint s z i = (z i : ℝ) / s := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphDegrees
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Degrees of the higher-dimensional retained graph

The vertex sets are the eligible depth-`p` grid cells for a
fixed pair of caps. A parallel test controls the first unknown cell; the
scalar constraint then controls the second, in its own cap direction.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The three center tests for a fixed pair of angular caps. -/
def retainedGridEdge {d : ℕ} (s : ℝ) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : (Fin d → ℤ) × (Fin d → ℤ)) : Prop :=
  ‖perpendicularPart w₁ (scaledGridPoint s col.1 - scaledGridPoint s row.1)‖ ≤ τ ∧
  ‖perpendicularPart w₂ (scaledGridPoint s col.2 - scaledGridPoint s row.2)‖ ≤ τ ∧
  |inner ℝ w₁ (scaledGridPoint s col.1 - scaledGridPoint s row.1) +
    inner ℝ w₂ (scaledGridPoint s col.2 - scaledGridPoint s row.2)| ≤ τ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_BadDirectionEnvelope
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Borel envelope for geometric bad directions

The finite anchor net and the envelope depend only on the point law and the
geometric test, before a direction measure is selected.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def boundedTubeUnion (D R : ℝ) (J : Finset (Space d))
    (w : Sphere d) : Set (Space d) :=
  {x | ‖x‖ ≤ D ∧ ∃ a ∈ J, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ R}

noncomputable def finiteBadDirections (μ : Measure (Space d))
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) : Set (Sphere d) :=
  {w | ∃ J ∈ G.powerset, J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Packing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing bounds for the cap centers

Disjoint Euclidean balls give a bound independent of the number of chosen
centers. This supplies the bounded-overlap count needed for a separated cap
partition, and a polynomial global bound on the cap count.
-/

namespace Falconer
open Set Metric MeasureTheory

theorem separated_sphere_overlap {d : ℕ} (S : Finset (Sphere d))
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) (w : Sphere d) :
    ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d := by
  classical
  let T := S.filter (fun c => dist w c ≤ δ)
  have hinj : Function.Injective (fun c : Sphere d => (c : Space d)) := Subtype.val_injective
  have he := separated_ball_card (T.image (fun c : Sphere d => (c : Space d))) (w : Space d)
    (half_pos hδ) hδ.le (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (fun hab => hxy (congrArg Subtype.val hab))) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      simpa only [Subtype.dist_eq,dist_comm] using (Finset.mem_filter.mp ha).2)
  rw [Finset.card_image_of_injective T hinj] at he
  have hratio : 2*δ/(δ/2)+1 = (5 : ℝ) := by
    field_simp
    norm_num
  simpa only [hratio] using he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapNet
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A separated finite cap net with uniform local multiplicity

The cardinality maximization takes place in the natural numbers. It needs
only the proved Euclidean packing bound, so no selection of infinitely many
centers or measurable choice is involved.
-/

namespace Falconer
open Set Metric

theorem sphere_separated_card {d : ℕ} (S : Finset (Sphere d)) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) :
    (S.card : ℝ) ≤ (4/δ+1)^d := by
  have hinj : Function.Injective (fun x : Sphere d => (x : Space d)) := Subtype.val_injective
  have hh := separated_ball_card (S.image (fun x : Sphere d => (x : Space d))) (0 : Space d)
    (half_pos hδ) (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact (hsep a ha b hb (fun hab => hxy (congrArg Subtype.val hab))).le) (by
      intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      simpa only [dist_zero_right,sphere_norm] using (le_refl (1 : ℝ)))
  rw [Finset.card_image_of_injective S hinj] at hh
  have hr : 2*1/(δ/2)+1 = 4/δ+1 := by ring
  simpa only [hr] using hh

theorem finite_separated_cap_net (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Sphere d),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) ∧
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) ∧
      (S.card : ℝ) ≤ (4/δ+1)^d ∧
      (∀ w : Sphere d, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d) := by
  classical
  let P : Finset (Sphere d) → Prop := fun S =>
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y
  let K : Set ℕ := {k | ∃ S : Finset (Sphere d), P S ∧ S.card = k}
  have hK : BddAbove K := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((4/δ+1)^d)
    refine ⟨N,?_⟩
    intro k hk
    obtain ⟨S,hS,rfl⟩ := hk
    exact_mod_cast (sphere_separated_card S hδ hS).trans hN
  have hne : K.Nonempty := ⟨0,∅,(by simp [P]),rfl⟩
  obtain ⟨k,hk,hmax⟩ := hK.exists_isGreatest_of_nonempty hne
  obtain ⟨S,hS,hcard⟩ := hk
  refine ⟨S,hS,?_,sphere_separated_card S hδ hS,?_⟩
  · intro w
    by_contra hn
    have hfar : ∀ c ∈ S, δ/2 < dist w c := by
      simpa only [not_exists,not_and,not_le] using hn
    have hw : w ∉ S := by
      intro hw
      have hh := hfar w hw
      simp only [dist_self] at hh
      linarith
    have hS' : P (insert w S) := by
      intro x hx y hy hxy
      by_cases hxw : x = w
      · subst x
        have hyw : y ≠ w := fun h => hxy h.symm
        have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyw
        exact hfar y hyS
      · have hxS : x ∈ S := Finset.mem_of_mem_insert_of_ne hx hxw
        by_cases hyw : y = w
        · subst y
          simpa only [dist_comm] using hfar x hxS
        · exact hS x hxS y (Finset.mem_of_mem_insert_of_ne hy hyw) hxy
    have hbad := hmax (show (insert w S).card ∈ K from ⟨insert w S,hS',rfl⟩)
    rw [Finset.card_insert_of_notMem hw,← hcard] at hbad
    omega
  · intro w
    exact separated_sphere_overlap S hδ (fun x hx y hy hxy => (hS x hx y hy hxy).le) w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

variable {d : ℕ}

noncomputable def labeledChildren (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (a b : ℕ) (p : CellPath d) : Finset (CellPath d) := by
  classical
  exact (L.filter fun q => q.take a = p.take a ∧ f q = f p).image (List.take b)

noncomputable def extendLabel (L : Finset (CellPath d)) (a b : ℕ)
    (f : CellPath d → List ℕ) (p : CellPath d) : List ℕ :=
  Nat.log 2 (labeledChildren L f a b p).card :: f p

theorem take_eq_of_take_eq {p q : CellPath d} {a c : ℕ}
    (hc : c ≤ a) (h : p.take a = q.take a) : p.take c = q.take c := by
  have := congrArg (List.take c) h
  simpa only [List.take_take, Nat.min_eq_left hc] using this

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationClasses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularization classes on the original all-dimensional dyadic tree

Classes are literal disjoint unions of half-open leaves. The measure
identities and the discarded mass bounds hold for the original law.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def leafUnion (Q : DyadicCube d) (L : Finset (CellPath d)) : Set (Space d) :=
  ⋃ p ∈ L, (Q.descendant p).carrier

noncomputable def retainedLeaves (Q : DyadicCube d) (μ : Measure (Space d)) (N : ℕ)
    (t : ℝ≥0∞) : Finset (CellPath d) := by
  classical
  exact (cubePaths d N).filter fun p => t ≤ μ (Q.descendant p).carrier

noncomputable def classLeaves (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ) : Finset (CellPath d) := by
  classical
  exact L.filter fun p => f p = T

noncomputable def classMeasure (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    Measure (Space d) := μ.restrict (leafUnion Q (classLeaves L f T))

noncomputable def normalizedClass (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    Measure (Space d) := (classMeasure Q μ L f T univ)⁻¹ • classMeasure Q μ L f T

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafMassBins
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original leaf mass bins with the dimension-dependent cutoff -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def sourceLeafLabel (Q : DyadicCube d) (μ : Measure (Space d)) (N : ℕ)
    (p : CellPath d) : List ℕ := [leafMassBin d N (μ (Q.descendant p).carrier).toReal]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

noncomputable def blockLabel (L : Finset (CellPath d)) (N B : ℕ)
    (f : CellPath d → List ℕ) : ℕ → CellPath d → List ℕ
  | 0 => f
  | i+1 => extendLabel L (blockDepth N B (i+1)) (blockDepth N B i) (blockLabel L N B f i)

noncomputable def regularizationLeaves (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N : ℕ) : Finset (CellPath d) := retainedLeaves Q μ N ((2:ENNReal)^((d+2)*N))⁻¹

noncomputable def regularizationLabel (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N B : ℕ) : CellPath d → List ℕ :=
  blockLabel (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N) (N/B+1)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the regular classes with their original masses

Classes are disjoint unions of original leaves. Discarding small leaves
costs 2^(-2N), and discarding small classes costs their number times the
class threshold. No lower density of the original law is required.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularizationIndex (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) : Finset (List ℕ) :=
  ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N B)).filter
    (fun T => t ≤ classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ)

noncomputable def regularizationSet (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : Set (Space d) :=
  leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


noncomputable def prefixFiber (C : Finset (CellPath d)) (a : ℕ) (P : CellPath d) : Finset (CellPath d) := by
  classical
  exact C.filter fun q => q.take a = P

noncomputable def prefixChildren (C : Finset (CellPath d)) (a b : ℕ) (P : CellPath d) :
    Finset (CellPath d) := (prefixFiber C a P).image (List.take b)

theorem prefixChildren_mem_image {C : Finset (CellPath d)} {a b : ℕ} {P q : CellPath d}
    (hq : q ∈ prefixChildren C a b P) : q ∈ C.image (List.take b) := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩

theorem prefixFiber_parent_filter {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    {P c : CellPath d} (hc : c ∈ prefixChildren C a b P) :
    (prefixFiber C a P).filter (fun q => q.take b = c) = prefixFiber C b c := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
  have hr := (Finset.mem_filter.mp hr).2
  ext q
  simp only [prefixFiber, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hq,he⟩
    exact ⟨⟨hq,(take_eq_of_take_eq hab he).trans hr⟩,he⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockLeafCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional block-leaf counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


noncomputable def blockBin (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : ℕ :=
  2 ^ Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card

noncomputable def blockProduct (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : ℕ := ∏ j ∈ Finset.range i, blockBin L F N B j p

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

noncomputable def blockSlope (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : ℝ :=
  (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card : ℝ) /
    (N:ℝ) / ((blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ))

noncomputable def regularizedProfile (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : ℝ → ℝ :=
  finiteRampProfile (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic profile values at selected depths -/

namespace Falconer.Regularization
variable {d : ℕ}

noncomputable def blockLogProduct (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : ℕ :=
  ∑ j ∈ Finset.range i,
    Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_IntermediateProfiles
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass-profile comparison at every depth in arbitrary dimension

The interpolation loss is (d+1)*lambda. The block depths satisfy the
same numerical bracketing as in the planar case.
-/

namespace Falconer.Regularization
variable {d : ℕ}
open MeasureTheory
open scoped ENNReal

noncomputable def sourceProfile (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : ℝ → ℝ :=
  regularizedProfile (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) N B (N/B+1) p

noncomputable def sourceClass (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : Measure (Space d) :=
  normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
    (regularizationLabel Q μ N B p)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UnitProfiles
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The constructed d-Lipschitz profiles on the unit interval

This is the paper's normalization of the finite-tree profile. Its slope
bound is the ambient dimension d, and its values lie between zero and d.
-/

namespace Falconer.Regularization
open Set
variable {d : ℕ}

noncomputable def unitProfile (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) (u : ℝ) : ℝ :=
  regularizedProfile L F N B (N/B+1) p ((N : ℝ)*u)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationProperties
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit-scale profiles and conditional mass ratios of the original classes -/

namespace Falconer.Regularization
open MeasureTheory Set
variable {d : ℕ}

noncomputable def sourceUnitProfile (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : ℝ → ℝ :=
  unitProfile (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) N B p

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds obtained from actual occupied-cell profile estimates -/

namespace Falconer.Regularization
open MeasureTheory Set Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellsMeetingBall (Q : DyadicCube d) (n : ℕ) (x : Space d) (r : ℝ) :
    Finset (CellPath d) := by
  classical
  exact (cubePaths d n).filter fun p => ∃ y ∈ (Q.descendant p).carrier, y ∈ ball x r

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellScaleMap (p : ℕ) (c : Space d) (z : Space d) : Space d :=
  (2:ℝ)^p • (z-c)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianConvolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian convolution of a finite measure Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace
variable {d : ℕ}

noncomputable def euclideanFourierPhase (v x : Space d) : ℂ :=
  Complex.exp (((-(2*Real.pi)*inner ℝ x v:ℝ):ℂ)*Complex.I)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual orthogonal-band geometry for the angular slicing argument -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

noncomputable def directionSliceBand (V : Submodule ℝ (Space d)) (δ : ℝ) :
    Set (Sphere d) := {w | ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLebesgue
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

noncomputable def gaussianLebesgue (d : ℕ) : Measure (Space d) :=
  (volume : Measure (Space d)).withDensity (fun x => ENNReal.ofReal (Real.exp (-(1/2:ℝ)*‖x‖^2)))

noncomputable def normalizedGaussianLebesgue (d : ℕ) : Measure (Space d) :=
  ENNReal.ofReal (gaussianVolumeNormalization d) • gaussianLebesgue d

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

noncomputable def coordinateBox (j : ℕ) (r : ℝ) : Set (Space j) :=
  {x | ∀ i, |x i| ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRows
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Gaussian rows used for the random-subspace estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRows (d h : ℕ) : Measure (Fin h → Space d) :=
  Measure.pi (fun _ => stdGaussian (Space d))

instance gaussianRows_probability : IsProbabilityMeasure (gaussianRows d h) := by
  unfold gaussianRows
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMoment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Second moments of the actual Gaussian direction bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionBand (A : Fin h → Space d) (r : ℝ) : Set (Sphere d) :=
  {w | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMean
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First moments of actual Gaussian direction slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionMass (ν : Measure (Sphere d))
    (r : ℝ) (A : Fin h → Space d) : ℝ≥0∞ :=
  ENNReal.ofReal (r^(-(h:ℝ)))*ν (gaussianDirectionBand A r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point bands in the actual Gaussian row coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRowCoordinates (A : Fin h → Space d) (x : Space d) : Space h :=
  WithLp.toLp 2 (fun i => inner ℝ x (A i))

noncomputable def gaussianPointBand (A : Fin h → Space d) (z : Space h) (r : ℝ) : Set (Space d) :=
  {x | ∀ i, |inner ℝ x (A i)-z i| ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) : ℕ := by
  classical
  exact (S.filter (fun i => a i ∈ gaussianPointBand A z r)).card

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianCloseMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized pairs in the actual Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionSliceMeasure (ν : Measure (Sphere d))
    (A : Fin h → Space d) (r : ℝ) : Measure (Sphere d) :=
  ENNReal.ofReal (r^(-(h:ℝ))) • ν.restrict (gaussianDirectionBand A r)

instance gaussianDirectionSliceMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (A : Fin h → Space d) (r : ℝ) : IsFiniteMeasure (gaussianDirectionSliceMeasure ν A r) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (r^(-(h:ℝ)))*(ν.restrict (gaussianDirectionBand A r)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

noncomputable def gaussianDirectionCloseMass (ν : Measure (Sphere d))
    (A : Fin h → Space d) (r ρ : ℝ) : ℝ≥0∞ :=
  (ν.prod ν) ({z | dist z.1 z.2 < ρ} ∩
    ((gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized point slices in Gaussian row coordinates -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointSliceMeasure (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : Measure (Space d) :=
  ENNReal.ofReal (r^(-(h:ℝ))) • μ.restrict (gaussianPointBand A z r)

noncomputable def gaussianPointMass (μ : Measure (Space d)) (r : ℝ)
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ENNReal.ofReal (r^(-(h:ℝ)))*μ (gaussianPointBand p.1 p.2 r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointClose
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized pairs of Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointCloseMass (μ : Measure (Space d))
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) : ℝ≥0∞ :=
  (μ.prod μ) ({z | dist z.1 z.2 < ρ} ∩
    ((gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r)))

instance gaussianPointSliceMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : IsFiniteMeasure (gaussianPointSliceMeasure μ A z r) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (r^(-(h:ℝ)))*(μ.restrict (gaussianPointBand A z r)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningSets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

def gaussianPointGood (μ : Measure (Space d)) (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) : Set (Space d) :=
  finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T

def gaussianDirectionGood (ν : Measure (Sphere d)) (δ : ℝ) (r : ι → ℝ)
    (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) : Set (Sphere d) :=
  {w | gaussianDirectionMass ν δ A ≤ M ∧ w ∈ finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence on the original labels after the marginal slice restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedIncidence
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)).prod
    ((gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)) E

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSlabBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Gaussian mass in a bounded coordinate slab -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

def coordinateSlabBox (c : Space (n+1)) (r ρ : ℝ) : Set (Space (n+1)) :=
  {x | |x 0| ≤ r ∧ ∀ i : Fin n, |x i.succ-c i.succ| ≤ ρ}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianControlledRows
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive band mass on uniformly controlled Gaussian row parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

def gaussianRowNeighborhood (B : Fin h → Space (n+1)) (ε : ℝ) :
    Set (Fin h → Space (n+1)) := {A | ∀ i, ‖A i-B i‖ ≤ ε}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedPair
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable parameter-dependent incidence on the retained original laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedPairMass
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  gaussianPrunedIncidence μ ν δ r TP TD M {t | (p,t) ∈ G} p

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveRelation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def gaussianActiveRelation (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ)
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
  {q | q.2 ∈ E ∧ if good then
      (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞) ≤ T
    else T < (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞)}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCover
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projected fiber cover keeps the original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) : Finset ι := by
  classical
  exact J.filter (fun i => a i ∈ gaussianPointBand A z R)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric Euclidean coordinates on the actual finite-dimensional slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

noncomputable def sliceCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : V ≃ₗᵢ[ℝ] Space m :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr hm)).repr

noncomputable def slicePointCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : Space d) : Space m :=
  sliceCoordinates V hm (V.orthogonalProjectionOnto x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_PlanarSliceGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oriented planar coordinates and the strip equations of sliced tubes -/

namespace Falconer
open NormedSpace

noncomputable def planarSlope (w : Space 2) : ℝ := w 1 / w 0

noncomputable def planarIntercept (w x : Space 2) : ℝ := x 1-planarSlope w*x 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CappedActiveCover
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded anchor lists for every original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {κ : Type*}

noncomputable def cappedActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R t : ℝ) : Finset κ :=
  if ((gaussianActiveAnchors A z J a R).card : ℝ) ≤ t then
    gaussianActiveAnchors A z J a R else ∅

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CubeCapacity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.sphereMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic capacities in the original ambient dimension

These capacities construct the compactly supported Frostman law needed by the
application. At each occupied cube the available mass is the smaller of its
geometric capacity and the total available mass of its children.
-/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

noncomputable def cubeOccupied {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) : ℝ :=
  if (E ∩ Q.carrier).Nonempty then Q.side^s else 0

noncomputable def cubeCapacity {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) : ℕ → ℝ
  | 0 => cubeOccupied E s Q
  | K+1 => min (cubeOccupied E s Q) (∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPairSwap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial Fubini for an original-label cap pair

The finite shell law and bounded measurable endpoint factors justify moving
its integral inside both the angles and the original spatial labels. No
spatial regularity or separation of the two angles is required.
-/

namespace Falconer
open MeasureTheory

noncomputable def expandedCapTerm {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℝ) (Ψ : ℝ → ℝ) (v₁ v₂ : X → Space d)
    (b₁ b₂ : X → Sphere d → ℂ) : ℂ :=
  ∫ r, ∫ z : Sphere d × Sphere d, ∫ x,
    Complex.exp (Complex.I*(r : ℂ)*
      ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+
       (inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
    ∂μ ∂(sphereMeasure d).prod (sphereMeasure d)
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FourPointCaps
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact cap expansion of an endpoint cross term

Each cap weight stays inside the original four-point amplitude. The only
factor removed from the integral is the product of the four model-mass
normalizations. The measures are the original restricted endpoint laws.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

noncomputable def capPairAmplitude {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) (x : Space d × Space d) (w : Sphere d) : ℂ :=
  (η w : ℂ) * (b x.1 w * star (b' x.2 w))

noncomputable def endpointCapCrossTerm {d : ℕ}
    (μ μ' ν ν' : Measure (Space d)) (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) : ℂ :=
  ∫ r, ∫ z : Sphere d × Sphere d,
    ((η z.1 : ℂ)*(θ z.2 : ℂ)) *
      ((endpointTransform μ M b r z.1 * endpointTransform ν P c r z.2) *
       star (endpointTransform μ' M' b' r z.1 * endpointTransform ν' P' c' r z.2))
    ∂(sphereMeasure d).prod (sphereMeasure d)
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EnergySplitting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact independent-energy expansion on the original dyadic cells

The two endpoint laws and their symbols are unchanged when passing to
occupied descendants. The identity keeps every complex cross term inside
the angular--radial integral, where nonstationary localization is applied.
-/

namespace Falconer
open MeasureTheory

noncomputable abbrev angularProductMeasure (d : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) :=
  (PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
    ((sphereMeasure d).prod (sphereMeasure d))

noncomputable def dyadicPairTransform {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ)
    (b c : Space d → Sphere d → ℂ)
    (p : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) : ℂ :=
  endpointTransform (μ.restrict (Q₁.descendant p.1).carrier) M₁ b z.1 z.2.1 *
    endpointTransform (ν.restrict (Q₂.descendant p.2).carrier) M₂ c z.1 z.2.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DyadicCapTerms
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap terms on the original dyadic descendants

The finite graph expansion and the analytic endpoint cross terms use the
same restricted laws and model masses. These identities connect them
without changing the spatial labels or taking an absolute value early.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def dyadicCapIntegrand {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ)
    (b c : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) : ℂ :=
  (η z.2.1*θ z.2.2) • (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
    star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem continuous_sphereMap {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    Continuous (sphereMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

noncomputable def sphereHomeomorph {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) : Sphere d ≃ₜ Sphere d where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv := by intro w; apply Subtype.ext; simp [sphereMap]
  right_inv := by intro w; apply Subtype.ext; simp [sphereMap]
  continuous_toFun := continuous_sphereMap e
  continuous_invFun := continuous_sphereMap e.symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def northHemisphere (n : ℕ) : Set (Sphere (n+1)) :=
  {w | 0 < (w : Space (n+1)) 0}

noncomputable def gnomonicDensity {n : ℕ} (x : Space n) : ℝ :=
  (1+‖x‖^2)^(-((n+1 : ℕ) : ℝ)/2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PublishedGnomonic
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published surface-measure formula used for angular integration

Besau, Hack, Pivovarov, Schuster, *Spherical centroid bodies*,
American Journal of Mathematics **145** (2023), 515–542,
DOI 10.1353/ajm.2023.0012, Lemma 2.3(a), with the inverse chart of
Lemma 2.2(a). The authors assume sphere dimension at least two.

Only the exact density of ordinary spherical Lebesgue measure under the
gnomonic chart is assumed. This input contains no incidence or oscillatory
estimate. The resulting integral formulas retain the actual sphere measure
used in `independentAngularEnergy`.
-/

namespace Falconer
open Set MeasureTheory

def PublishedGnomonicSurface : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    Measure.map (@gnomonicChart n)
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) =
        (sphereMeasure (n+1)).restrict (northHemisphere n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarSlopeBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direction-ball control transfers to the slope coordinate -/

namespace Falconer
open Set MeasureTheory NormedSpace

noncomputable def slopeVector (m : ℝ) : Space 2 := WithLp.toLp 2 ![1,m]

@[simp] theorem slopeVector_zero (m : ℝ) : slopeVector m 0 = 1 := rfl
@[simp] theorem slopeVector_one (m : ℝ) : slopeVector m 1 = m := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

theorem inner_northLift_zero (w : Space (n+1)) :
    inner ℝ w (northLift (0 : Space n)) = w 0 := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rectangular bound for the cone under a spherical cap -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable def northCapBox (n : ℕ) (r : ℝ) : Set (Space (n+1)) :=
  WithLp.ofLp ⁻¹' Icc (Fin.cons (-1) (fun _ : Fin n => -r))
    (Fin.cons 1 (fun _ : Fin n => r))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spherical surface measure has its dimensional cap bound -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

noncomputable def surfaceMeasure (d : ℕ) : Measure (Space d) :=
  (sphereMeasure d).map (Subtype.val : Sphere d → Space d)

instance surfaceMeasure_finite (d : ℕ) : IsFiniteMeasure (surfaceMeasure d) := by
  unfold surfaceMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

/-- Application-level specialization of Mattila (1995), Theorem 8.8.
The upper bound on the exponent only fixes a convenient unit-size gap. -/
def PublishedFrostmanAboveHalf : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ E : Set (Space d), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E →
    ∃ s : ℝ, (d : ℝ) / 2 < s ∧ s < (d : ℝ) / 2 + 1 ∧
      ∃ μ : ProbabilityMeasure (Space d), (μ : Measure (Space d)) Eᶜ = 0 ∧
        ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (μ : Measure (Space d)) s C

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanRieszEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

noncomputable def euclideanEnergyMajorant (x : Space d) (u : ℝ) (n : ℕ) : Space d → ℝ≥0∞ :=
  (ball x (2*energyScale n)).indicator
    (fun _ => ENNReal.ofReal ((energyScale n/2)^(-u)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMoments
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

instance instIsMarkovKernelSpaceRadialKernel {d : ℕ} (ν : ProbabilityMeasure (Space d)) : IsMarkovKernel (radialKernel ν) := by
  unfold radialKernel
  exact Kernel.IsMarkovKernel.map _ measurable_radialDirection_joint

/-- A single jointly measurable choice of the radial angular densities. -/
noncomputable def radialKernelDensity {d : ℕ} (ν : ProbabilityMeasure (Space d))
    (σ : Measure (Space d)) : Space d × Space d → ℝ≥0∞ :=
  fun z => (radialKernel ν).rnDeriv (Kernel.const (Space d) σ) z.1 z.2

@[fun_prop] theorem measurable_radialKernelDensity {d : ℕ}
    (ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d)) :
    Measurable (radialKernelDensity ν σ) :=
  Kernel.measurable_rnDeriv _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PublishedRadialMoment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact all-dimensional published radial moment input

T. Orponen, *On the dimension and smoothness of radial projections*,
Analysis & PDE 12 (2019), 1273–1294, proof of Theorem 1.13,
equations (3.5)–(3.6), printed pp. 1290–1292.
https://msp.org/apde/2019/12-5/apde-v12-n5-p06-s.pdf

Only s=h+delta/2, t=h-delta/4, p=1+delta/(8h) in dimension h+1 are used.
The strict parameter inequalities are proved locally. On disjoint compact
supports the source weight |x-y|^(-h) and its inverse are uniformly bounded,
so the published moment yields this unweighted finite moment and absolute
continuity. The reference measure is the actual Euclidean surface measure.
The moment bound concerns the radial projection and its absolute continuity.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def PublishedRadialMoment : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∀ (μ ν : ProbabilityMeasure (Space (h+1))) (δ : ℝ),
    0 < δ → δ < 1 →
    IsCompact (μ : Measure (Space (h+1))).support →
    IsCompact (ν : Measure (Space (h+1))).support →
    Disjoint (μ : Measure (Space (h+1))).support (ν : Measure (Space (h+1))).support →
    PlanarFalconer.rieszEnergyOn (μ : Measure (Space (h+1))) ((h:ℝ)+δ/2) < ∞ →
    PlanarFalconer.rieszEnergyOn (ν : Measure (Space (h+1))) ((h:ℝ)-δ/4) < ∞ →
    (∀ᵐ x ∂(ν : Measure (Space (h+1))),
      (μ : Measure (Space (h+1))).map (radialDirection x) ≪ surfaceMeasure (h+1)) ∧
    (∫⁻ x, ∫⁻ w,
      ((μ : Measure (Space (h+1))).map (radialDirection x)).rnDeriv (surfaceMeasure (h+1)) w ^
        (1+δ/(8*(h:ℝ))) ∂surfaceMeasure (h+1) ∂(ν : Measure (Space (h+1)))) < ∞

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTupleTransversality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative radial pin transversality from original-law slab bounds -/

namespace Falconer
open Set MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}

noncomputable def radialPinTuple (c : Space (n+1)) (w : Fin (n+1) → Space (n+1)) :=
  fun i => normalize (c-w i)

def radialResidualBad (c : Space (n+1)) (r : ℝ) (i : Fin (n+1)) :
    Set (Fin (n+1) → Space (n+1)) :=
  {w | ‖gramSchmidt ℝ (radialPinTuple c w) i‖ < r}

def radialTupleBad (c : Space (n+1)) (r : ℝ) : Set (Fin (n+1) → Space (n+1)) :=
  ⋃ i : Fin (n+1), radialResidualBad c r i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TroublesomePair
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable troublesome pairs use the full original conditional source law -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialTubeMass (μ : Measure (Space d)) (W : ℝ)
    (p : Space d × Space d) : ℝ≥0∞ :=
  μ {y | ‖perpendicularPart (normalize (p.1-p.2)) (y-p.2)‖ ≤ W}

noncomputable def troublesomePair (μ : Measure (Space d)) (c : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞) : Set (Space d × Space d) :=
  {p | r ≤ ‖c-p.2‖ ∧ p.1 ≠ p.2 ∧ ‖p.1-c‖ ≤ D ∧ ‖p.1‖ ≤ B ∧ F < radialTubeMass μ W p}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable radial collision masses and the original-pin Fubini identity -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialCollisionMass (μ : Measure (Space d)) (δ : ℝ)
    (p : Space d × Space d) : ℝ≥0∞ :=
  μ {y | dist (normalize (y-p.2)) (normalize (p.1-p.2)) ≤ δ}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereLaw
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sphere-valued original radial laws, with a harmless diagonal value -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def originalRadialSphereLaw (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) : Measure (Sphere d) :=
  Measure.map (fun x => normalizeToSphere w₀ (x-z)) (ν.restrict {x | (z,x) ∈ G})

instance originalRadialSphereLaw_finite (w₀ : Sphere d) (ν : Measure (Space d))
    [IsFiniteMeasure ν] (G : Set (Space d × Space d)) (z : Space d) :
    IsFiniteMeasure (originalRadialSphereLaw w₀ ν G z) := by
  unfold originalRadialSphereLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveRestriction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive original restrictions preserve all projected Frostman bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def positiveRestriction (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) : ProbabilityMeasure (Space d) :=
  normalizedSliceLaw ((μ : Measure (Space d)).restrict A) (by simpa using hA.ne')

theorem positiveRestriction_eq (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) :
    (positiveRestriction μ A hA : Measure (Space d)) =
      ENNReal.ofReal (((μ : Measure (Space d)) A).toReal⁻¹) • (μ : Measure (Space d)).restrict A := by
  rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hA.ne' (measure_ne_top _ _)),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp only [positiveRestriction,normalizedSliceLaw,Measure.restrict_apply_univ]
  rfl

theorem positiveRestriction_support (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) (hclosed : IsClosed A) :
    (positiveRestriction μ A hA : Measure (Space d)).support ⊆ A := by
  apply Measure.support_subset_of_isClosed hclosed
  change (positiveRestriction μ A hA : Measure (Space d)) Aᶜ = 0
  rw [positiveRestriction_eq,Measure.smul_apply,Measure.restrict_apply hclosed.measurableSet.compl,
    compl_inter_self,measure_empty,smul_zero]

theorem positiveRestriction_absolutelyContinuous (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) :
    (positiveRestriction μ A hA : Measure (Space d)) ≪ (μ : Measure (Space d)) := by
  rw [positiveRestriction_eq]
  exact Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem positiveRestriction_projected_frostman (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A)
    (P : Space d →L[ℝ] Space m) {s C : ℝ}
    (hfrost : FrostmanBallBound ((μ : Measure (Space d)).map P) s C) :
    FrostmanBallBound ((positiveRestriction μ A hA : Measure (Space d)).map P) s
      (((μ : Measure (Space d)) A).toReal⁻¹*C) := by
  intro x r hr
  rw [positiveRestriction_eq,Measure.map_smul,
    Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (((μ : Measure (Space d)) A).toReal⁻¹) * ENNReal.ofReal (C*r^s) :=
      mul_le_mul_right ((Measure.map_mono Measure.restrict_le_self P.continuous.measurable _).trans
        (hfrost x r hr)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EvenStartingCaps
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-pair starting cap estimate in even dimensions -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace ProjectedStartingPair
variable {d m : ℕ} {ζ : ProbabilityMeasure (Space d)} {s ε : ℝ}

def relation (p : ProjectedStartingPair ζ m s ε) : Set (Space d × Space d) :=
  (p.left : Measure (Space d)).support ×ˢ (p.right : Measure (Space d)).support

end ProjectedStartingPair

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCone
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gnomonic sectors as ordinary Euclidean cones -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

noncomputable def gnomonicCone {n : ℕ} (A : Set (Space n)) : Set (Space (n+1)) :=
  Ioo (0:ℝ) 1 • (Subtype.val '' (gnomonicChart '' A))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicPairGram
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair transversality retains the original affine separation -/

namespace Falconer
variable {n : ℕ}

noncomputable def pairGram {d : ℕ} (u v : Space d) : ℝ :=
  ‖u‖^2*‖v‖^2-(inner ℝ u v)^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GnomonicSliceLaw
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian direction slices retain the original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartSliceMeasure (μ : Measure (Space n))
    (A : Fin h → Space (n+1)) (r : ℝ) : Measure (Space n) :=
  ENNReal.ofReal (r^(-(h:ℝ))) •
    μ.restrict (gnomonicChart ⁻¹' gaussianDirectionBand A r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicPrunedLaw
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of restricted original chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

instance gaussianChartSliceMeasure_finite (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    (A : Fin h → Space (n+1)) (δ : ℝ) :
    IsFiniteMeasure (gaussianChartSliceMeasure ν₀ A δ) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (δ^(-(h:ℝ)))*(ν₀.restrict (gnomonicChart ⁻¹' gaussianDirectionBand A δ)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicTripleAngle
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The affine displacement angle controls the spherical triple determinant -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

noncomputable def displacementAngle (p q r : Space n) : ℝ :=
  ‖perpendicularPart (normalize (q-p)) (normalize (r-p))‖

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_MultiscaleCapMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying actual physical-tube charges for one retained radial cap -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

noncomputable def retainedRadialCap (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) : Set (Space d) :=
  {z | (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r}

noncomputable def radialCapHitCells (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) (j : ℕ) : Finset ι := by
  classical
  exact (I j).filter (fun i => ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NorthRotation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sending the prepared direction to the canonical north pole

An orthogonal reflection handles every equal-norm pair, including opposite
directions. Normalization and all cap distances commute with this fixed
linear isometry, so the original prepared cap can be transported exactly.
-/

namespace Falconer
open Set MeasureTheory NormedSpace

noncomputable def northRotation {n : ℕ} (u : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (ℝ ∙ ((u : Space (n+1))-(gnomonicChart (0 : Space n) : Space (n+1))))ᗮ.reflection

theorem northRotation_apply {n : ℕ} (u : Sphere (n+1)) :
    northRotation u u = (gnomonicChart (0 : Space n) : Space (n+1)) := by
  exact Submodule.reflection_sub (by rw [sphere_norm,sphere_norm])

/-- Preparation uses the direction `y-x`; the inverse phase uses `x-y`. -/
noncomputable def reverseNorthRotation {n : ℕ} (u : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (LinearIsometryEquiv.neg ℝ).trans (northRotation u)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FilteredLimit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits of decreasing original-pair filters

For the manuscript application, `ρ` is the original product measure with
the bounded distance weight, and `f` is the original distance map. These
lemmas do not replace distances by those of any auxiliary projection.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

instance filteredPushforward_finite (f : X → Y) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : Set X) : IsFiniteMeasure (filteredPushforward f ρ G) :=
  inferInstanceAs (IsFiniteMeasure (Measure.map f (ρ.restrict G)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

noncomputable def chartPole (n : ℕ) : Space (n+2) :=
  coordinateJoin (0 : Space (n+1)) 1

noncomputable def chartAxis (n : ℕ) : Space (n+2) :=
  coordinateJoin (coordinateJoin (0 : Space n) 1) 0

noncomputable def transverseLift {n : ℕ} (x : Space n) : Space (n+2) :=
  coordinateJoin (coordinateJoin x 0) 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BumpDerivatives
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of scaled cap bumps

A single compactly supported bump controls every center and radius. The
scale enters through the curve supplied to that fixed bump, so the k-th
bound loses only the k-th power of the inverse cap radius.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def unitCapBump (d : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrequencyMeasure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds for an actual radial frequency-shell pushforward -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def radialFrequencyMap {d : ℕ} (z : ℝ × Sphere d) : Space d :=
  z.1 • (z.2 : Space d)

noncomputable def radialFrequencyMeasure {d : ℕ} (ν : Measure (Sphere d)) (B : ℝ) :
    Measure (Space d) := Measure.map radialFrequencyMap
      ((volume.restrict (radialFrequencyAnnulus B)).prod ν)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FrequencyShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian localization for the actual frequency-shell law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

instance radialFrequencyMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (B : ℝ) :
    IsFiniteMeasure (radialFrequencyMeasure ν B) := by
  have hsub : radialFrequencyAnnulus B ⊆ Icc (-2*|B|) (2*|B|) := by
    intro t ht
    have hab : |t| ≤ 2*|B| := ht.2.trans (by nlinarith [le_abs_self B])
    simpa only [mem_Icc,neg_mul] using abs_le.mp hab
  have : IsFiniteMeasure (volume.restrict (radialFrequencyAnnulus B)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      apply (measure_mono hsub).trans_lt
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩
  unfold radialFrequencyMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FrequencyIntervals
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering the actual radial interval by its dyadic frequency annuli -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialIntervalMeasure (ν : Measure (Sphere d)) (H : ℝ) : Measure (Space d) :=
  Measure.map radialFrequencyMap ((volume.restrict (Icc (-H) H)).prod ν)

instance radialIntervalMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (H : ℝ) :
    IsFiniteMeasure (radialIntervalMeasure ν H) := by
  unfold radialIntervalMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianDamping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Damping a finite source measure and recovering its Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

noncomputable def gaussianDampedMeasure (β : Measure (Space d)) : Measure (Space d) :=
  β.withDensity (fun x => ENNReal.ofReal (Real.exp (-(Real.pi^2/2)*‖x‖^2)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianAmplification
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Undoing Gaussian damping on a bounded original probability -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianAmplifiedMeasure (μ : Measure (Space d)) : Measure (Space d) :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*‖x‖^2)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionLaw
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual scalar projection law and its sinc collision bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def scalarProjectionLaw (μ : Measure (Space d)) (w : Space d) : Measure ℝ :=
  μ.map (fun x => inner ℝ x w)

instance scalarProjectionLaw_finite (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) :
    IsFiniteMeasure (scalarProjectionLaw μ w) := by unfold scalarProjectionLaw; infer_instance

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse grouping of the actual all-dimensional distance cells

Two fine distance distributions sharing one bin force all distances of
their full cell pairs into a common coarse collision band. The width
constant retains the ambient dimension explicitly.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellDistance (μ ν : Measure (Space d)) (P Q : DyadicCube d) : Measure ℝ :=
  Measure.map (fun z : Space d × Space d => dist z.1 z.2)
    ((μ.restrict P.carrier).prod (ν.restrict Q.carrier))

instance cellDistance_finite (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : IsFiniteMeasure (cellDistance μ ν P Q) := by
  unfold cellDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedPairs
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

instance testedCellPair_finite (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) : IsFiniteMeasure (testedCellPair μ ν P Q G) := by
  unfold testedCellPair
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance testedCellDistance_finite (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) : IsFiniteMeasure (testedCellDistance μ ν P Q G) := by
  unfold testedCellDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def retainedCellPairs (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (n : ℕ) (G : Set (Space d × Space d)) :
    Finset (List (Fin d → Bool) × List (Fin d → Bool)) :=
  (P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n).filter fun c =>
    ∃ x ∈ (P.descendant c.1).carrier, ∃ y ∈ (Q.descendant c.2).carrier, (x,y) ∈ G

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_NearGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The near part of the independent angular energy

Nearness is imposed on both actual center displacements. Integer grid
packing gives a dimensional degree bound; positive Schur integration then
controls this part by the sum of the original child energies. No angular
localization or separation of the two parent cells is used.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

def nearDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  ‖(Q₁.descendant col.1).center-(Q₁.descendant row.1).center‖ ≤ τ ∧
  ‖(Q₂.descendant col.2).center-(Q₂.descendant row.2).center‖ ≤ τ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNear
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def profileNearEnergy (Q₁ Q₂ : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N a p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (b c : Space d → Sphere d → ℂ) : ℝ :=
  (profileModelMass m N p/profileModelMass m N a)^4 *
    (2:ℝ)^((d:ℝ)*(v-a)) *
    ‖∫ z, ∑ row ∈ Q₁.occupiedPaths ρ (p-a) ×ˢ Q₂.occupiedPaths ρ (p-a),
      ∑ col ∈ Q₁.occupiedPaths ρ (p-a) ×ˢ Q₂.occupiedPaths ρ (p-a),
        if nearDyadicEdge Q₁ Q₂ (10*((d:ℝ)+1)/(2:ℝ)^p) row col then
          dyadicPairTransform Q₁ Q₂ ρ ρ (profileModelMass m N p)
            (profileModelMass m N p) b c row z *
          star (dyadicPairTransform Q₁ Q₂ ρ ρ (profileModelMass m N p)
            (profileModelMass m N p) b c col z) else 0
      ∂angularProductMeasure d v Ψ‖

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyLowBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive low-prefix transition for the actual policy list -/

namespace Falconer
open Set MeasureTheory

noncomputable def policyMaskedDistance {d : ℕ} (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ)
    (σ : ℝ) (J i q a t : ℕ)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (X Y : DyadicCube d) : Measure ℝ :=
  maskedCellDistance w₀ Q ρ m N σ J i a
    (PlanarFalconer.policyDescriptorList A N q a t) S X Y

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PublishedQuadraticStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed negative-quadratic stationary-phase input

Maciej Zworski, *Semiclassical Analysis*, AMS Graduate Studies in Mathematics
138 (2012), Theorem 3.13, equation (3.5.3), and the remainder estimate in its
proof (printed pp. 54–55):
https://math.jhu.edu/~lindblad/633/Zworski_final.pdf

This is only the specialization `Q = -I`, `h = 1 / Λ`, in dimension
`n = d - 1 ≥ 2`, for amplitudes supported in the fixed closed unit ball.
The Fourier convention in the cited formula is `exp (-i ⟨x, ξ⟩)`, with
`D = (1/i) ∂`. Consequently `⟨Q⁻¹ D, D⟩` is the ordinary Laplacian
`∑ ∂ᵢ²`, and the coefficient is `Δʲ / ((2i)ʲ j!)`. The Gaussian factor is
`(2π)^(n/2) exp (-iπn/4)`, already defined as `sphereStationaryConstant`.

The source controls the remainder by derivatives through order `2J+n+1`.
An operator-norm bound for the iterated Fréchet derivatives bounds each
coordinate derivative; its dimensional constants are absorbed into `C`.
No spherical stationary-phase statement is assumed here.
-/

namespace Falconer
open Set MeasureTheory
open scoped BigOperators ContDiff

/-- The fixed-quadratic stationary-phase hypothesis, uniform over
amplitudes and frequencies. -/
def PublishedQuadraticStationary : Prop :=
  ∀ (n J : ℕ), 2 ≤ n → 1 ≤ J → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : Space n → ℂ), ContDiff ℝ ∞ a →
      tsupport a ⊆ Metric.closedBall (0 : Space n) 1 →
      ∀ B : ℝ, 0 ≤ B →
        (∀ k ≤ 2*J+n+1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ B) →
        ∀ Λ : ℝ, 1 ≤ Λ →
          ‖((Λ ^ ((n : ℝ)/2) : ℝ) : ℂ) *
              (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*
                (‖x‖^2 : ℝ)) * a x) -
            ∑ j ∈ Finset.range J,
              ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j a‖ ≤
            C * Λ ^ (-(J : ℝ)) * B

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ComparableBands
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Borel dyadic bands for the two original comparable displacements

The finite cover has the exact constants used by the far-cell partner
geometry. Nonnegative integration only needs a cover, so no arbitrary
choice of a depth or additional measurability hypothesis is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def comparableLengthBand (d b : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < dist z.1.1 z.1.2 ∧
          dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) ∧
        (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < dist z.2.1 z.2.2 ∧
          dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)))}

def comparableFarRegion (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤
          2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) ∧
        8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤ 2*dist z.1.1 z.1.2 ∧
        max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤ 2*dist z.2.1 z.2.2}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FourPointPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original four-point partitions before far rebinning

Each internal pair keeps its original two endpoint restrictions. These
identities allow a nonnegative kernel bound to discard a far-label
selection and then repartition at the common comparable-displacement depth.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def fourPointChildMeasure {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d))
    (u v : List (Fin d → Bool) × List (Fin d → Bool)) :
    Measure ((Space d × Space d) × (Space d × Space d)) :=
  ((μ.restrict (P.descendant u.1).carrier).prod (μ.restrict (P.descendant u.2).carrier)).prod
    ((ν.restrict (Q.descendant v.1).carrier).prod (ν.restrict (Q.descendant v.2).carrier))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticDifferential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differential of the quadratic-to-gnomonic coordinate change

The differential is a scalar multiple of the identity plus one radial
rank-one term. These are actual derivatives of the coordinate map, not
assumed Jacobian data.
-/

namespace Falconer

noncomputable def quadraticCoordinateDifferential {n : ℕ} (u : Space n) :
    Space n →L[ℝ] Space n :=
  quadraticRadialFactor (‖u‖^2) • ContinuousLinearMap.id ℝ (Space n) +
    (2 * quadraticRadialDerivative (‖u‖^2)) • (innerSL ℝ u).smulRight u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the quadratic expansion to the actual sphere integral

The amplitude is the explicitly computed surface density times the spherical
amplitude, extended by zero from the fixed unit chart. Smoothness and its
quantitative derivative bounds are retained as local obligations. The only
published inputs are the gnomonic measure formula and the fixed Euclidean
quadratic stationary-phase theorem.
-/

namespace Falconer
open Set MeasureTheory Metric
open scoped BigOperators ContDiff

noncomputable def quadraticSphereOscillation (m : ℕ) (Λ : ℝ)
    (b : Sphere (m+3) → ℂ) : ℂ :=
  ∫ w : Sphere (m+3),
    Complex.exp (Complex.I*(Λ : ℂ)*
      (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
    ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

noncomputable def stationaryPoleRotation {n : ℕ} (e : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (ℝ ∙ ((gnomonicChart (0 : Space n) : Space (n+1)) + (e : Space (n+1)))).reflection

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleCutoffs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

noncomputable def offPoleCutoff {d : ℕ} (e : Sphere d) (x : Space d) : ℝ :=
  1-poleCutoff e x-poleCutoff (oppositePole e) x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleStationarySupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual support conditions for the pole expansion

Geometric support in a radius-1/4 cap implies all support conditions in
the quadratic stationary theorem. The ambient pole bump is invisible to
the actual coefficient jets at its center.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def poleLocalizedAmbient {d : ℕ} (e : Sphere d)
    (B : Space d → ℂ) (x : Space d) : ℂ := (poleCutoff e x : ℂ)*B x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OffPoleAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The off-pole estimate with the original ambient derivative budget -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def offPoleLocalizedAmbient {d : ℕ} (e : Sphere d) (B : Space d → ℂ)
    (x : Space d) : ℂ := (offPoleCutoff e x : ℂ)*B x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialAnnulusKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth annular inverse-distance kernels in the ambient Euclidean space. -/

namespace Falconer
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap
variable {d : ℕ}

noncomputable def spatialInnerBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Space d) :=
  ⟨δ/2, δ, half_pos hδ, half_lt_self hδ⟩

noncomputable def spatialOuterBump (L : ℝ) (hL : 0 < L) : ContDiffBump (0 : Space d) :=
  ⟨L, L+1, hL, by linarith⟩

noncomputable def spatialAnnulusKernel (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (z : Space d) : ℂ :=
  ↑(spatialOuterBump (d := d) L hL z * (1-spatialInnerBump (d := d) δ hδ z) * (‖z‖^j)⁻¹)

theorem spatialAnnulusKernel_smooth (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ContDiff ℝ ∞ (spatialAnnulusKernel (d := d) δ L hδ hL j) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : spatialAnnulusKernel (d := d) δ L hδ hL j =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [(spatialInnerBump (d := d) δ hδ).eventuallyEq_one] with z hz
      simp [spatialAnnulusKernel, hz]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun z : Space d => (‖z‖^j)⁻¹) z :=
      ((contDiffAt_norm ℝ hz).pow j).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (((spatialOuterBump (d := d) L hL).contDiffAt.mul
        (contDiffAt_const.sub (spatialInnerBump (d := d) δ hδ).contDiffAt)).mul hn)

theorem spatialAnnulusKernel_compact (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : HasCompactSupport (spatialAnnulusKernel (d := d) δ L hδ hL j) := by
  exact (((spatialOuterBump (d := d) L hL).hasCompactSupport.mul_right).mul_right).comp_left
    (map_zero Complex.ofRealCLM)

noncomputable def spatialAnnulusSchwartz (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Space d, ℂ) :=
  (spatialAnnulusKernel_compact δ L hδ hL j).toSchwartzMap
    (spatialAnnulusKernel_smooth δ L hδ hL j)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AllDimensionalSpatialFourierSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact separated spatial factors in every dimension. Fourier inversion is applied on Space d, with an integrable coefficient and endpoint phases of norm one. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
variable {d : ℕ}

noncomputable def spatialFourierCoeff (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Space d, ℂ) := 𝓕 (spatialAnnulusSchwartz (d := d) δ L hδ hL j)

noncomputable def spatialFourierCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ℝ := ∫ ξ : Space d, ‖spatialFourierCoeff (d := d) δ L hδ hL j ξ‖

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CellSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cell restrictions inside original endpoint symbols

An indicator in the spatial variable leaves the restricted transform
unchanged and requires no spatial derivative. It makes all nonstationary
geometry hypotheses conditional on genuinely active point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def cellSymbol {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  if x ∈ Q.carrier then b x w else 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_SpatialSharedShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform independent-angle control removes the spatial Fourier variable

The spatial coefficient pays its squared L1 norm. All exchanges of the
radial and spatial integrations follow from bounded measurable endpoint
families and the finite original shell measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def spatialSharedAmplitude {d : ℕ} (c : Space d → ℂ)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (r : ℝ) : ℂ :=
  ∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,(r,w))*star (V (ξ,(r,w)))))
    ∂sphereMeasure d

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SpatialEndpointFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual endpoint family in the spatial Fourier shell bound

Spatial frequencies are parameters of bounded modulus-one multipliers.
The original endpoint laws and model masses are unchanged.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

noncomputable def spatialEndpointFamily (μ : Measure (Space d)) (M s : ℝ)
    (b : Space d → Sphere d → ℂ) (p : Space d × (ℝ × Sphere d)) : ℂ :=
  endpointTransform μ M (fun x w => spatialFourierPhase s p.1 x*b x w) p.2.1 p.2.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JointStationaryGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mixed bounds for the actual stationary chart

The reflection formula preserves norm even when its direction parameter is
off the sphere. This permits ambient derivatives in that parameter while
the original symbol is evaluated only on sphere points.
-/

namespace Falconer
open Set Metric
open scoped ContDiff RealInnerProductSpace

def jointStationaryCompact (m : ℕ) : Set (Space (m+3) × Space (m+2)) :=
  closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4) ×ˢ
    closedBall (0 : Space (m+2)) 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedInverseFactors
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size-one endpoint factors with the exact total derivative cost

Positive upper sizes are selected before the scale label. Division by
those sizes retains all zero sets and chart bounds; their product costs
only the sum of the original endpoint derivative orders.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def normalizedEndpoint {d : ℕ} (a : ℝ)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  (a⁻¹ : ℝ)*b x w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetDerivativeBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds for individual ambient mask jets

These estimates retain the order of each differentiated mask. Evaluation
on fixed unit vectors is a contraction, so differentiating a mask jet costs
only the corresponding higher derivative of that same mask.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def jetEvaluation {d k : ℕ} (v : Fin k → Space d) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space d) ℝ) →L[ℝ] ℝ where
  toFun L := L v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const v

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outgoing inverse expansion on the prepared patch

The finite inverse amplitudes remove the outgoing coefficient series.
Their fixed patch support removes every incoming coefficient. All errors
have the same total frequency order and the same derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def inverseSphereSum (m J : ℕ) (Λ : ℝ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) : ℂ :=
  ∑ j ∈ Finset.range (J+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*
    sphereOscillation Λ e (fun w => localInverseAmplitude m B j w)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DistanceInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse stationary phase for the original Euclidean displacement

The direction and oscillation parameter are exactly `z/‖z‖` and `r*‖z‖`.
No projected distance is substituted for the original distance.
-/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def displacementDirection {d : ℕ} (z : Space d) (hz : z ≠ 0) : Sphere d :=
  ⟨normalize z,by rw [mem_sphere,dist_zero_right,norm_normalize hz]⟩

noncomputable def inverseDisplacementSum (m J : ℕ) (r : ℝ) (z : Space (m+3))
    (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1), (((r*‖z‖)^(-(j : ℝ)) : ℝ) : ℂ)*
    ∫ w : Sphere (m+3), Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
      localInverseAmplitude m B j w ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FarRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay for spherical stationary coefficients

Scalar compact-support integration by parts gives decay for the stationary
coefficient, with the dimensional gain of the full ambient sphere.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def normalizedStationaryCoefficient (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ((Λ^j)⁻¹:ℝ)*actualStationaryCoefficient m j B e

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SignedStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual stationary signs and their radial scaling

The incoming coefficient is the conjugate coefficient of the antipodal
amplitude. Both signs use the original amplitude derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def signedStationaryCoefficient (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (outgoing : Bool) : ℂ :=
  if outgoing then normalizedStationaryCoefficient m j Λ B e
  else star (normalizedStationaryCoefficient m j Λ (antipodalConjugate B) e)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SignedRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay with both actual stationary signs

The two Boolean indices are the outgoing and incoming terms of the full
sphere expansion. The original amplitude remains the argument in all
four cases; antipodal conjugation is internal to its signed coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def signedRadialCoefficient (m j k : ℕ) (Ψ : ℝ → ℝ)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    (R d₁ d₂ : ℝ) (ε η : Bool) (s : ℝ) : ℂ :=
  (((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
    (signedStationaryCoefficient m j (R*d₁) B e ε*
      signedStationaryCoefficient m k (R*d₂) G f η)*
    PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) s

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SingleStationaryRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One stationary sphere against an unexpanded small displacement

Only the large sphere is expanded. The second displacement remains an
arbitrary scalar projection, bounded by the smaller displacement length.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def singleSignedRadialCoefficient (m j : ℕ) (Ψ : ℝ → ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (Λ : ℝ) (ε : Bool) (s : ℝ) : ℂ :=
  ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*signedStationaryCoefficient m j Λ B e ε *
    PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)/2-(j:ℝ)) s

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_StationaryRadialSum
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite radial expansion of the two full-sphere approximants -/

namespace Falconer
open Set MeasureTheory

noncomputable def stationaryPoleTerm (m j : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (ε : Bool) : ℂ :=
  ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*stationaryPhase (stationarySign ε*Λ)*
    signedStationaryCoefficient m j Λ B e ε

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FarOriginalSupport
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Far-label elimination under a positive original-law bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

def farDisplacementRegion (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  {z | max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ≤
      2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) ∧
    8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarRegionSplit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two noncomparable pieces and finite comparable bands -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

def leftNoncomparableFar (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  farDisplacementRegion d a h ∩ {z | 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2}

def rightNoncomparableFar (d a h : ℕ) :
    Set ((Space d × Space d) × (Space d × Space d)) :=
  farDisplacementRegion d a h ∩ {z | 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def jetStateBound {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a))*
    (((descriptorJetBound (n+2) K)^K*A⁻¹*μ.real univ/M)^2*
      ((descriptorJetBound (n+2) K)^K*A⁻¹*ν.real univ/P)^2*
      (sphereMeasure (n+2)).real univ^2)*
    (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DyadicGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Retained graph on the actual dyadic cells

The grid degree estimate is transported to arbitrary finite collections
of equal-depth descendants. Their original cube centers define every
test. The final Schur bound can therefore be applied directly to the
endpoint transforms restricted to those cells.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def retainedDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  ‖perpendicularPart w₁ ((Q₁.descendant col.1).center - (Q₁.descendant row.1).center)‖ ≤ τ ∧
  ‖perpendicularPart w₂ ((Q₂.descendant col.2).center - (Q₂.descendant row.2).center)‖ ≤ τ ∧
  |inner ℝ w₁ ((Q₁.descendant col.1).center - (Q₁.descendant row.1).center) +
    inner ℝ w₂ ((Q₂.descendant col.2).center - (Q₂.descendant row.2).center)| ≤ τ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_EligibleDyadicGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph of eligible original cell--cap incidences

Support of an endpoint symbol in a literal parallel test supplies the
witnesses used by the degree estimate. Eligibility only filters the finite
cell list; no angular support is cut by a pointwise edge decision.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

def eligibleDyadicEdge {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (A B : Finset (List (Fin d → Bool))) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) : Prop :=
  row ∈ A ×ˢ B ∧ col ∈ A ×ˢ B ∧ retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Profile normalization of the retained graph contribution

The sum is over the actual occupied descendants and retains both endpoint
symbols. The degree is the integer degree used in the graph energy estimate.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

noncomputable def twoProfileGraphContribution (Q₁ Q₂ : DyadicCube d)
    (ρ₁ ρ₂ : Measure (Space d)) (m₁ m₂ : ℝ → ℝ) (N a p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (b c : Space d → Sphere d → ℂ) (degree : ℕ) : ℝ :=
  ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
    ((2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * degree *
      ∑ row ∈ Q₁.occupiedPaths ρ₁ (p-a) ×ˢ Q₂.occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary inverse with the original distance weight

After multiplication by `‖z‖^(-(d-1)/2)`, the only spatial powers in
the finite expansion have integer exponents. These are exactly the
powers handled by the spatial Fourier separation.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

noncomputable def weightedInverseDisplacementSum (m J : ℕ) (r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1),
    ((r^(((m+2 : ℕ) : ℝ)/2)*(r^j)⁻¹*(‖z‖^j)⁻¹ : ℝ) : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
          localInverseAmplitude m B j w ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScaledWeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse expansion at the actual cell scale

Only the distance weight is rescaled. The oscillatory phase still uses the
original displacement and original radial frequency. The integer inverse
powers therefore match the spatial Fourier separation at the cell scale.
-/

namespace Falconer
open NormedSpace
open scoped ContDiff

noncomputable def scaledWeightedInverseSum (m J : ℕ) (s r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J+1),
    (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹*((‖z‖/s)^j)⁻¹ : ℝ) : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space (m+3)) z : ℂ))*
          localInverseAmplitude m B j w ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScaledInverseRemainder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse remainder under the original pair measure

The scaled distance weight and the original endpoint laws are retained.
The estimate integrates the pointwise stationary remainder; no change of
measure or unproved Fourier estimate is used.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def scaledDistanceKernel (m : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (((dist z.1 z.2/s)^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
    Complex.exp (Complex.I*((r*dist z.1 z.2 : ℝ) : ℂ))*B z.1 z.2 (NormedSpace.normalize (z.1-z.2))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorScaledKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked distance law as a cell-scaled stationary target

The unit profile is evaluated at depth divided by N in the descriptor
amplitude. Both masks and the original pair law remain in this identity.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def descriptorPairAmplitude {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (x y w : Space d) : ℂ :=
  (descriptorAmbientProduct Q ρ f N σ J i B S x w : ℂ)*
    (descriptorAmbientProduct Q ρ f N σ J i B S y w : ℂ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BaseJetAmplitude
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked amplitude is the zero-jet root state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

noncomputable def descriptorRootSymbol (n : ℕ) (F : Finset PolicyDescriptor) (L : ℕ) :
    DescriptorJetSymbol n 0 L F 1 :=
  DescriptorJetSymbol.base F 0 L 1 (by norm_num) (fun _ => 1) measurable_const (by simp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ComplexMaskJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized jets of the complex angular multiplier

The multiplier is treated as an additional label. Its new derivative
order is charged to the inverse, and its available smoothness budget is
reduced by exactly that order.
-/

namespace Falconer.MaskJetIndex
open Set
open scoped ContDiff
variable {d : ℕ}

noncomputable def jetEvaluation (j : MaskJetIndex d) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin j.order => Space d) ℂ) →L[ℝ] ℂ where
  toFun L := L j.vectors
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const j.vectors

end Falconer.MaskJetIndex

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting the inverse amplitude in the angular variable

The endpoint laws and their dyadic cells are not changed. Only the sphere
integration variable and the directional derivatives of its amplitude rotate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def rotatedInverseAmplitude (m : ℕ) (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3))
    (B : Space (m+3) → ℂ) (j : ℕ) (w : Space (m+3)) : ℂ :=
  localInverseAmplitude m (B ∘ T.symm) j (T w)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_RotatedInverseSymbols
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform original-mask symbols for a rotated inverse patch -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

abbrev RootInverseIndex (m j : ℕ) (F : Finset PolicyDescriptor) :=
  ((MaskJetExpansion.product : MaskJetExpansion ({b // b ∈ F} ⊕ {b // b ∈ F})
    (m+3) (Space (m+3))).inverse m j).index

noncomputable def rootInverseTerm (m j : ℕ) (F : Finset PolicyDescriptor)
    (a : RootInverseIndex m j F) :=
  (((MaskJetExpansion.product : MaskJetExpansion ({b // b ∈ F} ⊕ {b // b ∈ F})
    (m+3) (Space (m+3))).inverse m j).term a)

noncomputable def rootInverseLeftJets (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then ((rootInverseTerm m j F a).jet (.inl ⟨b,hb⟩)).mapIsometry T.symm
    else MaskJetIndex.zero (m+3)

noncomputable def rootInverseRightJets (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then ((rootInverseTerm m j F a).jet (.inr ⟨b,hb⟩)).mapIsometry T.symm
    else MaskJetIndex.zero (m+3)

structure RotatedRootSymbols (m j L : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (A : ℝ) where
  left : RootInverseIndex m j F → DescriptorJetSymbol (m+1) (2*j) L F 1
  right : RootInverseIndex m j F → DescriptorJetSymbol (m+1) (2*j) L F 1
  left_jet : ∀ a, (left a).jet = rootInverseLeftJets m j F T a
  right_jet : ∀ a, (right a).jet = rootInverseRightJets m j F T a
  left_angular : ∀ a, (left a).angular = normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
  right_angular : ∀ a, (right a).angular = fun _ => 1
  left_spatial : ∀ a, (left a).spatial = fun _ => 1
  right_spatial : ∀ a, (right a).spatial = fun _ => 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedInverseExpansion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rotated inverse on the original two endpoint laws -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

noncomputable def rootInverseRadii (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ) :
    {b // b ∈ F} ⊕ {b // b ∈ F} → ℝ :=
  Sum.elim (fun b => descriptorMaskRadius N σ b) (fun b => descriptorMaskRadius N σ b)

noncomputable def rootInverseWeight (m j : ℕ) (F : Finset PolicyDescriptor) (N : ℕ) (σ : ℝ)
    (a : RootInverseIndex m j F) : ℝ :=
  ∏ b, (rootInverseRadii F N σ b)⁻¹^((rootInverseTerm m j F a).jet b).order

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SeededSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint separation after a new inverse acts on existing jets

Both endpoint families keep all their original labels. Extracted scalar
weights charge only the newly added derivative orders, including the
complex angular multiplier when it is included as an extra label.
-/

namespace Falconer
open scoped ContDiff

variable {ι τ : Type} {X Y : Type*} [Fintype ι] [Fintype τ]
  [DecidableEq ι] [DecidableEq τ]

noncomputable abbrev seededPairJets (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3)) :
    MaskJetExpansion (ι ⊕ τ) (m+3) (Space (m+3)) :=
  (MaskJetExpansion.seed k).inverse m j

noncomputable def seededJetSeparation (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y)) :
    SmoothSeparation X Y (Space (m+3)) where
  index := (seededPairJets m j k).index
  finite := inferInstance
  left := fun a x z => ((seededPairJets m j k).term a).coefficient z *
    ∏ i, (((seededPairJets m j k).term a).jet (.inl i)).scaledValue (r (.inl i)) (B i x) z
  right := fun a y z =>
    ∏ i, (((seededPairJets m j k).term a).jet (.inr i)).scaledValue (r (.inr i)) (C i y) z
  left_smooth := fun a x => ((seededPairJets m j k).term a).coefficient_smooth.mul
    (contDiff_prod (fun i _ => MaskJetIndex.scaledValue_contDiff _ _ _ (hB i x)))
  right_smooth := fun _a y =>
    contDiff_prod (fun i _ => MaskJetIndex.scaledValue_contDiff _ _ _ (hC i y))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetValues
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact values of the descriptor inverse factors

The additional label is the actual smooth angular multiplier. The other
labels are the original ambient descriptor masks, each occurring once.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

noncomputable def descriptorInverseSeparation {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))) :
    SmoothSeparation (Space (m+3)) (Space (m+3)) (Space (m+3)) :=
  seededJetSeparation m j (descriptorInverseSeed f g)
    (Sum.elim (f.seedRadius N σ) (g.seedRadius N σ))
    (f.seedMask Q ρ profile N σ J i S) (g.seedMask Q ρ profile N σ J i S)
    (f.seedMask_smooth Q ρ profile N σ J i S) (g.seedMask_smooth Q ρ profile N σ J i S)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ScaledInverseIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the complete cell-scaled inverse

Every term uses the original endpoint measures. The distance weight is
separated at the cell scale, and the radial coefficient is kept explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def scaledInverseTerm (m j : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
    ∫ w : Sphere (m+3),
      Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
        localInverseAmplitude m (B z.1 z.2) j w ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common recursive budget for the complete finite inverse

Both descriptor lists and original endpoint laws stay fixed. The frequency
coefficient absorbs the added jet orders before the finite sum is bounded.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

noncomputable def descriptorInverseShellCost {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F D)
    (g : DescriptorJetSymbol (m+1) K L G D)
    (k : ℕ) (A B : Fin (k+1) → ℝ) (Af Ag U δ W : ℝ)
    (hδ : 0 < δ) (hW : 0 < W) : ℝ :=
  (Fintype.card (DescriptorInverseFamilyIndex f g k) : ℝ)*
    ∑ z : DescriptorInverseFamilyIndex f g k,
      ((|U*A z.1| *|U*B z.1| *|Af⁻¹| *|Ag⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
        (spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedWeightedInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cell-scaled inverse in a fixed orthogonal angular frame

Only the angular variable changes. All spatial displacements, distance powers,
frequencies and endpoint laws in the separated formula are the original ones.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ContDiff

noncomputable def rotatedScaledWeightedInverseSum (m J : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (z : Space (m+3)) (B : Space (m+3) → ℂ) : ℂ :=
  scaledWeightedInverseSum m J s r (T z) (B ∘ T.symm)

noncomputable def rotatedScaledInverseTerm (m j : ℕ)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
    ∫ w : Sphere (m+3),
      Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
        rotatedInverseAmplitude m T (B z.1 z.2) j w ∂sphereMeasure (m+3)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RotatedInverseShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full rotated inverse bounded by the original descriptor state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

abbrev RootInverseFamilyIndex (m k : ℕ) (F : Finset PolicyDescriptor) :=
  (j : Fin (k+1)) × RootInverseIndex m j.val F

noncomputable def rotatedInverseShellCost (m k : ℕ) (F : Finset PolicyDescriptor)
    (A : Fin (k+1) → ℝ) (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) : ℝ :=
  (Fintype.card (RootInverseFamilyIndex m k F) : ℝ)*
    ∑ z : RootInverseFamilyIndex m k F,
      ((|U*A z.1| *|U|)*4^(((m+2:ℕ):ℝ)/2))^2*
        (spatialFourierCost (d := m+3) δ W hδ hW z.1.val)^2

noncomputable def rotatedInverseNormalizedSum {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) (M P a v r : ℝ) : ℂ :=
  ∑ z : RootInverseFamilyIndex m k F,
    ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
      (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
      ((rootInverseWeight m z.1.val F N σ z.2*(U*A z.1)*U : ℝ) : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW z.1.val)
          (spatialEndpointFamily μ M s (((H z.1).left z.2).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star (((H z.1).right z.2).value Q ρ profile N σ J i S U x w))) r


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorEnvelope
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual descriptor tests used by the angular envelope

These are finite intersections of the original endpoint tests. Passing to
retained lists only weakens these support conditions. No deletion of an
angular factor or analytic estimate is inferred from this set inclusion.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDescriptorList remainingPolicyDescriptors)

variable {d : ℕ}

def descriptorListGood (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    Set (Space d × Sphere d) :=
  {z | ∀ b ∈ B, z ∈ descriptorEndpointGood Q ρ m N σ J i b}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ReachedStateRecursion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

@[simp] theorem extend_last_state (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).state (n+1) = u := ite_eq_right (by omega)

@[simp] theorem extend_last_label (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).label n = l := ite_eq_right (Nat.lt_irrefl n)

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRootGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer graph coefficient combined with the two recursive roots -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)


noncomputable def outerRootLoss (m : ℕ) (lam σ κ η : ℝ) : ℝ :=
  500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) lam σ+σ)/κ+η

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OuterAngularBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform two-profile angular bound from the actual recursive estimates -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def outerEntryExponent {m : ℕ} (P Q : PolicyJetData m) (c : ℕ) (κ : ℝ) : ℝ :=
  min (PlanarFalconer.height P.policy 0 c) (PlanarFalconer.height Q.policy 0 c)-
    (PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
      PlanarFalconer.potential Q.policy c Q.t (10*sourcePolicyBlock Q.N κ))/2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ValidDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial finite family containing every descriptor used at a scale -/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

noncomputable def validDescriptors (N : ℕ) : Finset PolicyDescriptor :=
  (((Finset.range (N+1) ×ˢ Finset.range (N+1)).image (fun p => PolicyDescriptor.parallel p.1 p.2)) ∪
    ((Finset.range (N+1) ×ˢ Finset.range (N+1)).image (fun p => PolicyDescriptor.projection p.1 p.2))).filter
      (descriptorValid N)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTestBad
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair failure of the level-zero tests, before smoothing -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

noncomputable def descriptorTestBad (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (b : PolicyDescriptor) (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  G ∩ {z | (z.1,normalizeToSphere w₀ (z.2-z.1)) ∉ descriptorEndpointGood Q ρ profile N σ J 0 b}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllTestsRestoration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One exceptional set restores every policy descriptor at the scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

noncomputable def allDescriptorTestBad (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  ⋃ b ∈ validDescriptors N, descriptorTestBad w₀ Q ρ profile N σ J b G

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SamplingGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite planar query balls for simultaneous iid estimates

Rounding one point of a ball to the spatial mesh and rounding its radius
up to an integer mesh multiple gives a query ball with radius at most
eight times the original radius. The number of queries is polynomial in
the reciprocal mesh. This is the finite-grid step in `ang:sample-caps`.
-/

namespace Falconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def planarMesh (δ : ℝ) (z : Fin 2 → ℤ) : Space 2 :=
  WithLp.toLp 2 (fun i => δ * (z i : ℝ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSampling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original labels, slope coordinates and prescribed strip covers

These adapters connect the two uniform sampling stages to the exact finite
Furstenberg obstruction. Every strip list remains indexed by its original
direction label, including when slope coordinates coincide.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def slopePoint (m : ℝ) : Space 2 := WithLp.toLp 2 ![m,0]

@[simp] theorem slopePoint_zero (m : ℝ) : slopePoint m 0 = m := rfl
@[simp] theorem slopePoint_one (m : ℝ) : slopePoint m 1 = 0 := rfl

noncomputable def stripLineCandidates (δ m : ℝ) (A : Finset ℝ) (L : ℕ) :
    Finset (Space 2) := A.biUnion (fun a => roundedStripCandidates δ m a L)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMultiband
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian multi-vector bands with their exact coordinate determinant -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

noncomputable def bandCoordinateMap (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) : Space j →L[ℝ] Space j :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin j => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (innerSL ℝ (w i)).comp
      (V.subtypeL.comp b.symm.toContinuousLinearEquiv.toContinuousLinearMap)))

@[simp] theorem bandCoordinateMap_apply (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) (x : Space j) (i : Fin j) :
    bandCoordinateMap w V b x i = inner ℝ (w i) (b.symm x : Space d) := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_AnchoredTriplePotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Gaussian bad-triple weight is integrable on every retained anchor -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartTripleWeight (h : ℕ) (r : ℝ) (p q z : Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
    gaussianRows (n+1) h {A | ∀ i,
      |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart z : Space (n+1)) (A i)| ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartTripleAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Gaussian averaging on triples of the original affine chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

def chartTripleBand (A : Fin h → Space (n+1)) (r : ℝ) :
    Set (Space n × Space n × Space n) :=
  (gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
    ((gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
      (gnomonicChart ⁻¹' gaussianDirectionBand A r))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPairSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating retained original pairs with their actual ball-mass cost -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def separatedRadialPairs (G : Set (Space d × Space d)) (r : ℝ) :
    Set (Space d × Space d) := {p | p ∈ G ∧ r ≤ dist p.1 p.2}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_BadTripleRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable bad-triple relation on retained original labels -/

namespace Falconer
open Set MeasureTheory
variable {n : ℕ}

noncomputable def chartTripleVolume (w : Space n × Space n × Space n) : ℝ :=
  Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
    (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1)))

def badChartTriples (G : Set (Space n × Space n)) (W : ℝ) :
    Set (Space n × Space n × Space n) :=
  {w | ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
    (w.1,w.2.1) ∈ G ∧ (w.1,w.2.2) ∈ G ∧ chartTripleVolume w < W}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredPairFailure
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original pair deletions in three-label slice incidence -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

def firstAnchoredPair (E : Set (Space n × Space n)) :
    Set (Space n × Space n × Space n) := {w | (w.1,w.2.1) ∈ E}

def secondAnchoredPair (E : Set (Space n × Space n)) :
    Set (Space n × Space n × Space n) := {w | (w.1,w.2.2) ∈ E}

def endpointExceptionalTriples (G : Set (Space n × Space n)) (W : ℝ) :
    Set (Space n × Space n × Space n) :=
  badChartTriples G W ∪ (firstAnchoredPair Gᶜ ∪ secondAnchoredPair Gᶜ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def tubeDegree (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : ℝ :=
  ∑ x ∈ P, if l ∈ T x then 1 else 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The row geometry in Orponen--Shmerkin, Appendix A.7, expressed in the
original line chart. A line is incident to only a bounded number of points
on a separated row. Its parameter projection stays close to that row point. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

noncomputable def lineParameterProjection (y : ℝ) (l : Space 2) : ℝ := y*l 0+l 1
noncomputable def rowPoint (y x : ℝ) : Space 2 := WithLp.toLp 2 ![y,x]

@[simp] theorem rowPoint_zero (y x : ℝ) : rowPoint y x 0 = y := rfl
@[simp] theorem rowPoint_one (y x : ℝ) : rowPoint y x 1 = x := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scale-delta covering cells for parameter projections. For a
family through a row, at most seven cells per row point are needed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def projectionCells (δ y : ℝ) (T : Finset (Space 2)) : Finset ℤ :=
  T.image fun l => ⌊lineParameterProjection y l/δ⌋

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFourPaths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-edge paths and their sum labels. Injectivity of the labels is the
counting step converting dense neighborhoods into small difference sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def integerFourPaths (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) : Finset IntegerPath :=
  B.sigma fun v => integerCommonNeighbors A e b v ×ˢ integerCommonNeighbors A e c v

def integerPathSums (b c : ℤ) (p : IntegerPath) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((p.2.1+b,p.2.1+p.1),(p.2.2+p.1,p.2.2+c))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarProductBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fine-scale ball bounds for a Cartesian product of separated scalar
sets, with its actual Euclidean embedding. -/
namespace Falconer

noncomputable def scalarProductPoints (X Y : Finset ℝ) : Finset (Space 2) :=
  (X ×ˢ Y).image fun p => rowPoint p.1 p.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCountingPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def planarCountingMeasure (P : Finset (Space 2)) : Measure (Space 2) :=
  ∑ x ∈ P, Measure.dirac x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteProjectionPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite projected-energy average used for the good projections in
Orponen--Shmerkin, Appendix A.4. The critical directional loss is linear in
the dyadic depth; the planar point potential is strictly subcritical. -/
namespace Falconer
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def planarProjectionEnergy (N : ℕ) (s c : ℝ) (P : Finset (Space 2)) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CoarsePlanarRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common coarse grid inside the original chart and the resulting
point-line incidence error. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def coarsePlanarRound (Δ : ℝ) (p : Space 2) : Space 2 :=
  rowPoint (lineGridRound Δ (p 0)) (lineGridRound Δ (p 1))

@[simp] theorem coarsePlanarRound_zero (Δ : ℝ) (p : Space 2) :
    coarsePlanarRound Δ p 0 = lineGridRound Δ (p 0) := rfl

@[simp] theorem coarsePlanarRound_one (Δ : ℝ) (p : Space 2) :
    coarsePlanarRound Δ p 1 = lineGridRound Δ (p 1) := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common-tube kernel valid at all point separations, including the diagonal. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

noncomputable def truncatedPlanarDistance (δ : ℝ) (x y : Space 2) : ℝ :=
  max δ (min 1 (dist x y))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ConeIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate and dilation integration for the gnomonic cone formula -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def euclideanTail {n : ℕ} (z : Space (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.succ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ConeSections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fiber volumes of the Euclidean cone over a gnomonic chart -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal Pointwise

noncomputable def euclideanCons {n : ℕ} (r : ℝ) (y : Space n) : Space (n+1) :=
  WithLp.toLp 2 (Fin.cons r (WithLp.ofLp y))

@[simp] theorem euclideanCons_zero {n : ℕ} (r : ℝ) (y : Space n) : euclideanCons r y 0 = r := rfl
@[simp] theorem euclideanCons_succ {n : ℕ} (r : ℝ) (y : Space n) (i : Fin n) :
    euclideanCons r y i.succ = y i := by simp [euclideanCons]

@[simp] theorem euclideanCons_self {n : ℕ} (z : Space (n+1)) :
    euclideanCons (z 0) (euclideanTail z) = z := by
  apply PiLp.ext
  intro i
  refine Fin.cases rfl (fun _ => rfl) i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePencilWeights
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Push original fine incidences to coarse line parameters, preserving their
multiplicities and the weighted ball bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def coarsePencilWeight (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2) (a : Space 2) : ℕ :=
  ∑ x ∈ P, ((T x).filter fun l => q l = a).card

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilFiberEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Average critical energy of the point fibers of a tube family.
This is the finite form of Orponen--Shmerkin, Appendix A, equation (A.18). -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def pencilFiberEnergy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : ℝ :=
  ∑ x ∈ P, ∑ y ∈ P, if l ∈ T x ∧ l ∈ T y then
    (1/max (dist x y) (1/(2:ℝ)^N))^τ else 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteEnergyRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-energy tube fiber contains a large regular set of original cells. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def pencilFiber (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : Finset (Space 2) :=
  P.filter fun x => l ∈ T x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinePacketCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original fine tubes have bounded multiplicity among cell-dependent
coarse packets. Thus freezing packet sizes preserves the needed total bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def fineCoarsePacket (Δ : ℝ) (C : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (a : Space 2) : Finset (Space 2) :=
  (C.biUnion T).filter fun l =>
    ∃ c ∈ C, l ∈ T c ∧ roundedIncidentLine Δ c (l 0) = a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteAnchorLabels
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

noncomputable def finiteAnchorLabels (G J : Finset (Space d)) : Finset {a // a ∈ G} := by
  classical
  exact J.subtype (fun a => a ∈ G)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Undo the harmless quarter scaling used in the projection sampler.
These are actual common-row points, with witnesses in the original packet. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def rowUnquarter (y a : ℝ) (p : Space 2) : Space 2 :=
  rowPoint y (a+4*p 1)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The robust projection theorem in the original coordinates of one
coarse cell. No projected point or fine-scale witness is replaced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def localPacketPoint (Δ y a : ℝ) (p : Space 2) : Space 2 :=
  rowPoint ((p 0-y)/Δ) ((p 1-a)/Δ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalCellLines
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact line map for an isotropically rescaled point cell. It preserves
the original line witnesses and their cardinalities; no direction thinning
is needed for the elementary local incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def localCellLine (Δ y a : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0) ((l 0*y+l 1-a)/Δ)

noncomputable def unlocalCellLine (Δ y a : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0) (Δ*l 1-l 0*y+a)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SupportPairFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restrict pair filters to the original supports without losing mass -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def supportPair (μ ν : ProbabilityMeasure (Space d)) : Set (Space d × Space d) :=
  (μ : Measure (Space d)).support ×ˢ (ν : Measure (Space d)).support

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OriginalPairFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lift the auxiliary filters to the original pair law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

noncomputable def liftedPairFilter (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Γ : ℕ → Set (Space k × Space k))
    (N : ℕ) : Set (Space d × Space d) :=
  supportPair μ ν ∩ Prod.map P P ⁻¹' Γ N

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketCentering
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Center a genuine coarse line packet by an affine shear. Translation in
line-parameter space preserves all pencil counts and ball bounds exactly;
the point-line residual is unchanged. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def packetCenterPoint (c b : ℝ) (p : Space 2) : Space 2 :=
  rowPoint (p 0) (p 1+c*p 0-b)

noncomputable def packetCenterLine (c b : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0+c) (l 1-b)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PairExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-sided exceptional sets measured on the original pair -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

def pairExceptional (A B : Set (Space d)) (D E : Set (Space d × Space d)) :
    Set (Space d × Space d) :=
  ((Aᶜ ×ˢ univ) ∪ (univ ×ˢ Bᶜ)) ∪ D ∪ Prod.swap ⁻¹' E

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates supplied by two distinct planar projection directions.
These are the actual coordinates used by the dense scalar graph reduction. -/
namespace Falconer

noncomputable def planarProjectionCoordinates (a b : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (lineParameterProjection a l) (lineParameterProjection b l)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCoordinateBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse coordinates and ball-count transport for the two
separated projections selected from the original planar configuration. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarProjectionInverse (a b : ℝ) (z : Space 2) : Space 2 :=
  rowPoint ((z 1-z 0)/(b-a)) ((b*z 0-a*z 1)/(b-a))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarQuarter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction puts the actual two projection coordinates inside
one bounded square without changing their finite combinatorics. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarQuarter (p : Space 2) : Space 2 := (1/4:ℝ) • p

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarChartRepair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing bounded representatives of almost-everywhere planar chart maps -/

namespace Falconer
open Set MeasureTheory

noncomputable def boundedPlanarPoint (x : Space 2) : Space 2 :=
  if ‖x‖ ≤ 1/4 then x else 0

noncomputable def chartedPlanarDirection (w : Space 2) : Space 2 :=
  if ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 then w
  else EuclideanSpace.basisFun (Fin 2) ℝ 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSelectedGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the published planar consequence to a selected original-label slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal Topology
variable {d h : ℕ} {κ : Type*}

def selectedActiveRelation (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    (R T : ℝ) : Set (Space d × Sphere d) :=
  {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
    (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSquash
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed anisotropic change of coordinates narrows every bounded slope.
The same map acts on points and line parameters; incidence widths contract
by four and both maps have inverse Lipschitz constant sixteen. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarSquash (p : Space 2) : Space 2 := rowPoint (p 0/4) (p 1/16)
noncomputable def planarUnsquash (p : Space 2) : Space 2 := rowPoint (4*p 0) (16*p 1)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PreparedPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original starting pairs with the complete finite-filter interface

The pair and its Frostman gap are fixed before the coarse loss is chosen.
All cap bounds and partitions concern the original marginal laws.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure PreparedOriginalPair {d : ℕ} (E : Set (Space d)) (ε : ℝ) where
  auxiliaryDimension : ℕ
  exponent : ℝ
  exponent_gt : (d:ℝ)/2 < exponent
  base : ProbabilityMeasure (Space d)
  pair : ProjectedStartingPair base auxiliaryDimension exponent ε
  left_subset : (pair.left : Measure (Space d)).support ⊆ E
  right_subset : (pair.right : Measure (Space d)).support ⊆ E
  filters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((pair.left : Measure (Space d)).prod (pair.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ pair.relation) ∧
      (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)))) ∧
      CapAvailable pair.left pair.right Γ ((d:ℝ)/2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CubeBallPacking
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A ball meets a bounded number of dyadic cubes of comparable side -/
namespace Falconer
open Set Metric

noncomputable def cubeBallHits {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (x : Space d) (r : ℝ) : Finset (List (Fin d → Bool)) := by
  classical
  exact (cubePaths d n).filter fun p => ((Q.descendant p).carrier ∩ ball x r).Nonempty

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PointBallCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer finite prefix bounds to geometric closed-ball counts. The
factor 7^d is the existing bounded overlap of dyadic cubes. -/
namespace Falconer
open Set Metric Regularization

noncomputable def pointPrefixFiber {d : ℕ} (P : Finset (Space d))
    (l : Space d → CellPath d) (n : ℕ) (q : CellPath d) : Finset (Space d) := by
  classical
  exact P.filter fun x => (l x).take n = q

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RetainedProfileBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Profile estimates on the actual endpoint centers after a retained class
is regularized again. The original profile remains the reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

noncomputable def blockEndpointSet (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) : Finset (Space 2) :=
  ((prefixChildren C a b p₀).image (fun r => (Q.descendant r).center)).image
    (localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuarterEndpointMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed quarter chart closes under the actual local cell map. Its
contraction does not accumulate with the number of selected intervals. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

noncomputable def quarterEndpointPoint (Q : DyadicCube 2) (a : ℕ)
    (p₀ r : CellPath 2) : Space 2 :=
  localPacketPoint (4/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
    (Q.descendant r).center

noncomputable def quarterEndpointSet (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) : Finset (Space 2) :=
  (prefixChildren C a b p₀).image (quarterEndpointPoint Q a p₀)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_TwoProfileInverseShell
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite two-profile inverse family controlled by actual angular energies -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

noncomputable def twoProfileInverseNormalizedSum {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (s : ℝ) (μ ν : Measure (Space (m+3))) (M P a v r : ℝ) : ℂ :=
  ∑ z : DescriptorInverseFamilyIndex f g k,
    ((((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^z.1.val)⁻¹ /
      (2:ℝ)^((v-a)*(((m+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
      ((T z.1).coefficient N σ Af Ag U U z.2 : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW z.1.val)
          (spatialEndpointFamily μ M s (((T z.1).left z.2).value Q₁ ρ₁ profile₁ N σ J i S₁ U))
          (spatialEndpointFamily ν P s
            (fun x w => star (((T z.1).right z.2).value Q₂ ρ₂ profile₂ N σ J i S₂ U x w))) r

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRoot
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual regularized classes as initial policy states -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor sourcePolicyBlock sourceSmoothingLevels)

noncomputable def descriptorNets (d N : ℕ) (σ : ℝ) : PolicyDescriptor → Finset (Sphere d) :=
  fun b => Classical.choose (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))

 theorem descriptorNets_separated (d N : ℕ) (σ : ℝ) (b : PolicyDescriptor) :
    ∀ w ∈ descriptorNets d N σ b, ∀ z ∈ descriptorNets d N σ b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z :=
  fun w hw z hz hne =>
    ((Classical.choose_spec (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))).1 w hw z hz hne).le

noncomputable def regularRoot {m N : ℕ} (Q : DyadicCube (m+3)) (hQ : Q.side = 1)
    (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ) {s lam σ κ Z : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile)
    (hN : 0 < N) (hκ : 0 < κ) (hZ : 0 < Z) : PolicyJetData m where
  Q := Q
  unit := hQ
  ρ := ρ
  profile := profile
  N := N
  s := s
  lam := lam
  regular := hreg
  N_pos := hN
  σ := σ
  J := sourceSmoothingLevels σ κ
  i := 0
  q := sourcePolicyBlock N κ
  q_pos := PlanarFalconer.sourcePolicyBlock_pos hN hκ
  policy := profileExcess (d := m+3) profile N
  a₀ := 0
  t₀ := N
  a := 0
  t := N
  base_left := le_rfl
  base_right := le_rfl
  base_N := le_rfl
  X := []
  Y := []
  X_length := rfl
  Y_length := rfl
  masks := descriptorNets (m+3) N σ
  separated := fun b _ => descriptorNets_separated (m+3) N σ b
  Z := Z
  Z_pos := hZ

noncomputable def regularOuterList {d : ℕ} (profile : ℝ → ℝ) (N : ℕ) (κ : ℝ) (c : ℕ) :
    Finset PolicyDescriptor :=
  insert (.parallel 0 c) (PlanarFalconer.remainingPolicyDescriptors
    (profileExcess (d := d) profile N) N (sourcePolicyBlock N κ) 0 N 0)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularOuterMask
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer mask, with both oriented restoration identities -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularOuterMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) : Space d → Space d → ℝ :=
  descriptorAmbientProduct Q ρ (fun u => profile (u/N)) N σ
    (PlanarFalconer.sourceSmoothingLevels σ κ) 0
    (regularOuterList (d := d) profile N κ c) (descriptorNets d N σ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRefinementData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite data retained by the regular-set scale argument. Every point
and fine line is a member of the original configuration. -/
namespace Falconer
open scoped BigOperators

structure RegularRefinementData (n : ℕ) (s t D : ℝ)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) where
  cells : Finset (Space 2)
  pencils : Space 2 → Finset (Space 2)
  points : Space 2 → Finset (Space 2)
  fine : Space 2 → Finset (Space 2)
  packets : Space 2 → Finset (Space 2)
  width : ℝ
  level : ℕ
  width_pos : 0 < width
  cells_nonempty : cells.Nonempty
  cells_chart : InBoundedLineChart cells
  cells_regular : NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t D cells
  pencil_data : ∀ c ∈ cells, width/D ≤ ((pencils c).card:ℝ) ∧
    ((pencils c).card:ℝ) ≤ D*width ∧ InBoundedLineChart (pencils c) ∧
    FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (pencils c) ∧
    NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s D (pencils c) ∧
    ∀ l ∈ pencils c, TubeIncident (1/(2:ℝ)^(n+3)) c l
  point_data : ∀ c ∈ cells, points c ⊆ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c) ∧
    (points c).Nonempty ∧
    (∀ p ∈ points c, |p 0-c 0| ≤ (1/(2:ℝ)^n)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^n)/4) ∧
    NormalizedFiniteBallBound (1/(2:ℝ)^n) t D
      ((points c).image (localPacketPoint (1/(2:ℝ)^n) (c 0) (c 1)))
  point_mass : (P.card:ℝ) ≤ D*((cells.biUnion points).card:ℝ)
  fine_data : ∀ c ∈ cells, ∀ p ∈ points c, fine p ⊆ V p ∧
    1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((fine p).card:ℝ) ∧
    ((fine p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
    NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s D (fine p)
  packet_cover : ∀ c ∈ cells, ∀ p ∈ points c, ∀ l ∈ fine p, ∃ a ∈ pencils c, l ∈ packets a
  packet_sum : (∑ a ∈ cells.biUnion pencils, ((packets a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ)
  packet_band : ∀ a ∈ cells.biUnion pencils, 2^level ≤ (packets a).card ∧ (packets a).card < 2^(level+1)
  coarse_cover : ((((cells.biUnion points).biUnion fine).image
    (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ 13*((cells.biUnion pencils).card:ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationTestBad
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the actual class test failures on the original product law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularizationTestBad (w₀ : Sphere d) (Q : DyadicCube d)
    (μ : Measure (Space d)) (N B : ℕ) (t : ℝ≥0∞) (σ : ℝ) (J : ℕ)
    (p : List ℕ → CellPath d) (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  ⋃ T ∈ regularizationIndex Q μ N B t,
    (regularizationSet Q μ N B T ×ˢ univ) ∩
      allDescriptorTestBad w₀ Q (sourceClass Q μ N B (p T))
        (fun u => sourceUnitProfile Q μ N B (p T) (u/N)) N σ J G

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FilteredEndpointDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact masked distance decomposition over a Borel product filter -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def filteredEndpointDistance (μ ν : Measure (Space d))
    (Γ : Set (Space d × Space d)) (B C : Space d → Space d → ℝ) : Measure ℝ :=
  (((μ.prod ν).restrict Γ).withDensity (fun z => ENNReal.ofReal (endpointDistanceWeight 1 B C z))).map
    (fun z => dist z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PartitionEndpointDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact distance law for class-dependent endpoint masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

noncomputable def endpointPairMask (B C : Space d → Space d → ℝ)
    (z : Space d × Space d) : ℝ :=
  B z.1 (NormedSpace.normalize (z.1-z.2)) * C z.2 (NormedSpace.normalize (z.1-z.2))

noncomputable def partitionEndpointDistance (μ ν : Measure (Space d))
    (Γ : Set (Space d × Space d)) (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ) : Measure ℝ :=
  (((μ.prod ν).restrict Γ).withDensity (fun z => ENNReal.ofReal
    ((dist z.1 z.2)^(-(((d:ℝ)-1)/2)) *
      finitePartitionMask F (fun i => S i ×ˢ T i) (fun i => endpointPairMask (B i) (C i)) z))).map
        (fun z => dist z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProductPartitionMask
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable mask on a pair of finite disjoint spatial partitions -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι κ : Type*}

noncomputable def productPartitionMask (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ) : Space d × Space d → ℝ :=
  finitePartitionMask (F.product G) (fun i => S i.1 ×ˢ T i.2)
    (fun i => endpointPairMask (B i) (C i))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationPairMask
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoration of the actual two-class outer mask on the original pair -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def retainedRegion (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) : Set (Space d) :=
  ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T

noncomputable def sourceOuterMask (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (σ κ : ℝ) (p : CellPath d) (c : ℕ) : Space d → Space d → ℝ :=
  regularOuterMask Q (sourceClass Q μ N B p) (sourceUnitProfile Q μ N B p) N σ κ c

noncomputable def regularizationPairMask (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) : Space d × Space d → ℝ :=
  productPartitionMask (regularizationIndex Q₁ μ N B₁ t₁) (regularizationIndex Q₂ ν N B₂ t₂)
    (regularizationSet Q₁ μ N B₁) (regularizationSet Q₂ ν N B₂)
    (fun i => sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
    (fun i => sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))

noncomputable def regularizationPairExceptional (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (w₀ : Sphere d) (G : Set (Space d × Space d)) :
    Set (Space d × Space d) :=
  pairExceptional (retainedRegion Q₁ μ N B₁ t₁) (retainedRegion Q₂ ν N B₂ t₂)
    (regularizationTestBad w₀ Q₁ μ N B₁ t₁ σ (PlanarFalconer.sourceSmoothingLevels σ κ) p₁ G)
    (regularizationTestBad w₀ Q₂ ν N B₂ t₂ σ (PlanarFalconer.sourceSmoothingLevels σ κ) p₂
      (Prod.swap ⁻¹' G))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ClassPairDistance
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-mass mixture for the two-class distance law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

noncomputable def classPairWeight (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (i : List ℕ × List ℕ) : ℝ≥0 :=
  (classMeasure Q₁ μ (regularizationLeaves Q₁ μ N) (regularizationLabel Q₁ μ N B₁) i.1 univ *
    classMeasure Q₂ ν (regularizationLeaves Q₂ ν N) (regularizationLabel Q₂ ν N B₂) i.2 univ).toNNReal

noncomputable def regularizationPairDistance (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ)
    (Γ : Set (Space d × Space d)) : Measure ℝ :=
  partitionEndpointDistance μ ν Γ
    ((regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂))
    (fun i => regularizationSet Q₁ μ N B₁ i.1) (fun i => regularizationSet Q₂ ν N B₂ i.2)
    (fun i => sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
    (fun i => sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationVariation
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-law variation cost of the actual regularized mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem distanceWeight_upper {δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ)
    {π : Measure (Space d × Space d)} (hsep : ∀ᵐ z ∂π, δ ≤ dist z.1 z.2) :
    ∀ᵐ z ∂π, distanceWeight (((d:ℝ)-1)/2) z ≤ ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) := by
  have hh : (1:ℝ) ≤ d := by exact_mod_cast hd
  filter_upwards [hsep] with z hz
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hδ hz (by linarith))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedTubeData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation of the original measurable tube relation and its finite labels -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι : Type*}

noncomputable def rotatedTubeRelation (e : Space d ≃ₗᵢ[ℝ] Space d)
    (E : Set (Space d × Sphere d)) : Set (Space d × Sphere d) :=
  (Prod.map e.symm (sphereMap e.symm)) ⁻¹' E

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real coordinates of the scalar dyadic tree used in the initial
 regularization. These are the existing geometric descendants. -/
namespace Falconer

noncomputable def scalarPathCenter (p : List (Fin 1 → Bool)) : ℝ :=
  ((⟨0,1⟩ : DyadicCube 1).descendant p).center 0

 theorem scalar_space_dist (x y : Space 1) : dist x y = |x 0-y 0| := by
  rw [PiLp.dist_eq_of_L2]
  simp [Real.dist_eq,Real.sqrt_sq_eq_abs]

 theorem scalarPathCenter_separated {b : ℕ} {p q : List (Fin 1 → Bool)}
    (hp : p.length = b) (hq : q.length = b) (hne : p ≠ q) :
    (1/2:ℝ)^b ≤ |scalarPathCenter p-scalarPathCenter q| := by
  have hh := (⟨0,1⟩ : DyadicCube 1).centers_separated (by norm_num) hp hq hne
  simpa only [scalar_space_dist,scalarPathCenter,div_pow,one_pow] using hh

 theorem scalarPathCenter_injOn {b : ℕ} (C : Finset (List (Fin 1 → Bool)))
    (hlen : ∀ p ∈ C, p.length = b) : Set.InjOn scalarPathCenter (C : Set (List (Fin 1 → Bool))) := by
  intro p hp q hq heq
  by_contra hne
  have hh := scalarPathCenter_separated (hlen p hp) (hlen q hq) hne
  rw [heq,sub_self,abs_zero] at hh
  exact (not_le_of_gt (pow_pos (by norm_num : (0:ℝ) < 1/2) b)) hh

 theorem scalarPathCenter_same_parent {a b : ℕ} {p q : List (Fin 1 → Bool)}
    (hp : p.length = b) (hab : a ≤ b) (heq : p.take a = q.take a) :
    |scalarPathCenter p-scalarPathCenter q| ≤ (1/2:ℝ)^a := by
  have hh := (⟨0,1⟩ : DyadicCube 1).same_ancestor_center_dist (by norm_num) p q hp hab heq
  simpa only [scalar_space_dist,scalarPathCenter,Nat.cast_one,Real.sqrt_one,one_mul,
    div_pow,one_pow] using hh

namespace Regularization

 theorem scalar_prefix_children_length {N a b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) (p : CellPath 1) :
    ∀ q ∈ prefixChildren L a b p, q.length = b := by
  classical
  intro q hq
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  have hrN := (mem_cubePaths 1 N r).mp (hL (Finset.mem_filter.mp hr).1)
  simp only [List.length_take,hrN,min_eq_left hb]

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarPrefixPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-child pruning in the scalar dyadic tree. Lower completed levels
 retain their exact fibers, which makes bottom-up regularization stable. -/
namespace Falconer.Regularization

noncomputable def scalarPruneLeaves (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) : Finset (CellPath 1) := by
  classical
  exact L.filter fun q => q.take b ∈ K (q.take a)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarChildChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single local choice for every occupied parent. Both the collapsed
 and branching alternatives have a dyadic child count and finite tags. -/
namespace Falconer.Regularization

def ScalarChildChoice (L : Finset (CellPath 1)) (a b : ℕ) (p : CellPath 1)
    (K : Finset (CellPath 1)) (k n : ℕ) : Prop :=
  K ⊆ prefixChildren L a b p ∧ K.card = 2^k ∧ k ≤ b-a ∧ a ≤ n ∧ n ≤ b ∧
    (prefixChildren L a b p).card ≤ 2050*K.card ∧
    (k = 0 ∨ (a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ K, ∀ r ∈ K, q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ K, ∃ r ∈ K, q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBranchingLevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric data retained by scalar regularization at each block.
 Subsequent coarser pruning preserves this data exactly. -/
namespace Falconer.Regularization

structure ScalarBranchingLevel (L : Finset (CellPath 1)) (a b k n : ℕ) : Prop where
  exponent_le : k ≤ b-a
  level_lo : a ≤ n
  level_hi : n ≤ b
  children_card : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card = 2^k
  fork_geometry : ∀ p ∈ L.image (List.take a), k = 0 ∨
    (a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ prefixChildren L a b p, ∀ r ∈ prefixChildren L a b p,
        q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ prefixChildren L a b p, ∃ r ∈ prefixChildren L a b p,
        q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarForkGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A witnessed pair of regularized child centers separates their entire
 descendant fibers. This supplies the nonporous binary fork geometry. -/
namespace Falconer.Regularization

 theorem scalar_prefix_leaf_center_dist {N b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) {c u : CellPath 1}
    (hu : u ∈ prefixFiber L b c) :
    |scalarPathCenter u-scalarPathCenter c| ≤ (1/2:ℝ)^b := by
  classical
  have huL := (Finset.mem_filter.mp hu).1
  have huc := (Finset.mem_filter.mp hu).2
  have huN := (mem_cubePaths 1 N u).mp (hL huL)
  have hcc : c.take b = c := by rw [← huc,List.take_take,min_self]
  exact scalarPathCenter_same_parent huN hb (huc.trans hcc.symm)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSelectedForks
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embedding selected regularized forks into the scalar binary cube.
 Gaps between selected levels are filled by actual descendant fibers. -/
namespace Falconer.Regularization

 theorem prefixFiber_child_subset {L : Finset (CellPath 1)} {a b : ℕ}
    (hab : a ≤ b) {p c : CellPath 1} (hc : c ∈ prefixChildren L a b p) :
    prefixFiber L b c ⊆ prefixFiber L a p := by
  classical
  rw [← prefixFiber_parent_filter hab hc]
  exact Finset.filter_subset _ _

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathNodes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating actual scalar prefix nodes into their distinct centers.
 This is the coordinate bridge to the separated-tree projection estimate. -/
namespace Falconer.Regularization

noncomputable def scalarPrefixPath (Q : Finset (CellPath 1)) (d : ℕ) (x : ℝ) : CellPath 1 :=
  Function.invFunOn scalarPathCenter (Q.image (List.take d) : Set (CellPath 1)) x

noncomputable def scalarPrefixPoints (Q : Finset (CellPath 1)) (d : ℕ) (x : ℝ) : Finset ℝ :=
  (prefixFiber Q d (scalarPrefixPath Q d x)).image scalarPathCenter

noncomputable def scalarPrefixChildren (Q : Finset (CellPath 1)) (a b : ℕ) (x : ℝ) : Finset ℝ :=
  (prefixChildren Q a b (scalarPrefixPath Q a x)).image scalarPathCenter

 theorem scalar_prefix_path_eq {N d : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hd : d ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take d)) : scalarPrefixPath Q d (scalarPathCenter p) = p := by
  have hlen : ∀ q ∈ Q.image (List.take d), q.length = d := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    have hrN := (mem_cubePaths 1 N r).mp (hQ hr)
    simp only [List.length_take,hrN,min_eq_left hd]
  exact (scalarPathCenter_injOn _ hlen).leftInvOn_invFunOn hp

 theorem scalar_prefix_points_eq {N d : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hd : d ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take d)) :
    scalarPrefixPoints Q d (scalarPathCenter p) = (prefixFiber Q d p).image scalarPathCenter := by
  unfold scalarPrefixPoints
  rw [scalar_prefix_path_eq hQ hd hp]

 theorem scalar_prefix_children_eq {N a b : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (ha : a ≤ N) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take a)) :
    scalarPrefixChildren Q a b (scalarPathCenter p) = (prefixChildren Q a b p).image scalarPathCenter := by
  unfold scalarPrefixChildren
  rw [scalar_prefix_path_eq hQ ha hp]

 theorem scalar_prefix_points_children {N a b : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N)
    (x : ℝ) :
    scalarPrefixPoints Q a x =
      (scalarPrefixChildren Q a b x).biUnion (scalarPrefixPoints Q b) := by
  classical
  let p := scalarPrefixPath Q a x
  ext y
  constructor
  · intro hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    have hc : u.take b ∈ prefixChildren Q a b p := Finset.mem_image_of_mem _ hu
    have hcm := prefixChildren_mem_image hc
    apply Finset.mem_biUnion.mpr
    refine ⟨scalarPathCenter (u.take b),Finset.mem_image_of_mem _ hc,?_⟩
    rw [scalar_prefix_points_eq hQ hb hcm]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,rfl⟩)
  · intro hy
    obtain ⟨z,hz,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    rw [scalar_prefix_points_eq hQ hb (prefixChildren_mem_image hc)] at hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem _ (prefixFiber_child_subset hab hc hu)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathLevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated levels retain only the information used by the projection
 argument. They allow bunching without requiring a new closest-pair witness. -/
namespace Falconer.Regularization

structure ScalarPathLevel (Q : Finset (CellPath 1)) (a b K : ℕ) (g : ℝ) : Prop where
  order : a ≤ b
  card : ∀ p ∈ Q.image (List.take a), (prefixChildren Q a b p).card = K
  separated : ∀ p ∈ Q.image (List.take a), ∀ u ∈ prefixChildren Q a b p,
    ∀ v ∈ prefixChildren Q a b p, u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterPathTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cluster tree formed by actual path fibers. Terminal fibers retain
 their full uniform cardinality and original fine-scale separation. -/
namespace Falconer.Regularization

 theorem scalar_prefix_points_separated {N : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (a : ℕ) (x : ℝ) :
    ∀ u ∈ scalarPrefixPoints Q a x, ∀ v ∈ scalarPrefixPoints Q a x,
      u ≠ v → (1/2:ℝ)^N ≤ |u-v| := by
  classical
  intro u hu v hv huv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  have hpN := (mem_cubePaths 1 N p).mp (hQ (Finset.mem_filter.mp hp).1)
  have hqN := (mem_cubePaths 1 N q).mp (hQ (Finset.mem_filter.mp hq).1)
  exact scalarPathCenter_separated hpN hqN (fun he => huv (congrArg scalarPathCenter he))

noncomputable def scalarClusterPathTreeOfLevels {N K m : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d branch : ℕ → ℕ) (gap : ℕ → ℝ)
    (hd : ∀ i ≤ K, d i ≤ N) (hm : 0 < m)
    (hbranch : ∀ i < K, 0 < branch i)
    (hlevel : ∀ i < K, ScalarPathLevel Q (d (i+1)) (d i) (branch i) (gap i))
    (hgap : ∀ i < K, 5*(1/2:ℝ)^(d i) < gap i)
    (hleaf : ∀ p ∈ Q.image (List.take (d 0)), (prefixFiber Q (d 0) p).card = m) :
    ScalarClusterTree ((1/2:ℝ)^N) K := by
  classical
  refine {
    nodes := fun i => (Q.image (List.take (d i))).image scalarPathCenter
    children := fun i x => scalarPrefixChildren Q (d (i+1)) (d i) x
    points := fun i x => scalarPrefixPoints Q (d i) x
    branching := branch
    radius := fun i => (1/2:ℝ)^(d i)
    gap := gap
    branch_pos := hbranch
    radius_ge := fun i hi => pow_le_pow_of_le_one (by norm_num) (by norm_num) (hd i hi.le)
    gap_pos := fun i hi => lt_trans (by positivity) (hgap i hi)
    gap_gt := hgap
    child_subset := ?_
    child_card := ?_
    child_sep := ?_
    child_bound := ?_
    parent_eq := ?_
    leaf_size := m
    leaf_pos := hm
    leaf_card := ?_
    leaf_sep := fun x _ => scalar_prefix_points_separated hQ (d 0) x
  }
  · intro i hi x hx y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem _ (prefixChildren_mem_image hc)
  · intro i hi x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp]
    rw [Finset.card_image_of_injOn (scalarPathCenter_injOn _
      (scalar_prefix_children_length (a := d (i+1)) hQ (hd i hi.le) p))]
    exact (hlevel i hi).card p hp
  · intro i hi x hx y hy z hz hyz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (hlevel i hi).separated p hp c hc e he (fun hce => hyz (congrArg scalarPathCenter hce))
  · intro i hi x hx y hy z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_children_eq hQ (hd (i+1) (by omega)) hp] at hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    rw [scalar_prefix_points_eq hQ (hd i hi.le) (prefixChildren_mem_image hc)] at hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact scalar_prefix_leaf_center_dist hQ (hd i hi.le) hu
  · intro i hi x _
    exact scalar_prefix_points_children hQ (hlevel i hi).order (hd i hi.le) x
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [scalar_prefix_points_eq hQ (hd 0 (Nat.zero_le K)) hp]
    rw [Finset.card_image_of_injOn (scalarPathCenter_injOn (prefixFiber Q (d 0) p) (fun q hq =>
      (mem_cubePaths 1 N q).mp (hQ (Finset.mem_filter.mp hq).1)))]
    exact hleaf p hp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchClusterTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bunch ledger realized as a tree of entire terminal fibers. -/
namespace Falconer.Regularization

noncomputable def scalarBunchClusterTree {N top lo m : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdtop : d top ≤ N) (hm : 0 < m)
    (g : ScalarBunch → ℝ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (g b))
    (hgap : ∀ b ∈ bs, 5*(1/2:ℝ)^(d b.stop) < g b)
    (hleaf : ∀ p ∈ Q.image (List.take (d top)), (prefixFiber Q (d top) p).card = m) :
    ScalarClusterTree ((1/2:ℝ)^N) bs.length := by
  let depth := fun i => d (scalarBunchBoundary lo bs i)
  let branch := fun i => (bs.map (fun b => 2^(∑ j ∈ Finset.Ico b.start b.cut, k j))).getD i 1
  let gap := fun i => (bs.map g).getD i 1
  apply scalarClusterPathTreeOfLevels Q hQ depth branch gap
  · intro i _
    exact (hd (hchain.boundary_bounds i).2).trans hdtop
  · exact hm
  · intro i hi
    dsimp [branch]
    rw [scalarBunchValue_at _ _ hi]
    positivity
  · intro i hi
    have he := hchain.boundary_edges i hi
    dsimp [depth,branch,gap]
    rw [he.1,he.2,scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact hlevels bs[i] (List.getElem_mem hi)
  · intro i hi
    have he := hchain.boundary_edges i hi
    dsimp [depth,gap]
    rw [he.1,scalarBunchValue_at _ _ hi]
    exact hgap bs[i] (List.getElem_mem hi)
  · dsimp [depth]
    rw [hchain.boundary_zero]
    exact hleaf


end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPointPaths
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Place actual scalar points in the existing half-open dyadic tree. -/
namespace Falconer.Regularization

noncomputable def scalarUnitPoint (x : ℝ) : Space 1 := WithLp.toLp 2 (fun _ => x)

 theorem scalar_point_has_path (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    ∃ p ∈ cubePaths 1 N, scalarUnitPoint x ∈ ((⟨0,1⟩ : DyadicCube 1).descendant p).carrier := by
  apply (⟨0,1⟩ : DyadicCube 1).mem_descendant_at_depth N
  intro i
  simpa only [DyadicCube.carrier,scalarUnitPoint,PiLp.toLp_apply,PiLp.zero_apply,zero_add] using hx

noncomputable def scalarPointPath (N : ℕ) (x : ℝ) : CellPath 1 :=
  if hx : 0 ≤ x ∧ x < 1 then Classical.choose (scalar_point_has_path N hx)
  else List.replicate N (fun _ => false)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding an actual separated scalar set to dyadic centers preserves
 its cardinality and moves each point by at most half a fine cell. -/
namespace Falconer.Regularization

noncomputable def scalarPointLeaves (N : ℕ) (X : Finset ℝ) : Finset (CellPath 1) :=
  X.image (scalarPointPath N)

noncomputable def scalarRoundedPoints (N : ℕ) (X : Finset ℝ) : Finset ℝ :=
  (scalarPointLeaves N X).image scalarPathCenter

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanCross
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three-dimensional dual directions and the Gram determinant -/

namespace Falconer
open scoped Matrix

noncomputable def euclideanCross (u v : Space 3) : Space 3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

theorem euclidean_inner_dot (u v : Space 3) :
    inner ℝ u v = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inner_self_euclideanCross (u v : Space 3) : inner ℝ u (euclideanCross u v) = 0 := by
  rw [euclidean_inner_dot]
  exact dot_self_cross _ _

theorem inner_euclideanCross_self (u v : Space 3) : inner ℝ v (euclideanCross u v) = 0 := by
  rw [euclidean_inner_dot]
  exact dot_cross_self _ _

theorem euclideanCross_cyclic (u v w : Space 3) :
    inner ℝ u (euclideanCross v w) = inner ℝ v (euclideanCross w u) := by
  rw [euclidean_inner_dot,euclidean_inner_dot]
  exact triple_product_permutation _ _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleColumns
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit cofactor coordinates for three transverse directions -/

namespace Falconer
open scoped BigOperators

noncomputable def tripleCofactors (u v w : Space 3) : Fin 3 → Space 3 :=
  ![euclideanCross v w,euclideanCross w u,euclideanCross u v]

theorem tripleCofactors_inner (u v w : Space 3) (i j : Fin 3) :
    inner ℝ (tripleCofactors u v w i) (![u,v,w] j) =
      if i = j then inner ℝ u (euclideanCross v w) else 0 := by
  have h0 : inner ℝ (euclideanCross v w) u = inner ℝ u (euclideanCross v w) := real_inner_comm _ _
  have h1 : inner ℝ (euclideanCross w u) v = inner ℝ u (euclideanCross v w) :=
    (real_inner_comm _ _).trans (euclideanCross_cyclic u v w).symm
  have h2 : inner ℝ (euclideanCross u v) w = inner ℝ u (euclideanCross v w) :=
    (real_inner_comm _ _).trans ((euclideanCross_cyclic v w u).symm.trans
      (euclideanCross_cyclic u v w).symm)
  have hz₁ (a b : Space 3) : inner ℝ (euclideanCross a b) a = 0 :=
    (real_inner_comm _ _).trans (inner_self_euclideanCross a b)
  have hz₂ (a b : Space 3) : inner ℝ (euclideanCross a b) b = 0 :=
    (real_inner_comm _ _).trans (inner_euclideanCross_self a b)
  fin_cases i <;> fin_cases j <;> simp [tripleCofactors,h0,h1,h2,hz₁,hz₂]

noncomputable def tripleColumnLinear (u v w : Space 3) : Space 3 →ₗ[ℝ] Space 3 where
  toFun x := ∑ i : Fin 3, x i • (![u,v,w] i)
  map_add' x y := by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

noncomputable def tripleDualCoordinates (u v w x : Space 3) : Space 3 :=
  WithLp.toLp 2 (fun i => inner ℝ (tripleCofactors u v w i) x /
    inner ℝ u (euclideanCross v w))

theorem tripleDualCoordinates_column (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    tripleDualCoordinates u v w (tripleColumnLinear u v w x) = x := by
  apply PiLp.ext
  intro i
  change (inner ℝ (tripleCofactors u v w i)
    (∑ j : Fin 3, x j • (![u,v,w] j)))/inner ℝ u (euclideanCross v w) = x i
  simp only [inner_sum,inner_smul_right,tripleCofactors_inner]
  simp [mul_ite,ht]

theorem tripleColumnLinear_injective (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) :
    Function.Injective (tripleColumnLinear u v w) :=
  Function.LeftInverse.injective (tripleDualCoordinates_column u v w ht)

noncomputable def tripleColumnEquiv (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) : Space 3 ≃L[ℝ] Space 3 :=
  (LinearEquiv.ofBijective (tripleColumnLinear u v w)
    ⟨tripleColumnLinear_injective u v w ht,
      LinearMap.injective_iff_surjective.mp (tripleColumnLinear_injective u v w ht)⟩).toContinuousLinearEquiv

@[simp] theorem tripleColumnEquiv_apply (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    tripleColumnEquiv u v w ht x = tripleColumnLinear u v w x := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubePacketDilation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dilation of a coarse line packet and the error from moving
its incident points to a common row. Used in the product extraction step
of the planar regular-set argument (Orponen--Shmerkin, Appendix A.6). -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def packetLineDilate (Δ : ℝ) (l : Space 2) : Space 2 := Δ⁻¹ • l

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian Fourier pairing in the actual ambient dimension. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable def gaussianFourierKernel (n : ℕ) (a : ℂ) (ξ : Space n) : ℂ :=
  ((Real.pi : ℂ) / a) ^ ((n : ℂ) / 2) *
    Complex.exp (-(Real.pi : ℂ)^2 * (‖ξ‖^2 : ℝ) / a)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CompactFourierBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-support Fourier moment bounds with a total derivative budget. -/

namespace Falconer
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Space n) 1)).toReal

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanLpTrace
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-dimensional Sobolev trace estimate used for radial densities. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal FourierTransform SchwartzMap

noncomputable def euclideanComplexSchwartz {n : ℕ} (f : 𝓢(Space n, ℝ)) : 𝓢(Space n, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM f

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineSlabCluster
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine slabs with a common point and nearby normal directions -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

noncomputable def normalDistance (u v : Space d) : ℝ := min ‖u-v‖ ‖u+v‖

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized projection kernels, including their diagonal convention. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def directionalProjectionKernel {d : ℕ} (s : ℝ) (w : Sphere d)
    (v : Space d) : ℝ≥0∞ :=
  if v = 0 then 1 else
    (ENNReal.ofReal ‖perpendicularPart (w : Space d) (‖v‖⁻¹ • v)‖)^(-s)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Riesz-energy moments for actual orthogonal hyperplane projections. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def hyperplaneProjectedMeasure {d : ℕ} (μ : Measure (Space d))
    (w : Sphere d) : Measure (Space d) :=
  μ.map (perpendicularPart (w : Space d))

noncomputable def euclideanDifferenceEnergyMeasure {d : ℕ} (μ : Measure (Space d))
    (s : ℝ) : Measure (Space d × Space d) :=
  (μ.prod μ).withDensity (fun z => (edist z.1 z.2)^(-s))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SphereSlab
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear slab bounds for the surface measure, obtained from cone volume. -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable def northSlabBox (n : ℕ) (r : ℝ) : Set (Space (n+1)) :=
  WithLp.ofLp ⁻¹' Icc (Fin.cons (-r) (fun _ : Fin n => -1))
    (Fin.cons r (fun _ : Fin n => 1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SlabSliceAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging thin hyperplane slabs before taking their slice limit. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable def slabSliceAverage {n : ℕ} (r : ℝ) (F : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) : ℝ≥0∞ :=
  (ENNReal.ofReal (2*r))⁻¹ *
    ∫⁻ x : Space (n+1),
      {x : Space (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r}.indicator F x

noncomputable def slabSliceMajorant {n : ℕ} (F : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) : ℝ≥0∞ :=
  liminf (fun k : ℕ => slabSliceAverage (1/((k : ℝ)+1)) F w) atTop

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_HyperplaneSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual hyperplane slices are bounded by the measurable thin-slab majorant. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable def hyperplaneSliceEmbedding {n : ℕ} (w : Sphere (n+1))
    (y : Space n) : Space (n+1) :=
  (northRotation w).symm (coordinateJoin y 0)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_HyperplaneSliceEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable majorant for the actual Fourier energy on each hyperplane. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal Topology

noncomputable def hyperplaneFourierWeight {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (ξ : Space (n+1)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * ‖ξ‖^(s-n))

noncomputable def hyperplaneFourierEnergy {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) : ℝ≥0∞ :=
  ∫⁻ ξ : Space n, hyperplaneFourierWeight μ s (hyperplaneSliceEmbedding w ξ)

noncomputable def hyperplaneEnergyMajorant {n : ℕ} (μ : Measure (Space (n+1)))
    (s : ℝ) (w : Sphere (n+1)) : ℝ≥0∞ :=
  slabSliceMajorant (hyperplaneFourierWeight μ s) w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume coordinates on a fixed normal's orthogonal hyperplane and fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def hyperplaneProjection {n : ℕ} (w : Sphere (n+1))
    (x : Space (n+1)) : Space n :=
  euclideanTail (northRotation w x)

noncomputable def hyperplaneFrame {n : ℕ} (w : Sphere (n+1))
    (p : Space n × ℝ) : Space (n+1) :=
  (northRotation w).symm (coordinateJoin p.1 p.2)

@[fun_prop] theorem contDiff_hyperplaneProjection {n : ℕ} (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneProjection w) := by
  unfold hyperplaneProjection euclideanTail
  apply (contDiff_piLp 2).mpr
  intro i
  exact (contDiff_piLp_apply 2 (i := i.succ)).comp (northRotation w).contDiff

@[fun_prop] theorem contDiff_hyperplaneFrame {n : ℕ} (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneFrame w) := by
  apply (northRotation w).symm.contDiff.comp
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [coordinateJoin_eq]
  · exact contDiff_snd
  · exact (contDiff_piLp_apply 2 (i := j)).comp contDiff_fst

theorem hyperplaneProjection_frame {n : ℕ} (w : Sphere (n+1)) (y : Space n) (t : ℝ) :
    hyperplaneProjection w (hyperplaneFrame w (y,t)) = y := by
  simp only [hyperplaneProjection, hyperplaneFrame, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  simp [euclideanTail, coordinateJoin_eq]

theorem hyperplaneFrame_inner {n : ℕ} (w : Sphere (n+1)) (p : Space n × ℝ) :
    inner ℝ (hyperplaneFrame w p) (w : Space (n+1)) = p.2 := by
  rw [hyperplaneFrame, ← (northRotation w).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply, northRotation_apply,
    gnomonicChart_zero_coe, inner_northLift_zero]
  simp [coordinateJoin_eq]

noncomputable def hyperplaneCoordinateMeasure {n : ℕ} (μ : Measure (Space (n+1)))
    (w : Sphere (n+1)) : Measure (Space n) := μ.map (hyperplaneProjection w)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compactly supported fibers in the actual hyperplane coordinates. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform Convolution

noncomputable def hyperplaneFiberDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) (y : Space n) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, a (hyperplaneFrame w (y,r))

noncomputable def hyperplaneRealFiber {n : ℕ} (a : Space (n+1) → ℝ)
    (w : Sphere (n+1)) (y : Space n) : ℝ := ∫ r : ℝ, a (hyperplaneFrame w (y,r))

theorem hyperplaneRealFiber_compact {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (w : Sphere (n+1)) :
    HasCompactSupport (hyperplaneRealFiber a w) := by
  apply HasCompactSupport.intro (hc.image (contDiff_hyperplaneProjection w).continuous)
  intro y hy
  apply integral_eq_zero_of_ae
  filter_upwards with r
  by_contra hn
  exact hy ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneProjection_frame w y r⟩

theorem hyperplaneRealFiber_smooth {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (w : Sphere (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (hyperplaneRealFiber a w) := by
  let g : Space n → ℝ → ℝ := fun y r => a (hyperplaneFrame w (y,r))
  let K := (fun x : Space (n+1) => inner ℝ x (w : Space (n+1))) '' tsupport a
  have hK : IsCompact K := hc.image (by fun_prop)
  have hgs : ∀ y r, y ∈ (univ : Set (Space n)) → r ∉ K → g y r = 0 := by
    intro y r _ hr
    by_contra hn
    exact hr ⟨hyperplaneFrame w (y,r), subset_tsupport a hn, hyperplaneFrame_inner w (y,r)⟩
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (univ ×ˢ univ) :=
    (ha.comp (contDiff_hyperplaneFrame w)).contDiffOn
  have h := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : Space n => (0 : ℝ)) contDiffOn_const
    isOpen_univ hK hgs (f := fun _ : ℝ => (1 : ℝ)) (continuous_const.locallyIntegrable) hg
  rw [contDiffOn_univ] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  simp only [convolution, ContinuousLinearMap.mul_apply', one_mul, zero_sub, g, hyperplaneRealFiber]
  exact (integral_neg_eq_self (fun r : ℝ => a (hyperplaneFrame w (y,r))) volume).symm

noncomputable def hyperplaneSchwartzFiber {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (w : Sphere (n+1)) :
    𝓢(Space n, ℝ) :=
  (hyperplaneRealFiber_compact a hc w).toSchwartzMap (hyperplaneRealFiber_smooth a hc ha w)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HyperplaneFourier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier slice identity for the fixed hyperplane fiber. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal SchwartzMap FourierTransform

noncomputable def euclideanDensityMeasure {n : ℕ} (a : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (a x))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanMollifier
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized compact smooth mollifiers in the source dimension. -/
namespace Falconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution
variable {d : ℕ}

noncomputable def euclideanBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Space d) where
  rIn := ε/2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def euclideanMollifier (ε : ℝ) (hε : 0 < ε) : Space d → ℝ :=
  (euclideanBump (d := d) ε hε).normed volume

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EuclideanSmoothConvolution
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth densities for convolution with the chosen Euclidean mollifier. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal NNReal Convolution
variable {d : ℕ}


noncomputable def euclideanSmoothDensity (α : Measure (Space d)) (b : Space d → ℝ) (x : Space d) : ℝ :=
  ∫ y, b (x-y) ∂α

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarScalarGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scalar grid coordinates for a planar finite set. Rounding is
injective below the separation scale and coordinate counts are exactly the
original scalar cell counts. -/
namespace Falconer

noncomputable def planarGridFloor (δ : ℝ) (x : Space 2) : Space 2 :=
  rowPoint (scalarGridFloor δ (x 0)) (scalarGridFloor δ (x 1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GridProjectionTransfer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted projection counts through actual coordinate changes and
rounding, with all losses given by finite covering factors. -/
namespace Falconer

noncomputable def cartesianProjection (c : ℝ) (p : Space 2) : ℝ := p 0+c*p 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BoundedProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded actual projection coordinates, with exact finite cell-count
comparison to the original planar projections. -/
namespace Falconer

noncomputable def boundedProjectionCoordinates (a b : ℝ) (p : Space 2) : Space 2 :=
  planarQuarter (planarProjectionCoordinates a b p)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TransverseGridCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling physical tube tests back to transverse coordinates -/

namespace Falconer
variable {d : ℕ}

noncomputable def tripleGridPoint (δ : ℝ) (z : ℤ × ℤ × ℤ) : Space 3 :=
  WithLp.toLp 2 ![δ*(z.1:ℝ),δ*(z.2.1:ℝ),δ*(z.2.2:ℝ)]

@[simp] theorem tripleGridPoint_zero (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 0 = δ*(z.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_one (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 1 = δ*(z.2.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_two (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 2 = δ*(z.2.2:ℝ) := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralTransverseGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # General-dimensional physical grid count from the precise published input -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

noncomputable def euclideanIntegerGrid (δ : ℝ) (z : Fin (n+1) → ℤ) : Space (n+1) :=
  WithLp.toLp 2 (fun j => δ*(z j:ℝ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

noncomputable def tripleRound (δ : ℝ) (x : Space 3) : ℤ × ℤ × ℤ :=
  (round (x 0/δ),round (x 1/δ),round (x 2/δ))

noncomputable def roundedTripleGrid (E : Set (Space 3)) (δ : ℝ) (L : ℕ) :
    Finset (ℤ × ℤ × ℤ) := by
  classical
  exact (tripleIntegerBox L).filter (fun z => ∃ x ∈ E, tripleRound δ x = z)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralGridRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

noncomputable def euclideanRound (δ : ℝ) (x : Space (n+1)) : Fin (n+1) → ℤ :=
  fun j => round (x j/δ)

noncomputable def roundedEuclideanGrid (E : Set (Space (n+1))) (δ : ℝ) (L : ℕ) :
    Finset (Fin (n+1) → ℤ) := by
  classical
  exact (integerGridBox n L).filter (fun z => ∃ x ∈ E, euclideanRound δ x = z)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFivePaths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Five-edge sum labels give the two-sided small-sumset refinement used
to pass from projection collisions to a Cartesian product. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

noncomputable def integerFivePaths (A B G : Finset ℤ) (e : ℤ → ℤ → Prop)
    (a c : ℤ) : Finset IntegerFivePath :=
  (G.filter fun b => e a b).sigma fun b => integerFourPaths A B e b c

def integerFiveSums (a c : ℤ) (p : IntegerFivePath) : ℤ × ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (a+p.1,integerPathSums p.1 c p.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Put compact projected supports in a fixed unit cube -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def centeredUnitCube (d : ℕ) : DyadicCube d :=
  ⟨WithLp.toLp 2 (fun _ => -(1/2:ℝ)),1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RoundedProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate graph used in the planar projection application:
actual points, a fixed contraction, and an injective fine-grid rounding. -/
namespace Falconer

noncomputable def roundedProjectionCoordinates (σ a b : ℝ) (p : Space 2) : Space 2 :=
  planarGridFloor σ (boundedProjectionCoordinates a b p)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SelectedChartRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected incidence in its original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*}

def selectedChartRelation (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset κ)
    (a : κ → Space (n+1)) (R T : ℝ) : Set (Space (n+1) × Space n) :=
  {u | (u.1,gnomonicChart u.2) ∈ selectedActiveRelation A z δ E J a R T ∧ ‖u.2‖ ≤ 1}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SimilarityGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common similarities for original pairs

Only a common orthogonal map and a positive dilation are used. The direction
map is exactly orthogonal, so the original radial cap constants are unchanged.
-/
namespace Falconer
open Set MeasureTheory NormedSpace

noncomputable def pairHomeomorph {d : ℕ} (f : Space d ≃ₜ Space d) :
    (Space d × Space d) ≃ₜ (Space d × Space d) := f.prodCongr f

@[simp] theorem pairHomeomorph_apply {d : ℕ} (f : Space d ≃ₜ Space d)
    (z : Space d × Space d) : pairHomeomorph f z = (f z.1,f z.2) := rfl

noncomputable def scaledIsometry {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) : Space d ≃ₜ Space d :=
  e.toHomeomorph.trans (Homeomorph.smulOfNeZero a ha.ne')

@[simp] theorem scaledIsometry_apply {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x : Space d) : scaledIsometry e a ha x = a • e x := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SmallChartCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed unit cube for the small gnomonic chart -/

namespace Falconer
open Set Metric MeasureTheory

noncomputable def smallChartCube (d : ℕ) : DyadicCube d :=
  ⟨WithLp.toLp 2 (fun _ => -(1/2:ℝ)),1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SurfaceTestNorm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous test norms against the actual ambient surface measure.
These measure-duality lemmas match the published radial pushforward directly. -/

namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology
variable {d : ℕ}

noncomputable def surfaceTestNorm (q : ℝ) (γ : Measure (Space (d+1))) : ℝ≥0∞ :=
  ⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ)
    (_ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1),
      ENNReal.ofReal ‖∫ w, F w ∂γ‖


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized auxiliary frame for the odd-dimensional preparation -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure TwoProjectionFrame {d : ℕ} (μ : ProbabilityMeasure (Space d)) (m k : ℕ) (s : ℝ) where
  first : Space d →L[ℝ] Space m
  second : Space m →L[ℝ] Space k
  first_contractive : ‖first‖ ≤ 1
  second_contractive : ‖second‖ ≤ 1
  first_root : ∀ x ∈ (μ : Measure (Space d)).support,
    first x ∈ (centeredUnitCube m).carrier
  second_root : ∀ x ∈ (μ : Measure (Space d)).support,
    (second.comp first) x ∈ (centeredUnitCube k).carrier
  noncharging : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
    ((μ : Measure (Space d)).map first) {x | inner ℝ w x = t} = 0
  constant : ℝ
  constant_pos : 0 < constant
  original_frostman : FrostmanBallBound (μ : Measure (Space d)) s constant
  first_frostman : FrostmanBallBound ((μ : Measure (Space d)).map first) s constant
  second_frostman : FrostmanBallBound ((μ : Measure (Space d)).map (second.comp first)) s constant

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionPieces
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive compact pieces in the normalized two-projection frame -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure TwoProjectionPieces {d m k : ℕ} {μ : ProbabilityMeasure (Space d)}
    {s : ℝ} (f : TwoProjectionFrame μ m k s) (ε : ℝ) where
  leftSet : Set (Space d)
  rightSet : Set (Space d)
  left_compact : IsCompact leftSet
  right_compact : IsCompact rightSet
  left_subset : leftSet ⊆ (μ : Measure (Space d)).support
  right_subset : rightSet ⊆ (μ : Measure (Space d)).support
  left_pos : 0 < (μ : Measure (Space d)) leftSet
  right_pos : 0 < (μ : Measure (Space d)) rightSet
  radius : ℝ
  radius_pos : 0 < radius
  lower : ℝ
  lower_pos : 0 < lower
  direction : Space d
  direction_unit : ‖direction‖ = 1
  geometry : ∀ x ∈ leftSet, ∀ y ∈ rightSet,
    radius/2 ≤ dist x y ∧ dist x y ≤ 2*radius ∧
    lower ≤ ‖(f.second.comp f.first) (radialDirection x y)‖ ∧
    lower ≤ ‖(f.second.comp f.first) (radialDirection y x)‖ ∧
    dist (radialDirection x y) direction < ε

variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}

namespace TwoProjectionPieces
variable {f : TwoProjectionFrame μ m k s} (p : TwoProjectionPieces f ε)

noncomputable def left : ProbabilityMeasure (Space d) :=
  positiveRestriction μ p.leftSet p.left_pos

noncomputable def right : ProbabilityMeasure (Space d) :=
  positiveRestriction μ p.rightSet p.right_pos

theorem left_support : (p.left : Measure (Space d)).support ⊆ p.leftSet :=
  positiveRestriction_support μ p.leftSet p.left_pos p.left_compact.isClosed

theorem right_support : (p.right : Measure (Space d)).support ⊆ p.rightSet :=
  positiveRestriction_support μ p.rightSet p.right_pos p.right_compact.isClosed

theorem left_support_compact : IsCompact (p.left : Measure (Space d)).support :=
  p.left_compact.of_isClosed_subset Measure.isClosed_support p.left_support

theorem right_support_compact : IsCompact (p.right : Measure (Space d)).support :=
  p.right_compact.of_isClosed_subset Measure.isClosed_support p.right_support

theorem left_ac : (p.left : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
  positiveRestriction_absolutelyContinuous μ p.leftSet p.left_pos

theorem right_ac : (p.right : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
  positiveRestriction_absolutelyContinuous μ p.rightSet p.right_pos

theorem first_lower {x y : Space d} (hx : x ∈ p.leftSet) (hy : y ∈ p.rightSet) :
    p.lower ≤ ‖f.first (radialDirection x y)‖ ∧
    p.lower ≤ ‖f.first (radialDirection y x)‖ := by
  have hbound (v : Space d) : ‖(f.second.comp f.first) v‖ ≤ ‖f.first v‖ :=
    (f.second.le_opNorm (f.first v)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right f.second_contractive (norm_nonneg (f.first v)))
  exact ⟨(p.geometry x hx y hy).2.2.1 |>.trans (hbound _),
    (p.geometry x hx y hy).2.2.2.1 |>.trans (hbound _)⟩

noncomputable def constant : ℝ :=
  max (((μ : Measure (Space d)) p.leftSet).toReal⁻¹)
    (((μ : Measure (Space d)) p.rightSet).toReal⁻¹) * f.constant

theorem constant_pos : 0 < p.constant := by
  apply mul_pos _ f.constant_pos
  exact (inv_pos.mpr (ENNReal.toReal_pos p.left_pos.ne' (measure_ne_top _ _))).trans_le (le_max_left _ _)

theorem projected_frostman {q : ℕ} (P : Space d →L[ℝ] Space q)
    (h : FrostmanBallBound ((μ : Measure (Space d)).map P) s f.constant) :
    FrostmanBallBound ((p.left : Measure (Space d)).map P) s p.constant ∧
    FrostmanBallBound ((p.right : Measure (Space d)).map P) s p.constant := by
  constructor
  · intro x r hr
    apply (positiveRestriction_projected_frostman μ p.leftSet p.left_pos P h x r hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) f.constant_pos.le
  · intro x r hr
    apply (positiveRestriction_projected_frostman μ p.rightSet p.right_pos P h x r hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) f.constant_pos.le

end TwoProjectionPieces
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoProjectionPiecePair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first auxiliary pair and its inherited root geometry -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m k : ℕ} {μ : ProbabilityMeasure (Space d)} {s ε : ℝ}
  {f : TwoProjectionFrame μ m k s}

namespace TwoProjectionPieces
variable (p : TwoProjectionPieces f ε)

noncomputable def firstPair : ProjectedStartingPair μ m s ε := by
  have horig := p.projected_frostman (ContinuousLinearMap.id ℝ (Space d))
    (by simpa using f.original_frostman)
  have hfirst := p.projected_frostman f.first f.first_frostman
  refine {
    projection := f.first
    left := p.left
    right := p.right
    left_compact := p.left_support_compact
    right_compact := p.right_support_compact
    left_ac := p.left_ac
    right_ac := p.right_ac
    constant := p.constant
    constant_pos := p.constant_pos
    left_frostman := by simpa using horig.1
    right_frostman := by simpa using horig.2
    projected_left_frostman := hfirst.1
    projected_right_frostman := hfirst.2
    contractive := f.first_contractive
    radius := p.radius
    radius_pos := p.radius_pos
    lower := p.lower
    lower_pos := p.lower_pos
    direction := p.direction
    direction_unit := p.direction_unit
    geometry := ?_ }
  intro x hx y hy
  have hx' := p.left_support hx
  have hy' := p.right_support hy
  obtain ⟨h1,h2,_,_,h5⟩ := p.geometry x hx' y hy'
  obtain ⟨h3,h4⟩ := p.first_lower hx' hy'
  exact ⟨h1,h2,h3,h4,h5⟩

end TwoProjectionPieces
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RoundedRowPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the width-three incidences produced by a coarse packet into exact
mesh-scale incidences. The output slope and intercept lie on the mesh, and
every output line remains within nine mesh lengths of its original line. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def rowAdjustedRaw (δ : ℝ) (p l : Space 2) : Space 2 :=
  rowPoint (l 0) (p 1-scalarGridFloor δ (l 0)*p 0)

noncomputable def rowAdjustedLine (δ : ℝ) (p l : Space 2) : Space 2 :=
  planarGridFloor δ (rowAdjustedRaw δ p l)

@[simp] theorem rowAdjustedLine_zero (δ : ℝ) (p l : Space 2) :
    rowAdjustedLine δ p l 0 = scalarGridFloor δ (l 0) := rfl

@[simp] theorem rowAdjustedLine_one (δ : ℝ) (p l : Space 2) :
    rowAdjustedLine δ p l 1 = scalarGridFloor δ (p 1-scalarGridFloor δ (l 0)*p 0) := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_CommonRowNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the rounded product rows into the bounded line chart without
changing their first coordinate. All size losses are explicit. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def verticalQuarter (p : Space 2) : Space 2 := rowPoint (p 0) (p 1/4)
noncomputable def verticalFour (p : Space 2) : Space 2 := rowPoint (p 0) (4*p 1)

@[simp] theorem verticalQuarter_zero (p : Space 2) : verticalQuarter p 0 = p 0 := rfl
@[simp] theorem verticalQuarter_one (p : Space 2) : verticalQuarter p 1 = p 1/4 := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularEnergyPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-energy deletion with its geometric budgets discharged. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def pencilEnergyBudget (N : ℕ) (s t K M : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  (K*(80*(1/(2:ℝ)^N))^s*M)*(1+2*K*planarCriticalConstant N t)*(P.card:ℝ)^2

noncomputable def pencilMomentBudget (N : ℕ) (s t K M : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)*(P.card:ℝ)^2

noncomputable def pencilEnergyCutoff (N : ℕ) (s t K M m : ℝ)
    (P : Finset (Space 2)) : ℝ :=
  16*pencilEnergyBudget N s t K M P*pencilMomentBudget N s t K M P /
    (m*(P.card:ℝ))^2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_NormalizedProductPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the common-row rounding into actual pencil families. The
pencil cardinality drops by at most 361, and the complete union grows by
at most 361. No separation assumption is needed on the original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def normalizedPencil (δ : ℝ) (p : Space 2) (S : Finset (Space 2)) :
    Finset (Space 2) := (S.image (rowAdjustedLine δ p)).image planarQuarter

noncomputable def normalizedRowPencils (δ : ℝ) (T : Space 2 → Finset (Space 2))
    (p : Space 2) : Finset (Space 2) :=
  normalizedPencil δ (verticalFour p) (T (verticalFour p))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_QuarterPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of a finite pencil family under the fixed contraction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def quarterPencils (V : Space 2 → Finset (Space 2)) (z : Space 2) :
    Finset (Space 2) := (V ((4:ℝ) • z)).image (localCellLine 4 0 0)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_SquashedPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original bounded-chart pencils, thinned by a fixed factor and moved
to the slope chart required by the regular incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def squashedPencils (V : Space 2 → Finset (Space 2)) (z : Space 2) :
    Finset (Space 2) := (V (planarUnsquash z)).image planarSquash

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEndpointBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The induction statement retains the original reference profile. Its
single budget bounds parent mass loss, pencil regularity and pencil size ratio. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

def QuarterPencilData (δ s W m : ℝ) (P : Finset (Space 2))
    (V : Space 2 → Finset (Space 2)) : Prop :=
  ∀ x ∈ P, m ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ W*m ∧
    InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
    NormalizedFiniteBallBound δ s W (V x) ∧
    ∀ l ∈ V x, |l 0| ≤ 1/2 ∧ TubeIncident δ x l

def ProfileEndpointBound (N B K : ℕ) (L : Finset (CellPath 2))
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2)
    (i j : ℕ) (s W A : ℝ) : Prop :=
  ∀ (L' : Finset (CellPath 2)) (g : CellPath 2 → List ℕ) (q : CellPath 2)
    (a₀ : ℕ) (r₀ : CellPath 2), L' ⊆ cubePaths 2 N →
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    S ⊆ prefixFiber C a₀ r₀ → ((prefixFiber C a₀ r₀).card:ℝ) ≤ W*(S.card:ℝ) →
    a₀ ≤ blockDepth N B i → ∀ p₀ ∈ S.image (List.take (blockDepth N B i)),
    ∀ m : ℝ, 0 < m → ∀ V : Space 2 → Finset (Space 2),
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    QuarterPencilData (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s W m Z V →
    A ≤ ((Z.biUnion V).card:ℝ)/m

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockProfileCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the rounded real profile cells and their gains to the exact
block-index pairs used by the recursive incidence estimates. -/
namespace Falconer
open Set Regularization

noncomputable def blockProfileCell (N B : ℕ) (r : ℕ × ℕ) : ℝ × ℝ :=
  ((blockDepth N B r.1:ℝ)/N,
    ((blockDepth N B r.2:ℝ)-(blockDepth N B r.1:ℝ))/N)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularClassRadialIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak radial incidence for the actual conditional regularized class laws -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

noncomputable def radialClassBallBound (Q : DyadicCube (n+1))
    (μ : Measure (Space (n+1))) (N B : ℕ) (p : CellPath (n+1))
    (a b : ℕ) (lam : ℝ) : ℝ :=
  ((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ)*
    ((2:ℝ)^N)^(sourceProfile Q μ N B p a-sourceProfile Q μ N B p b+
      2*(((n+1:ℕ):ℝ)+1)*lam)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisBase
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Base and induction for the finite weighted projection inequality -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

def twoCoordinateEquiv : (Fin 2 → X) ≃ (Fin 1 → X) × (Fin 1 → X) where
  toFun z := (eraseFinCoordinate 0 z,eraseFinCoordinate 1 z)
  invFun w := Fin.cons (w.2 0) (fun _ => w.1 0)
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineSubspaceFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for neighborhoods of lower-dimensional affine subspaces -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

def affineSubspaceNeighborhood (V : Submodule ℝ (Space d)) (a : Space d) (r : ℝ) :
    Set (Space d) := {x | ‖Vᗮ.starProjection (x-a)‖ ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PublishedHeavyPlates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published heavy-hyperplane cover used by the coarse-filter construction

P. Shmerkin, *A non-linear version of Bourgain's projection theorem*,
J. Eur. Math. Soc. 25 (2023), 4155--4204, Appendix B, Lemma B.3,
printed pages 4201--4202, DOI 10.4171/JEMS/1283.
Publisher PDF: https://ems.press/content/serial-article-files/32954 .

This is only the hyperplane case k=d-1, at the single scale used in the
application, with heavy threshold delta^(a/8192). The lower-dimensional
concentration hypothesis is retained explicitly. The conclusion covers
each heavy plate in the unit ball by one of finitely many thicker plates.
The constant is allowed to depend on the dimension, a and C. No assertion
about dyadic filters, retained product mass or distance sets is assumed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def PublishedHeavyHyperplanes : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a C : ℝ, 1/2 < a → a < 1 → 0 < C →
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (μ : ProbabilityMeasure (Space d)) (δ : ℝ),
      0 < δ → δ ≤ 1 →
      (∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ < 1) →
      (∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
        ∀ p : Space d, (μ : Measure (Space d)) (affineSubspaceNeighborhood V p δ) ≤
          ENNReal.ofReal (C*δ^a)) →
      ∃ S : Finset (Space d × ℝ),
        (∀ p ∈ S, ‖p.1‖ = 1) ∧ (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent a) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent a)) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ < 1 → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(a-2*heavyPlateExponent a)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyPlateCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual dyadic cell-pair exclusion generated by heavy affine plates -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def heavyPlateCellPairs (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j : ℕ) (r m : ℝ) : Set (Space d × Space d) := by
  classical
  exact ⋃ pq ∈ (cubePaths d j).product (cubePaths d j),
    if HeavyPlateHits ρ (Q.descendant pq.1) (Q.descendant pq.2) r m then
      (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier else ∅

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateFilter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decreasing coarse dyadic filters and their unnormalized fiber bounds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def coarsePlateFilter (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) : Set (Space d × Space d) :=
  (Q.carrier ×ˢ Q.carrier) \ ⋃ j ∈ Finset.Icc j₀ J, heavyPlateCellPairs ρ Q j (r j) (m j)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_CoarsePlateDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-radius directional slab estimate for each coarse filter -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

noncomputable def coarseDirectionalConstant {d : ℕ} (Q : DyadicCube d)
    (j₀ : ℕ) (b : ℝ) : ℝ :=
  coarseSlabConstant j₀ b*(2*max (Real.sqrt d*Q.side) 1)^b

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EuclideanRadialDensity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial densities and their comparison with full-line fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def euclideanRadialDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (x : Space (n+1)) (w : Sphere (n+1)) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^n) * a (x+r • (w : Space (n+1)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FinitePlateException
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite family of plates: exceptional intersections and clustering -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ}

noncomputable def slabPairException (S : Finset (Space d × ℝ)) (r τ : ℝ) : Set (Space d) :=
  ⋃ p ∈ S, ⋃ q ∈ S, if τ ≤ normalDistance p.1 q.1 then
    {x | |inner ℝ p.1 x-p.2| ≤ r ∧ |inner ℝ q.1 x-q.2| ≤ r} else ∅

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LatePlateTail
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The tail of all first-time plate exclusions has small product mass -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable def dyadicPlateExclusions {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (b : ℝ) (j : ℕ) : Set (Space d × Space d) :=
  heavyPlateCellPairs ρ Q j (plateScale j) (2*(plateScale j)^b)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LocalRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One level of measurable radial pruning and its original-law cost -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

noncomputable def levelRadialBad (μ : Measure (Space d)) (I : Finset ι)
    (Q : ι → Set (Space d)) (c : ι → Space d) (r D B W : ℝ) (F : ℝ≥0∞) :
    Set (Space d × Space d) :=
  nearPinPairs I Q c r ∪ ⋃ i ∈ I,
    troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F ∩ (Q i ×ˢ univ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MultilevelRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable surviving pair relation at finitely many radial levels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

noncomputable def multilevelRadialBad (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞) : Set (Space d × Space d) :=
  ⋃ j ∈ Finset.range J, levelRadialBad μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)

noncomputable def radialGoodPairs (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞) : Set (Space d × Space d) :=
  (Prod.swap ⁻¹' multilevelRadialBad μ J I Q c r D W B F)ᶜ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialBadWitness
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleting original pairs whose witness direction is exceptional -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialBadWitness (w₀ : Sphere d) (G : Set (Space d × Space d))
    (B : Set (Sphere d)) : Set (Space d × Space d) :=
  G ∩ {p | normalizeToSphere w₀ (p.2-p.1) ∈ B}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileCompactness
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness of normalized Lipschitz scale profiles -/

namespace Falconer
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal

def normalizedLipschitzProfiles (K : ℝ≥0) : Set BoundedProfile :=
  {f | f ⟨0,by constructor <;> norm_num⟩ = 0 ∧ LipschitzWith K f}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileUniformLimit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform limits of the actual real-variable profiles -/

namespace Falconer
open Set Filter Metric BoundedContinuousFunction
open scoped Topology NNReal

noncomputable def profileClamp (u : ℝ) : ProfileDomain :=
  ⟨max 0 (min u 1),le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩

@[simp] theorem profileClamp_val {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (profileClamp u : ℝ) = u := by
  simp only [profileClamp,min_eq_left hu.2,max_eq_right hu.1]

noncomputable def profileOfBounded (f : BoundedProfile) (u : ℝ) : ℝ := f (profileClamp u)

noncomputable def boundedProfileOfReal (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    BoundedProfile := mkOfCompact ⟨fun u => f u,hf.domRestrict⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_AffineSliceCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric coordinates and ball bounds on an actual charged affine plane -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

noncomputable def affineSliceMap (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) : Space n :=
  slicePointCoordinates V hn (x-p)

noncomputable def affineSliceModel (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) (x : Space n) : Space d :=
  p + ((sliceCoordinates V hn).symm x : Space d)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartPairAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair averaging on the original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartPairWeight (h : ℕ) (r : ℝ) (p q : Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (r^(-(h:ℝ))))^2 * gaussianRows (n+1) h
    {A | ∀ i, |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_EndpointSliceCosts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two concrete radial costs used in endpoint slice selection -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def endpointPairCost (ν : Measure (Space n)) (δ : ℝ)
    (G : Set (Space n × Space n)) (A : Fin h → Space (n+1)) : ℝ≥0∞ :=
  ((gaussianChartSliceMeasure ν A δ).prod (gaussianChartSliceMeasure ν A δ)) Gᶜ

noncomputable def endpointTripleCost (ν : Measure (Space n)) (δ W : ℝ)
    (G : Set (Space n × Space n)) (A : Fin h → Space (n+1)) : ℝ≥0∞ :=
  ((gaussianChartSliceMeasure ν A δ).prod
    ((gaussianChartSliceMeasure ν A δ).prod (gaussianChartSliceMeasure ν A δ)))
    (badChartTriples G W)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSpanRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian rows projected onto a fixed finite-dimensional span -/
namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def projectedGaussianRows (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) (A : Fin m → Space d) : Fin m → Space m :=
  fun i => b (V.orthogonalProjectionOnto (A i))

end Falconer

end OAI
end


