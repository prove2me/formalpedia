-- Prove2me | Definitions.Def_OAIQ073V000
-- name    : OAIQ073V000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:57:19.825666+00:00
-- url     : https://prove2.me/theorems/499018bc-a026-4a66-9409-1766cd6ca530
-- title:
--   Definitions bundle OAIQ073V000 of the split of OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 472 declarations of OpenAI's Lean: 452 definitions, 11 inductive types or structures, 2 instances and 7 theorems. The definitions and types are `OAI.RVM.BoundedClassicalPrefix`, `OAI.RVM.BoundedFlowRegularity`, `OAI.RVM.BoundedSpatiallySmoothSlab`, `OAI.RVM.C1ClassicalPrefix`, `OAI.RVM.ClassicalBefore`, `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.ConeKernelState`, `OAI.RVM.ConeParameters`, `OAI.RVM.CurvatureBound`, `OAI.RVM.CutoffState`, `OAI.RVM.DatumRestartControl`, `OAI.RVM.DirectOuterIndex`, `OAI.RVM.DirectionOverlap`, `OAI.RVM.DyadicBand`, `OAI.RVM.DyadicWindow`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.EquationsBefore`, `OAI.RVM.FieldControl`, `OAI.RVM.GlobalFieldBound`, `OAI.RVM.ImprovedWindow`, `OAI.RVM.InClosedConeBin`, `OAI.RVM.IncrementBootstrap`, `OAI.RVM.LocalParticleBound`, `OAI.RVM.Magnetic.coneLorentz`, `OAI.RVM.Magnetic.sourceAngularCore`, `OAI.RVM.Magnetic.sourceAngularProfile`, `OAI.RVM.Magnetic.sourceConeCoefficient`, `OAI.RVM.Magnetic.sourceDivisionBulk`, `OAI.RVM.Magnetic.sourceFixedCoefficient`, `OAI.RVM.Magnetic.sourceFixedFlux`, `OAI.RVM.Magnetic.sourceJointFlux`, `OAI.RVM.Magnetic.sourceReceiverKernel`, `OAI.RVM.Magnetic.sourceReceiverParticlePacket`, `OAI.RVM.Magnetic.sourceVelocityProfile`, `OAI.RVM.Magnetic.sourceWeightedPacket`, `OAI.RVM.Magnetic.transportAngularCore`, `OAI.RVM.Magnetic.transportConeCoefficient`, `OAI.RVM.Magnetic.transportSingularBulk`, `OAI.RVM.Magnetic.transportSingularShell` and 423 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `VlasovMaxwell_Continuation_Bootstrap`, `VlasovMaxwell_Continuation_GlobalContinuation`, `VlasovMaxwell_Continuation_IncrementBootstrap`, `VlasovMaxwell_Continuation_PrefixClamp`, `VlasovMaxwell_Continuation_PrefixMomentumForce`, `VlasovMaxwell_Continuation_PrefixParticle`, `VlasovMaxwell_Flow_ExtendedLorentz`, `VlasovMaxwell_Flow_FlowDerivative`, `VlasovMaxwell_Flow_HighFlow`, `VlasovMaxwell_Flow_LorentzPhase`, `VlasovMaxwell_Flow_PhaseAcceleration`, `VlasovMaxwell_Flow_PhaseHits`, `VlasovMaxwell_Flow_PhaseTimePullback`, `VlasovMaxwell_Flow_TransportDifferentiation`, `VlasovMaxwell_Flow_WithinFlow`, `VlasovMaxwell_Geometry_ActualCutoffCoordinates`, `VlasovMaxwell_Geometry_ActualLabelCutoffCost`, `VlasovMaxwell_Geometry_ArrivalDomain`, `VlasovMaxwell_Geometry_BallCutoff`, `VlasovMaxwell_Geometry_ClippedRamp`, `VlasovMaxwell_Geometry_ClosedBranchDomain`, `VlasovMaxwell_Geometry_CollisionLabels`, `VlasovMaxwell_Geometry_CrossCLM`, `VlasovMaxwell_Geometry_CutoffState`, `VlasovMaxwell_Geometry_ParticleBySpacetime`, `VlasovMaxwell_Geometry_PhysicalDivision`, `VlasovMaxwell_Geometry_PhysicalGeometryCutoffDensity`, `VlasovMaxwell_Geometry_QuadIndexEquiv`, `VlasovMaxwell_Geometry_RelativeAngleCoordinate`, `VlasovMaxwell_Geometry_SelectedRemainderPhysical`, `VlasovMaxwell_Geometry_ShiftedRho`, `VlasovMaxwell_Geometry_SpaceDiv`, `VlasovMaxwell_Geometry_Sphere`, `VlasovMaxwell_Geometry_UpperTimeCut`, `VlasovMaxwell_LocalPDE_EquationsBefore`, `VlasovMaxwell_LocalPDE_PicardBounds`, `VlasovMaxwell_LocalPDE_PicardContraction`, `VlasovMaxwell_LocalPDE_PicardCurvature`, `VlasovMaxwell_LocalPDE_RelativeCauchyConstant`, `VlasovMaxwell_LocalPDE_SlabEquations`, `VlasovMaxwell_LocalPDE_SlabRHS`, `VlasovMaxwell_LocalPDE_StrongLocalExistence`, `VlasovMaxwell_LocalPDE_VlasovConstruction`, `VlasovMaxwell_Maxwell_DifferenceFieldEnergy`, `VlasovMaxwell_Maxwell_ElectricBoundaryField`, `VlasovMaxwell_Maxwell_ExtendedField`, `VlasovMaxwell_Maxwell_WaveGradient`, `VlasovMaxwell_Maxwell_WaveK`, `VlasovMaxwell_Population_BinHits`, `VlasovMaxwell_Population_BulkSpatialUniform`, `VlasovMaxwell_Population_CentralOccupation`, `VlasovMaxwell_Population_DatumElectricFluxKernel`, `VlasovMaxwell_Population_DirectionCounts`, `VlasovMaxwell_Population_DirectionCutoffs`, `VlasovMaxwell_Population_DirectionOverlap`, `VlasovMaxwell_Population_DyadicBalanceConstant`, `VlasovMaxwell_Population_DyadicCut`, `VlasovMaxwell_Population_GoodCrossings`, `VlasovMaxwell_Population_GoodSharedEstimates`, `VlasovMaxwell_Population_HomogeneousCancellation`, `VlasovMaxwell_Population_InitialSignedBoundaryDensity`, `VlasovMaxwell_Population_LabelOccupation`, `VlasovMaxwell_Population_LabelWeight`, `VlasovMaxwell_Population_MagneticEstimates`, `VlasovMaxwell_Population_MomentumDirection`, `VlasovMaxwell_Population_NullConeFlux`, `VlasovMaxwell_Population_PartitionOccupation`, `VlasovMaxwell_Population_PhysicalBinPhaseSet`, `VlasovMaxwell_Population_ReceiverWeights`, `VlasovMaxwell_Population_RepresentativeCosts`, `VlasovMaxwell_Population_RetardedSameTimeSeparation`, `VlasovMaxwell_Population_SelectedDirection`, `VlasovMaxwell_Population_SelectedReceiverWeightBoundFinite`, `VlasovMaxwell_Population_SelectionCounts`, `VlasovMaxwell_Population_SelectionWeight`, `VlasovMaxwell_Population_SharedBudget`, `VlasovMaxwell_Population_SharedOccupation`, `VlasovMaxwell_Population_SignedRemainder`, `VlasovMaxwell_Population_SourceJointFlux`, `VlasovMaxwell_Population_SourceWeightedPacket`, `VlasovMaxwell_Population_SpatialEstimates`, `VlasovMaxwell_Population_TransportRemainder`, `VlasovMaxwell_Population_TransportSingularBulk`, `VlasovMaxwell_Population_UnselectedCover`, `VlasovMaxwell_Regularity_BoundaryJets`, `VlasovMaxwell_Regularity_CurvatureBounds`, `VlasovMaxwell_Regularity_EnergyBump`, `VlasovMaxwell_Regularity_NormalisedPartialCutoff`, `VlasovMaxwell_Regularity_ParamPrimitive`, `VlasovMaxwell_Regularity_PhysicalCutoffCoordinates`, `VlasovMaxwell_Regularity_PositiveExtension`, `VlasovMaxwell_Regularity_SlabEvolutionRegularity`, `VlasovMaxwell_Regularity_SlabL2`, `VlasovMaxwell_Regularity_SmoothIntegral`, `VlasovMaxwell_Regularity_SpatialJets`, `VlasovMaxwell_Retarded_AngularBump`, `VlasovMaxwell_Retarded_ArrivalConeKernelPolarNorm`, `VlasovMaxwell_Retarded_ConeArgument`, `VlasovMaxwell_Retarded_ConeEulerianIntegrand`, `VlasovMaxwell_Retarded_ConeForceSplit`, `VlasovMaxwell_Retarded_ConeKernelInterior`, `VlasovMaxwell_Retarded_ConeMotion`, `VlasovMaxwell_Retarded_ConeRadius`, `VlasovMaxwell_Retarded_ConeRegularity`, `VlasovMaxwell_Retarded_CutoffRateMajorant`, `VlasovMaxwell_Retarded_CutoffSourceTangent`, `VlasovMaxwell_Retarded_DirectForce`, `VlasovMaxwell_Retarded_DirectLargeAngularSharp`, `VlasovMaxwell_Retarded_DirectMixedCover`, `VlasovMaxwell_Retarded_ElectricConeBoundary`, `VlasovMaxwell_Retarded_InitialPuncturedCone`, `VlasovMaxwell_Retarded_MagneticMomentDensity`, `VlasovMaxwell_Retarded_PhysicalAngularBound`, `VlasovMaxwell_Retarded_PhysicalDirectTransportDensity`, `VlasovMaxwell_Retarded_PhysicalElectricKernel`, `VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity`, `VlasovMaxwell_Retarded_PicardKernel`, `VlasovMaxwell_Retarded_ReceiverQ`, `VlasovMaxwell_Retarded_ReceiverQCLM`, `VlasovMaxwell_Retarded_ReceiverRadialDomain`, `VlasovMaxwell_Retarded_RetardedMomentumForce`, `VlasovMaxwell_Retarded_RetardedPhaseDomain`, `VlasovMaxwell_Retarded_RetardedRadiusSeparatedClosed`, `VlasovMaxwell_Retarded_SelectedConeTransfer`, `VlasovMaxwell_Retarded_SourceCellLast`, `VlasovMaxwell_Retarded_SourceField`, `VlasovMaxwell_Retarded_SourceForceConeKernel`, `VlasovMaxwell_Retarded_SourceKernels`, `VlasovMaxwell_Retarded_SourceMajorant`, `VlasovMaxwell_Retarded_SourceVelocityProfile`, `VlasovMaxwell_Retarded_SourceWaveSpatialIbp`, `VlasovMaxwell_Retarded_SpaceConeDomain`, `VlasovMaxwell_Retarded_TransportAngularCore`, `VlasovMaxwell_Retarded_VolterraKernels`.
--
--   **Imports.** It imports the published bundle `Def_VlasovMaxwell`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ073V002`; the statements `OAI.RVM.Admissible.bulk_geometry_uniform`, `OAI.RVM.Admissible.bulk_rate_uniform`, `OAI_RVM_Admissible_bulk_receiver_uniform`, `OAI.RVM.Admissible.bulk_remainder_uniform`, `OAI.RVM.Admissible.bulk_selected_family_uniform`, `OAI_RVM_Admissible_bulk_signed_cost_uniform`, `OAI.RVM.Admissible.bulk_source_uniform`, `OAI.RVM.Admissible.bulk_spatial_uniform`, `OAI.RVM.Admissible.central_density_baseline_radial_sum`, `OAI.RVM.Admissible.central_density_low_receiver_log_sum`, `OAI.RVM.Admissible.central_density_small_sector_log_sum`, `OAI.RVM.Admissible.central_regular_uniform`, `OAI.RVM.Admissible.central_uniform`, `OAI.RVM.Admissible.direct_remaining_source_complete_uniform`, `OAI.RVM.Admissible.direct_remaining_source_deficit_short_uniform_expanded`, `OAI_RVM_Admissible_direct_remaining_source_large_uniform_expanded`, `OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded`, `OAI.RVM.Admissible.direct_remaining_transport_angular_expanded`, `OAI.RVM.Admissible.direct_source_absolute_uniform`, `OAI_RVM_Admissible_direct_source_all_radii`, `OAI.RVM.Admissible.direct_source_deficit_short_sum`, `OAI_RVM_Admissible_direct_source_general_large_sum`, `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.direct_source_physical_log_bound`, `OAI.RVM.Admissible.direct_source_relative_budget`, `OAI.RVM.Admissible.direct_source_relative_short_radial_sum`, `OAI_RVM_Admissible_direct_source_relative_short_radius`, `OAI.RVM.Admissible.direct_source_remaining_all_radii`, `OAI_RVM_Admissible_direct_source_remaining_large_sum`, `OAI_RVM_Admissible_direct_source_shared_radius_budget`, `OAI.RVM.Admissible.direct_source_shared_short_angles_expanded`, `OAI.RVM.Admissible.direct_source_small_all_radii`, `OAI.RVM.Admissible.direct_source_small_deficit_short_sum`, `OAI.RVM.Admissible.direct_source_two_budget_bound`, `OAI.RVM.Admissible.direct_transport_low_receiver_radii`, `OAI.RVM.Admissible.direct_transport_remaining_all_radii`, `OAI.RVM.Admissible.direct_transport_sharp_all_radii`, `OAI.RVM.Admissible.direct_transport_sharp_physical_log_bound`, `OAI.RVM.Admissible.direct_transport_uniform`, `OAI.RVM.Admissible.direction_closedEulerian_grid`, `OAI_RVM_Admissible_direction_closedEulerian_improved`, `OAI.RVM.Admissible.direction_complete_count_cost_bound`, `OAI.RVM.Admissible.direction_count_bound`, `OAI_RVM_Admissible_direction_family_moving_log_bound`, `OAI_RVM_Admissible_direction_family_weight_log_bound`, `OAI.RVM.Admissible.direction_physical_family_log_bound`, `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_remainder_label_log_bound`, `OAI.RVM.Admissible.direction_selected_bulk_log_bound`, `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_stable_closed_cell_bound`, `OAI.RVM.Admissible.direction_unselected_label_log_bound`, `OAI.RVM.Admissible.exists_bounded_direction_partition`, `OAI.RVM.Admissible.exists_stable_direction_partition`, `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform`, `OAI.RVM.Admissible.force_bulk_uniform`, `OAI.RVM.Admissible.geometry_cutoff_small_sector_log_sum`, `OAI.RVM.Admissible.good_regular_double_sum`, `OAI.RVM.Admissible.good_structural_uniform`, `OAI.RVM.Admissible.label_moving_primitive_near_constant`, `OAI.RVM.Admissible.label_projected_primitive_near_constant`, `OAI.RVM.Admissible.magnetic_low_uniform`, `OAI_RVM_Admissible_magnetic_regular_short_uniform`, `OAI.RVM.Admissible.magnetic_small_uniform`, `OAI.RVM.Admissible.projected_remainder_small_sector_log_sum`, `OAI.RVM.Admissible.projected_source_baseline_far`, `OAI_RVM_Admissible_projected_source_low_receiver_log_sum`, `OAI.RVM.Admissible.projected_source_near_real_bin`, `OAI.RVM.Admissible.projected_source_stable_far_log_sum`, `OAI.RVM.Admissible.projected_source_structural_edge_log_sum`, `OAI.RVM.Admissible.projected_source_two_budget_bound`, `OAI.RVM.Admissible.representative_large_shared_occupation`, `OAI.RVM.Admissible.representative_magnetic_large`, `OAI.RVM.Admissible.representative_pure_occupation`, `OAI.RVM.Admissible.representative_receiver_envelope`, `OAI.RVM.Admissible.representative_regular_central_shared`, `OAI.RVM.Admissible.representative_regular_good_structural_double_sum`, `OAI.RVM.Admissible.representative_regular_short_magnetic`, `OAI.RVM.Admissible.representative_shared_occupation`, `OAI.RVM.Admissible.selected_moving_bound`, `OAI.RVM.Admissible.selected_receiver_weight_bound`, `OAI.RVM.Admissible.selected_time_weight_uniform`, `OAI.RVM.Admissible.small_good_uniform`, `OAI.RVM.Admissible.small_source_absolute_uniform`, `OAI.RVM.Admissible.small_transport_regular_uniform`, `OAI.RVM.Admissible.small_transport_uniform`, `OAI.RVM.Admissible.source_majorant_large_radius`, `OAI.RVM.Admissible.source_majorant_relative_budget`, `OAI.RVM.Admissible.source_majorant_relative_short_radial_sum`, `OAI_RVM_Admissible_source_majorant_relative_short_radius`, `OAI.RVM.Admissible.source_majorant_remaining_all_radii`, `OAI.RVM.Admissible.source_majorant_remaining_large_sum`, `OAI.RVM.Admissible.source_majorant_remaining_log_sum`, `OAI_RVM_Admissible_source_majorant_remaining_radial_cover`, `OAI.RVM.Admissible.source_majorant_short_near_sum`, `OAI.RVM.Admissible.source_majorant_two_budget_bound`, `OAI_RVM_Admissible_spatial_structural_uniform`, `OAI.RVM.Admissible.spatial_transition_regular_uniform`, `OAI.RVM.Admissible.time_weight_bin_near`, `OAI.RVM.Admissible.uniform_actual_bin_Cauchy`, `OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy`, `OAI.RVM.Admissible.uniform_physical_population_increment`, `OAI_RVM_Admissible_unselected_good_uniform`, `OAI.RVM.Admissible.unselected_small_source_uniform`, `OAI.RVM.Admissible.unselected_source_uniform`, `OAI.RVM.Admissible.unselected_spatial_polynomial_cap`, `OAI.RVM.BoundedClassicalPrefix.paste`, `OAI.RVM.C1ClassicalPrefix.smooth`, `OAI.RVM.EnergyPrefix.goodFieldBudget_finite`, `OAI.RVM.EnergyPrefix.goodFieldBudget_uniform`, `OAI.RVM.EnergyPrefix.shared_magneticFieldBudget`, `OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound`, `OAI.RVM.Magnetic.magnetic_source_particle_gradient_volterra_bound`, `OAI.RVM.Magnetic.magnetic_transport_deriv_bound`, `OAI.RVM.PhaseFlowOn.actualLabelCutoffCost_integrable`, `OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkReceiver_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum`, `OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum`, `OAI.RVM.PhaseFlowOn.bulkSource_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkSource_cost_sum`, `OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_shared_budget`, `OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound`, `OAI.RVM.PhaseFlowOn.cutoff_label_integral_split`, `OAI.RVM.PhaseFlowOn.labelConeKernel_integrable`, `OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm`, `OAI.RVM.PhaseFlowOn.label_occupation_cell_bound`, `OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle`, `OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum`, `OAI.RVM.PhaseFlowOn.physicalBin_magneticField`, `OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude`, `OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer`, `OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound`, `OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable`, `OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le`, `OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable`, `OAI.RVM.PhaseFlowOn.stable_jointBudget_entry`, `OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split`, `OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum`, `OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound`, `OAI_RVM_SmoothClassicalPrefix_direct_lorentz_triangle_bound`, `OAI_RVM_SmoothClassicalPrefix_direction_force_family_triangle`, `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable`, `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_label`, `OAI.RVM.SmoothClassicalPrefix.physical_vectors`, `OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum`, `OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar`, `OAI.RVM.SmoothLorentzFlow.backward_derivative_tame`, `OAI.RVM.SmoothLorentzFlow.reversePath_derivatives_bound`, `OAI_RVM_bounded_momentum_field_bound`, `OAI.RVM.bounded_momentum_field_gradient_bound`, `OAI.RVM.bounded_momentum_particle_lipschitz_bound`, `OAI.RVM.bounded_momentum_second_jet_bound`, `OAI.RVM.bounded_momentum_uniform_restart`, `OAI.RVM.classical_electric_log_closed_bound`, `OAI.RVM.classical_fields_curvature_volterra_bound`, `OAI_RVM_classical_magnetic_log_closed_bound`, `OAI.RVM.classical_shifted_electric_physical_representation_before`, `OAI.RVM.classical_shifted_electric_potential_representation_before`, `OAI.RVM.classical_shifted_magnetic_physical_representation_before`, `OAI.RVM.constructed_maxwell_equations`, `OAI.RVM.datum_boundary_global_jets`, `OAI.RVM.datum_boundary_global_jets_horizon`, `OAI.RVM.electric_source_deriv_volterra_bound`, `OAI.RVM.electric_transport_deriv_bound`, `OAI.RVM.exists_local_spatially_smooth_bounded_classical`, `OAI.RVM.exists_picard_field_limit`, `OAI.RVM.exists_picard_regular`, `OAI.RVM.exists_smoothLorentzFlow`, `OAI.RVM.family_bounded_classical_prefix`, `OAI.RVM.family_global_picard_invariance`, `OAI.RVM.family_local_spatially_smooth_bounded_classical`, `OAI.RVM.family_picard_field_limit`, `OAI.RVM.global_classical_of_arbitrarily_long_prefixes`, `OAI.RVM.global_classical_of_uniform_prefix_momentum`, `OAI.RVM.integrated_electricMomentDensity_transport`, `OAI.RVM.integrated_magneticMomentDensity_actual_before`, `OAI.RVM.integrated_magneticMomentDensity_transport`, `OAI.RVM.local_c1_limit_of_picard`, `OAI.RVM.maxwell_timeContinuousL2`, `OAI.RVM.mixed_electric_physical_representation`, `OAI.RVM.mixed_magnetic_physical_representation`, `OAI.RVM.physicalProjectedSourceIntegral_le_majorant`, `OAI.RVM.physicalProjectedSource_integral_bound`, `OAI.RVM.physicalReceiverCutoff_near`, `OAI.RVM.physical_cone_derivative_tame`, `OAI.RVM.physical_fields_volterra`, `OAI.RVM.prefix_second_jet_volterra`, `OAI.RVM.prefix_spatial_gradient_volterra`, `OAI.RVM.remaining_stable_source_angular`, `OAI.RVM.selectedInitialKernel_integrable_bound`, `OAI.RVM.transported_comparison`, `OAI.RVM.transported_derivative_tame`, `OAI.RVM.transported_spatial_lipschitz` and `OAI.RVM.uniform_picard_sequence_jets`; the proofs of `OAI.RVM.Admissible.bulk_geometry_uniform`, `OAI.RVM.Admissible.bulk_rate_uniform`, `OAI_RVM_Admissible_bulk_receiver_uniform`, `OAI.RVM.Admissible.bulk_remainder_uniform`, `OAI.RVM.Admissible.bulk_selected_family_uniform`, `OAI_RVM_Admissible_bulk_signed_cost_uniform`, `OAI.RVM.Admissible.bulk_source_uniform`, `OAI.RVM.Admissible.bulk_spatial_uniform`, `OAI.RVM.Admissible.central_density_baseline_radial_sum`, `OAI.RVM.Admissible.central_density_low_receiver_log_sum`, `OAI.RVM.Admissible.central_density_small_sector_log_sum`, `OAI.RVM.Admissible.central_regular_uniform`, `OAI.RVM.Admissible.central_uniform`, `OAI.RVM.Admissible.direct_remaining_source_complete_uniform`, `OAI.RVM.Admissible.direct_remaining_source_deficit_short_uniform_expanded`, `OAI_RVM_Admissible_direct_remaining_source_large_uniform_expanded`, `OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded`, `OAI.RVM.Admissible.direct_remaining_transport_angular_expanded`, `OAI.RVM.Admissible.direct_source_absolute_uniform`, `OAI_RVM_Admissible_direct_source_all_radii`, `OAI.RVM.Admissible.direct_source_deficit_short_sum`, `OAI_RVM_Admissible_direct_source_general_large_sum`, `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.direct_source_physical_log_bound`, `OAI.RVM.Admissible.direct_source_relative_budget`, `OAI.RVM.Admissible.direct_source_relative_short_radial_sum`, `OAI_RVM_Admissible_direct_source_relative_short_radius`, `OAI.RVM.Admissible.direct_source_remaining_all_radii`, `OAI_RVM_Admissible_direct_source_remaining_large_sum`, `OAI_RVM_Admissible_direct_source_shared_radius_budget`, `OAI.RVM.Admissible.direct_source_shared_short_angles_expanded`, `OAI.RVM.Admissible.direct_source_small_all_radii`, `OAI.RVM.Admissible.direct_source_small_deficit_short_sum`, `OAI.RVM.Admissible.direct_source_two_budget_bound`, `OAI.RVM.Admissible.direct_transport_low_receiver_radii`, `OAI.RVM.Admissible.direct_transport_remaining_all_radii`, `OAI.RVM.Admissible.direct_transport_sharp_all_radii`, `OAI.RVM.Admissible.direct_transport_sharp_physical_log_bound`, `OAI.RVM.Admissible.direct_transport_uniform`, `OAI.RVM.Admissible.direction_closedEulerian_grid`, `OAI_RVM_Admissible_direction_closedEulerian_improved`, `OAI.RVM.Admissible.direction_complete_count_cost_bound`, `OAI.RVM.Admissible.direction_count_bound`, `OAI_RVM_Admissible_direction_family_moving_log_bound`, `OAI_RVM_Admissible_direction_family_weight_log_bound`, `OAI.RVM.Admissible.direction_physical_family_log_bound`, `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_remainder_label_log_bound`, `OAI.RVM.Admissible.direction_selected_bulk_log_bound`, `OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound`, `OAI.RVM.Admissible.direction_stable_closed_cell_bound`, `OAI.RVM.Admissible.direction_unselected_label_log_bound`, `OAI.RVM.Admissible.exists_bounded_direction_partition`, `OAI.RVM.Admissible.exists_stable_direction_partition`, `OAI.RVM.Admissible.force_bulk_uniform`, `OAI.RVM.Admissible.geometry_cutoff_small_sector_log_sum`, `OAI.RVM.Admissible.good_regular_double_sum`, `OAI.RVM.Admissible.good_structural_uniform`, `OAI.RVM.Admissible.label_moving_primitive_near_constant`, `OAI.RVM.Admissible.label_projected_primitive_near_constant`, `OAI.RVM.Admissible.magnetic_low_uniform`, `OAI_RVM_Admissible_magnetic_regular_short_uniform`, `OAI.RVM.Admissible.magnetic_small_uniform`, `OAI.RVM.Admissible.projected_remainder_small_sector_log_sum`, `OAI.RVM.Admissible.projected_source_baseline_far`, `OAI_RVM_Admissible_projected_source_low_receiver_log_sum`, `OAI.RVM.Admissible.projected_source_near_real_bin`, `OAI.RVM.Admissible.projected_source_stable_far_log_sum`, `OAI.RVM.Admissible.projected_source_structural_edge_log_sum`, `OAI.RVM.Admissible.projected_source_two_budget_bound`, `OAI.RVM.Admissible.representative_large_shared_occupation`, `OAI.RVM.Admissible.representative_magnetic_large`, `OAI.RVM.Admissible.representative_pure_occupation`, `OAI.RVM.Admissible.representative_receiver_envelope`, `OAI.RVM.Admissible.representative_regular_central_shared`, `OAI.RVM.Admissible.representative_regular_good_structural_double_sum`, `OAI.RVM.Admissible.representative_regular_short_magnetic`, `OAI.RVM.Admissible.representative_shared_occupation`, `OAI.RVM.Admissible.selected_moving_bound`, `OAI.RVM.Admissible.selected_receiver_weight_bound`, `OAI.RVM.Admissible.selected_time_weight_uniform`, `OAI.RVM.Admissible.small_good_uniform`, `OAI.RVM.Admissible.small_source_absolute_uniform`, `OAI.RVM.Admissible.small_transport_regular_uniform`, `OAI.RVM.Admissible.small_transport_uniform`, `OAI.RVM.Admissible.source_majorant_large_radius`, `OAI.RVM.Admissible.source_majorant_relative_budget`, `OAI.RVM.Admissible.source_majorant_relative_short_radial_sum`, `OAI_RVM_Admissible_source_majorant_relative_short_radius`, `OAI.RVM.Admissible.source_majorant_remaining_all_radii`, `OAI.RVM.Admissible.source_majorant_remaining_large_sum`, `OAI.RVM.Admissible.source_majorant_remaining_log_sum`, `OAI_RVM_Admissible_source_majorant_remaining_radial_cover`, `OAI.RVM.Admissible.source_majorant_short_near_sum`, `OAI.RVM.Admissible.source_majorant_two_budget_bound`, `OAI_RVM_Admissible_spatial_structural_uniform`, `OAI.RVM.Admissible.spatial_transition_regular_uniform`, `OAI.RVM.Admissible.time_weight_bin_near`, `OAI.RVM.Admissible.uniform_actual_bin_Cauchy`, `OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy`, `OAI.RVM.Admissible.uniform_physical_population_increment`, `OAI_RVM_Admissible_unselected_good_uniform`, `OAI.RVM.Admissible.unselected_small_source_uniform`, `OAI.RVM.Admissible.unselected_source_uniform`, `OAI.RVM.Admissible.unselected_spatial_polynomial_cap`, `OAI.RVM.BoundedClassicalPrefix.paste`, `OAI.RVM.C1ClassicalPrefix.smooth`, `OAI.RVM.EnergyPrefix.goodFieldBudget_finite`, `OAI.RVM.EnergyPrefix.goodFieldBudget_uniform`, `OAI.RVM.EnergyPrefix.shared_magneticFieldBudget`, `OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound`, `OAI.RVM.Magnetic.magnetic_source_particle_gradient_volterra_bound`, `OAI.RVM.Magnetic.magnetic_transport_deriv_bound`, `OAI.RVM.PhaseFlowOn.actualLabelCutoffCost_integrable`, `OAI.RVM.PhaseFlowOn.bulkGeometry_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkReceiver_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkReceiver_selected_sum`, `OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum`, `OAI.RVM.PhaseFlowOn.bulkSource_bin_integral`, `OAI.RVM.PhaseFlowOn.bulkSource_cost_sum`, `OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_crude_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_joint_large_budget`, `OAI.RVM.PhaseFlowOn.closedEulerian_shared_budget`, `OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound`, `OAI.RVM.PhaseFlowOn.cutoff_label_integral_split`, `OAI.RVM.PhaseFlowOn.labelConeKernel_integrable`, `OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm`, `OAI.RVM.PhaseFlowOn.label_occupation_cell_bound`, `OAI.RVM.PhaseFlowOn.partialCutoffLabelCost_triangle`, `OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum`, `OAI.RVM.PhaseFlowOn.physicalBin_magneticField`, `OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude`, `OAI.RVM.PhaseFlowOn.selectedConeTriangle_norm_transfer`, `OAI.RVM.PhaseFlowOn.selectedMultiplierCosts_family_bound`, `OAI.RVM.PhaseFlowOn.selectedMultiplier_integrable`, `OAI.RVM.PhaseFlowOn.selectedSourceTriangle_majorant_le`, `OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable`, `OAI.RVM.PhaseFlowOn.stable_jointBudget_entry`, `OAI.RVM.PhaseFlowOn.unselected_force_label_integral_split`, `OAI.RVM.PhaseFlowOn.unselected_source_label_physical_sum`, `OAI_RVM_SmoothClassicalPrefix_direct_lorentz_triangle_bound`, `OAI_RVM_SmoothClassicalPrefix_direction_force_family_triangle`, `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_integrable`, `OAI.RVM.SmoothClassicalPrefix.multiplier_retarded_force_label`, `OAI.RVM.SmoothClassicalPrefix.physical_vectors`, `OAI.RVM.SmoothClassicalPrefix.representativeJointEnergy_sum`, `OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar`, `OAI.RVM.SmoothLorentzFlow.backward_derivative_tame`, `OAI.RVM.SmoothLorentzFlow.reversePath_derivatives_bound`, `OAI_RVM_bounded_momentum_field_bound`, `OAI.RVM.bounded_momentum_field_gradient_bound`, `OAI.RVM.bounded_momentum_particle_lipschitz_bound`, `OAI.RVM.bounded_momentum_second_jet_bound`, `OAI.RVM.bounded_momentum_uniform_restart`, `OAI.RVM.classical_electric_log_closed_bound`, `OAI.RVM.classical_fields_curvature_volterra_bound`, `OAI_RVM_classical_magnetic_log_closed_bound`, `OAI.RVM.classical_shifted_electric_physical_representation_before`, `OAI.RVM.classical_shifted_electric_potential_representation_before`, `OAI.RVM.classical_shifted_magnetic_physical_representation_before`, `OAI.RVM.constructed_maxwell_equations`, `OAI.RVM.datum_boundary_global_jets`, `OAI.RVM.datum_boundary_global_jets_horizon`, `OAI.RVM.electric_source_deriv_volterra_bound`, `OAI.RVM.electric_transport_deriv_bound`, `OAI.RVM.exists_local_spatially_smooth_bounded_classical`, `OAI.RVM.exists_picard_field_limit`, `OAI.RVM.exists_picard_regular`, `OAI.RVM.exists_smoothLorentzFlow`, `OAI.RVM.family_bounded_classical_prefix`, `OAI.RVM.family_global_picard_invariance`, `OAI.RVM.family_local_spatially_smooth_bounded_classical`, `OAI.RVM.family_picard_field_limit`, `OAI.RVM.global_classical_of_arbitrarily_long_prefixes`, `OAI.RVM.global_classical_of_uniform_prefix_momentum`, `OAI.RVM.global_classical_solution`, `OAI.RVM.integrated_electricMomentDensity_transport`, `OAI.RVM.integrated_magneticMomentDensity_actual_before`, `OAI.RVM.integrated_magneticMomentDensity_transport`, `OAI.RVM.local_c1_limit_of_picard`, `OAI.RVM.maxwell_timeContinuousL2`, `OAI.RVM.mixed_electric_physical_representation`, `OAI.RVM.mixed_magnetic_physical_representation`, `OAI.RVM.physicalProjectedSourceIntegral_le_majorant`, `OAI.RVM.physicalProjectedSource_integral_bound`, `OAI.RVM.physicalReceiverCutoff_near`, `OAI.RVM.physical_cone_derivative_tame`, `OAI.RVM.physical_fields_volterra`, `OAI.RVM.prefix_second_jet_volterra`, `OAI.RVM.prefix_spatial_gradient_volterra`, `OAI.RVM.remaining_stable_source_angular`, `OAI.RVM.selectedInitialKernel_integrable_bound`, `OAI.RVM.transported_comparison`, `OAI.RVM.transported_derivative_tame`, `OAI.RVM.transported_spatial_lipschitz` and `OAI.RVM.uniform_picard_sequence_jets`.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_VlasovMaxwell

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_FlowDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal

open Set MeasureTheory

namespace RVM

def determinantMultilinear (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def endomorphismMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) : (E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ :=
  ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma dot_eq_inner (a b : Vec) : dot a b = inner ℝ a b := by
  simp [dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma dot_self (a : Vec) : dot a a = ‖a‖ ^ 2 := by
  rw [dot_eq_inner, real_inner_self_eq_norm_sq]

def coneMotion (a u n : Vec) : Vec :=
  ((1 - dot n u) / (1 - dot n a)) • (a - n) + n - u

def signedPrimitive (a u n : Vec) : Vec :=
  u - ((1 - dot a u) / (1 - dot n a)) • n

def signedPrimitiveRate (a u n a' u' n' : Vec) : Vec :=
  u' - (((1 - dot a u) / (1 - dot n a)) • n' +
    ((-(dot a u' + dot a' u) * (1 - dot n a) +
        (1 - dot a u) * (dot n a' + dot n' a)) / (1 - dot n a) ^ 2) • n)

def retardedPrimitive (r : ℝ) (a u n : Vec) : Vec :=
  (r * (1 - dot n u))⁻¹ • signedPrimitive a u n

def retardedPrimitiveRate (r : ℝ) (a u n : Vec) (r' : ℝ) (a' u' n' : Vec) : Vec :=
  (r * (1 - dot n u))⁻¹ • signedPrimitiveRate a u n a' u' n' +
  (-(r' * (1 - dot n u) - r * (dot n u' + dot n' u)) /
    (r * (1 - dot n u)) ^ 2) • signedPrimitive a u n

def coneTransform (a n b : Vec) : Vec := b + (dot a b / (1 - dot n a)) • n

def sourceVelocityRate (u n u' : Vec) : Vec :=
  (1 - dot n u)⁻¹ • u' + (dot n u' / (1 - dot n u)^2) • (u - n)

def signedForceKernel (r : ℝ) (a u n u' : Vec) : Vec :=
  -(r⁻¹ • coneTransform a n (sourceVelocityRate u n u')) -
    ((1 - dot u u) / (r^2 * (1 - dot n u))) •
      coneTransform a n ((1 - dot n u)⁻¹ • (u - n))

def squaredCone (X Y : ℝ → Vec) (z : ℝ × ℝ) : ℝ :=
  (z.2-z.1)^2 - ‖X z.2 - Y z.1‖^2

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma cross_dot_square (a b : Vec) :
    dot (cross a b) (cross a b) = dot a a * dot b b - (dot a b)^2 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma norm_cross_le (a b : Vec) : ‖cross a b‖ ≤ ‖a‖*‖b‖ := by
  have h := cross_dot_square a b
  simp only [dot_self] at h
  nlinarith [norm_nonneg (cross a b), norm_nonneg a, norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b), sq_nonneg (dot a b)]

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

def particleBySpacetime (f : Particle) : (ℝ × Vec) × Vec → ℝ :=
  fun z => f (z.1.1,z.1.2,z.2)

def particleEnergy (s : Solution) (p : ℝ × Vec) : ℝ :=
  ∫ v : Vec, q v * s.f (p.1,p.2,v)

def particleFlux (s : Solution) (p : ℝ × Vec) : Vec :=
  ∫ v : Vec, s.f (p.1,p.2,v) • v

def totalEnergy (s : Solution) (p : ℝ × Vec) : ℝ :=
  (‖s.E p‖^2 + ‖s.B p‖^2)/2 + particleEnergy s p

def totalFlux (s : Solution) (p : ℝ × Vec) : Vec :=
  cross (s.E p) (s.B p) + particleFlux s p

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_LorentzPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory
open scoped ContDiff

namespace RVM

def lorentzPhase (E B : Vec → Vec) (z : Phase) : Phase :=
  (velocity z.2, E z.1 + cross (velocity z.2) (B z.1))

end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace RVM

def cutLorentz (E B : Field) (χ : Vec → ℝ) (p : ℝ × Phase) : Phase :=
  (velocity p.2.2, χ p.2.1 • (E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ExtendedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

def lorentzField (E B : Field) (z : ℝ × Phase) : Phase :=
  lorentzPhase (fun x => E (z.1,x)) (fun x => B (z.1,x)) z.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_WithinFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

section WithinFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spaceDerivative (f : ℝ × E → E) (z : ℝ × E) : E →L[ℝ] E :=
  fderiv ℝ (fun x => f (z.1,x)) z.2

def withinVariationalField (f : ℝ × E → E) (χ : (E →L[ℝ] E) → ℝ)
    (z : ℝ × (E × (E →L[ℝ] E))) : E × (E →L[ℝ] E) :=
  (f (z.1,z.2.1),χ z.2.2 • (spaceDerivative f (z.1,z.2.1)).comp z.2.2)

end WithinFlow

lemma cross_smul_right (a b : Vec) (c : ℝ) : cross a (c • b) = c • cross a b := by
  ext i
  fin_cases i <;> simp [cross] <;> ring


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def timeFlowDerivative (v : E) (A : E →L[ℝ] E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A)

omit [FiniteDimensional ℝ E] in

def inversePhase (α : E → ℝ → E) (z : ℝ × E) : E := Function.invFun (α · z.1) z.2

end

open Set MeasureTheory Filter
open scoped Topology ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


structure PhaseFlowOn (E B : Field) (T : ℝ) where
  flow : Phase → ℝ → Phase
  differential : Phase → ℝ → (Phase →L[ℝ] Phase)
  initial : ∀ z, flow z 0 = z
  ode : ∀ z t, t ∈ Icc 0 T →
    HasDerivWithinAt (flow z) (lorentzField E B (t,flow z t)) (Icc 0 T) t
  label : ∀ z t, t ∈ Icc 0 T → HasFDerivAt (flow · t) (differential z t) z
  det_one : ∀ z t, t ∈ Icc 0 T → (differential z t).det=1
  joint : ∀ z t, t ∈ Ioo 0 T → HasStrictFDerivAt (fun p : ℝ × Phase => flow p.2 p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,flow z t))).coprod
        (differential z t)) (t,z)
  bijective : ∀ t, t ∈ Icc 0 T → Function.Bijective (flow · t)

instance phaseVolume_isAddHaarMeasure : (volume : Measure Phase).IsAddHaarMeasure := by
  change (volume.prod volume : Measure Phase).IsAddHaarMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


open Set MeasureTheory Filter
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverRadialDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def receiverRadialDomain (s T : ℝ) : Set Vec := {w | 0 < ‖w‖ ∧ s+‖w‖ < T}

def receiverRadial (α : Phase → ℝ → Phase) (z : Phase) (s : ℝ) (w : Vec) : Vec :=
  (α z (s+‖w‖)).1-w

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CollisionLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def collisionLabels (α : Phase → ℝ → Phase) (z : Phase) (T : ℝ) : Set Phase :=
  {y | ∃ t ∈ Ioo 0 T, (α y t).1 = (α z t).1}

def collisionChart (α : Phase → ℝ → Phase) (z : Phase) (p : ℝ × Vec) : Phase :=
  inversePhase α (p.1, (α z p.1).1, p.2)

def branchDomain (α : Phase → ℝ → Phase) (zX zY : Phase) (T : ℝ) : Set ℝ :=
  {s | s ∈ Ioo 0 T ∧ s+‖(α zX T).1-(α zY s).1‖ < T}

def branchTime (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ t, t ∈ Icc s T ∧ t-s=‖(α zX t).1-(α zY s).1‖ then h.choose else 0

def branchRate (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : ℝ :=
  let τ := branchTime α zX zY T s
  let n := (τ-s)⁻¹ • ((α zX τ).1-(α zY s).1)
  (1-dot n (velocity (α zY s).2))/(1-dot n (velocity (α zX τ).2))

end RVM
end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def jointBranchDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Phase) :=
  {p | p.1 ∈ branchDomain α zX p.2 T ∧ (α zX p.1).1 ≠ (α p.2 p.1).1}

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

def energyBump : ContDiffBump (0 : Vec) := ⟨1,2,by norm_num,by norm_num⟩
def energyCutoff (n : ℕ) (x : Vec) : ℝ := energyBump (((n:ℝ)+1)⁻¹ • x)

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

def RegularParticle (f : Particle) : Prop :=
  ContDiffOn ℝ 1 f particleHalfSpace ∧
    CompactOnFiniteHorizons ⟨f,0,0⟩

def particleMoment {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Particle) (w : Vec → W) (p : ℝ × Vec) : W :=
  ∫ v : Vec, f (p.1,p.2,v) • w v

def squareDifference (s₁ s₂ : Solution) : Particle :=
  fun z => (s₁.f z-s₂.f z)^2/2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_Sphere
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology NNReal

namespace RVM
abbrev Sphere := sphere (0 : Vec) 1
abbrev sphereMeasure : Measure Sphere := (volume : Measure Vec).toSphere

end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def labelOccupation (f₀ : Phase → ℝ) (H : Phase → Set ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (f₀ z) * volume (H z)

def branchDirection (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : Vec :=
  let t := branchTime α zX zY T s
  (t-s)⁻¹ • ((α zX t).1-(α zY s).1)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def initialConeLabels (t : ℝ) (x : Vec) : Set Phase := {z | ‖x-z.1‖ < t}

def VlasovOn (f : Particle) (E B : Field) (T : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 T, ∀ x v,
    deriv (fun r => f (r,x,v)) t +
      (∑ i : Fin 3, velocity v i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, (E (t,x)+cross (velocity v) (B (t,x))) i *
        spatialPartial (fun w => f (t,x,w)) v i) = 0

end RVM
end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

structure EnergyPrefix (s : Solution) (T : ℝ) : Prop where
  f_smooth : ContDiffOn ℝ 1 s.f (Icc 0 T ×ˢ (univ : Set Phase))
  E_smooth : ContDiffOn ℝ 1 s.E (Icc 0 T ×ˢ (univ : Set Vec))
  B_smooth : ContDiffOn ℝ 1 s.B (Icc 0 T ×ˢ (univ : Set Vec))
  nonnegative : ∀ t ∈ Icc 0 T, ∀ z, 0 ≤ s.f (t,z)
  E_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.E (t,x))
  B_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.B (t,x))
  compact : ∃ K : Set Phase, IsCompact K ∧ ∀ t ∈ Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K
  vlasov : VlasovOn s.f s.E s.B T
  maxwell : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun r => s.E (r,x)) t - curl (fun y => s.B (t,y)) x = -current (fun z => s.f (t,z)) x ∧
    deriv (fun r => s.B (r,x)) t + curl (fun y => s.E (t,y)) x = 0

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def phaseHits (α : Phase → ℝ → Phase) (T : ℝ) (H : Set (ℝ × Phase)) : Set (ℝ × Phase) :=
  {p | p.1 ∈ Ioo 0 T ∧ (p.1,α p.2 p.1) ∈ H}

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SpaceConeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def spaceConeDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Phase) :=
  {p | p.1 ∈ Ioo 0 T ∧ p.2.1 ∈ ball (α zX T).1 (T-p.1)}

def coneOccupation (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (f : Particle) (H : Set (ℝ × Phase)) : ENNReal :=
  ∫⁻ s in Ioo (0 : ℝ) T, ∫⁻ n : Sphere, ∫⁻ r in Ioo (0 : ℝ) (T-s),
    ENNReal.ofReal (r^2*(1-dot n.1 (velocity (α zX (s+r)).2))) *
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (f p))
        (s,((α zX (s+r)).1-r • n.1,v)) ∂volume ∂volume ∂sphereMeasure

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ArrivalDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def arrivalDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Vec) :=
  {p | p.1 ∈ Ioo 0 T ∧ p.1+‖(α zX T).1-p.2‖<T ∧ (α zX p.1).1≠p.2}

def arrivalLabel (α : Phase → ℝ → Phase) (p : ℝ × Vec) : ℝ × Phase :=
  (p.1,inversePhase α (p.1,(p.2,0)))

def arrivalTime (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : ℝ :=
  branchTime α zX (arrivalLabel α p).2 T p.1

def arrivalRadius (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : ℝ :=
  arrivalTime α zX T p-p.1

def arrivalDirection (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : Vec :=
  (arrivalRadius α zX T p)⁻¹ • ((α zX (arrivalTime α zX T p)).1-p.2)

def arrivalVelocity (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : Vec :=
  velocity (α zX (arrivalTime α zX T p)).2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def coneArgument (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  ((T-p.1)^2 - ‖p.2-x₀‖^2)/ε

def coneCutoff (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  Real.smoothTransition (coneArgument T ε x₀ p)

def coneShellFlux (s : Solution) (T ε : ℝ) (x₀ : Vec) (p : ℝ × Vec) : ℝ :=
  (2/ε)*deriv Real.smoothTransition (coneArgument T ε x₀ p) *
    ((T-p.1)*totalEnergy s p + ⟪p.2-x₀,totalFlux s p⟫)

def radialConeWeight (R ε r : ℝ) : ℝ :=
  (2*r/ε)*deriv Real.smoothTransition ((R^2-r^2)/ε)

def radialConeProfile (s : Solution) (t R : ℝ) (x₀ : Vec) (r : ℝ) (n : Sphere) : ℝ :=
  r * (R*totalEnergy s (t,x₀+r • n.1) + r*⟪n.1,totalFlux s (t,x₀+r • n.1)⟫)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def ballCutoff (R ε : ℝ) (x : Vec) : ℝ :=
  Real.smoothTransition ((R^2-‖x‖^2)/ε)

end RVM
end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def sphereSum (g : Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  ∫ n : Sphere, g (p.2+p.1 • n.1) ∂sphereMeasure

def laplace (g : Vec → ℝ) : Vec → ℝ := divergence (gradient g)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SignedRemainder
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

def signedRemainder (r : ℝ) (a u n aₜ : Vec) : Vec :=
  ((1-dot a u)/(r^2*(1-dot n a)^2)) •
    (((1-dot a a)/(1-dot n a)) • n-a) +
  (dot aₜ (signedPrimitive a u n)/(r*(1-dot n a)^2)) • n

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseAcceleration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def phaseAcceleration (E B : Field) (α : Phase → ℝ → Phase) (z : Phase) (t : ℝ) : Vec :=
  fderiv ℝ velocity (α z t).2 (E (t,(α z t).1)+cross (velocity (α z t).2) (B (t,(α z t).1)))

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace RVM

def DyadicWindow (k n : ℕ) (x : ℝ) : Prop :=
  1/(2:ℝ)^k ≤ (2:ℝ)^n*x ∧ (2:ℝ)^n*x ≤ (2:ℝ)^k

def sameTimeBudgetSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (n : ℕ × ℕ) : Set (ℝ × Phase) :=
  {p | p.1∈Ioo 0 T ∧ DyadicWindow k n.1 (q p.2.2)⁻¹ ∧
    DyadicWindow k n.2 ‖velocity p.2.2-velocity (α zX p.1).2‖}

def arrivalFinalDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Vec) :=
  {p | p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-p.2‖=T}

def arrivalBudgetSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (n : ℕ × ℕ) : Set (ℝ × Phase) :=
  {p | DyadicWindow k n.1 (q p.2.2)⁻¹ ∧
    (( (p.1,p.2.1)∈arrivalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot (arrivalDirection α zX T (p.1,p.2.1))
        (arrivalVelocity α zX T (p.1,p.2.1)))/2))) ∨
    ((p.1,p.2.1)∈arrivalFinalDomain α zX T ∧
      DyadicWindow k n.2 (Real.sqrt ((1-dot ((T-p.1)⁻¹ • ((α zX T).1-p.2.1))
        (velocity (α zX T).2))/2))))}

def prefixPhaseEnergy (s : Solution) (T : ℝ) : ℝ × Phase → ℝ≥0∞ :=
  (Icc 0 T ×ˢ (univ : Set Phase)).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p))

def jointEnergyBudget (s : Solution) (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (a b I : ℝ) (n : ℕ × ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
    (sameTimeBudgetSet α zX T k n).indicator (prefixPhaseEnergy s T) (t,z)+
    (arrivalBudgetSet α zX T k n).indicator (prefixPhaseEnergy s T) (t,z)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def prefixClamp (T t : ℝ) : ℝ := max 0 (min T t)

def prefixFlow (α : Phase → ℝ → Phase) (T : ℝ) (z : Phase) (t : ℝ) : Phase :=
  α z (prefixClamp T t)

structure ClosedConeBin where
  (rmin rmax qmin qmax wmin wmax dmin dmax Dmin Dmax emin emax : ℝ)

def InClosedConeBin (α : Phase → ℝ → Phase) (zX : Phase) (B : ClosedConeBin)
    (t r : ℝ) (z : Phase) : Prop :=
  let R := t-r
  let Δ := (α zX t).1-(α z r).1
  let u := velocity (α z r).2
  let a := velocity (α zX t).2
  R=‖Δ‖ ∧ R∈Icc B.rmin B.rmax ∧ q (α z r).2∈Icc B.qmin B.qmax ∧
    q (α zX t).2∈Icc B.wmin B.wmax ∧
    R-dot Δ u∈Icc (R*B.dmin) (R*B.dmax) ∧
    R-dot Δ a∈Icc (R*B.Dmin) (R*B.Dmax) ∧
    1-dot a u∈Icc B.emin B.emax

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_IncrementBootstrap
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def IncrementBootstrap (V : ℝ → Vec) (T M A P L : ℝ) : Prop :=
  ∀ (n : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ T →
    (∀ t ∈ Icc a b, (2 : ℝ)^n/8 ≤ q (V t) ∧ q (V t) ≤ 8*(2 : ℝ)^n) →
    ‖V b-V a‖ ≤ M*P*Real.sqrt (b-a)+A*(b-a)*(P^2*L/(2 : ℝ)^n)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalElectricKernel
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

def physicalElectricKernel (r : ℝ) (n u b : Vec) : Vec :=
  ((1-dot u u)/(r^2*(1-dot n u)^3)) • (n-u) +
    (r*(1-dot n u)^3)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b)

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedSameTimeSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) : Set Vec :=
  {v | q v ∈ Icc B.qmin B.qmax ∧ 1-dot n (velocity v) ∈ Icc B.dmin B.dmax ∧
    1-dot a (velocity v) ∈ Icc B.emin B.emax}

def physicalBinDensity (s : Solution) (X V : ℝ → Vec) (B : ClosedConeBin)
    (t r : ℝ) (n : Sphere) : ℝ≥0∞ :=
  ∫⁻ v in coneBinMomentumSet B n.1 (velocity (V t)),
    ENNReal.ofReal (s.f (r,(X t-(t-r) • n.1,v)))

abbrev ConeCoordinate := ℝ × ℝ × Sphere

def physicalBinBase (V : ℝ → Vec) (B : ClosedConeBin) (J : Set ℝ) : Set ConeCoordinate :=
  {z | z.1 ∈ J ∧ z.2.1 ∈ Icc 0 z.1 ∧ z.1-z.2.1 ∈ Icc B.rmin B.rmax ∧
    q (V z.1) ∈ Icc B.wmin B.wmax ∧
    1-dot z.2.2.1 (velocity (V z.1)) ∈ Icc B.Dmin B.Dmax}

def physicalBinMeasure (V : ℝ → Vec) (B : ClosedConeBin) (J : Set ℝ) : Measure ConeCoordinate :=
  (volume.prod (volume.prod sphereMeasure)).restrict (physicalBinBase V B J)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

def nullConeFlux (s : Solution) (T : ℝ) (x₀ : Vec) (t : ℝ) (n : Sphere) : ℝ :=
  (T-t)^2 * (totalEnergy s (t,x₀-(T-t) • n.1) -
    dot n.1 (totalFlux s (t,x₀-(T-t) • n.1)))

def goodConeDensity (s : Solution) (p : ℝ × Vec) (n : Vec) : ℝ :=
  (‖s.E p + cross n (s.B p)‖ + |dot n (s.B p)|)^2 +
    (particleEnergy s p - dot n (particleFlux s p))

def velocityProjection (u b : Vec) : Vec := b - dot u b • u

def goodField (E B n : Vec) : ℝ := ‖E+cross n B‖+|dot n B|

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceCellLast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

namespace RVM

def sourceCellLast (T len : ℝ) : ℕ := ⌊T/len⌋₊
def sourceCellLo (len : ℝ) (i : ℕ) : ℝ := i*len
def sourceCellHi (T len : ℝ) (i : ℕ) : ℝ := min T ((i+1:ℕ)*len)

def selectedSourceCells (T len a b r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (sourceCellLast T len+1)).filter fun i =>
    sourceCellLo len i ≤ b ∧ a-r ≤ sourceCellHi T len i

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def goodFieldConeMass (s : Solution) (t : ℝ) (x : Vec) : ℝ≥0∞ :=
  ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
    ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,x-(t-r) • n.1))
      (s.B (r,x-(t-r) • n.1)) n.1^2) ∂sphereMeasure

def goodConeIntegrand (s : Solution) (t : ℝ) (x : Vec) (r : ℝ) (n : Sphere) : ℝ :=
  (t-r)^2 * goodConeDensity s (r,x-(t-r) • n.1) n.1

def receiverAngularSet (a : ℝ → Vec) (k j : ℕ) (t : ℝ) : Set Sphere :=
  {n | DyadicWindow k j (Real.sqrt ((1-dot n.1 (a t))/2))}

def goodFieldBinConeMass (s : Solution) (X a : ℝ → Vec) (k j : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
    (receiverAngularSet a k j t).indicator (fun n =>
      ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
        (s.B (r,X t-(t-r) • n.1)) n.1^2)) n ∂sphereMeasure

def goodFieldBudget (s : Solution) (X a : ℝ → Vec) (k : ℕ) (lo hi I : ℝ) (j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, goodFieldBinConeMass s X a k j t

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def arrivalAngularSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k j : ℕ) : Set (ℝ × Vec) :=
  {p | (p∈arrivalDomain α zX T ∧
      DyadicWindow k j (Real.sqrt ((1-dot (arrivalDirection α zX T p)
        (arrivalVelocity α zX T p))/2))) ∨
    (p∈arrivalFinalDomain α zX T ∧
      DyadicWindow k j (Real.sqrt ((1-dot ((T-p.1)⁻¹ • ((α zX T).1-p.2))
        (velocity (α zX T).2))/2)))}

def magneticFieldBudget (s : Solution) (α : Phase → ℝ → Phase) (zX : Phase)
    (T : ℝ) (k : ℕ) (lo hi I : ℝ) (j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, ∫⁻ x : Vec,
    (arrivalAngularSet α zX T k j).indicator (fun p => ENNReal.ofReal (‖s.B p‖^2)) (t,x)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def prefixParticle (s : Solution) (T : ℝ) (p : ℝ × Phase) : ℝ :=
  s.f (prefixClamp T p.1,p.2)

def prefixField (E : Field) (T : ℝ) (p : ℝ × Vec) : Vec :=
  E (prefixClamp T p.1,p.2)

def prefixConeGood (s : Solution) (T : ℝ) (X : ℝ → Vec) (z : ConeCoordinate) : ℝ :=
  goodField (prefixField s.E T (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (prefixField s.B T (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQ
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def receiverQ (a n h : Vec) : Vec := (1-dot n a) • h + dot a h • n

def sourceNumerator (n u b : Vec) : Vec := (dot n b) • (n-u)-(1-dot n u) • b

def transverseProjection (w h : Vec) : Vec := velocityProjection (‖w‖⁻¹ • w) h

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BinHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


def closedBinHits (α : Phase → ℝ → Phase) (zX : Phase) (B : ClosedConeBin)
    (S : Set Phase) (a b c d : ℝ) (z : Phase) : Set ℝ :=
  {r | z∈S ∧ r∈Icc c d ∧ ∃ t∈Icc a b, InClosedConeBin α zX B t r z}



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


def closedBinEulerian (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (B : ClosedConeBin) (S : Set Phase) (a b c d : ℝ) : Set (ℝ × Phase) :=
  (fun p : ℝ × Phase => (p.1,prefixFlow α T p.2 p.1)) ''
    {p : ℝ × Phase | p.1∈closedBinHits α zX B S a b c d p.2}
      ∩ spaceConeDomain α zX T



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


open Set MeasureTheory
open scoped ENNReal


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeEulerianIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def coneEulerianIntegrand (s : Solution) (T : ℝ) (X V : ℝ → Vec)
    (H : Set (ℝ × Phase)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))) *
    ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (prefixParticle s T p))
      (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def dyadicCut (x : ℝ) : ℝ := 1-Real.smoothTransition (x-1)
def dyadicBump (x : ℝ) : ℝ := dyadicCut x-dyadicCut (2*x)
def dyadicFactor (n : ℕ) (x : ℝ) : ℝ := dyadicBump ((2:ℝ)^n*x)

def DyadicBand (n : ℕ) (x : ℝ) : Prop := 1/2≤(2:ℝ)^n*x ∧ (2:ℝ)^n*x≤2

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def dyadicMultiFactor {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, dyadicFactor (n i) (x i)

def dyadicBox (ι : Type*) [Fintype ι] (N : ℕ) : Finset (ι → ℕ) :=
  by classical exact Fintype.piFinset (fun _ : ι => Finset.range N)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalCutoffCoordinates
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def physicalCutoffCoordinates (T r : ℝ) (n v w : Vec) : Fin 4 → ℝ :=
  ![1/q v,Real.sqrt ((1-dot n (velocity v))/2),
    Real.sqrt ((1-dot n (velocity w))/2),r/max 1 T]

noncomputable def selectedDyadicBox {ι : Type*} [Fintype ι] (N : ℕ) (S : Set (ι→ℕ)) : Finset (ι→ℕ) := by
  classical
  exact (dyadicBox ι N).filter (fun n => n∈S)

def selectedDyadicCutoff {ι : Type*} [Fintype ι] (S : Set (ι→ℕ)) (x : ι→ℝ) : ℝ :=
  ∑' n : ι→ℕ, S.indicator (fun n => dyadicMultiFactor n x) n

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def waveK (g : Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  (4*Real.pi)⁻¹ * (p.1*sphereSum g p)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParamPrimitive
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def paramPrimitive {H W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : H × ℝ → W) (p : ℝ × H) : W := ∫ s in 0..p.1, F (p.2,s)

def dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : H → W) (e x : H) : W :=
  fderiv ℝ F x e

def volterra {H : Type*} (F : (ℝ × H) × ℝ → ℝ) (p : ℝ × H) : ℝ :=
  ∫ s in 0..p.1, F (p,s)

def sourceWaveKernel (ρ : ℝ × Vec → ℝ) (z : (ℝ × Vec) × ℝ) : ℝ :=
  waveK (fun y => ρ (z.2,y)) (z.1.1-z.2,z.1.2)

def sourceWave (ρ : ℝ × Vec → ℝ) : ℝ × Vec → ℝ := volterra (sourceWaveKernel ρ)

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveGradient
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def waveGradient (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => dirD u (0,basis i) p)

def waveEnergy (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  ((dirD u (1,0) p)^2+‖waveGradient u p‖^2)/2

def waveFlux (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : Vec :=
  -(dirD u (1,0) p) • waveGradient u p

def waveBox (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  dirD (dirD u (1,0)) (1,0) p -
    ∑ i : Fin 3, dirD (dirD u (0,basis i)) (0,basis i) p

def freeWave (g h : Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  dirD (waveK g) (1,0) p + waveK h p

def curlA : Fin 3 → Fin 3 := ![1,2,0]
def curlB : Fin 3 → Fin 3 := ![2,0,1]

def spaceCurl (F : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => dirD F (0,basis (curlA i)) p (curlB i) -
    dirD F (0,basis (curlB i)) p (curlA i))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def electricPotentialComponent (ρ : ℝ × Vec → ℝ) (j : Field) (i : Fin 3) : ℝ × Vec → ℝ :=
  fun p => -dirD (sourceWave ρ) (0,basis i) p - dirD (sourceWave (fun q => j q i)) (1,0) p

def magneticPotentialComponent (j : Field) (i : Fin 3) : ℝ × Vec → ℝ :=
  fun p => dirD (sourceWave (fun q => j q (curlB i))) (0,basis (curlA i)) p -
    dirD (sourceWave (fun q => j q (curlA i))) (0,basis (curlB i)) p

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def coneRadius (x y : Vec) : ℝ := ‖x-y‖
def coneDirection (x y : Vec) : Vec := (coneRadius x y)⁻¹ • (x-y)

def eulerianG (r : ℝ) (n u : Vec) : Vec := (r*(1-dot n u))⁻¹ • (n-u)

def retardedG (x : Vec) (z : Phase) : Vec :=
  eulerianG (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)

def retardedDensity (f : Particle) (t : ℝ) (x : Vec) (z : Phase) : ℝ :=
  f (t-coneRadius x z.1,z)

def retardedH (x : Vec) (z : Phase) : Vec := cross (coneDirection x z.1) (retardedG x z)

def holeCutoff (ε : ℝ) (x : Vec) : ℝ := 1-ballCutoff (ε/2) (ε^2/8) x



section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def retardedSpaceDomain (t : ℝ) (x : Vec) : Set Vec :=
  {y | x≠y ∧ 0<t-coneRadius x y}

def radiusWaveKernel (ρ : ℝ × Vec → ℝ) (z : (ℝ × Vec) × ℝ) : ℝ :=
  (4*Real.pi)⁻¹*z.2*(∫ n : Sphere, ρ (z.1.1-z.2,z.1.2+z.2 • n.1) ∂sphereMeasure)

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def coneSpatialCoefficient (x y v e : Vec) : ℝ :=
  dot (coneDirection x y) e/(1-dot (coneDirection x y) (velocity v))

def coneSpatialLift (x y v e : Vec) : Vec :=
  e+coneSpatialCoefficient x y v e • velocity v

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ActualCutoffCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def actualCutoffCoordinates (α : Phase→ℝ→Phase) (T : ℝ) (zX zY : Phase) (σ : ℝ) : Fin 4→ℝ :=
  physicalCutoffCoordinates T (branchTime α zX zY T σ-σ) (branchDirection α zX zY T σ)
    (α zY σ).2 (α zX (branchTime α zX zY T σ)).2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def momentumDirection (v : Vec) : Vec := ‖v‖⁻¹ • v

def angularMultiplier (w : ℝ) (v h : Vec) : Vec :=
  (w/‖v‖) • transverseProjection v h

def sourceRepresentative (n : ℕ) : ℝ := 64*(2:ℝ)^n

def cappedRepresentative (n : ℕ) : ℝ := (2:ℝ)⁻¹^n

def transverseCLM (v : Vec) : Vec→L[ℝ]Vec :=
  ContinuousLinearMap.id ℝ Vec -
    ((InnerProductSpace.toDual ℝ Vec) (momentumDirection v)).smulRight (momentumDirection v)

def angularMultiplierCLM (w : ℝ) (v : Vec) : Vec→L[ℝ]Vec := (w/‖v‖) • transverseCLM v

def angularDerivativeCLM (w : ℝ) (v K : Vec) : Vec→L[ℝ] Vec :=
  (-w/‖v‖^2) •
    (dot (momentumDirection v) K • transverseCLM v +
     ((InnerProductSpace.toDual ℝ Vec) (momentumDirection v)).smulRight (transverseProjection v K) +
     ((InnerProductSpace.toDual ℝ Vec) (transverseProjection v K)).smulRight (momentumDirection v))



open MeasureTheory Set

open Filter Set
open scoped Topology

open scoped Topology Pointwise

open Set MeasureTheory Metric ODE
open scoped Topology NNReal

open scoped ContDiff

open Set MeasureTheory Metric

open Set MeasureTheory Metric Filter ODE

open Set MeasureTheory Filter Metric ODE

open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter

open scoped Topology ContDiff RealInnerProductSpace NNReal

open Set Filter MeasureTheory Metric

open scoped Topology ContDiff NNReal RealInnerProductSpace

open scoped Topology ContDiff NNReal ENNReal

open Set MeasureTheory
open scoped ENNReal

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open scoped Topology ContDiff ENNReal

open scoped Topology ContDiff NNReal

open scoped Topology ContDiff

open Set

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_AngularBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def angularZeroBump (w : ℝ) (hw : 0<w) : ContDiffBump (0:Vec) :=
  ⟨w/64,w/32,by positivity,by linarith⟩

def extendedAngularCLM (w : ℝ) (hw : 0<w) (v : Vec) : Vec→L[ℝ]Vec :=
  (1-angularZeroBump w hw v) • angularMultiplierCLM w v

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixMomentumForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def prefixMomentumForce (s : Solution) (α : Phase→ℝ→Phase) (T : ℝ) (z : Phase) (t : ℝ) : Vec :=
  (lorentzField s.E s.B (prefixClamp T t,prefixFlow α T z t)).2

def prefixAngularMultiplier (_s : Solution) (α : Phase→ℝ→Phase) (T w : ℝ)
    (hw : 0<w) (z : Phase) (t : ℝ) : Vec→L[ℝ]Vec :=
  extendedAngularCLM w hw (prefixFlow α T z t).2

def prefixAngularRate (s : Solution) (α : Phase→ℝ→Phase) (T w : ℝ)
    (hw : 0<w) (z : Phase) (t : ℝ) : Vec→L[ℝ]Vec :=
  fderiv ℝ (extendedAngularCLM w hw) (prefixFlow α T z t).2
    (prefixMomentumForce s α T z t)

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseTimePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def phaseTimePullback {W : Type*} [Zero W] (α : Phase→ℝ→Phase) (T : ℝ)
    (g : ℝ×Phase→W) : ℝ×Phase→W :=
  (Ioo (0:ℝ) T ×ˢ (univ : Set Phase)).indicator (fun p=>g (p.1,α p.2 p.1))

def arrivalInverseSquare (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Vec→ℝ :=
  (arrivalDomain α zX T).indicator (fun p=>(arrivalRadius α zX T p)⁻¹^2)

def phaseArrivalMajorant (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (K : Set Vec) (p : ℝ×Phase) : ℝ :=
  arrivalInverseSquare α zX T (p.1,p.2.1)*K.indicator (fun _=>1) p.2.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SpaceDiv
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def spaceDiv (F : Field) (p : ℝ × Vec) : ℝ :=
  ∑ i : Fin 3, dirD F (0, basis i) p i

def freeField (G H : Vec → Vec) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => freeWave (fun x => G x i) (fun x => H x i) p)

def fieldBox (F : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => waveBox (fun q => F q i) p)

def electricResidual (E B j : Field) : Field :=
  fun p => dirD E (1,0) p-spaceCurl B p+j p

def magneticResidual (E B : Field) : Field :=
  fun p => dirD B (1,0) p+spaceCurl E p

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceField
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def sourceField (J : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => sourceWave (fun q => J q i) p)

def maxwellElectric (E₀ B₀ : Vec → Vec) (ρ : ℝ × Vec → ℝ) (j : Field) : Field :=
  fun p => freeField E₀ (fun x => curl B₀ x-j (0,x)) p +
    sourceField (fun q => -waveGradient ρ q-dirD j (1,0) q) p

def maxwellMagnetic (E₀ B₀ : Vec → Vec) (j : Field) : Field :=
  fun p => freeField B₀ (fun x => -curl E₀ x) p+sourceField (spaceCurl j) p

def maxwellEnergy (E B : Field) (p : ℝ × Vec) : ℝ := (‖E p‖^2+‖B p‖^2)/2

def maxwellFlux (E B : Field) (p : ℝ × Vec) : Vec := cross (E p) (B p)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_DifferenceFieldEnergy
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

def differenceFieldEnergy (s₁ s₂ : Solution) (p : ℝ × Vec) : ℝ :=
  (‖s₁.E p-s₂.E p‖^2+‖s₁.B p-s₂.B p‖^2)/2

def differenceEnergy (s₁ s₂ : Solution) (p : ℝ × Vec) : ℝ :=
  differenceFieldEnergy s₁ s₂ p+particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) p

def differenceFlux (s₁ s₂ : Solution) (p : ℝ × Vec) : Vec :=
  cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)+particleMoment (squareDifference s₁ s₂) velocity p

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def freeMaxwellElectric (E₀ B₀ : Vec → Vec) : Field :=
  maxwellElectric E₀ B₀ (fun p => divergence E₀ p.2) 0

def freeMaxwellMagnetic (E₀ B₀ : Vec → Vec) : Field := maxwellMagnetic E₀ B₀ 0

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_VlasovConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM

universe u

def BoundedFlowRegularity (n : ℕ) : Prop :=
  ∀ (E Z : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : ℝ × E → E) (T L : ℝ) (U : Set Z) (g : Z → E) (α : Z → ℝ → E),
    0 < T → 0 ≤ L → ContDiff ℝ ∞ f →
    (∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L) →
    IsOpen U → ContDiffOn ℝ ∞ g U →
    (∀ x ∈ U, α x 0 = g x) →
    (∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) →
    ContDiffOn ℝ n (fun z : ℝ × Z => α z.2 z.1) (Ioo 0 T ×ˢ U)

structure SymmetricLorentzFlow (E B : Field) (R : ℝ) where
  forward : Phase → ℝ → Phase
  backward : ℝ × Phase → Phase
  initial : ∀ z, forward z 0 = z
  ode : ∀ z t, t ∈ Ioo (-R) R →
    HasDerivAt (forward z) (lorentzField E B (t,forward z t)) t
  smooth_forward : ContDiffOn ℝ ∞ (fun w : ℝ × Phase => forward w.2 w.1)
    (Ioo (-R) R ×ˢ (univ : Set Phase))
  smooth_backward : ContDiffOn ℝ ∞ backward (Ioo (-R) R ×ˢ (univ : Set Phase))
  left_inverse : ∀ t ∈ Ioo (-R) R, ∀ z, backward (t,forward z t) = z
  right_inverse : ∀ t ∈ Ioo (-R) R, ∀ z, forward (backward (t,z)) t = z

structure SmoothLorentzFlow (E B : Field) where
  forward : Phase → ℝ → Phase
  backward : ℝ × Phase → Phase
  initial : ∀ z, forward z 0 = z
  ode : ∀ z t, HasDerivAt (forward z) (lorentzField E B (t,forward z t)) t
  smooth_forward : ContDiff ℝ ∞ (fun w : ℝ × Phase => forward w.2 w.1)
  smooth_backward : ContDiff ℝ ∞ backward
  left_inverse : ∀ t z, backward (t,forward z t) = z
  right_inverse : ∀ t z, forward (backward (t,z)) t = z

namespace SmoothLorentzFlow

variable {E B : Field} (F : SmoothLorentzFlow E B)

def particle (f₀ : Phase → ℝ) : Particle := fun w => f₀ (F.backward w)

end SmoothLorentzFlow

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def MaxwellFor (s : Solution) : Prop := ∀ t, 0 ≤ t → ∀ x,
  dirD s.E (1,0) (t,x)=spaceCurl s.B (t,x)-current (fun z => s.f (t,z)) x ∧
  dirD s.B (1,0) (t,x)= -spaceCurl s.E (t,x) ∧
  spaceDiv s.E (t,x)=rho (fun z => s.f (t,z)) x ∧ spaceDiv s.B (t,x)=0

def TransportFor (s : Solution) (E B : Field) : Prop := ∀ t (z : Phase),
  fderiv ℝ s.f (t,z) (1,lorentzField E B (t,z))=0

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def normalisedElectricKernel (r : ℝ) (n u b : Vec) : Vec :=
  ((1-dot u u)/(1-dot n u)^3) • (n-u) +
    (r/(1-dot n u)^3) • ((dot n b) • (n-u)-(1-dot n u) • b)

def retardedElectricDensity (s : Solution) (t : ℝ) (x y : Vec) : Vec :=
  ∫ v : Vec, (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
    physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
      (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))

def retardedElectricFlux (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (y : Vec) : Vec :=
  ∫ v : Vec, (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CrossCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def crossCLM (n : Vec) : Vec →L[ℝ] Vec :=
  LinearMap.mkContinuous
    { toFun := cross n
      map_add' := by intro a b; ext i; fin_cases i <;> simp [cross] <;> ring
      map_smul' := by intro a b; exact cross_smul_right n b a }
    ‖n‖ (fun v => norm_cross_le n v)

def retardedMagneticDensity (s : Solution) (t : ℝ) (x y : Vec) : Vec :=
  cross (coneDirection x y) (retardedElectricDensity s t x y)

def retardedMagneticFlux (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (y : Vec) : Vec :=
  ∫ v : Vec, (retardedDensity s.f t x (y,v)*retardedH x (y,v) i) • velocity v

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PositiveExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def positiveTimeCut (a t : ℝ) : ℝ := Real.smoothTransition ((t-a/4)/(a/4))
def positiveTimeExtend (a : ℝ) (F : ℝ × H → W) (p : ℝ × H) : W :=
  positiveTimeCut a p.1 • F p

def positiveTimeShift (a : ℝ) (F : ℝ × H → W) (p : ℝ × H) : W :=
  positiveTimeExtend a F (a+p.1,p.2)

end PositiveExtension

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ShiftedRho
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def shiftedRho (s : Solution) (a : ℝ) : ℝ × Vec → ℝ :=
  positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2)
def shiftedCurrent (s : Solution) (a : ℝ) : Field :=
  positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)
def electricMomentDensity (ρ : ℝ × Vec → ℝ) (j : Field)
    (t : ℝ) (x : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  -(z i/‖z‖^3*ρ (t-‖z‖,x+z)) - z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) -
    dirD (fun p => j p i) (1,0) (t-‖z‖,x+z)/‖z‖

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticMomentDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def magneticMomentDensity (j : Field) (t : ℝ) (x : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  z (curlA i)/‖z‖^2*dirD (fun p => j p (curlB i)) (1,0) (t-‖z‖,x+z) +
    z (curlA i)/‖z‖^3*j (t-‖z‖,x+z) (curlB i) -
    (z (curlB i)/‖z‖^2*dirD (fun p => j p (curlA i)) (1,0) (t-‖z‖,x+z) +
    z (curlB i)/‖z‖^3*j (t-‖z‖,x+z) (curlA i))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ElectricConeBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def electricConeBoundary (s : Solution) (T : ℝ) (x : Vec) (i : Fin 3) (a : ℝ) : ℝ :=
  freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T-a,x) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)^2*dot n.1
      (retardedElectricFlux s T x i (x+(T-a) • n.1)) ∂sphereMeasure) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)*n.1 i*
      rho (fun z => s.f (a,z)) (x+(T-a) • n.1) ∂sphereMeasure) -
    waveK (fun y => current (fun z => s.f (a,z)) y i) (T-a,x)

def magneticConeBoundary (s : Solution) (T : ℝ) (x : Vec) (i : Fin 3) (a : ℝ) : ℝ :=
  freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T-a,x) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)^2*dot n.1
      (retardedMagneticFlux s T x i (x+(T-a) • n.1)) ∂sphereMeasure) +
    (4*Real.pi)⁻¹ * (∫ n : Sphere,
      (T-a)*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+(T-a) • n.1) (curlB i) -
      (T-a)*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+(T-a) • n.1) (curlA i) ∂sphereMeasure)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def electricBoundaryField (s : Solution) (t : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i => electricConeBoundary s t x i 0)

def magneticBoundaryField (s : Solution) (t : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i => magneticConeBoundary s t x i 0)

def boundaryLorentzForce (s : Solution) (t : ℝ) (x a : Vec) : Vec :=
  electricBoundaryField s t x+cross a (magneticBoundaryField s t x)

def datumBoundarySolution (d : Datum) : Solution :=
  ⟨fun p => d.f₀ p.2,fun p => d.E₀ p.2,fun p => d.B₀ p.2⟩

def forceTransportKernel (r : ℝ) (n a v : Vec) : Vec :=
  (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ • receiverQ a n (n-velocity v)

def forceSourceKernel (r : ℝ) (n a v b : Vec) : Vec :=
  (r*(1-dot n (velocity v))^2)⁻¹ • receiverQ a n (sourceNumerator n (velocity v) b)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def receiverQCLM (a n : Vec) : Vec →L[ℝ] Vec :=
  ContinuousLinearMap.id ℝ Vec+(crossCLM a).comp (crossCLM n)

def retardedForceKernel (s : Solution) (t : ℝ) (x a : Vec) (y v : Vec) : Vec :=
  s.f (t-coneRadius x y,y,v) •
    (forceTransportKernel (coneRadius x y) (coneDirection x y) a v+
      forceSourceKernel (coneRadius x y) (coneDirection x y) a v
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))))

def retardedNormalisedForce (s : Solution) (t : ℝ) (x a : Vec) (p : (Vec × Vec) × Vec) : Vec :=
  (1-dot p.1.2 (velocity p.2)) • receiverQ a p.1.2
    (normalisedElectricKernel ‖p.1.1‖ p.1.2 (velocity p.2)
      (fderiv ℝ velocity p.2 (s.E (t-‖p.1.1‖,x+p.1.1)+
        cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

abbrev ConeKernelState := (ℝ×ℝ)×(Vec×Phase)
def coneKernelDomain (T : ℝ) : Set ConeKernelState :=
  (Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T) ×ˢ (sphere (0:Vec) 1 ×ˢ univ)

def normalisedSignedForce (r : ℝ) (a u n b : Vec) : Vec :=
  ((1-dot n u)/(1-dot n a)) • receiverQ a n (normalisedElectricKernel r n u b)

def sourceAcceleration (s : Solution) (p : ℝ×Phase) : Vec :=
  fderiv ℝ velocity p.2.2 (s.E (p.1,p.2.1)+cross (velocity p.2.2) (s.B (p.1,p.2.1)))

def arrivalPhaseDomain (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set (ℝ×Phase) :=
  (fun p=>(p.1,p.2.1)) ⁻¹' arrivalDomain α zX T

def arrivalKernelState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (p : ℝ×Phase) : ConeKernelState :=
  ((arrivalTime α zX T (p.1,p.2.1),p.1),(arrivalDirection α zX T (p.1,p.2.1),p.2))

def arrivalConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : ℝ×Phase→Vec :=
  (arrivalPhaseDomain α zX T).indicator (fun p=>
    (arrivalRadius α zX T (p.1,p.2.1))⁻¹^2 • (s.f p • A (arrivalKernelState α zX T p)))

def actualArrivalSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (arrivalPhaseDomain α zX T).indicator (fun p=>s.f p •
    signedForceKernel (arrivalRadius α zX T (p.1,p.2.1))
      (velocity (α zX (arrivalTime α zX T (p.1,p.2.1))).2)
      (velocity p.2.2) (arrivalDirection α zX T (p.1,p.2.1)) (sourceAcceleration s p))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_EquationsBefore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def EquationsBefore (s : Solution) (H : ℝ) : Prop := ∀ t, 0 ≤ t → t < H →
  (∀ x v,
    derivWithin (fun t' => s.f (t', x, v)) (Ici 0) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f (t, y, v)) x i) +
    (∑ i : Fin 3, (s.E (t, x) + cross (velocity v) (s.B (t, x))) i *
      spatialPartial (fun v' => s.f (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Ici 0) t -
    curl (fun y => s.B (t, y)) x = -current (fun z => s.f (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Ici 0) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho (fun z => s.f (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

def ClassicalBefore (d : Datum) (s : Solution) (H : ℝ) : Prop :=
  ContDiffOn ℝ 1 s.f particleHalfSpace ∧
  ContDiffOn ℝ 1 s.E fieldHalfSpace ∧ ContDiffOn ℝ 1 s.B fieldHalfSpace ∧
  (∀ t, 0 ≤ t → ∀ z, 0 ≤ s.f (t, z)) ∧
  TimeContinuousL2 s.E ∧ TimeContinuousL2 s.B ∧
  CompactOnFiniteHorizons s ∧ EquationsBefore s H ∧
  (∀ z, s.f (0, z) = d.f₀ z) ∧
  (∀ x, s.E (0, x) = d.E₀ x) ∧ (∀ x, s.B (0, x) = d.B₀ x)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_UpperTimeCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def upperTimeCut (τ H t : ℝ) : ℝ := positiveTimeCut (2*(H-τ)) (H-t)

section Generic
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def upperTimeExtend (τ H : ℝ) (F : ℝ × X → W) (p : ℝ × X) : W :=
  upperTimeCut τ H p.1 • F p

end Generic

structure SmoothClassicalPrefix (d : Datum) (s : Solution) (H : ℝ) : Prop where
  f_smooth : ContDiffOn ℝ ∞ s.f (particleSlab H)
  E_smooth : ContDiffOn ℝ ∞ s.E (fieldSlab H)
  B_smooth : ContDiffOn ℝ ∞ s.B (fieldSlab H)
  nonnegative : ∀ t ∈ Icc 0 H, ∀ z, 0 ≤ s.f (t,z)
  E_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 H) ∧
    ∀ t ∈ Icc 0 H, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.E (t,x))
  B_L2 : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 H) ∧
    ∀ t ∈ Icc 0 H, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => s.B (t,x))
  compact : ∃ K : Set Phase, IsCompact K ∧ ∀ t ∈ Icc 0 H, tsupport (fun z => s.f (t,z)) ⊆ K
  equations : EquationsBefore s H
  initial_f : ∀ z, s.f (0,z)=d.f₀ z
  initial_E : ∀ x, s.E (0,x)=d.E₀ x
  initial_B : ∀ x, s.B (0,x)=d.B₀ x

def cutoffPrefix (τ H : ℝ) (s : Solution) : Solution :=
  ⟨upperTimeExtend τ H s.f,upperTimeExtend τ H s.E,upperTimeExtend τ H s.B⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DatumElectricFluxKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def datumElectricFluxKernel (i : Fin 3) (p : Vec × Vec) : Vec :=
  ((1-dot p.1 (velocity p.2))⁻¹*(p.1 i-velocity p.2 i)) • velocity p.2

def datumMagneticFluxKernel (i : Fin 3) (p : Vec × Vec) : Vec :=
  ((1-dot p.1 (velocity p.2))⁻¹*cross p.1 (p.1-velocity p.2) i) • velocity p.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_InitialSignedBoundaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def initialSignedBoundaryDensity (f : Phase→ℝ) (x w : Vec) (t ψ χ : ℝ)
    (P : Vec→L[ℝ]Vec) (n v : Vec) : Vec :=
  (t^2*(1-dot n (velocity w))*f (x-t • n,v)*ψ*χ) •
    P (retardedPrimitive t (velocity w) (velocity v) n)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClosedBranchDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def closedBranchDomain (α : Phase→ℝ→Phase) (zX zY : Phase) (T : ℝ) : Set ℝ :=
  {s | s∈Icc 0 T ∧ s+‖(α zX T).1-(α zY s).1‖ ≤ T}

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def labelBranchDomain (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set (ℝ×Phase) :=
  {p | p.1∈branchDomain α zX p.2 T ∧ (α zX p.1).1≠(α p.2 p.1).1}

def actualLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    signedForceKernel (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2)
      (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1)
      (sourceAcceleration s (p.1,α p.2 p.1)))

def normalisedPrimitive (r : ℝ) (a u n : Vec) : Vec :=
  (r/(1-dot n u)) • signedPrimitive a u n

def normalisedRemainder (r : ℝ) (a u n b : Vec) : Vec :=
  ((1-dot a u)/(1-dot n a)^2) • (((1-dot a a)/(1-dot n a)) • n-a)+
    (r*dot b (signedPrimitive a u n)/(1-dot n a)^2) • n

def labelKernelState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) : ConeKernelState :=
  ((branchTime α zX p.2 T p.1,p.1),(branchDirection α zX p.2 T p.1,α p.2 p.1))

def labelConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>(branchTime α zX p.2 T p.1-p.1)⁻¹^2 •
    (s.f (0,p.2) • A (labelKernelState α zX T p)))

def actualLabelPrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    retardedPrimitive (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1))

def actualLabelRemainder (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    signedRemainder (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1)
      (phaseAcceleration s.E s.B α zX (branchTime α zX p.2 T p.1)))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedRadiusSeparatedClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def initialClosedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set Phase :=
  {z | ‖(α zX T).1-z.1‖≤T}

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CutoffState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

abbrev CutoffState := ℝ × Vec × Vec × Vec

def stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) (z : CutoffState) : ℝ :=
  selectedDyadicCutoff Q (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2)

def branchCutoffState (α : Phase→ℝ→Phase) (T : ℝ) (zX zY : Phase) (σ : ℝ) : CutoffState :=
  (branchTime α zX zY T σ-σ,branchDirection α zX zY T σ,
    (α zY σ).2,(α zX (branchTime α zX zY T σ)).2)

def branchCutoffStateRate (E B : Field) (α : Phase→ℝ→Phase) (T : ℝ)
    (zX zY : Phase) (σ : ℝ) : CutoffState :=
  let τ := branchTime α zX zY T σ
  let n := branchDirection α zX zY T σ
  let ρ := branchRate α zX zY T σ
  (ρ-1,(τ-σ)⁻¹ • coneMotion (velocity (α zX τ).2) (velocity (α zY σ).2) n,
    (lorentzField E B (σ,α zY σ)).2,ρ • (lorentzField E B (τ,α zX τ)).2)

def branchSelectedRate (E B : Field) (α : Phase→ℝ→Phase) (T : ℝ)
    (zX zY : Phase) (Q : Set (Fin 4→ℕ)) (σ : ℝ) : ℝ :=
  fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX zY σ)
    (branchCutoffStateRate E B α T zX zY σ)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffRateMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def cutoffRateMajorant (r : ℝ) (a u n vy vx : Vec) : ℝ :=
  let ρ := (1-dot n u)/(1-dot n a)
  |r| *‖vy‖+(‖coneMotion a u n‖+|r| *‖vy‖)/(2*(1-dot n u))+
    (‖coneMotion a u n‖+|r| *‖ρ • vx‖)/(2*(1-dot n a))+|ρ-1|

def normalisedCutoffPrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (K : ℝ) (p : ConeKernelState) : Vec :=
  (K*cutoffRateMajorant (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1
    (lorentzField s.E s.B (p.1.2,p.2.2)).2 (lorentzField s.E s.B (p.1.1,α zX p.1.1)).2) •
    normalisedPrimitive 1 (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ActualLabelCutoffCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def actualLabelCutoffCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (p : ℝ×Phase) : Vec :=
  (jointBranchDomain α zX T).indicator
    (fun p=>branchSelectedRate s.E s.B α T zX p.2 Q p.1) p • actualLabelPrimitive s α zX T p

def labelReceiverTime (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→ℝ :=
  (labelBranchDomain α zX T).indicator (fun p=>branchTime α zX p.2 T p.1)

def labelSelectedCutoff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) : ℝ×Phase→ℝ :=
  (jointBranchDomain α zX T).indicator
    (fun p=>selectedDyadicCutoff Q (actualCutoffCoordinates α T zX p.2 p.1))

def actualLabelRatePrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (p : ℝ×Phase) : Vec :=
  branchRate α zX p.2 T p.1 • actualLabelPrimitive s α zX T p

def normalisedRatePrimitive (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  ((1-dot p.2.1 (velocity p.2.2.2))/(1-dot p.2.1 (velocity (α zX p.1.1).2))) •
    normalisedPrimitive (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ArrivalConeKernelPolarNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def arrivalReceiverTime (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) : ℝ :=
  (arrivalDomain α zX T).indicator (arrivalTime α zX T) (p.1,p.2.1)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClippedRamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def clippedRamp (a ℓ t : ℝ) : ℝ := min 1 (max 0 ((t-a)/ℓ))

def directionWeight (a b ℓ t : ℝ) : ℝ := clippedRamp a ℓ t-clippedRamp (b-ℓ) ℓ t

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def labelWeight (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : ℝ :=
  ψ (labelReceiverTime α zX T p)*labelSelectedCutoff α zX T Q p

def selectedLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  labelWeight α zX T Q ψ p • actualLabelSignedForce s α zX T p

def selectedLabelCosts (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p +
    ψ (labelReceiverTime α zX T p) • actualLabelCutoffCost s α zX T Q p +
      labelWeight α zX T Q ψ p • actualLabelRemainder s α zX T p

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_InitialPuncturedCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def initialPuncturedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set Phase :=
  initialConeLabels T (α zX T).1 ∩ {z : Phase | z.1≠zX.1}

def initialConeState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (z : Phase) : CutoffState :=
  let t := branchTime α zX z T 0
  (t,branchDirection α zX z T 0,z.2,(α zX t).2)

def selectedInitialKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec) : Phase→Vec :=
  (initialPuncturedCone α zX T).indicator (fun z=>
    let t := branchTime α zX z T 0
    (f z*ψ t*stateCutoff T Q (initialConeState α zX T z)) •
      W t (retardedPrimitive t (velocity (α zX t).2) (velocity z.2)
        (branchDirection α zX z T 0)))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def selectedMultiplierForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : Vec :=
  G (labelReceiverTime α zX T p) (selectedLabelSignedForce s α zX T Q ψ p)

def selectedMultiplierCosts (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (G G' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : Vec :=
  G (labelReceiverTime α zX T p) (selectedLabelCosts s α zX T Q ψ p)+
    G' (labelReceiverTime α zX T p)
      (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedMomentumForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def physicalProjectedPrimitiveDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def physicalMovingProjectorDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (K : ℝ→Vec) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffSourceTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped ENNReal Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def cutoffSourceTangent (K : Vec) : CutoffState := (0,0,K,0)
def cutoffGeometryTangent (r ρ : ℝ) (a u n : Vec) : CutoffState :=
  (ρ-1,r⁻¹ • coneMotion a u n,0,0)
def cutoffReceiverTangent (ρ : ℝ) (K : Vec) : CutoffState := (0,0,0,ρ • K)

def partialCutoffLabelCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (H : ℝ×Phase→CutoffState) (p : ℝ×Phase) : Vec :=
  (jointBranchDomain α zX T).indicator
    (fun p=>fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX p.2 p.1) (H p)) p •
      actualLabelPrimitive s α zX T p

def dyadicSelectionBoundary {ι : Type*} (Q : Set (ι→ℕ)) : Set (ι→ℕ) :=
  {k | (∃j∈Q,∀i,j i≤k i+2 ∧ k i≤j i+2) ∧
       (∃j∉Q,∀i,j i≤k i+2 ∧ k i≤j i+2)}

end RVM

end

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalReceiverCutoffDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (K : ℝ→Vec)
    (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1)))) (K z.1))) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def representativeClosedBin (T w : ℝ) (k : Fin 4→ℕ) : ClosedConeBin where
  rmin := max 1 T*cappedRepresentative (k 3)/2
  rmax := 2*max 1 T*cappedRepresentative (k 3)
  qmin := sourceRepresentative (k 0)/128
  qmax := sourceRepresentative (k 0)/32
  wmin := w/8
  wmax := 8*w
  dmin := cappedRepresentative (k 1)^2/2
  dmax := 8*cappedRepresentative (k 1)^2
  Dmin := cappedRepresentative (k 2)^2/2
  Dmax := 8*cappedRepresentative (k 2)^2
  emin := 0
  emax := 2

def coneDyadicFactor (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (k : Fin 4→ℕ)
    (p : ConeKernelState) : ℝ :=
  dyadicMultiFactor k (physicalCutoffCoordinates T (p.1.1-p.1.2) p.2.1 p.2.2.2 (α zX p.1.1).2)

def projectedDyadicRateKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) (p : ConeKernelState) : Vec :=
  coneDyadicFactor α zX T k p • G p.1.1 (normalisedRatePrimitive α zX p)

def physicalDyadicPrimitiveDensity (s : Solution) (X V : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ∫⁻v : Vec, ENNReal.ofReal (dyadicMultiFactor k
    (physicalCutoffCoordinates T (z.1-z.2.1) z.2.2.1 v (V z.1))*(z.1-z.2.1)*
      ‖s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖)

def positiveCoordinate (i : Fin 3) (v : Vec) : Vec := max (v i) 0 • basis 0

abbrev TrianglePhase := ConeCoordinate×Vec

def trianglePhaseDomain (T : ℝ) : Set TrianglePhase :=
  {p | p.1.1∈Ioo 0 T ∧ p.1.2.1∈Ioo 0 p.1.1}

def trianglePhaseMeasure : Measure TrianglePhase :=
  ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod sphereMeasure)).prod volume

def triangleKernelState (α : Phase→ℝ→Phase) (zX : Phase) (p : TrianglePhase) : ConeKernelState :=
  ((p.1.1,p.1.2.1),(p.1.2.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))

def triangleConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : TrianglePhase→Vec :=
  (trianglePhaseDomain T).indicator (fun p=>
    (1-dot p.1.2.2.1 (velocity (α zX p.1.1).2)) •
      (s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2) •
        A (triangleKernelState α zX p)))

def directionWeightMajorant (N : ℕ) (k : Fin 4→ℕ) : ℝ :=
  (if k 0<N then 1 else 0)*(if k 1<N then 1 else 0)*
    (1/2:ℝ)^(k 2)*Real.sqrt ((1/2:ℝ)^(k 3))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def receiverBoundaryBinCost (s : Solution) (X V K : ℝ→Vec) (T w : ℝ)
    (J : Set ℝ) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ) : ℝ≥0∞ :=
  ∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V
    (representativeClosedBin T w k) T w Q K z
    ∂physicalBinMeasure V (representativeClosedBin T w k) J

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedReceiverWeightBoundFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalDyadicMovingDensity (s : Solution) (X V K : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ∫⁻v : Vec, ENNReal.ofReal (dyadicMultiFactor k
    (physicalCutoffCoordinates T (z.1-z.2.1) z.2.2.1 v (V z.1))*(z.1-z.2.1)*
      ‖s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖)

def selectedAngularMovingCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T w : ℝ) (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) : ℝ≥0∞ :=
  ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (α zX (labelReceiverTime α zX T p)).2
    (lorentzField s.E s.B (labelReceiverTime α zX T p,α zX (labelReceiverTime α zX T p))).2
    (labelWeight α zX T Q b p • actualLabelRatePrimitive s α zX T p)‖

def selectedAngularWeightCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T w : ℝ) (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) : ℝ≥0∞ :=
  ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (α zX (labelReceiverTime α zX T p)).2
    (labelWeight α zX T Q (deriv b) p • actualLabelRatePrimitive s α zX T p)‖

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology

namespace RVM

def selectionWeight (P θ φ h : ℝ) : ℝ :=
  (P*θ)^(-1/100000 : ℝ)*φ^(1/100000 : ℝ)*h^(1/100000 : ℝ)

def receiverCoefficient (w p θ φ h : ℝ) : ℝ :=
  w⁻¹ * min (h^2*(p*θ)^3) ((p*θ*h*φ^2)⁻¹)

def stabilityRate (P C₁ M A p w φ : ℝ) : ℝ :=
  C₁*(P/min p w)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ))

def stabilityLength (P C₁ M A p w φ : ℝ) : ℝ :=
  (stabilityRate P C₁ M A p w φ)⁻¹ ^ 2

def ImprovedWindow (P p w φ : ℝ) : Prop :=
  P^(7/10 : ℝ) ≤ p ∧ P^(7/10 : ℝ) ≤ w ∧
  p^(-49/100 : ℝ) ≤ φ ∧ φ ≤ p^(-16/100 : ℝ) ∧
  w^(-49/100 : ℝ) ≤ φ ∧ φ ≤ w^(-16/100 : ℝ)

def PureOccupationBounds (P C₀ C₁ M A p w φ h I μ : ℝ) : Prop :=
  μ ≤ max I h/p ∧
  (C₀/min p w < φ → μ ≤ (h/p)*max 1
    (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))) ∧
  (ImprovedWindow P p w φ → μ ≤ (h/p)*φ^(-29/25 : ℝ)*
    max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2)))

def pureOccupationEnvelope (P C₀ C₁ M A p w φ h I : ℝ) : ℝ := by
  classical
  exact let e := max I h/p
  let a := (h/p)*max 1
    (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))
  let b := (h/p)*φ^(-29/25 : ℝ)*
    max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))
  min (if C₀/min p w < φ then min e a else e)
    (if ImprovedWindow P p w φ then min e b else e)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeKernelInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def coneKernelInterior (T : ℝ) : Set ConeKernelState :=
  coneKernelDomain T ∩ {p | p.1.2<p.1.1}

def coneCutoffState (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : CutoffState :=
  (p.1.1-p.1.2,p.2.1,p.2.2.2,(α zX p.1.1).2)

def coneCutoffRate (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  let a := velocity (α zX p.1.1).2
  let u := velocity p.2.2.2
  let n := p.2.1
  let ρ := (1-dot n u)/(1-dot n a)
  (ρ-1,(p.1.1-p.1.2)⁻¹ • coneMotion a u n,
    (lorentzField s.E s.B (p.1.2,p.2.2)).2,
    ρ • (lorentzField s.E s.B (p.1.1,α zX p.1.1)).2)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceForceConeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def sourceForceConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : Vec :=
  normalisedSignedForce (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 (sourceAcceleration s (p.1.2,p.2.2))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_NormalisedPartialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def normalisedPartialCutoff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState) (p : ConeKernelState) : Vec :=
  fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX p) (H p) •
    normalisedPrimitive (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_PhysicalGeometryCutoffDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalGeometryCutoffDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffGeometryTangent (z.1-z.2.1)
            ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1))))
            (velocity (V z.1)) (velocity v) z.2.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalProjectedRemainderDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (K : ℝ→Vec) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖

def coneReceiverJacobian (V : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  (z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))

def coneFoot (X : ℝ→Vec) (z : ConeCoordinate) : ℝ×Vec :=
  (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)

def prefixConeMagnetic (s : Solution) (T : ℝ) (X : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  ‖prefixField s.B T (coneFoot X z)‖

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalProjectedSourceDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      let f := s.f (z.2.1,(y,v))
      let K := s.E (z.2.1,y)+cross (velocity v) (s.B (z.2.1,y))
      ENNReal.ofReal (‖f • angularMultiplierCLM w W
        (forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v K))‖+
        ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (r,n,v,W) (cutoffSourceTangent K)) •
          angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PhysicalBinPhaseSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalBinPhaseSet (V : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) : Set TrianglePhase :=
  {p | p.1∈physicalBinBase V B J ∧ p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}

def partialCutoffTriangle (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState)
    (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ) : TrianglePhase→Vec :=
  {p : TrianglePhase | p.1.1∈J}.indicator (fun p=>W p.1.1
    (triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p))

def coneReceiverCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  (0,0,0,(coneCutoffRate s α zX p).2.2.2)

def coneSourceCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  (0,0,(coneCutoffRate s α zX p).2.2.1,0)

def coneGeometryCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  ((coneCutoffRate s α zX p).1,(coneCutoffRate s α zX p).2.1,0,0)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_RelativeAngleCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def relativeAngleCoordinate (v w : Vec) : ℝ :=
  Real.sqrt ((1-dot (velocity w) (velocity v))/2)

def relativePhysicalFactor (T r : ℝ) (n v w : Vec) (k : Fin 4→ℕ) (j : ℕ) : ℝ :=
  dyadicMultiFactor k (physicalCutoffCoordinates T r n v w)*
    dyadicFactor j (relativeAngleCoordinate v w)

def relativeRepresentativeClosedBin (T w : ℝ) (k : Fin 4→ℕ) (j : ℕ) : ClosedConeBin :=
  {representativeClosedBin T w k with
    emin := cappedRepresentative j^2/2
    emax := 8*cappedRepresentative j^2}

def relativeBinRefinement (B : ClosedConeBin) (j : ℕ) : ClosedConeBin :=
  {B with emin := cappedRepresentative j^2/2,emax := 8*cappedRepresentative j^2}

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicBalanceConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def dyadicBalanceConstant (α β : ℝ) : ℝ :=
  (1-((2:ℝ)^α)⁻¹)⁻¹+2^β/(1-((2:ℝ)^β)⁻¹)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalDirectTransportDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def physicalDirectTransportDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  let r := z.1-z.2.1
  let y := X z.1-r • z.2.2.1
  ENNReal.ofReal (r^2)*∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
    ENNReal.ofReal ‖s.f (z.2.1,(y,v)) • forceTransportKernel r z.2.2.1 (velocity (V z.1)) v‖

def physicalDirectSourceDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      let f := s.f (z.2.1,(y,v))
      let K := s.E (z.2.1,y)+cross (velocity v) (s.B (z.2.1,y))
      ENNReal.ofReal ‖f • forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v K)‖

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_QuadIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def quadIndexEquiv : (Fin 4→ℕ) ≃ ℕ×ℕ×ℕ×ℕ where
  toFun k := (k 0,k 1,k 2,k 3)
  invFun k := ![k.1,k.2.1,k.2.2.1,k.2.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv k := by rcases k with ⟨a,b,c,d⟩; rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_RelativeCauchyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def relativeCauchyConstant (C E Z : ℝ) : ℝ :=
  31457280*C*Real.sqrt Z+10240*Real.sqrt Z*Real.sqrt (62914560*C*E)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

abbrev DirectOuterIndex (N : ℕ) := Fin 4→Fin N

def directOuterBin {N : ℕ} (T w : ℝ) (i : DirectOuterIndex N) (nr : ℕ) : ClosedConeBin :=
  relativeRepresentativeClosedBin T w ![(i 0).val,(i 1).val,(i 2).val,nr] (i 3).val

def directTriangleDomain (T : ℝ) (J : Set ℝ) : Set TrianglePhase :=
  trianglePhaseDomain T ∩ {p | p.1.1∈J}

def directTriangleDensity (s : Solution) (X : ℝ→Vec) (T : ℝ) (J : Set ℝ)
    (K : TrianglePhase→Vec) (p : TrianglePhase) : ℝ≥0∞ :=
  (directTriangleDomain T J).indicator (fun p=>
    ENNReal.ofReal ((p.1.1-p.1.2.1)^2)*
    ENNReal.ofReal ‖prefixParticle s T
      (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) • K p‖) p

def directTransportTriangleKernel (V : ℝ→Vec) (p : TrianglePhase) : Vec :=
  forceTransportKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (V p.1.1)) p.2

def directSourceTriangleKernel (s : Solution) (X V : ℝ→Vec) (T : ℝ) (p : TrianglePhase) : Vec :=
  let y := X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1
  forceSourceKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (V p.1.1)) p.2
    (fderiv ℝ velocity p.2 (prefixField s.E T (p.1.2.1,y)+
      cross (velocity p.2) (prefixField s.B T (p.1.2.1,y))))

end RVM

end

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directOuterIndexEquiv (N : ℕ) : DirectOuterIndex N ≃ Fin N×Fin N×Fin N×Fin N where
  toFun k := (k 0,k 2,k 1,k 3)
  invFun k := ![k.1,k.2.2.1,k.2.1,k.2.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv k := by rcases k with ⟨a,b,c,d⟩; rfl

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def sourceMajorantKernel (r : ℝ) (n W v E B : Vec) : ℝ :=
  (10*Real.sqrt (2*(1-dot n (velocity W)))/(r*q v))*
    (goodField E B n/(1-dot n (velocity v))+‖B‖)

def physicalSourceMajorantDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      ENNReal.ofReal (s.f (z.2.1,(y,v))*sourceMajorantKernel r n W v
        (s.E (z.2.1,y)) (s.B (z.2.1,y)))

def majorant_relativeCauchyConstant (C E Z : ℝ) : ℝ :=
  31457280*C*Real.sqrt Z+10240*Real.sqrt Z*Real.sqrt (62914560*C*E)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def directionSelection (T : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1)≤(1/1024)*cappedRepresentative (k 2) ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}

def directionSourceEdge : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}

def directionSourceLow (w : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
    cappedRepresentative (k 2)*w≤32}

def directionSourceFar (T w P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤128*P ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
    32≤ cappedRepresentative (k 2)*w ∧
    1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))}

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

structure PicardRegular (d : Datum) (s : Solution) : Prop where
  smooth_f : ContDiff ℝ ∞ s.f
  smooth_E : ContDiff ℝ ∞ s.E
  smooth_B : ContDiff ℝ ∞ s.B
  nonneg : ∀ p, 0 ≤ s.f p
  compact : CompactOnFiniteHorizons s
  l2E : TimeContinuousL2 s.E
  l2B : TimeContinuousL2 s.B
  initial_f : ∀ z, s.f (0,z)=d.f₀ z
  initial_E : ∀ x, s.E (0,x)=d.E₀ x
  initial_B : ∀ x, s.B (0,x)=d.B₀ x
  maxwell : MaxwellFor s
  smooth_rho : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2)
  smooth_current : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2)

def LocalParticleBound (T A R P : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, ∀ x v : Vec, |f (t,x,v)|≤A ∧
    (f (t,x,v)≠0 → ‖x‖≤R ∧ ‖v‖≤P)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PicardKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def normalisedPhysicalIntegrand (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) : Vec :=
  (p.2.1*(1-dot p.1.2.1 (velocity p.1.2.2))) •
    normalisedElectricKernel p.1.1 p.1.2.1 (velocity p.1.2.2)
      (fderiv ℝ velocity p.1.2.2 (p.2.2.1+cross (velocity p.1.2.2) p.2.2.2))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def GlobalFieldBound (T L : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x : Vec, ‖E (t,x)‖≤L ∧ ‖B (t,x)‖≤L

def SpatialFieldLip (T N : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x y : Vec,
    ‖E (t,y)-E (t,x)‖≤N*‖y-x‖ ∧ ‖B (t,y)-B (t,x)‖≤N*‖y-x‖

def FieldControl (T L N : ℝ) (E B : Field) : Prop :=
  GlobalFieldBound T L E B ∧ SpatialFieldLip T N E B

def PhaseParticleLip (T M : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, ∀ z z' : Phase, |f (t,z)-f (t,z')|≤M*‖z-z'‖

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

def CurvatureBound {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : U → W) (C : ℝ) : Prop :=
  ∀ x h, ‖f (x+h)+f (x-h)-(2:ℝ) • f x‖≤C*‖h‖^2

def SmoothLorentzFlow.reversePath {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) (u : ℝ) : Phase := F.forward (F.backward (t,z)) (t-u)

@[simp] lemma SmoothLorentzFlow.reversePath_zero {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) : F.reversePath t z 0=z := by
  simp [SmoothLorentzFlow.reversePath,F.right_inverse]

@[simp] lemma SmoothLorentzFlow.reversePath_end {E B : Field} (F : SmoothLorentzFlow E B)
    (t : ℝ) (z : Phase) : F.reversePath t z t=F.backward (t,z) := by
  simp [SmoothLorentzFlow.reversePath,F.initial]

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SmoothIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

def SmoothCompactFamily (F : α → E → W) : Prop :=
  (∀ a, ContDiff ℝ ∞ (F a)) ∧ ∀ n : ℕ,
    Continuous (fun p : E × α => iteratedFDeriv ℝ n (F p.2) p.1)

end CompactFamily

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_HighFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SpatialJetBound (n : ℕ) (T A : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, i ≤ n →
    ‖iteratedFDeriv ℝ i (fun y => E (t,y)) x‖ ≤ A ∧
    ‖iteratedFDeriv ℝ i (fun y => B (t,y)) x‖ ≤ A

def lorentzNonlinearity (w : Vec × (Vec × Vec)) : Phase :=
  (w.1,w.2.1+cross w.1 w.2.2)

def lorentzArgument (E B : Vec → Vec) (z : Phase) : Vec × (Vec × Vec) :=
  (velocity z.2,(E z.1,B z.1))

universe u

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section

def smoothReciprocal (δ x : ℝ) : ℝ := Real.smoothTransition (2*x/δ-1)/x

def smoothNormalisedPhysical (δ : ℝ) (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) : Vec :=
  let r := p.1.1
  let n := p.1.2.1
  let u := velocity p.1.2.2
  let b := fderiv ℝ velocity p.1.2.2 (p.2.2.1+cross u p.2.2.2)
  let D := 1-dot n u
  let R := (smoothReciprocal δ D)^3
  (p.2.1*D) • (((1-dot u u)*R) • (n-u)+(r*R) • ((dot n b) • (n-u)-D • b))

attribute [local instance] Measure.Subtype.measureSpace

variable (t P : ℝ)

abbrev ConeParameters := Sphere × Icc (0:ℝ) t × closedBall (0:Vec) P
abbrev coneParameterMeasure : Measure (ConeParameters t P) := sphereMeasure.prod (volume.prod volume)

def compactPolarIntegral (G : (ℝ × Vec × Vec) × Vec → Vec) (x : Vec) : Vec :=
  ∫ p : ConeParameters t P, G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x) ∂coneParameterMeasure t P

end

def normalisedRetardedExtension (δ : ℝ) (s : Solution) (t : ℝ)
    (p : (ℝ × Vec × Vec) × Vec) : Vec :=
  smoothNormalisedPhysical δ (p.1,
    (s.f (t-p.1.1,(p.2-p.1.1 • p.1.2.1,p.1.2.2)),
      s.E (t-p.1.1,p.2-p.1.1 • p.1.2.1),s.B (t-p.1.1,p.2-p.1.1 • p.1.2.1)))

def ParticleJetBound (n : ℕ) (T A : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc (0:ℝ) T, ∀ i : ℕ, i≤n → ∀ z, ‖iteratedFDeriv ℝ i (fun w => f (t,w)) z‖≤A

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_BoundaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section
attribute [local instance] Measure.Subtype.measureSpace

def datumWeightedSphere (f : Phase → ℝ) (H : Vec × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  (4*Real.pi)⁻¹*(∫ a : Sphere, p.1*(∫ v : Vec, f (p.2+p.1 • a.1,v)*H (a.1,v)) ∂sphereMeasure)

end

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SpatialFieldCurvature (T H : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, CurvatureBound (fun x => E (t,x)) H ∧ CurvatureBound (fun x => B (t,x)) H

def PhaseParticleCurvature (T H : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, CurvatureBound (fun z => f (t,z)) H

def curlMap : (Vec →L[ℝ] Vec) →L[ℝ] Vec :=
  ({ toFun := fun A => WithLp.toLp 2 ![A (basis 1) 2-A (basis 2) 1,
        A (basis 2) 0-A (basis 0) 2,A (basis 0) 1-A (basis 1) 0]
     map_add' := by intro A B; ext i; fin_cases i <;> simp <;> ring
     map_smul' := by intro r A; ext i; fin_cases i <;> simp <;> ring } :
       (Vec →L[ℝ] Vec) →ₗ[ℝ] Vec).toContinuousLinearMap

def divMap : (Vec →L[ℝ] Vec) →L[ℝ] ℝ :=
  ({ toFun := fun A => ∑ i : Fin 3, A (basis i) i
     map_add' := by intro A B; simp [Finset.sum_add_distrib]
     map_smul' := by intro r A; simp [Finset.mul_sum] } :
       (Vec →L[ℝ] Vec) →ₗ[ℝ] ℝ).toContinuousLinearMap

def assembleDerivative {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Dt : W) (Dx : U →L[ℝ] W) : (ℝ × U) →L[ℝ] W :=
  (ContinuousLinearMap.fst ℝ ℝ U).smulRight Dt+Dx.comp (ContinuousLinearMap.snd ℝ ℝ U)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SlabL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SlabTimeContinuousL2 (T : ℝ) (F : Field) : Prop :=
  ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t∈Icc 0 T, (F₂ t : Vec → Vec)=ᵐ[volume] (fun x => F (t,x))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SlabEquations (s : Solution) (T : ℝ) : Prop := ∀ t∈Icc 0 T,
  (∀ x v,
    derivWithin (fun t' => s.f (t', x, v)) (Icc 0 T) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f (t, y, v)) x i) +
    (∑ i : Fin 3, (s.E (t, x) + cross (velocity v) (s.B (t, x))) i *
      spatialPartial (fun v' => s.f (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Icc 0 T) t -
    curl (fun y => s.B (t, y)) x = -current (fun z => s.f (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Icc 0 T) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho (fun z => s.f (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

structure C1ClassicalPrefix (d : Datum) (s : Solution) (T : ℝ) : Prop where
  f_c1 : ContDiffOn ℝ 1 s.f (particleSlab T)
  E_c1 : ContDiffOn ℝ 1 s.E (fieldSlab T)
  B_c1 : ContDiffOn ℝ 1 s.B (fieldSlab T)
  nonnegative : ∀ t∈Icc 0 T, ∀ z, 0 ≤ s.f (t,z)
  E_L2 : SlabTimeContinuousL2 T s.E
  B_L2 : SlabTimeContinuousL2 T s.B
  compact : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K
  equations : EquationsBefore s T
  initial_f : ∀ z, s.f (0,z)=d.f₀ z
  initial_E : ∀ x, s.E (0,x)=d.E₀ x
  initial_B : ∀ x, s.B (0,x)=d.B₀ x

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SpatialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

def SpatiallySmoothSlab {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : ℝ) (F : ℝ × U → W) : Prop :=
  (∀ t∈Icc (0:ℝ) T, ContDiff ℝ ∞ (fun x => F (t,x))) ∧
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × U => iteratedFDeriv ℝ k (fun x => F (p.1,x)) p.2)
      {p | p.1∈Icc (0:ℝ) T}

universe u

def SpatialJetRegular {U W : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ∞) (J : Set ℝ) (F : ℝ × U → W) : Prop :=
  (∀ t∈J, ContDiff ℝ ∞ (fun x => F (t,x))) ∧
    ∀ j : ℕ, ContDiffOn ℝ n (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => F (p.1,x)) p.2) {p | p.1∈J}

end

universe u

end


open Set Filter Metric MeasureTheory
open scoped Topology

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

universe u

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SelectedConeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def selectedConeKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (p : ConeKernelState) : Vec :=
  stateCutoff T Q (coneCutoffState α zX p) • A p

def selectedConeTriangle (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    (J : Set ℝ) (p : TrianglePhase) : Vec :=
  J.indicator W p.1.1 (triangleConeKernel s α zX T (selectedConeKernel α zX T Q A) p)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SelectedRemainderPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def remainderConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  normalisedRemainder (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 (phaseAcceleration s.E s.B α zX p.1.1)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal

namespace RVM

def selectedMultiplierBulkDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (W : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p) (actualLabelCutoffCost s α zX T Q p)‖ +
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
    (labelSelectedCutoff α zX T Q p • actualLabelRemainder s α zX T p)‖

def selectedMultiplierWeightDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
    (labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p)‖

def selectedMultiplierMovingDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W' (labelReceiverTime α zX T p)
    (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p)‖

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeForceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def transportOnlyConeKernel (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  normalisedSignedForce (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 0

def sourceOnlyConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  sourceForceConeKernel s α zX p-transportOnlyConeKernel α zX p

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def directionRemaining : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}

def directionUnionBudget (E T w M A P Ct Cr Cf Cl Cg : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cr*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)+
  ENNReal.ofReal (Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)



section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal


structure WeightedDirectionPartition (V K : ℝ → Vec) (a b w δ : ℝ) where
  count : ℕ
  time : ℕ → ℝ
  ramp : ℕ → ℝ
  initial : time 0 = a
  terminal : time count = b
  time_mem : ∀ i ≤ count, time i ∈ Icc a b
  strict : StrictMonoOn time (Iic count)
  direction_control : ∀ i < count, ∀ t ∈ Icc (time i) (time (i+1)),
    ‖momentumDirection (V t) - momentumDirection (V (time i))‖ ≤ δ
  exit : ∀ i < count-1,
    ‖momentumDirection (V (time (i+1))) - momentumDirection (V (time i))‖ = δ
  ramp_pos : ∀ i < count-1, 0 < ramp i
  ramp_separation : ∀ i < count-1, 2*ramp i ≤ time (i+1)-time i
  signed_exit : ∀ i < count-1,
    w*δ/2 ≤ ‖∫ t in time i..time (i+1),
      directionWeight (time i) (time (i+1)) (ramp i) t • angularMultiplier w (V t) (K t)‖
  variation : ∀ i < count-1,
    (∫ t in time i..time (i+1), |deriv (directionWeight (time i) (time (i+1)) (ramp i)) t|) = 2

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def directionUnionConstant (E H M A Ct Cr Cf Cl Cg : ℝ) : ℝ :=
  Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H+
  Cr*(1+E)*(1+M+Real.sqrt A)+Cf*E*(1+16384*(M+Real.sqrt A))+
  Cl*(1+E)*H^2+Cg*H*(1+E)*(1+16384*(M+Real.sqrt A))



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def datumEnergyNumber (d : Datum) : ℝ :=
  ∫x : Vec,(‖d.E₀ x‖^2+‖d.B₀ x‖^2)/2+∫v : Vec,q v*d.f₀ (x,v)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open Set MeasureTheory
open scoped ENNReal

namespace RVM

def DirectionOverlap {ι κ : Type*} (l r : ι → ℝ) (l' r' : κ → ℝ) :=
  {ij : ι × κ // max (l ij.1) (l' ij.2) < min (r ij.1) (r' ij.2)}

noncomputable instance instFintypeDirectionOverlap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ) : Fintype (DirectionOverlap l r l' r') := by
  unfold DirectionOverlap
  exact Fintype.ofFinite _

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PartitionOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def directionGridRate (M A L : ℝ) : ℝ :=
  131072+536870912*(M+Real.sqrt (A*L))^2

def directionGridConstant (M A : ℝ) : ℝ :=
  131072+1073741824*(M^2+A)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def representativeGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (φ/(p*θ^2)) *
    (∫⁻z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
        ∂physicalBinMeasure V B (Icc a b))

def selectionDecay : ℝ := (2:ℝ)^(-1/100000:ℝ)

def pairCountConstant : ℝ := 2+1/Real.log 2

def representativeSelected (P M A w I : ℝ) (k : Fin 4→ℕ) : Prop :=
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  P*Real.sqrt I*selectionWeight P θ φ h <
    min (I*Real.sqrt h*p^2*φ^2)
      (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P 512 16384 M A p w φ h I)/(θ*h))

def representativeSmallSector (P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤P ∧
    1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16}

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def representativeJointEnergy {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (n : ℕ×ℕ) : ℝ :=
  (jointEnergyBudget s F.flow zX T 4 (max 0 (a-2*I)) (min T (b+I)) I n).toReal

def representativeSharedRadius {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A w a b I : ℝ) (n : ℕ×ℕ) : ℝ :=
  1+Real.sqrt (I/stabilityLength P 16384 M A (sourceRepresentative n.1) w
      (cappedRepresentative n.2))*Real.sqrt (representativeJointEnergy s F zX a b I n)

def representativeCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b)

def representativeSpatialCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cappedRepresentative (k 2)/cappedRepresentative (k 1))*
    representativeCentralCost s F zX w k a b

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CentralOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def regularCentralIndex (P M A I w : ℝ) (k : Fin 4→ℕ) : Prop :=
  512/min (sourceRepresentative (k 0)) w < cappedRepresentative (k 2) ∨
  min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
    (cappedRepresentative (k 2))) < cappedRepresentative (k 3)

noncomputable def representativeRegularCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then representativeCentralCost s F zX w k a b else 0

noncomputable def representativeExceptionCentralCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then 0 else representativeCentralCost s F zX w k a b

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_GoodCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

noncomputable def representativeRegularGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then
    representativeGoodCost s F zX w k a b else 0

noncomputable def representativeLowShortGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if cappedRepresentative (k 2)≤512/min (sourceRepresentative (k 0)) w ∧
    cappedRepresentative (k 3)≤I then representativeGoodCost s F zX w k a b else 0

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def spatialThresholdA (P p φ : ℝ) : ℝ :=
  P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/(p*φ)

def spatialThresholdB (P I p φ : ℝ) : ℝ :=
  P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/((32768:ℝ)^2*I*p^4*φ^4)

def centralIndexSector (P : ℝ) : Set (Fin 4→ℕ) :=
  {k | sourceRepresentative (k 0)≤P ∧
    1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 2) ∧
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16}

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def prefixConeDensity (s : Solution) (T : ℝ) (X : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  goodConeDensity s (prefixClamp T z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1) z.2.2.1

def representativeReceiverCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) (g : ℝ→ℝ≥0∞) : ℝ≥0∞ :=
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (θ/(w*φ^2)) *
    (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b))

def representativeTimeWeightCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w I : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (θ/(I*φ)) *
    (∫⁻z : ConeCoordinate,ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B (Icc a b))



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SpatialEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


def representativeMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (φ/p) *
    (∫⁻z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
        ∂physicalBinMeasure V B (Icc a b))

def representativeSpatialTransition (P M A w I : ℝ) (k : Fin 4→ℕ) : Prop :=
  ¬ representativeSelected P M A w I k ∧
    ∃j : Fin 4→ℕ,representativeSelected P M A w I j ∧
      ∀i,j i≤k i+2 ∧ k i≤j i+2

def bulkSelection (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/1024 ∧
    representativeSelected P M A w I k}

def bulkSourceBoundary (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | k∈representativeSmallSector P ∧
    (cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1) ∨
      representativeSpatialTransition P M A w I k)}


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


noncomputable def representativeExceptionSpatialCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then 0 else representativeSpatialCost s F zX w k a b



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkSpatialUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def bulkSpatialBoundary (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | k∈centralIndexSector P ∧
    (cappedRepresentative (k 2)/16384 ≤ cappedRepresentative (k 1) ∨
      representativeSpatialTransition P M A w I k)}

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MagneticEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

noncomputable def representativeRegularShortMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k ∧ cappedRepresentative (k 3)≤I then
    representativeMagneticCost s F zX w k a b else 0

noncomputable def representativeLowShortMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if cappedRepresentative (k 2)≤512/min (sourceRepresentative (k 0)) w ∧
    cappedRepresentative (k 3)≤I then representativeMagneticCost s F zX w k a b else 0

noncomputable def representativeLargeMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if I < cappedRepresentative (k 3) then representativeMagneticCost s F zX w k a b else 0

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


def relativeSourceAngle (θ φ σ : ℝ) : ℝ :=
  (min θ σ)^(3/2:ℝ)*(1+φ/σ)^(1/4:ℝ)

def relativeAngularConstant (K κ e : ℝ) : ℝ :=
  (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e+
    ((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))

def remainingGoodConstant (K κ β : ℝ) : ℝ :=
  relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*κ^(1/2+β)

def remainingMagneticConstant (K κ β : ℝ) : ℝ :=
  relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(3/2-β))⁻¹

def smallTransportCoefficient (k : Fin 4→ℕ) : ℝ :=
  4194304*cappedRepresentative (k 2)/((sourceRepresentative (k 0))^2*(cappedRepresentative (k 1))^3)


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directReceiverGoodBudget {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (nφ : ℕ) : ℝ :=
  (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1)
    (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal

def directReceiverMagneticBudget {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (nφ : ℕ) : ℝ :=
  2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectLargeAngularSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directDyadicPowerConstant (α : ℝ) : ℝ := (1-((2:ℝ)⁻¹)^α)⁻¹

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_UnselectedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

abbrev UnselectedCoverIndex (N : ℕ) := (Fin 4→ℕ) ⊕ (DirectOuterIndex N×ℕ)

def unselectedCoverBin (T w : ℝ) {N : ℕ} : UnselectedCoverIndex N→ClosedConeBin :=
  Sum.elim (representativeClosedBin T w) (fun i=>directOuterBin T w i.1 i.2)

def unselectedCoverSector (P M A w I : ℝ) (N : ℕ) : Set (UnselectedCoverIndex N) :=
  {i | match i with
    | .inl k => k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k
    | .inr i => sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_GoodSharedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


def goodInverseHalfConstant : ℝ := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹

noncomputable def representativeExceptionGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  if regularCentralIndex P M A I w k then 0 else representativeGoodCost s F zX w k a b


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectMixedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directMixedSector (P : ℝ) (N : ℕ) : Set (UnselectedCoverIndex N) :=
  {i | match i with
    | .inl k => k∈representativeSmallSector P
    | .inr i => sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_Bootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def PopulationIncrement {α : Type*} (V : α → ℝ → Vec) (K : Set α)
    (T M A P₀ : ℝ) : Prop :=
  ∀ τ ∈ Ico 0 T, ∀ k : ℕ, P₀ ≤ (2 : ℝ)^k →
    (∀ t ∈ Icc 0 τ, ∀ z ∈ K, 1024*q (V z t) ≤ (2 : ℝ)^k) →
    ∀ z ∈ K, IncrementBootstrap (V z) τ M A (2^k) (Real.log (2+2^k))

end RVM
end

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def incrementBound (M A P L w I : ℝ) : ℝ :=
  M*P*Real.sqrt I+A*I*(P^2*L/w)

def PhaseFlowOn.restrict {E B : Field} {T τ : ℝ} (F : PhaseFlowOn E B T) (hτT : τ≤T) :
    PhaseFlowOn E B τ where
  flow := F.flow
  differential := F.differential
  initial := F.initial
  ode := fun z t ht=>(F.ode z t ⟨ht.1,ht.2.trans hτT⟩).mono (Icc_subset_Icc le_rfl hτT)
  label := fun z t ht=>F.label z t ⟨ht.1,ht.2.trans hτT⟩
  det_one := fun z t ht=>F.det_one z t ⟨ht.1,ht.2.trans hτT⟩
  joint := fun z t ht=>F.joint z t ⟨ht.1,ht.2.trans_le hτT⟩
  bijective := fun t ht=>F.bijective t ⟨ht.1,ht.2.trans hτT⟩

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def crossBilinearCLM : Vec →L[ℝ] Vec →L[ℝ] Vec :=
  ({ toFun := crossCLM
     map_add' := by
       intro a b; ext c i; fin_cases i <;> simp [crossCLM,cross] <;> ring
     map_smul' := by
       intro r a; ext b i; fin_cases i <;> simp [crossCLM,cross] <;> ring } :
    Vec →ₗ[ℝ] Vec →L[ℝ] Vec).toContinuousLinearMap

def slabParticleRHS (s : Solution) (p : ℝ × Phase) : ℝ :=
  -(fderiv ℝ (fun z => s.f (p.1,z)) p.2) (lorentzField s.E s.B p)
def slabElectricRHS (s : Solution) (p : ℝ × Vec) : Vec :=
  curlMap (fderiv ℝ (fun x => s.B (p.1,x)) p.2) - current (fun z => s.f (p.1,z)) p.2
def slabMagneticRHS (s : Solution) (p : ℝ × Vec) : Vec :=
  -curlMap (fderiv ℝ (fun x => s.E (p.1,x)) p.2)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_StrongLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def BoundedSpatiallySmoothSlab {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : ℝ) (F : ℝ × U → W) : Prop :=
  SpatiallySmoothSlab T F ∧ ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x,
    ‖iteratedFDeriv ℝ k (fun y => F (t,y)) x‖≤C

def timeSliceDatum (s : Solution) (t : ℝ) : Datum :=
  ⟨fun z => s.f (t,z),fun x => s.E (t,x),fun x => s.B (t,x)⟩

structure DatumRestartControl (d : Datum) (A R P D D₁ A₁ : ℝ) : Prop where
  particle : ∀ z, |d.f₀ z|≤A
  support : ∀ z : Phase, d.f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P
  fields : ∀ x, ‖d.E₀ x‖≤D ∧ ‖d.B₀ x‖≤D
  boundary : ∀ t∈Ioc (0:ℝ) 1, ∀ x,
    ‖electricBoundaryField (datumBoundarySolution d) t x‖≤D ∧
    ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤D
  fields_lip : ∀ x y, ‖d.E₀ y-d.E₀ x‖≤D₁*‖y-x‖ ∧ ‖d.B₀ y-d.B₀ x‖≤D₁*‖y-x‖
  boundary_lip : ∀ t∈Ioc (0:ℝ) 1, ∀ x y,
    ‖electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x‖≤D₁*‖y-x‖ ∧
    ‖magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x‖≤D₁*‖y-x‖
  particle_lip : ∀ z w : Phase, |d.f₀ z-d.f₀ w|≤A₁*‖z-w‖

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def timePaste {U W : Type*} (T : ℝ) (F G : ℝ × U → W) (p : ℝ × U) : W :=
  if p.1≤T then F p else G (p.1-T,p.2)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SlabEvolutionRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

structure BoundedClassicalPrefix (d : Datum) (s : Solution) (T : ℝ) : Prop where
  classical : SmoothClassicalPrefix d s T
  closed_equations : SlabEquations s T
  f_jets : BoundedSpatiallySmoothSlab T s.f
  E_jets : BoundedSpatiallySmoothSlab T s.E
  B_jets : BoundedSpatiallySmoothSlab T s.B

def pasteSolution (T : ℝ) (s a : Solution) : Solution :=
  ⟨timePaste T s.f a.f,timePaste T s.E a.E,timePaste T s.B a.B⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_HomogeneousCancellation
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def transportAngularCore (n u : Vec) : Vec :=
  ((1-dot u u)/(1-dot n u)^2) • (n-u)

def sourceAngularCore (n u b : Vec) : Vec :=
  ((1-dot n u)^2)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b)

def transportSpatialFlux (v e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  (((coneRadius 0 z)^2)⁻¹*transportAngularCore (coneDirection 0 z) (velocity v) i) •
    coneSpatialLift 0 z v e

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalAngularBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def spatialTranslateParticle (x : Vec) (f : Particle) : Particle :=
  fun p => f (p.1,x+p.2.1,p.2.2)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_PhysicalDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def transportConeCoefficient (i : Fin 3) (p : Phase) : ℝ :=
  ((coneRadius 0 p.1)^2)⁻¹*transportAngularCore (coneDirection 0 p.1) (velocity p.2) i

def coneLorentz (s : Solution) (t : ℝ) (x : Vec) (p : Phase) : Vec :=
  s.E (t-coneRadius 0 p.1,x+p.1)+cross (velocity p.2) (s.B (t-coneRadius 0 p.1,x+p.1))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_TransportDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


section

def transportSingularShell (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (r : ℝ) : ℝ :=
  r⁻¹ * ∫ v in closedBall (0:Vec) P, ∫ n : Sphere,
    divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v) ∂sphereMeasure

attribute [local instance] Measure.Subtype.measureSpace

end

section
attribute [local instance] Measure.Subtype.measureSpace

def transportSingularBulk (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, divergence (transportSpatialFlux v e i) z * f (t-coneRadius 0 z,x+z,v)

end

def transportVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (transportAngularCore p.1.1 (velocity p.2) i *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

def transportVelocityBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, s.f (t-coneRadius 0 z,x+z,v)*
    divergence (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_TransportAngularCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def transportAngularCore (n u : Vec) : Vec :=
  cross n (RVM.transportAngularCore n u)

def sourceAngularCore (n u b : Vec) : Vec :=
  cross n (RVM.sourceAngularCore n u b)

def transportSpatialFlux (v e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  (((coneRadius 0 z)^2)⁻¹*transportAngularCore (coneDirection 0 z) (velocity v) i) •
    coneSpatialLift 0 z v e

def transportConeCoefficient (i : Fin 3) (p : Phase) : ℝ :=
  ((coneRadius 0 p.1)^2)⁻¹*transportAngularCore (coneDirection 0 p.1) (velocity p.2) i

def coneLorentz (s : Solution) (t : ℝ) (x : Vec) (p : Phase) : Vec :=
  s.E (t-coneRadius 0 p.1,x+p.1)+cross (velocity p.2) (s.B (t-coneRadius 0 p.1,x+p.1))

def transportSingularShell (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (r : ℝ) : ℝ :=
  r⁻¹ * ∫ v in closedBall (0:Vec) P, ∫ n : Sphere,
    divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v) ∂sphereMeasure

attribute [local instance] Measure.Subtype.measureSpace

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def transportVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (transportAngularCore p.1.1 (velocity p.2) i *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def sourceAngularProfile (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : ℝ :=
  sourceAngularCore p.1.1 (velocity p.2)
    (fderiv ℝ velocity p.2 (p.1.2.1+cross (velocity p.2) p.1.2.2)) i

def sourceFixedCoefficient (v E B : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  (coneRadius 0 z)⁻¹*sourceAngularProfile i ((coneDirection 0 z,E,B),v)

def sourceFixedFlux (v E B e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  sourceFixedCoefficient v E B i z • coneSpatialLift 0 z v e

def sourceConeCoefficient (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (p : Phase) : ℝ :=
  sourceFixedCoefficient p.2 (s.E (t-coneRadius 0 p.1,x+p.1))
    (s.B (t-coneRadius 0 p.1,x+p.1)) i p.1

def sourceJointFlux (e : Vec) (i : Fin 3) (p : Phase × Phase) : Vec :=
  sourceFixedFlux p.1.2 p.2.1 p.2.2 e i p.1.1

def sourceVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (sourceAngularProfile i p *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

def sourceDivisionBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P,s.f (t-coneRadius 0 z,x+z,v)*
    (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
      divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)

def sourceReceiverKernel (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceConeCoefficient s t p.1 i p.2

def sourceWeightedPacket (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceReceiverKernel s t i p*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

def sourceReceiverParticlePacket (s : Solution) (t : ℝ) (e : Vec) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  fderiv ℝ (sourceReceiverKernel s t i) p (e,0,0)*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceAngularProfile (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : ℝ :=
  sourceAngularCore p.1.1 (velocity p.2)
    (fderiv ℝ velocity p.2 (p.1.2.1+cross (velocity p.2) p.1.2.2)) i

def sourceFixedCoefficient (v E B : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  (coneRadius 0 z)⁻¹*sourceAngularProfile i ((coneDirection 0 z,E,B),v)

def sourceFixedFlux (v E B e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  sourceFixedCoefficient v E B i z • coneSpatialLift 0 z v e

def sourceConeCoefficient (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (p : Phase) : ℝ :=
  sourceFixedCoefficient p.2 (s.E (t-coneRadius 0 p.1,x+p.1))
    (s.B (t-coneRadius 0 p.1,x+p.1)) i p.1

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SourceJointFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceJointFlux (e : Vec) (i : Fin 3) (p : Phase × Phase) : Vec :=
  sourceFixedFlux p.1.2 p.2.1 p.2.2 e i p.1.1

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceVelocityProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (sourceAngularProfile i p *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportSingularBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

section
attribute [local instance] Measure.Subtype.measureSpace

def transportSingularBulk (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, divergence (transportSpatialFlux v e i) z * f (t-coneRadius 0 z,x+z,v)

end

def transportVelocityBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, s.f (t-coneRadius 0 z,x+z,v)*
    divergence (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceDivisionBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P,s.f (t-coneRadius 0 z,x+z,v)*
    (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
      divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_VolterraKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceReceiverKernel (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceConeCoefficient s t p.1 i p.2

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SourceWeightedPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceWeightedPacket (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceReceiverKernel s t i p*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

def sourceReceiverParticlePacket (s : Solution) (t : ℝ) (e : Vec) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  fderiv ℝ (sourceReceiverKernel s t i) p (e,0,0)*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

end RVM.Magnetic

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_GlobalContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def secondJetSum (s : Solution) (t : ℝ) (z : Phase) : ℝ :=
  ‖iteratedFDeriv ℝ 2 (fun w => s.f (t,w)) z‖+
  ‖iteratedFDeriv ℝ 2 (fun y => s.E (t,y)) z.1‖+
  ‖iteratedFDeriv ℝ 2 (fun y => s.B (t,y)) z.1‖

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end


