-- Prove2me | Definitions.Def_OAIQ078B002
-- name    : OAIQ078B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:24:10.182616+00:00
-- url     : https://prove2.me/theorems/b2f8cde2-7158-4c30-aa37-d53ae7fb25f8
-- title:
--   Definitions bundle OAIQ078B002 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 726 declarations of OpenAI's Lean: 481 definitions, 10 inductive types or structures, 10 instances and 225 theorems. The definitions and types are `OAI.CriticalPercolation.ClusterDeletion.residual`, `OAI.CriticalPercolation.Corridor.CoordinateData`, `OAI.CriticalPercolation.Corridor.CoordinateData.Bounds`, `OAI.CriticalPercolation.Corridor.CoordinateData.T`, `OAI.CriticalPercolation.Corridor.CoordinateData.scheme`, `OAI.CriticalPercolation.Corridor.GrowthState`, `OAI.CriticalPercolation.Corridor.GrowthState.Covered`, `OAI.CriticalPercolation.Corridor.GrowthState.Valid`, `OAI.CriticalPercolation.Corridor.GrowthState.advance`, `OAI.CriticalPercolation.Corridor.GrowthState.initial`, `OAI.CriticalPercolation.Corridor.Scheme`, `OAI.CriticalPercolation.Corridor.Scheme.Stable`, `OAI.CriticalPercolation.Corridor.Scheme.accepted`, `OAI.CriticalPercolation.Corridor.Scheme.actual`, `OAI.CriticalPercolation.Corridor.Scheme.allGood`, `OAI.CriticalPercolation.Corridor.Scheme.block`, `OAI.CriticalPercolation.Corridor.Scheme.edgeDomain`, `OAI.CriticalPercolation.Corridor.Scheme.enlarged`, `OAI.CriticalPercolation.Corridor.Scheme.hit`, `OAI.CriticalPercolation.Corridor.Scheme.incomingHit`, `OAI.CriticalPercolation.Corridor.Scheme.nextHit`, `OAI.CriticalPercolation.Corridor.Scheme.rootEvent`, `OAI.CriticalPercolation.Corridor.Scheme.rule`, `OAI.CriticalPercolation.Corridor.box`, `OAI.CriticalPercolation.Corridor.boxEdges`, `OAI.CriticalPercolation.Corridor.corridorEdges`, `OAI.CriticalPercolation.Corridor.domain`, `OAI.CriticalPercolation.Corridor.endpoints`, `OAI.CriticalPercolation.Corridor.graphBox`, `OAI.CriticalPercolation.Corridor.graphDomain`, `OAI.CriticalPercolation.Corridor.heightCenter`, `OAI.CriticalPercolation.Corridor.incoming`, `OAI.CriticalPercolation.Corridor.localHeight`, `OAI.CriticalPercolation.Corridor.localTime`, `OAI.CriticalPercolation.Corridor.mark`, `OAI.CriticalPercolation.Corridor.normalized`, `OAI.CriticalPercolation.Corridor.revealed`, `OAI.CriticalPercolation.Corridor.slotSite`, `OAI.CriticalPercolation.Corridor.source`, `OAI.CriticalPercolation.Corridor.target` and 451 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `BenjaminiSchramm_BallSnapshot`, `BenjaminiSchramm_Cayley`, `BenjaminiSchramm_ExteriorConnection`, `BenjaminiSchramm_FiniteEnergyModification`, `BenjaminiSchramm_FreshSlabCrossing`, `BenjaminiSchramm_GhostBondBK`, `BenjaminiSchramm_GhostField`, `BenjaminiSchramm_GhostPivotalBoundary`, `BenjaminiSchramm_GhostPivotalGeometry`, `BenjaminiSchramm_HeightMaximumSlices`, `BenjaminiSchramm_IntrinsicBallExposure`, `BenjaminiSchramm_IntrinsicBallGrowth`, `BenjaminiSchramm_IntrinsicConnection`, `BenjaminiSchramm_IntrinsicSphere`, `BenjaminiSchramm_KernelDeletionDiagram`, `BenjaminiSchramm_KernelExterior`, `BenjaminiSchramm_LayerFrontierExpectation`, `BenjaminiSchramm_LayerFrontierGeometry`, `BenjaminiSchramm_PeakClusterCorrelation`, `BenjaminiSchramm_PhaseInput`, `BenjaminiSchramm_PublishedConsequences`, `BenjaminiSchramm_SelectedLayerVertex`, `BenjaminiSchramm_ThinSphere`, `BenjaminiSchramm_ThinSphereStopping`, `BenjaminiSchramm_TiltedGhost`, `BenjaminiSchramm_TiltedMomentBridge`, `BenjaminiSchramm_TiltedMoments`, `CriticalPercolation_Clusters_DeleteBot`, `CriticalPercolation_Criticality_ActualGrowth`, `CriticalPercolation_Criticality_BoundaryCount`, `CriticalPercolation_Criticality_CutInside`, `CriticalPercolation_Criticality_DeleteImageIso`, `CriticalPercolation_Criticality_GrowthProcess`, `CriticalPercolation_Criticality_Leak`, `CriticalPercolation_Criticality_SharpnessPhi`, `CriticalPercolation_Criticality_TwoPoint`, `CriticalPercolation_Criticality_Weight`, `CriticalPercolation_Entropy_AeEvalNe`, `CriticalPercolation_Entropy_MarkedEntropy`, `CriticalPercolation_Entropy_ReverseGuess`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_AncestryForest`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_ClosedPivotWeight`, `CriticalPercolation_Exploration_ClusterUsers`, `CriticalPercolation_Exploration_Exhaustive`, `CriticalPercolation_Exploration_GlobalNode`, `CriticalPercolation_Exploration_GrowthHistoryGeometry`, `CriticalPercolation_Exploration_IncidenceIdentity`, `CriticalPercolation_Exploration_IncidenceSearch`, `CriticalPercolation_Exploration_ListScore`, `CriticalPercolation_Exploration_LocalNode`, `CriticalPercolation_Exploration_Node`, `CriticalPercolation_Exploration_PhaseFrontier`, `CriticalPercolation_Exploration_PrefixState`, `CriticalPercolation_Exploration_QueryTree`, `CriticalPercolation_Exploration_Score`, `CriticalPercolation_Exploration_SearchTree`, `CriticalPercolation_Exploration_Select`, `CriticalPercolation_Exploration_State`, `CriticalPercolation_Exploration_TargetSearch`, `CriticalPercolation_Exploration_Users`, `CriticalPercolation_Exploration_Visits`, `CriticalPercolation_Gluing_CorridorGraph`, `CriticalPercolation_Gluing_CorridorNormalization`, `CriticalPercolation_Gluing_CorridorSeparation`, `CriticalPercolation_Gluing_StoredPrediction`, `CriticalPercolation_GraphGeometry_CoordinateScheme`, `CriticalPercolation_GraphGeometry_LatticeGrowth`, `CriticalPercolation_GraphGeometry_Link2`, `CriticalPercolation_GraphGeometry_VertexBall`, `CriticalPercolation_Growth_HomogeneousAverage`, `CriticalPercolation_Growth_HomogeneousGrowth`, `CriticalPercolation_Growth_HomogeneousTransport`, `CriticalPercolation_Modular_ClusterMassInfinite`, `CriticalPercolation_Modular_ClusterTransportFinite`, `CriticalPercolation_Modular_ClusterTransportGeometry`, `CriticalPercolation_Modular_ClusterTransportSums`, `CriticalPercolation_Modular_InputMass`, `CriticalPercolation_Modular_OrderMass`, `CriticalPercolation_Modular_WeightedQuery`, `CriticalPercolation_ProductMeasure_Potential`, `CriticalPercolation_ProductMeasure_QueryMartingale`, `CriticalPercolation_ProductMeasure_Variance`, `UnimodularPercolation_Clusters_ExteriorMoments`, `UnimodularPercolation_Clusters_KernelMoments`, `UnimodularPercolation_Clusters_LargeContacts`, `UnimodularPercolation_Clusters_Resampling`, `UnimodularPercolation_Clusters_Uniqueness`, `UnimodularPercolation_Criticality_Operator`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Deformation_AveragedDecrease`, `UnimodularPercolation_Deformation_Calibration`, `UnimodularPercolation_Deformation_ClusterProducts`, `UnimodularPercolation_Deformation_Corridors`, `UnimodularPercolation_Deformation_Derivatives`, `UnimodularPercolation_Escape_CollisionTails`, `UnimodularPercolation_Escape_Labels`, `UnimodularPercolation_Escape_PathSelection`, `UnimodularPercolation_Escape_PositiveEscapes`, `UnimodularPercolation_Escape_SelectionBounds`, `UnimodularPercolation_Exploration_FractionalMoments`, `UnimodularPercolation_Exploration_Goodness`, `UnimodularPercolation_Exploration_Marked`, `UnimodularPercolation_Exploration_Moments`, `UnimodularPercolation_Exploration_TailBounds`, `UnimodularPercolation_Graph_Automorphisms`, `UnimodularPercolation_Graph_Basic`, `UnimodularPercolation_Graph_Paths`, `UnimodularPercolation_Kernel_Amplification`, `UnimodularPercolation_Kernel_Bounds`, `UnimodularPercolation_Kernel_Connections`, `UnimodularPercolation_Kernel_ContactTrace`, `UnimodularPercolation_Kernel_Covariance`, `UnimodularPercolation_Kernel_DistinctMoments`, `UnimodularPercolation_Kernel_RussoRows`, `UnimodularPercolation_Kernel_ScaleBudget`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_Kernel_TraceBounds`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_EndpointMoments`, `UnimodularPercolation_Splicing_GapCodes`, `UnimodularPercolation_Splicing_Geometry`, `UnimodularPercolation_Splicing_MomentBounds`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`, `UnimodularPercolation_Subdivision_Coupling`, `UnimodularPercolation_Subdivision_Graph`, `UnimodularPercolation_Transport_EndpointKernels`, `UnimodularPercolation_Transport_TrajectoryMass`, `UnimodularPercolation_TwoCluster_Bounds`, `UnimodularPercolation_TwoCluster_Score`, `UnimodularPercolation_TwoCluster_Transport`.
--
--   **Imports.** It imports the published bundle `Def_BenjaminiSchramm`; the bundles `OAIQ078B000` and `OAIQ078B001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_CriticalPercolation_BinaryLaw_conditioned_configuration_entropy`, `OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_event_bound`, `OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_inverse_cost`, `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_pair_entropy`, `OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_twoPoint_decay`, `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs`, `OAI_CriticalPercolation_ExactExposure_marked_pair_bound`, `OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs`, `OAI_CriticalPercolation_LazyDFS_young_phase_score_bound`, `OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs`, `OAI_CriticalPercolation_Sharpness_local_bound_propagation`, `OAI.CriticalPercolation.Sharpness.local_bound_propagation_bs`, `OAI_Percolation_BenjaminiSchramm_criticalRadiiInput_of_nonamenable`, `OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs`, `OAI_Percolation_BenjaminiSchramm_critical_ceiling_zero_band_profile`, `OAI.Percolation.BenjaminiSchramm.critical_ceiling_zero_band_profile_bs`, `OAI_Percolation_BenjaminiSchramm_critical_endpoint_fractional_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_endpoint_fractional_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_fullspace_threeQuarter_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_halfspace_fractional_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_lower_slab_fractional_profile`, `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs`, `OAI_Percolation_BenjaminiSchramm_critical_normalized_exact_exponent`, `OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent_bs`, `OAI_Percolation_BenjaminiSchramm_critical_peak_comparison_at_rate`, `OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs`, `OAI_Percolation_BenjaminiSchramm_critical_slab_fractional_of_peak_survival`, `OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_conditional`, `OAI.Percolation.BenjaminiSchramm.full_application_conditional_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_gap`, `OAI.Percolation.BenjaminiSchramm.full_application_gap_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_reduced`, `OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs`, `OAI_Percolation_BenjaminiSchramm_normalized_peak_surgery`, `OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs`, `OAI_Percolation_BenjaminiSchramm_root_quarterGhost_differential`, `OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_layer_prefactor`, `OAI.Percolation.BenjaminiSchramm.subcritical_layer_prefactor_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_peak_band_probability`, `OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_weighted_peak_conditional_layers`, `OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs`, `OAI_Percolation_BenjaminiSchramm_subdivision_gap_input_proved`, `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs`, `OAI_Percolation_BenjaminiSchramm_unrestricted_upward_bound_of_layer_rate`, `OAI.Percolation.BenjaminiSchramm.unrestricted_upward_bound_of_layer_rate_bs`, `OAI_Percolation_critical_bounded_of_transport_finiteness`, `OAI.Percolation.critical_bounded_of_transport_finiteness_bs`, `OAI_Percolation_critical_rootTriangleSqrt_derivative`, `OAI.Percolation.critical_rootTriangleSqrt_derivative_bs`, `OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment`, `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_bs`, `OAI_Percolation_exists_finite_scale_obstruction` and `OAI.Percolation.exists_finite_scale_obstruction_bs`; the proofs of `OAI_CriticalPercolation_BinaryLaw_conditioned_configuration_entropy`, `OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_event_bound`, `OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_inverse_cost`, `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_pair_entropy`, `OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs`, `OAI_CriticalPercolation_BinaryLaw_conditioned_reference_density_le`, `OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs`, `OAI_CriticalPercolation_BinaryLaw_selected_density_le`, `OAI.CriticalPercolation.BinaryLaw.selected_density_le_bs`, `OAI_CriticalPercolation_BondGraph_CombinatoriallyUnimodular_exponential_critical_null`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs`, `OAI_CriticalPercolation_BondGraph_UnimodularRoot_subcritical_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.UnimodularRoot.subcritical_adjacent_bound_bs`, `OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction`, `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs`, `OAI_CriticalPercolation_BondGraph_critical_null_of_action_coordinates`, `OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs`, `OAI_CriticalPercolation_BondGraph_critical_strip_null`, `OAI.CriticalPercolation.BondGraph.critical_strip_null_bs`, `OAI_CriticalPercolation_BondGraph_eventually_no_superpolynomial_band`, `OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs`, `OAI_CriticalPercolation_BondGraph_expected_heavy_normalizedDiscrepancy_bound`, `OAI.CriticalPercolation.BondGraph.expected_heavy_normalizedDiscrepancy_bound_bs`, `OAI_CriticalPercolation_BondGraph_fresh_contact_transfer`, `OAI.CriticalPercolation.BondGraph.fresh_contact_transfer_bs`, `OAI_CriticalPercolation_BondGraph_halfspace_fractional_profile_bootstrap`, `OAI.CriticalPercolation.BondGraph.halfspace_fractional_profile_bootstrap_bs`, `OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample`, `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs`, `OAI_CriticalPercolation_BondGraph_main_light_or_sparse_polynomial_boundary`, `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae`, `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_critical_twoPoint_decay`, `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs`, `OAI_CriticalPercolation_BondGraph_nonunimodular_no_percolation_at_criticality`, `OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs`, `OAI_CriticalPercolation_BondGraph_normalized_crossing_exponent_approximation`, `OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs`, `OAI_CriticalPercolation_BondGraph_peak_sprinkling_eventual_survival`, `OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs`, `OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs`, `OAI_CriticalPercolation_BondGraph_subcritical_normalized_layer_rate`, `OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs`, `OAI_CriticalPercolation_BondGraph_subcritical_seedExpectation_bound`, `OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs`, `OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs`, `OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks`, `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_bs`, `OAI_CriticalPercolation_BondGraph_uniform_rooted_probability`, `OAI.CriticalPercolation.BondGraph.uniform_rooted_probability_bs`, `OAI_CriticalPercolation_BondGraph_upward_ceiling_profile`, `OAI.CriticalPercolation.BondGraph.upward_ceiling_profile_bs`, `OAI_CriticalPercolation_BondGraph_upward_fractional_slab_profile`, `OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs`, `OAI_CriticalPercolation_ExactExposure_marked_pair_bound`, `OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs`, `OAI_CriticalPercolation_HomogeneousAnalysis_Geometry_finite_stabilizer_harmonic_image`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image_bs`, `OAI_CriticalPercolation_LazyDFS_young_phase_score_bound`, `OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs`, `OAI_CriticalPercolation_Sharpness_critical_null_of_unique`, `OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs`, `OAI_CriticalPercolation_Sharpness_local_bound_propagation`, `OAI.CriticalPercolation.Sharpness.local_bound_propagation_bs`, `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI_Percolation_BenjaminiSchramm_criticalRadiiInput_of_nonamenable`, `OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs`, `OAI_Percolation_BenjaminiSchramm_critical_ceiling_zero_band_profile`, `OAI.Percolation.BenjaminiSchramm.critical_ceiling_zero_band_profile_bs`, `OAI_Percolation_BenjaminiSchramm_critical_endpoint_fractional_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_endpoint_fractional_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_finite_general`, `OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs`, `OAI_Percolation_BenjaminiSchramm_critical_fullspace_threeQuarter_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_halfspace_fractional_profiles`, `OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs`, `OAI_Percolation_BenjaminiSchramm_critical_lower_slab_fractional_profile`, `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs`, `OAI_Percolation_BenjaminiSchramm_critical_normalized_exact_exponent`, `OAI.Percolation.BenjaminiSchramm.critical_normalized_exact_exponent_bs`, `OAI_Percolation_BenjaminiSchramm_critical_peak_comparison_at_rate`, `OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs`, `OAI_Percolation_BenjaminiSchramm_critical_slab_fractional_of_peak_survival`, `OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs`, `OAI_Percolation_BenjaminiSchramm_critical_volume_upper_of_operator`, `OAI.Percolation.BenjaminiSchramm.critical_volume_upper_of_operator_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_conditional`, `OAI.Percolation.BenjaminiSchramm.full_application_conditional_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_gap`, `OAI.Percolation.BenjaminiSchramm.full_application_gap_bs`, `OAI_Percolation_BenjaminiSchramm_full_application_reduced`, `OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs`, `OAI.Percolation.BenjaminiSchramm.full_main`, `OAI_Percolation_BenjaminiSchramm_normalized_peak_surgery`, `OAI.Percolation.BenjaminiSchramm.normalized_peak_surgery_bs`, `OAI_Percolation_BenjaminiSchramm_root_quarterGhost_differential`, `OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_layer_prefactor`, `OAI.Percolation.BenjaminiSchramm.subcritical_layer_prefactor_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_peak_band_probability`, `OAI.Percolation.BenjaminiSchramm.subcritical_peak_band_probability_bs`, `OAI_Percolation_BenjaminiSchramm_subcritical_weighted_peak_conditional_layers`, `OAI.Percolation.BenjaminiSchramm.subcritical_weighted_peak_conditional_layers_bs`, `OAI_Percolation_BenjaminiSchramm_subdivision_gap_input_proved`, `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs`, `OAI_Percolation_BenjaminiSchramm_susceptibility_upper_of_critical_operator`, `OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs`, `OAI_Percolation_BenjaminiSchramm_unrestricted_upward_bound_of_layer_rate`, `OAI.Percolation.BenjaminiSchramm.unrestricted_upward_bound_of_layer_rate_bs`, `OAI_Percolation_critical_bounded_of_transport_finiteness`, `OAI.Percolation.critical_bounded_of_transport_finiteness_bs`, `OAI_Percolation_critical_rootTriangleSqrt_derivative`, `OAI.Percolation.critical_rootTriangleSqrt_derivative_bs`, `OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment`, `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment_bs`, `OAI_Percolation_exists_finite_scale_obstruction` and `OAI.Percolation.exists_finite_scale_obstruction_bs`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Potential
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def potential (w : E → Prop → ℝ) (U R : Set E → Prop) : ℝ :=
  prob w R - (prob w R)^2/prob w U

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Variance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def variance (w : E → Prop → ℝ) (F : Set E → Prop) : ℝ :=
  prob w F - (prob w F)^2

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Basic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

theorem conn_trans {x y z : V} (hxy : Conn G ω x y) (hyz : Conn G ω y z) :
    Conn G ω x z := hxy.trans hyz

theorem conn_symm {x y : V} (h : Conn G ω x y) : Conn G ω y x := by
  induction h with
  | refl => exact conn_refl G ω _
  | @tail y z _ hyz ih =>
    rcases hyz with ⟨e, he, hlink⟩
    exact (Relation.ReflTransGen.single ⟨e, he, hlink.trans (Sym2.eq_swap ..)⟩).trans ih

theorem conn_mono {ω₁ ω₂ : Set E} (hω : ω₁ ⊆ ω₂) {x y : V}
    (h : Conn G ω₁ x y) : Conn G ω₂ x y := by
  apply Relation.ReflTransGen.mono (r := fun a b => ∃ e ∈ ω₁, G e = s(a, b)) ?_ x y h
  rintro a b ⟨e, he, hab⟩
  exact ⟨e, hω he, hab⟩

end Deterministic

section Probability
variable (G : BondGraph V E)

theorem twoPoint_nonneg (p : unitInterval) (x y : V) : 0 ≤ twoPoint G p x y :=
  ENNReal.toReal_nonneg

end Probability

section Countability


def reachBall (G : BondGraph V E) (x : V) : ℕ → Set V
  | 0 => {x}
  | n + 1 => reachBall G x n ∪ ⋃ y ∈ reachBall G x n, {z | Adj G y z}

theorem finite_reachBall {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    ∀ n, (reachBall G x n).Finite := by
  intro n
  induction n with
  | zero => exact Set.finite_singleton x
  | succ n hn =>
    exact hn.union (hn.biUnion (fun y _ => finite_neighbors hG y))

theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Measurability

 

theorem measurableSet_conn [Countable V] [Countable E]
    (G : BondGraph V E) (x y : V) : MeasurableSet {ω | Conn G ω x y} := by
  classical
  have hedge (a b : V) : MeasurableSet {ω : Set E | ∃ e ∈ ω, G e = s(a, b)} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro e
    by_cases he : G e = s(a, b)
    · simpa [he] using (measurableSet_setOfPred.mpr (measurable_set_mem e))
    · simp [he]
  have hlist (l : List V) : MeasurableSet {ω : Set E |
      l.IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b))} := by
    induction l with
    | nil => simp
    | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
        simpa only [List.isChain_cons_cons, Set.ofPred_and] using (hedge a b).inter ih
  have he : {ω | Conn G ω x y} = ⋃ l : List V,
      {ω | (x :: l).IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b)) ∧
        (x :: l).getLast (by simp) = y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hy⟩ => List.relationReflTransGen_of_exists_isChain_cons l hl hy⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  by_cases hlast : (x :: l).getLast (by simp) = y
  · simpa [hlast] using hlist (x :: l)
  · simp [hlast]

end Measurability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology


def clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ t : Finset V, n ≤ t.card ∧ ∀ y ∈ t, Conn G ω x y}

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable


theorem law_map_preimage_equiv (p : unitInterval) (b : E ≃ E) :
    (law p : Measure (Set E)).map (fun ω => b ⁻¹' ω) = law p := by
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_set_preimage b) measurable_setOfPred]
  have he : (fun ω : Set E => b ⁻¹' ω) ∘ (fun f : E → Prop => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘
        MeasurableEquiv.piCongrLeft (fun _ : E => Prop) b.symm := by
    funext f
    ext e
    simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq]
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => Prop) b.symm f (b e)
    exact iff_of_eq (by simpa only [Equiv.symm_apply_apply] using hh.symm)
  rw [he, ← Measure.map_map measurable_setOfPred (MeasurableEquiv.measurable _)]
  simp only [Set.mem_univ]
  congr 1
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : E => unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False) b.symm

theorem cluster_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x : V) :
    a '' cluster G (b ⁻¹' ω) x = cluster G ω (a x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (conn_aut_iff G h ω x z).mp hz
  · intro hy
    change Conn G ω (a x) y at hy
    refine ⟨a.symm y, ?_, by simp⟩
    exact (conn_aut_iff G h ω x (a.symm y)).mpr (by simpa only [Equiv.apply_symm_apply] using hy)

end Automorphisms

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Uniqueness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section InfiniteOrbits
attribute [local instance] Classical.propDecidable

def vertexOrbit (G : BondGraph V E) (x : V) : Set V :=
  {y | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a x = y}

theorem adj_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} (hxy : Adj G x y) : Adj G (a x) (a y) := by
  obtain ⟨e, he⟩ := hxy
  exact ⟨b e, by rw [h e, he, Sym2.map_mk]⟩

theorem mem_reachBall_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} {n : ℕ} (hy : y ∈ reachBall G x n) :
    a y ∈ reachBall G (a x) n := by
  induction n generalizing y with
  | zero => simpa only [reachBall, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq] using hy
  | succ n ih =>
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · change a y ∈ reachBall G (a x) n ∪ ⋃ z ∈ reachBall G (a x) n, {w | Adj G z w}
      apply Or.inr
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy ⊢
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨a z, ih hz, adj_aut G h hzy⟩



end InfiniteOrbits

section CoupledCovers
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]


def TouchedCover (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    (labels : E → unitInterval) : Prop :=
  ∃ f : Fin n → V, ∀ x, (cluster G (openEdges labels p) x).Infinite →
    ∃ i, Conn G (openEdges labels q) x (f i)

end CoupledCovers

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Paths
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 def Step (G : BondGraph V E) (x : V) := {ey : E × V // G ey.1 = s(x,ey.2)}

 noncomputable def stepEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : Step G x ≃ Step G (a x) where
  toFun d := ⟨(b d.val.1, a d.val.2), by rw [h, d.property, Sym2.map_mk]⟩
  invFun d := ⟨(b.symm d.val.1, a.symm d.val.2), by
    rw [isAut_symm G h, d.property, Sym2.map_mk, Equiv.symm_apply_apply]⟩
  left_inv d := by apply Subtype.ext; exact Prod.ext (b.symm_apply_apply _) (a.symm_apply_apply _)
  right_inv d := by apply Subtype.ext; exact Prod.ext (b.apply_symm_apply _) (a.apply_symm_apply _)

 noncomputable def degree (G : BondGraph V E) (x : V) : ℕ := Nat.card (Step G x)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

def TrailLength (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y l, Along G x l y ∧ l.Nodup ∧ l.length = n ∧ ∀ e ∈ l, e ∈ ω}

 theorem Along.mem_reachBall {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) : y ∈ reachBall G x l.length := by
  induction h with
  | nil => exact Set.mem_singleton _
  | @cons x z y l e he ht ih =>
    have hadj : Adj G x z := ⟨e,he⟩
    have hstep : ∀ n, reachBall G z n ⊆ reachBall G x (n+1) := by
      intro n
      induction n with
      | zero =>
        rintro w rfl
        exact Or.inr (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨Set.mem_singleton _, hadj⟩⟩)
      | succ n ih =>
        rintro w (hw | hw)
        · exact Or.inl (ih hw)
        · right
          simp only [Set.mem_iUnion] at hw ⊢
          obtain ⟨v,hv,hvw⟩ := hw
          exact ⟨v,ih hv,hvw⟩
    exact hstep _ ih

 theorem reachBall_mono (G : BondGraph V E) (x : V) : Monotone (reachBall G x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

noncomputable def fieldLaw (p a : unitInterval) : Measure (Bool → Set E) :=
  Measure.infinitePi (fun b => law (pairParameter p a b))

end SprinklingLaw

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 noncomputable def dartSource (G : BondGraph V E) (d : E × Bool) : V :=
   if d.2 then (G d.1).out.1 else (G d.1).out.2
 noncomputable def dartTarget (G : BondGraph V E) (d : E × Bool) : V :=
   if d.2 then (G d.1).out.2 else (G d.1).out.1

end ColoredSprinkling

section FiniteGraphOperators
attribute [local instance] Classical.propDecidable

 noncomputable def edgeVertices [Fintype E] (G : BondGraph V E) : Finset V :=
   Finset.univ.biUnion (fun e => (G e).toFinset)

 noncomputable def adjacencyOperator [Fintype E] (G : BondGraph V E) :
    Hilbert V →L[ℂ] Hilbert V :=
  ∑ d : E × Bool, (lp.singleContinuousLinearMap ℂ (fun _ : V => ℂ) 2 (dartSource G d)).comp
    (lp.evalCLM ℂ (fun _ : V => ℂ) 2 (dartTarget G d))

end FiniteGraphOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
theorem conn_insert_iff (G : BondGraph V E) (ω : Set E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    Conn G (insert e ω) x y ↔ Conn G ω x y ∨
      (Conn G ω x a ∧ Conn G ω b y) ∨ (Conn G ω x b ∧ Conn G ω a y) := by
  constructor
  · intro hh
    induction hh with
    | refl => exact Or.inl (conn_refl G ω x)
    | @tail u v huv huv' ih =>
      obtain ⟨f,hf,hfuv⟩ := huv'
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · have hp : s(a,b) = s(u,v) := he.symm.trans hfuv
        rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rcases ih with h | ⟨hxa,hba⟩ | ⟨hxb,haa⟩
          · exact Or.inr (Or.inl ⟨h,conn_refl G ω b⟩)
          · exact Or.inr (Or.inl ⟨hxa,conn_refl G ω b⟩)
          · exact Or.inl hxb
        · rcases ih with h | ⟨hxa,hbb⟩ | ⟨hxb,hab⟩
          · exact Or.inr (Or.inr ⟨h,conn_refl G ω a⟩)
          · exact Or.inl hxa
          · exact Or.inr (Or.inr ⟨hxb,conn_refl G ω a⟩)
      · have huvω : Conn G ω u v := .single ⟨f,hf,hfuv⟩
        rcases ih with h | ⟨hxa,hbu⟩ | ⟨hxb,hau⟩
        · exact Or.inl (h.trans huvω)
        · exact Or.inr (Or.inl ⟨hxa,hbu.trans huvω⟩)
        · exact Or.inr (Or.inr ⟨hxb,hau.trans huvω⟩)
  · intro hh
    have hm : ω ⊆ insert e ω := Set.subset_insert e ω
    have hab : Conn G (insert e ω) a b := .single ⟨e,Set.mem_insert e ω,he⟩
    rcases hh with h | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
    · exact conn_mono G hm h
    · exact (conn_mono G hm hxa).trans (hab.trans (conn_mono G hm hby))
    · exact (conn_mono G hm hxb).trans ((conn_symm G _ hab).trans (conn_mono G hm hay))


def escapeEvent (G : BondGraph V E) (Λ : Set V) (x : V) : Set (Set E) :=
  {ω | x ∉ unexposed G Λ ω}

attribute [local instance] Classical.decEq


noncomputable def internalSupport (G : BondGraph V E) (S : Set V) (F : Finset E) : Finset E :=
  F.filter (fun e => e ∈ internalEdges G S)


noncomputable def regionProbability (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial F (fun t => if unexposed G Λ (t : Set E) = S then 1 else 0) p


def crossingReach (G : BondGraph V E) (S : Set V) (x : V) (ω : Set E) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S ∧ Conn G ω x a

noncomputable def crossingCount (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if crossingReach G S x ω e then (1:ℝ) else 0

 
noncomputable def boundaryExpectation (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial (internalSupport G S F)
    (fun t => crossingCount G S x F (t : Set E)) p

noncomputable def closedEscapeCount (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if ω ∈ closedPivotal (escapeEvent G Λ x) e then (1:ℝ) else 0

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem incidentSupport_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    {S Λ : Finset V} (hS : S ⊆ Λ) : incidentSupport G hloc S ⊆ incidentSupport G hloc Λ := by
  intro e he
  obtain ⟨x,hx,hxe⟩ := (mem_incidentSupport G hloc S e).mp he
  exact (mem_incidentSupport G hloc Λ e).mpr ⟨x,hS hx,hxe⟩


noncomputable def boundaryCost (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : ℝ) : ℝ :=
  p*boundaryExpectation G S x (incidentSupport G hloc S) p

theorem incidentSupport_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) :
    incidentSupport G hloc (S.map a.toEmbedding) =
      (incidentSupport G hloc S).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp only [mem_incidentSupport,Finset.mem_map,Equiv.toEmbedding_apply,
    b.injective.eq_iff,exists_eq_right]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,hx⟩
    rw [h d,Sym2.mem_map] at hx
    obtain ⟨z,hz,hzy⟩ := hx
    have hz' : z = y := a.injective hzy
    exact ⟨y,hy,hz' ▸ hz⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨a x,⟨x,hx,rfl⟩,by rw [h d]; exact Sym2.mem_map.mpr ⟨x,he,rfl⟩⟩

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainTwoPoint (G : BondGraph V E) (S : Set V) (p : unitInterval)
    (x y : V) : ℝ := (law p).real {ω | Conn G (ω ∩ internalEdges G S) x y}

theorem conn_internal_endpoint (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (hx : x ∈ S) (h : Conn G (ω ∩ internalEdges G S) x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ((mem_internalEdges_of_ends G S e a b heq).mp he.2).2

noncomputable def cutInside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose else Classical.arbitrary V

noncomputable def cutOutside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose_spec.choose else Classical.arbitrary V

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Marked
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GraphMarkedSearch
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
def SearchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ t.2.2 ∉ R ∧ G t.1 = s(t.2.1,t.2.2)

noncomputable def searchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) : E × V × V := Classical.choose h


def SearchAvailable (G : BondGraph V E) (Q : Finset E) (R F : Finset V) : Prop :=
  ∀ e ∈ Q, ∀ v ∈ G e, v ∈ R ∨ v ∈ F

noncomputable def clusterSearch (G : BondGraph V E) : ℕ → Finset E → Finset V → LabelledTree V E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .edge t.1 (clusterSearch G n (Q.erase t.1) R)
        (.mark t.2.2 (clusterSearch G n (Q.erase t.1) (insert t.2.2 R)) (.done true))
    else .done false


def SeedMarked (G : BondGraph V E) (ω : Set E) (R m : Finset V) : Prop :=
  ∃ a ∈ R, ∃ b ∈ m, Conn G ω a b

end GraphMarkedSearch

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def queryPotential (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Finset E :=
  Q.filter (fun e => ∃ v ∈ R, v ∈ G e)

noncomputable def searchVertices (G : BondGraph V E) (Q : Finset E) : Finset V :=
  Q.biUnion fun e => (G e).toFinset

noncomputable def markedClusterTree (G : BondGraph V E) (Q : Finset E) (x : V) : LabelledTree V E :=
  .mark x (clusterSearch G Q.card Q {x}) (.done true)

end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def markedConnectionPolynomial (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => if ∃ y ∈ m, Conn G (ω : Set E) x y then 1 else 0) h) p


noncomputable def markedPivotalMomentOne (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => ((markedOpenPivotals G Q x ω m).card:ℝ)) h) p

end MarkedFirstMoment

section PivotalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


theorem edge_cluster_sides (G : BondGraph V E) (ω : Set E) (x : V)
    {e : E} {a b : V} (he : e ∈ ω) (hab : G e = s(a,b)) :
    a ∈ cluster G ω x ↔ b ∈ cluster G ω x := by
  have hc : Conn G ω a b := .single ⟨e,he,hab⟩
  exact ⟨fun h => h.trans hc,fun h => h.trans (conn_symm G ω hc)⟩

 
theorem conn_restrict_cluster_compl (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω hau))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x he heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

theorem conn_restrict_cluster (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans hau
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x he heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 
theorem openMarkedPivotal_oriented (G : BondGraph V E) (ω : Set E) (m : Set V)
    (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e) :
    ∃ a b, G e = s(a,b) ∧ Conn G (ω \ {e}) x a ∧
      ¬Conn G (ω \ {e}) x b ∧ MarkedEvent G (ω \ {e}) m b := by
  obtain ⟨y,hy,hxy⟩ := he.2.1
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  have heq : insert e (ω \ {e}) = ω := by
    have heω : e ∈ ω := he.1
    ext d
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases h : d = e <;> simp_all
  rw [← heq,conn_insert_iff G _ e a b x y hab] at hxy
  rcases hxy with hxy | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
  · exact (he.2.2 ⟨y,hy,hxy⟩).elim
  · exact ⟨a,b,hab,hxa,fun hxb => he.2.2 ⟨y,hy,hxb.trans hby⟩,y,hy,hby⟩
  · exact ⟨b,a,hab.trans (Sym2.eq_swap ..),hxb,
      fun hxa => he.2.2 ⟨y,hy,hxa.trans hay⟩,y,hy,hay⟩


theorem conn_delete_internal_of_outside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x))
    (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster_compl G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨u,v,heq⟩ : ∃ u v, G f = s(u,v) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  exact ((mem_internalEdges_of_ends G _ f u v heq).mp he.2).1
    ((mem_internalEdges_of_ends G _ f u v heq).mp hf).1

 
theorem pivotal_other_sides (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (_he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : f ≠ e) :
    f ∈ internalEdges G (cluster G (ω \ {e}) x) ∨
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G f = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  have hop : f ∈ ω \ {e} := ⟨hf.1,hne⟩
  have hiff := edge_cluster_sides G (ω \ {e}) x hop hab
  by_cases ha : a ∈ cluster G (ω \ {e}) x
  · exact Or.inl ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,hiff.mp ha⟩)
  · exact Or.inr ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,fun hb => ha (hiff.mpr hb)⟩)

 
theorem conn_delete_exterior_of_inside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x)ᶜ)
    (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨⟨u,v⟩,heq⟩ := Quot.exists_rep (G f)
  exact ((mem_internalEdges_of_ends G _ f u v heq.symm).mp hf).1
    ((mem_internalEdges_of_ends G _ f u v heq.symm).mp he.2).1

 
theorem pivotal_rootSide_ssubset (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e) (hne : e ≠ f)
    (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x := by
  have hsub : cluster G (ω \ {e}) x ⊆ cluster G (ω \ {f}) x := by
    intro y hy
    exact conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hf (conn_refl G _ x) hy)
  refine ⟨hsub,?_⟩
  obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G ω m x he
  intro hback
  apply hxb
  apply hback
  exact (hsub hxa).tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem pivotal_rootSides_nested (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : e ≠ f) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x ∨
      cluster G (ω \ {f}) x ⊂ cluster G (ω \ {e}) x := by
  rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | houtside
  · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
    obtain ⟨y,hy,hby⟩ := hbm
    have hby' : Conn G (ω \ {f}) b y := conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
    have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
    have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
      hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
    exact Or.inr (pivotal_rootSide_ssubset G ω m x hf hne.symm
      ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩))
  · exact Or.inl (pivotal_rootSide_ssubset G ω m x he hne houtside)

 
theorem conn_restrict_cluster_compl_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∉ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω (conn_mono G hη hau)))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x (hη he) heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩



noncomputable def pivotalRank (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : ℕ :=
  (cluster G (ω \ {e}) x).ncard

end PivotalGeometry

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Moments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteMarkedMoment (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (markedMomentValue G Q x i ω) h) p

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def cutMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if cluster G ω x = (W : Set V) then
    if Disjoint (W : Set V) (m : Set V) then
      markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i
        (exteriorBonds G ω W) (exteriorMarks m W)
    else 0
  else 0

end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def pivotalSuffixValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if OpenMarkedPivotal G ω m x e then
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) else 0


end PointwiseRecursion

section FiniteMomentRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

 
noncomputable def cutCoefficient (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial ((Q.erase e) \ exteriorBonds G Q W)
    (fun a => if cluster G a x = (W : Set V) then (1:ℝ) else 0) p * (1-h)^W.card


end FiniteMomentRecursion

section MarkedExponential
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteMarkedGenerating (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (z h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x then (1+z)^(markedOpenPivotals G Q x ω m).card else 0) h) p

noncomputable def finiteMarkedTail (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (r : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x ∧ r ≤ (markedOpenPivotals G Q x ω m).card then (1:ℝ) else 0) h) p

end MarkedExponential

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_Goodness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq


def CappedRadiusEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M r : ℕ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧
    ∃ y, Conn G (ω : Set E) x y ∧ r ≤ (pairOpenPivotals G Q x y ω).card

noncomputable def finiteCappedRadiusTail (G : BondGraph V E) (Q : Finset E)
    (x : V) (M r : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedRadiusEvent G Q x M r ω then 1 else 0) p


end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def pruneContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) : Finset E :=
  ω.filter fun f => ¬CutExists G W f ∨ f = e

end PruningGeometry

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def openContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => CutExists G W e

 
def BadPieceEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M K : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ∃ W : Finset V,
    W ⊆ finiteRootComponent G ω x ∧
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) ∧
    (openContacts G ω (W : Set V)).card = K ∧
    ∃ a ∈ W, ∃ b ∈ W, (K:ℝ)*L < (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card


end GoodnessGeometry

section FiniteGoodnessProbability
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteBadPieceProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M K : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if BadPieceEvent G Q x M K L ω then 1 else 0) p



def FiniteGoodForScale (G : BondGraph V E) (Q : Finset E) (x : V) (L : ℝ) (ω : Finset E) : Prop :=
  ∀ W : Finset V, W ⊆ finiteRootComponent G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) →
    0 < (openContacts G ω (W : Set V)).card →
    ∀ a ∈ W, ∀ b ∈ W,
      (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card ≤
        ((openContacts G ω (W : Set V)).card:ℝ)*L

def CappedBadGoodnessEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ¬FiniteGoodForScale G Q x L ω

noncomputable def finiteBadGoodnessProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedBadGoodnessEvent G Q x M L ω then 1 else 0) p


end FiniteGoodnessProbability

section ClusterLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_le_step (G : BondGraph V E) (x : V) (n : ℕ) :
    reachBall G x n ⊆ reachBall G x (n+1) := fun _ h => Or.inl h

theorem reachBall_mono_local (G : BondGraph V E) (x : V) : Monotone (reachBall G x) :=
  monotone_nat_of_le_succ (reachBall_le_step G x)

theorem walk_mem_reachBall (G : BondGraph V E) (ω : Set E) {a b x : V}
    (w : (openSimpleGraph G ω).Walk a b) (n : ℕ) (ha : a ∈ reachBall G x n) :
    b ∈ reachBall G x (n+w.length) := by
  induction w generalizing n with
  | nil => simpa using ha
  | @cons a z b hz w ih =>
    have hz' : z ∈ reachBall G x (n+1) := by
      apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      obtain ⟨e,he,hend⟩ := hz.2
      exact ⟨a,ha,e,hend⟩
    simpa only [SimpleGraph.Walk.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using ih (n+1) hz'

 
theorem finite_cluster_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) (M : ℕ) (hM : (cluster G ω x).ncard ≤ M) :
    cluster G ω x ⊆ reachBall G x M := by
  intro y hy
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hy
  let q := w.toPath
  have hs : q.val.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    have hz' : z ∈ q.val.support := List.mem_toFinset.mp hz
    exact hfin.mem_toFinset.mpr ((conn_iff_reachable G ω x z).mpr ⟨q.val.takeUntil z hz'⟩)
  have hc : q.val.length+1 ≤ (cluster G ω x).ncard := by
    have hc := Finset.card_le_card hs
    rwa [List.toFinset_card_of_nodup q.property.support_nodup,
      SimpleGraph.Walk.length_support,← Set.ncard_eq_toFinset_card _ hfin] at hc
  have hr := walk_mem_reachBall G ω q.val 0 (Set.mem_singleton x)
  simp only [Nat.zero_add] at hr
  exact reachBall_mono_local G x (by omega) hr

 

theorem cluster_restrict_incident_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V)
    (hsub : cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hend⟩ := hab
      have heQ : e ∈ incidentSupport G hloc Λ :=
        (mem_incidentSupport G hloc Λ e).mpr ⟨a,hsub ih,by simp [hend]⟩
      exact ih.tail ⟨e,⟨he,heQ⟩,hend⟩

theorem cluster_restrict_incident_of_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (hsub : cluster G ω x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply cluster_restrict_incident_eq G hloc Λ ω x
  exact (fun _ h => hsub (conn_mono G Set.inter_subset_left h))

 
theorem capped_cluster_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧
        (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) := by
  dsimp only
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  constructor
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G ω x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hcap
    rw [cluster_restrict_incident_of_full G hloc Λ ω x hsub]
    exact ⟨hfin,hcap⟩
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G (ω ∩ (Q : Set E)) x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hfin M hcap
    have heq := cluster_restrict_incident_eq G hloc Λ ω x hsub
    rw [heq] at hfin hcap
    exact ⟨hfin,hcap⟩

end ClusterLocality

section InfiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq


def GoodForScale (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ) : Prop :=
  ∀ W : Finset V, (W : Set V) ⊆ cluster G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (ω ∩ internalEdges G (W : Set V)) a b) →
    0 < (contactSet G ω (W : Set V)).ncard →
    ∀ a ∈ W, ∀ b ∈ W,
      (pivotalDistance G (ω ∩ internalEdges G (W : Set V)) a b : ℝ) ≤
        (contactSet G ω (W : Set V)).ncard*L

 
def CappedBadGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ ¬GoodForScale G ω x L


theorem internal_config_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    ω ∩ internalEdges G W = η ∩ internalEdges G W := by
  ext e
  by_cases hi : e ∈ internalEdges G W
  · have hinc : ∃ v ∈ C, v ∈ G e :=
      ⟨(G e).out.1,hW (hi _ (Sym2.out_fst_mem _)),Sym2.out_fst_mem _⟩
    simp only [Set.mem_inter_iff,hi,and_true,he e hinc]
  · simp only [Set.mem_inter_iff,hi,and_false]

theorem contacts_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    contactSet G ω W = contactSet G η W := by
  ext e
  by_cases hi : CutExists G W e
  · obtain ⟨a,b,hab,ha,_⟩ := hi
    have hinc : ∃ v ∈ C, v ∈ G e := ⟨a,hW ha,by simp [hab]⟩
    simp only [contactSet,Set.mem_ofPred_eq,he e hinc]
  · simp only [contactSet,Set.mem_ofPred_eq,hi,and_false]

 
theorem goodForScale_congr (G : BondGraph V E) (ω η : Set E) (x : V) (L : ℝ)
    (hC : cluster G ω x = cluster G η x)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    GoodForScale G ω x L ↔ GoodForScale G η x L := by
  unfold GoodForScale
  apply forall_congr'
  intro W
  rw [← hC]
  apply forall_congr'
  intro hW
  rw [internal_config_eq_of_incident G ω η _ _ hW he,contacts_eq_of_incident G ω η _ _ hW he]

theorem goodForScale_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (L : ℝ) (hsub : cluster G ω x ⊆ Λ) :
    GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (incidentSupport G hloc Λ : Set E)) x L := by
  apply goodForScale_congr G ω _ x L
    (cluster_restrict_incident_of_full G hloc Λ ω x hsub).symm
  intro e he
  obtain ⟨v,hv,hve⟩ := he
  have hQ := (mem_incidentSupport G hloc Λ e).mpr ⟨v,hsub hv,hve⟩
  simp only [Set.mem_inter_iff,Finset.mem_coe,hQ,and_true]

 
theorem cappedBadGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L := by
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  change CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L
  have hcap := capped_cluster_local G hloc x M ω
  change ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
    ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) at hcap
  have hg : ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) →
      (GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (Q : Set E)) x L) := by
    rintro ⟨hfin,hM⟩
    apply goodForScale_restrict_incident G hloc Λ ω x L
    simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hM
  constructor
  · rintro ⟨hfin,hM,hbad⟩
    exact ⟨(hcap.mp ⟨hfin,hM⟩).1,(hcap.mp ⟨hfin,hM⟩).2,fun hh => hbad ((hg ⟨hfin,hM⟩).mpr hh)⟩
  · rintro ⟨hfin,hM,hbad⟩
    have hc := hcap.mpr ⟨hfin,hM⟩
    exact ⟨hc.1,hc.2,fun hh => hbad ((hg hc).mp hh)⟩

end InfiniteGoodness

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Spectral
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


noncomputable def neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : Finset V := S ∪ S.biUnion (neighbors G hloc)

end IsoperimetricEnergy

section SymmetricWalk
attribute [local instance] Classical.propDecidable

 

noncomputable def walkKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : ℝ :=
  (if x = y then 1 - a * (neighbors G hloc x).card else 0) +
    (if Adj G x y then a else 0)

end SymmetricWalk

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

 
def vertexAut (G : BondGraph V E) : Set (V ≃ V) := {a | ∃ b : E ≃ E, IsAut G a b}

theorem twoPoint_aut [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x y : V) :
    twoPoint G p (a x) (a y) = twoPoint G p x y := by
  have he : {ω | Conn G ω (a x) (a y)} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | Conn G ω x y} := by
    ext ω
    exact (conn_aut_iff G h ω x y).symm
  unfold twoPoint
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_conn G x y), law_map_preimage_equiv]

end InvariantPercolationOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Geometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq



theorem exchangeOn_involutive (mask ω η : Set E) :
    exchangeOn mask (exchangeOn mask ω η) (exchangeOn mask η ω) = ω := by
  ext e
  by_cases h : e ∈ mask <;> simp [h]



theorem slit_cluster_subset (G : BondGraph V E) (S : Set V) (η : Set E)
    (y : V) (hy : y ∉ S) : cluster G (η ∩ internalEdges G Sᶜ) y ⊆ Sᶜ := by
  exact fun z hz => conn_internal_endpoint G Sᶜ hy hz

theorem spliceMask_not_internal (G : BondGraph V E) (S B : Set V) (e : E)
    (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) {f : E}
    (hf : f ∈ internalEdges G S) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hout⟩)
  · exact hb (((mem_internalEdges_of_ends G S f a b he).mp hf).2)
  · exact (hout _ (Sym2.out_fst_mem _)) (hf _ (Sym2.out_fst_mem _))

theorem spliceMask_of_internal_piece (G : BondGraph V E) (S B : Set V) (e : E)
    (hB : B ⊆ Sᶜ) {f : E} (hf : f ∈ internalEdges G B) : f ∈ spliceMask G S B e := by
  right
  exact ⟨⟨(G f).out.1,hf _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩,
    fun v hv => hB (hf v hv)⟩

 
theorem splice_internal_fields (G : BondGraph V E) (S B : Set V) (e : E)
    (ω η : Set E) (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) (hB : B ⊆ Sᶜ) :
    spliceField G S B e ω η ∩ internalEdges G S = ω ∩ internalEdges G S ∧
    spliceField G S B e ω η ∩ internalEdges G B = η ∩ internalEdges G B := by
  constructor
  · ext f
    by_cases hf : f ∈ internalEdges G S
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_right (spliceMask_not_internal G S B e a b he hb hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]
  · ext f
    by_cases hf : f ∈ internalEdges G B
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_left (spliceMask_of_internal_piece G S B e hB hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]

 
theorem splice_crossing_unique (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e : E) {f : E} {a b : V}
    (hf : f ∈ spliceField G (cluster G ω x) B e ω η)
    (hab : G f = s(a,b)) (ha : a ∈ cluster G ω x) (hb : b ∉ cluster G ω x) : f = e := by
  have hno : f ∉ ω := fun h => hb ((edge_cluster_sides G ω x h hab).mp ha)
  have hm : f ∈ spliceMask G (cluster G ω x) B e := by
    by_contra h
    have hh := hf
    simp only [spliceField,mem_exchangeOn,ite_eq_right h] at hh
    exact hno hh
  rcases hm with rfl | ⟨_,hout⟩
  · rfl
  · exact ((((mem_internalEdges_of_ends G _ f a b hab).mp hout).1) ha).elim

 

theorem splice_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η) x = S ∪ B := by
  let S := cluster G ω x
  let ζ := η ∩ internalEdges G Sᶜ
  let B := cluster G ζ y
  let ω' := spliceField G S B e ω η
  change cluster G ω' x = S ∪ B
  have hB : B ⊆ Sᶜ := slit_cluster_subset G S η y hy
  have hbS : b ∉ S := hB hb
  have hfields := splice_internal_fields G S B e ω η a b he hbS hB
  have he' : e ∈ ω' := by
    change e ∈ exchangeOn (spliceMask G S B e) ω η
    rw [mem_exchangeOn,ite_eq_left (show e ∈ spliceMask G S B e from Set.mem_insert _ _)]
    exact heη
  have hSconn (z : V) (hz : z ∈ S) : Conn G ω' x z := by
    have h := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ h
    intro f hf
    exact (hfields.1.symm ▸ hf).1
  have hBconn (u v : V) (hu : u ∈ B) (hv : v ∈ B) : Conn G ω' u v := by
    have h := conn_restrict_cluster G ζ y hu (conn_trans G ζ (conn_symm G ζ hu) hv)
    apply conn_mono G _ h
    intro f hf
    exact (hfields.2.symm ▸ (show f ∈ η ∩ internalEdges G B from ⟨hf.1.1,hf.2⟩)).1
  apply Set.Subset.antisymm
  · intro z hz
    induction hz with
    | refl => exact Or.inl (mem_cluster_self G ω x)
    | @tail u v hxu huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · rcases ih with huS | huB
        · have hfe := splice_crossing_unique G ω η x B e hf hfv huS hvS
          subst f
          have hends := Sym2.eq_iff.mp (he.symm.trans hfv)
          rcases hends with ⟨hau,hbv⟩ | ⟨hav,hbu⟩
          · exact Or.inr (hbv ▸ hb)
          · exact (hvS (hav ▸ ha)).elim
        · have huS : u ∉ S := hB huB
          have hm : f ∈ spliceMask G S B e := by
            right
            exact ⟨⟨u,huB,by simp [hfv]⟩,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩
          have hfη : f ∈ η := by
            change f ∈ exchangeOn (spliceMask G S B e) ω η at hf
            rwa [mem_exchangeOn,ite_eq_left hm] at hf
          exact Or.inr ((edge_cluster_sides G ζ y
            ⟨hfη,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩ hfv).mp huB)
  · intro z hz
    rcases hz with hz | hz
    · exact hSconn z hz
    · exact ((hSconn a ha).tail ⟨e,he',he⟩).trans (hBconn b z hb hz)


end SpliceGeometry

section SpliceInverse
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem splice_close_seam_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (_heη : e ∈ η) (_ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η \ {e}) x = S := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  let ω' := spliceField G S B e ω η
  have hB := slit_cluster_subset G S η y hy
  have hf := (splice_internal_fields G S B e ω η a b he (hB hb) hB).1
  apply Set.Subset.antisymm
  · intro v hxv
    induction hxv with
    | refl => exact mem_cluster_self G ω x
    | @tail u v _ huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_contra hvS
      have hfe := splice_crossing_unique G ω η x B e hf.1 hfv ih hvS
      exact hf.2 (Set.mem_singleton_iff.mpr hfe)
  · intro z hz
    have hc := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ hc
    intro f hfin
    refine ⟨(hf.symm ▸ hfin).1,?_⟩
    intro hfe
    have hfe' := Set.mem_singleton_iff.mp hfe
    subst f
    exact hB hb (((mem_internalEdges_of_ends G S e a b he).mp hfin.2).2)

 
theorem splice_recover_piece (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    let ω' := spliceField G S B e ω η
    cluster G ω' x \ cluster G (ω' \ {e}) x = B := by
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]
  have hB := slit_cluster_subset G (cluster G ω x) η y hy
  ext z
  constructor
  · rintro ⟨hz,hzS⟩
    exact hz.resolve_left hzS
  · intro hz
    exact ⟨Or.inr hz,hB hz⟩

 
def recoveredMask (G : BondGraph V E) (ω' : Set E) (x : V) (e : E) : Set E :=
  spliceMask G (cluster G (ω' \ {e}) x)
    (cluster G ω' x \ cluster G (ω' \ {e}) x) e

theorem recoveredMask_splice (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    recoveredMask G (spliceField G S B e ω η) x e = spliceMask G S B e := by
  unfold recoveredMask
  dsimp only
  rw [splice_recover_piece G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]


end SpliceInverse

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
def deletionContacts (G : BondGraph V E) (ω : Set E) (A B : Set V) : Set E :=
  {e | e ∈ ω ∧ ∃ a ∈ B, ∃ b ∈ A, G e = s(a,b)}



end DeletionGoodness

section SpliceSelection
attribute [local instance] Classical.propDecidable Classical.decEq



theorem cluster_eq_of_incident_agreement (G : BondGraph V E) (ω η : Set E) (x : V)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    cluster G η x = cluster G ω x := by
  have hforward : cluster G ω x ⊆ cluster G η x := by
    intro y hy
    induction hy with
    | refl => exact conn_refl G _ _
    | @tail a b hxa hab ih =>
      obtain ⟨e,heω,hab⟩ := hab
      exact ih.tail ⟨e,(he e ⟨a,hxa,by simp [hab]⟩).mp heω,hab⟩
  apply Set.Subset.antisymm _ hforward
  intro y hy
  induction hy with
  | refl => exact conn_refl G _ _
  | @tail a b _ hab ih =>
    obtain ⟨e,heη,hab⟩ := hab
    exact ih.tail ⟨e,(he e ⟨a,ih,by simp [hab]⟩).mpr heη,hab⟩

 

theorem spliceMask_avoids_prefix (G : BondGraph V E) (S B R : Set V) (hRS : R ⊆ S)
    (e : E) (a b : V) (hab : G e = s(a,b)) (ha : a ∉ R) (hb : b ∉ S)
    {f : E} (hf : ∃ v ∈ R, v ∈ G f) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hfo⟩)
  · obtain ⟨v,hv,hvf⟩ := hf
    rw [hab] at hvf
    rcases Sym2.mem_iff.mp hvf with rfl | rfl
    · exact ha hv
    · exact hb (hRS hv)
  · obtain ⟨v,hv,hvf⟩ := hf
    exact hfo v hvf (hRS hv)

 

theorem splice_preserves_prefix_cut (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e f : E) (a b : V) (hab : G e = s(a,b))
    (ha : a ∉ cluster G (ω \ {f}) x) (hb : b ∉ cluster G ω x) :
    cluster G ((spliceField G (cluster G ω x) B e ω η) \ {f}) x =
      cluster G (ω \ {f}) x := by
  apply cluster_eq_of_incident_agreement
  intro g hg
  have hRS : cluster G (ω \ {f}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  have hno := spliceMask_avoids_prefix G _ B _ hRS e a b hab ha hb hg
  simp only [Set.mem_sdiff,spliceField,mem_exchangeOn,ite_eq_right hno]

end SpliceSelection

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.preserve_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (f : E)
    (havoid : ∀ l, j < l → l ≤ k →
      Disjoint (cluster G (η l) (y l)) (cluster G (ω \ {f}) x)) :
    cluster G (ωf \ {f}) x = cluster G (ω \ {f}) x := by
  induction h with
  | stop => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    have hBC : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
    have haC : a ∈ cluster G (η i) (y i) := (edge_cluster_sides G (η i) (y i) he hab).mpr hBC
    have haR : a ∉ cluster G (ω \ {f}) x := fun hh => Set.disjoint_left.mp (havoid i hji hik) haC hh
    have hbS : b ∉ cluster G ω x := slit_cluster_subset G _ (η i) (y i) hy hb
    have heq := splice_preserves_prefix_cut G ω (η i) x
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e f a b hab haR hbS
    rw [ih]
    · exact heq
    · intro l hil hlk
      rw [heq]
      exact havoid l (hji.trans hil) hlk

 
theorem SpliceTrace.endpoint (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : y k ∈ cluster G ωf x := by
  induction h with
  | stop _ _ hs => exact hs
  | step => assumption

 

theorem SpliceTrace.seams_pivotal (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, OpenMarkedPivotal G ωf {y k} x q.2 := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · let S := cluster G ω x
      let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
      let ω' := spliceField G S B e ω (η i)
      have hcut : cluster G (ω' \ {e}) x = S :=
        splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
      have hfinal : cluster G (ωf \ {e}) x = S := by
        rw [SpliceTrace.preserve_cut G x η y k i ω' ωf rest ht e]
        · exact hcut
        · intro l hil hlk
          rw [hcut]
          exact hmax l hil hlk
      have hconn := SpliceTrace.endpoint G x η y k i ω' ωf rest ht
      have hno : ¬Conn G (ωf \ {e}) x (y k) := by
        intro hc
        have : y k ∈ cluster G (ωf \ {e}) x := hc
        rw [hfinal] at this
        exact hn this
      have heω : e ∈ ωf := by
        by_contra heω
        have heq : ωf \ {e} = ωf := by
          ext f
          constructor
          · exact fun hh => hh.1
          · intro hh
            exact ⟨hh,fun hfe => heω ((Set.mem_singleton_iff.mp hfe) ▸ hh)⟩
        exact hno (heq.symm ▸ hconn)
      exact ⟨heω,⟨y k,rfl,hconn⟩,by simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hno⟩
    · exact ih q hq

end SpliceTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_GapCodes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceExecution
attribute [local instance] Classical.propDecidable Classical.decEq



theorem exchangeState_involutive (mask : Set E) (i : ℕ) :
    Function.Involutive (exchangeState mask i (E := E)) := by
  intro s
  apply Prod.ext
  · simp only [exchangeState_first, exchangeState_at]
    exact exchangeOn_involutive mask s.1 (s.2 i)
  · funext l
    by_cases hli : l = i
    · subst l
      simp only [exchangeState_at, exchangeState_first]
      exact exchangeOn_involutive mask (s.2 i) s.1
    · rw [exchangeState_away _ _ _ _ hli, exchangeState_away _ _ _ _ hli]

 

def undoState (G : BondGraph V E) (x : V) (q : ℕ × E) (s : SpliceState E) :
    SpliceState E := exchangeState (recoveredMask G s.1 x q.2) q.1 s



theorem undoState_of_valid (G : BondGraph V E) (x : V) (s s' : SpliceState E)
    (q : ℕ × E) (h : ValidSpliceStep G x s q s') : undoState G x q s' = s := by
  obtain ⟨y,a,b,hy,he,hab,ha,hb,rfl⟩ := h
  unfold undoState
  rw [show recoveredMask G
      (exchangeState (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s).1 x q.2 =
      spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2 from
    recoveredMask_splice G s.1 (s.2 q.1) x y hy q.2 a b hab he ha hb]
  exact exchangeState_involutive _ _ s


def undoExecution (G : BondGraph V E) (x : V) :
    List (ℕ × E) → SpliceState E → SpliceState E
  | [], s => s
  | q::qs, s => undoState G x q (undoExecution G x qs s)

theorem SpliceExecution.undo (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') : undoExecution G x code s' = s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q qs hstep hrest ih =>
    change undoState G x q (undoExecution G x qs s'') = s
    rw [ih]
    exact undoState_of_valid G x s s' q hstep

 

theorem SpliceExecution.input_unique (G : BondGraph V E) (x : V)
    (s₁ s₂ out : SpliceState E) (code : List (ℕ × E))
    (h₁ : SpliceExecution G x s₁ code out) (h₂ : SpliceExecution G x s₂ code out) :
    s₁ = s₂ := by
  exact (h₁.undo G x s₁ out code).symm.trans (h₂.undo G x s₂ out code)



end SpliceExecution

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeCode
attribute [local instance] Classical.propDecidable Classical.decEq


theorem pivotalRank_injective_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) :
    Set.InjOn (pivotalRank G ω x) {e | OpenMarkedPivotal G ω m x e} := by
  have hcut (f : E) : (cluster G (ω \ {f}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  intro e he f hf heq
  by_contra hne
  rcases pivotal_rootSides_nested G ω m x he hf hne with h | h
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut f))) heq
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut e))) heq.symm

 

noncomputable def bridgeIndex (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) : ℕ :=
  ((separatingBonds G ω x z).filter fun f => pivotalRank G ω x f ≤ pivotalRank G ω x e).card

theorem bridgeIndex_lt_of_rank_lt (G : BondGraph V E) (ω : Set E) (x z : V) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z e < bridgeIndex G ω x z f := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      (Finset.mem_filter.mp hd).2.trans (Nat.le_of_lt hlt)⟩
  · intro heq
    have hmem : f ∈ (separatingBonds G ω x z).filter
        (fun d => pivotalRank G ω x d ≤ pivotalRank G ω x f) :=
      Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
    rw [← heq] at hmem
    exact (Nat.not_le_of_lt hlt) (Finset.mem_filter.mp hmem).2

theorem bridgeIndex_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    Set.InjOn (bridgeIndex G ω x z) {e | OpenMarkedPivotal G ω {z} x e} := by
  intro e he f hf heq
  apply pivotalRank_injective_of_cluster_finite G ω {z} x hC he hf
  rcases lt_trichotomy (pivotalRank G ω x e) (pivotalRank G ω x f) with h | h | h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z hf h)) heq).elim
  · exact h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z he h)) heq.symm).elim

 
noncomputable def ordinalSpliceCode (G : BondGraph V E) (ω : Set E) (x z : V)
    (code : List (ℕ × E)) : List (ℕ × ℕ) :=
  code.map fun q => (q.1,bridgeIndex G ω x z q.2)

theorem ordinalSpliceCode_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) (c₁ c₂ : List (ℕ × E))
    (h₁ : ∀ q ∈ c₁, OpenMarkedPivotal G ω {z} x q.2)
    (h₂ : ∀ q ∈ c₂, OpenMarkedPivotal G ω {z} x q.2)
    (heq : ordinalSpliceCode G ω x z c₁ = ordinalSpliceCode G ω x z c₂) : c₁ = c₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons q qs => simp [ordinalSpliceCode] at heq
  | cons q qs ih =>
    cases c₂ with
    | nil => simp [ordinalSpliceCode] at heq
    | cons r rs =>
      have heq' := List.cons.inj heq
      have hqr : q = r := by
        apply Prod.ext
        · exact congrArg (fun t : ℕ × ℕ => t.1) heq'.1
        · exact bridgeIndex_injective G ω x z hC (h₁ q (by simp)) (h₂ r (by simp))
            (congrArg Prod.snd heq'.1)
      exact congrArg₂ List.cons hqr (ih rs
        (fun a ha => h₁ a (List.mem_cons_of_mem _ ha))
        (fun a ha => h₂ a (List.mem_cons_of_mem _ ha)) heq'.2)

 

theorem SpliceTrace.input_unique_of_ordinalCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : ordinalSpliceCode G ωf x (y₁ k) c₁ = ordinalSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  have hc : c₁ = c₂ := ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂) heq
  subst c₂
  exact he₁.input_unique G x (ω₁,η₁) (ω₂,η₂) (ωf,θf) c₁ he₂

end BridgeCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def spliceTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p

end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotalRank_lt_iff_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f) :
    pivotalRank G ω x e < pivotalRank G ω x f ↔
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hcut (q : E) : (cluster G (ω \ {q}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  have hexterior (hout : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    obtain ⟨a,b,hab,hxa,_,_⟩ := openMarkedPivotal_oriented G ω m x he
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hout).1 hxa
  constructor
  · intro hlt
    have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
    rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | hout
    · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
      obtain ⟨y,hy,hby⟩ := hbm
      have hby' : Conn G (ω \ {f}) b y := conn_mono G
        (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
        (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
      have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
      have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
        hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
      have hs := pivotal_rootSide_ssubset G ω m x hf hne.symm
        ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩)
      have hrev := Set.ncard_lt_ncard hs (hcut e)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hrev) hlt).elim
    · exact hout
  · intro hout
    exact Set.ncard_lt_ncard (pivotal_rootSide_ssubset G ω m x he (hexterior hout) hout) (hcut f)

theorem pivotal_internal_of_rank_lt (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    e ∈ internalEdges G (cluster G (ω \ {f}) x) := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  rcases pivotal_other_sides G ω m x hf he hne with h | h
  · exact h
  · have hr := (pivotalRank_lt_iff_of_cluster_finite G ω m x hC hf he).mpr h
    omega

 
theorem conn_far_end_avoids_later_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a) :
    Conn G (ω \ {g}) x b := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp hlt
  have hne : e ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hc : Conn G (ω \ {g}) x a :=
    conn_mono G (ω₁ := (ω \ {e}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hout (conn_refl G _ x) ha)
  exact hc.tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem conn_near_end_avoids_earlier_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {f g : E}
    (hf : OpenMarkedPivotal G ω {z} x f) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x g < pivotalRank G ω x f)
    (c d : V) (hcd : G f = s(c,d)) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z) : Conn G (ω \ {g}) c z := by
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hlt
  have hne : f ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h.symm)
  have hc : Conn G (ω \ {g}) d z :=
    conn_mono G (ω₁ := (ω \ {f}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {f}) x hin hd hdz)
  exact (Relation.ReflTransGen.single ⟨f,⟨hf.1,hne⟩,hcd⟩).trans hc

 

theorem pivotal_between_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (hgf : pivotalRank G ω x g < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) {c} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hgf
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨c,rfl,hbc⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbc' : Conn G (ω \ {g}) b c := by
    have hw' : w = c := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  apply hg.2.2
  exact ⟨z,rfl,(conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans
    (hbc'.trans (conn_near_end_avoids_earlier_pivotal G ω x z hC hf hg hgf c d hcd hd hdz))⟩

 
theorem pivotal_after_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) {z} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin : g ∈ internalEdges G (cluster G ω x) := by
    obtain ⟨u,v,huv,hxu,_,_⟩ := openMarkedPivotal_oriented G ω {z} x hg
    have hu : u ∈ cluster G ω x := conn_mono G Set.sdiff_subset hxu
    exact (mem_internalEdges_of_ends G _ g u v huv).mpr
      ⟨hu,(edge_cluster_sides G ω x hg.1 huv).mp hu⟩
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨z,rfl,hbz⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbz' : Conn G (ω \ {g}) b z := by
    have hw' : w = z := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  exact hg.2.2 ⟨z,rfl,
    (conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans hbz'⟩

end BridgeGapGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapCount
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def bridgeInterval (G : BondGraph V E) (ω : Set E) (x z : V) (e f : E) : Finset E :=
  (separatingBonds G ω x z).filter fun g =>
    pivotalRank G ω x e < pivotalRank G ω x g ∧ pivotalRank G ω x g < pivotalRank G ω x f

theorem bridgeIndex_interval_identity (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z f = bridgeIndex G ω x z e + (bridgeInterval G ω x z e f).card + 1 := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := bridgeInterval G ω x z e f
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro g hgA hgB
    have h₁ := (Finset.mem_filter.mp hgA).2
    have h₂ := (Finset.mem_filter.mp hgB).2.1
    omega
  have hnot : f ∉ A ∪ B := by
    intro hh
    rcases Finset.mem_union.mp hh with h | h
    · have hr := (Finset.mem_filter.mp h).2
      omega
    · exact (Nat.lt_irrefl _) (Finset.mem_filter.mp h).2.2
  have hset : P.filter (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x f) = insert f (A ∪ B) := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgP,hgf⟩ := Finset.mem_filter.mp hg
      by_cases hge : g = f
      · exact Finset.mem_insert.mpr (Or.inl hge)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        by_cases hga : pivotalRank G ω x g ≤ pivotalRank G ω x e
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgP,hga⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨hgP,Nat.lt_of_not_ge hga,?_⟩
          apply lt_of_le_of_ne hgf
          intro hr
          exact hge (pivotalRank_injective_of_cluster_finite G ω {z} x hC
            ((mem_separatingBonds G ω x z g).mp hgP) hf hr)
    · intro hg
      rcases Finset.mem_insert.mp hg with heq | hg
      · subst g
        exact Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
      · rcases Finset.mem_union.mp hg with hg | hg
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            (Finset.mem_filter.mp hg).2.trans (Nat.le_of_lt hlt)⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            Nat.le_of_lt (Finset.mem_filter.mp hg).2.2⟩
  change (P.filter _).card = A.card+B.card+1
  rw [hset,Finset.card_insert_of_notMem hnot,Finset.card_union_of_disjoint hdis]

theorem bridgeInterval_card_le (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    (bridgeInterval G ω x z e f).card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  rw [← separatingBonds_card]
  apply Finset.card_le_card
  intro g hg
  obtain ⟨hgP,heg,hgf⟩ := Finset.mem_filter.mp hg
  apply (mem_separatingBonds _ _ _ _ _).mpr
  exact pivotal_between_is_internal G ω x z hC he hf
    ((mem_separatingBonds G ω x z g).mp hgP) heg hgf a b c d hab hcd ha hd hdz hbc

 
theorem bridge_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    bridgeIndex G ω x z f - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hid := bridgeIndex_interval_identity G ω x z hC hf hlt
  have hle := bridgeInterval_card_le G ω x z hC he hf a b c d hab hcd ha hd hdz hbc
  omega

 
theorem bridge_terminal_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e : E}
    (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    (separatingBonds G ω x z).card + 1 - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := P.filter fun g => pivotalRank G ω x e < pivotalRank G ω x g
  have hid : A.card + B.card = P.card := by
    simpa only [A,B,not_le] using Finset.card_filter_add_card_filter_not
      (s := P) (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e)
  have hle : B.card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
    rw [← separatingBonds_card]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hgP,heg⟩ := Finset.mem_filter.mp hg
    apply (mem_separatingBonds _ _ _ _ _).mpr
    exact pivotal_after_is_internal G ω x z hC he
      ((mem_separatingBonds G ω x z g).mp hgP) heg a b hab ha hbz
  change P.card+1-A.card ≤ _
  omega

 
theorem pivotalDistance_le_cluster_card (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    pivotalDistance G ω x z ≤ (cluster G ω x).ncard - 1 := by
  rw [← separatingBonds_card]
  let N := (cluster G ω x).ncard
  have hm : Set.MapsTo (pivotalRank G ω x) (separatingBonds G ω x z : Set E)
      (Finset.Ico 1 N : Set ℕ) := by
    intro e he
    have he' := (mem_separatingBonds G ω x z e).mp he
    have hfin : (cluster G (ω \ {e}) x).Finite :=
      hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
    have hpos : 0 < pivotalRank G ω x e :=
      (Set.ncard_pos hfin).mpr ⟨x,conn_refl G _ x⟩
    have hlt : pivotalRank G ω x e < N := by
      apply Set.ncard_lt_ncard _ hC
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun v hv => conn_mono G Set.sdiff_subset hv,?_⟩
      intro heq
      obtain ⟨v,hv,hxv⟩ := he'.2.1
      apply he'.2.2
      refine ⟨v,hv,?_⟩
      change v ∈ cluster G (ω \ {e}) x
      rw [heq]
      exact hxv
    exact Finset.mem_Ico.mpr ⟨hpos,hlt⟩
  have hi : Set.InjOn (pivotalRank G ω x) (separatingBonds G ω x z : Set E) := by
    intro e he f hf h
    exact pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp he) ((mem_separatingBonds G ω x z f).mp hf) h
  simpa only [Nat.card_Ico,N] using Finset.card_le_card_of_injOn (pivotalRank G ω x) hm hi



end BridgeGapCount

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgePiecePath
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_restrict_cluster_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∈ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans (conn_mono G hη hau)
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x (hη he) heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 

theorem conn_between_pivotals_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hb : ¬Conn G (ω \ {e}) x b)
    (hc : Conn G (ω \ {f}) x c) :
    Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hf).mp hlt
  have hcnot : c ∉ cluster G (ω \ {e}) x :=
    ((mem_internalEdges_of_ends G _ f c d hcd).mp hout).1
  have hins : insert e ((ω \ {e}) \ {f}) = ω \ {f} := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨⟨hq,hqe⟩,hqf⟩)
      · exact ⟨he.1,hne⟩
      · exact ⟨hq,hqf⟩
    · rintro ⟨hq,hqf⟩
      by_cases hqe : q = e
      · exact Or.inl hqe
      · exact Or.inr ⟨⟨hq,hqe⟩,hqf⟩
  have hbc : Conn G ((ω \ {e}) \ {f}) b c := by
    rw [← hins,conn_insert_iff G _ e a b x c hab] at hc
    rcases hc with h | ⟨_,h⟩ | ⟨h,_⟩
    · exact (hcnot (conn_mono G Set.sdiff_subset h)).elim
    · exact h
    · exact (hb (conn_mono G Set.sdiff_subset h)).elim
  have hbo : b ∈ cluster G (ω \ {f}) x :=
    conn_far_end_avoids_later_pivotal G ω x z hC he hf hlt a b hab ha
  have hp := conn_restrict_cluster_compl_of_subset G (ω \ {e}) x Set.sdiff_subset hb hbc
  have hp' := conn_restrict_cluster_of_subset G (ω \ {f}) x
    (η := ((ω \ {e}) \ {f}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => ⟨h.1.1.1,h.1.2⟩) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem conn_after_pivotal_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hb : ¬Conn G (ω \ {e}) x b) (hbz : Conn G (ω \ {e}) b z) :
    Conn G (ω ∩ internalEdges G (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  have hbo : b ∈ cluster G ω x :=
    (conn_mono G Set.sdiff_subset ha).tail ⟨e,he.1,hab⟩
  have hp := conn_restrict_cluster_compl G (ω \ {e}) x hb hbz
  have hp' := conn_restrict_cluster_of_subset G ω x
    (η := (ω \ {e}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => h.1.1) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem pivotalDistance_le_induced_card (G : BondGraph V E) (ω : Set E)
    (B : Set V) (hB : B.Finite) {a b : V} (ha : a ∈ B) :
    pivotalDistance G (ω ∩ internalEdges G B) a b ≤ B.ncard-1 := by
  have hsub : cluster G (ω ∩ internalEdges G B) a ⊆ B :=
    fun _ h => conn_internal_endpoint G B ha h
  exact (pivotalDistance_le_cluster_card G (ω ∩ internalEdges G B) a b (hB.subset hsub)).trans
    (Nat.sub_le_sub_right (Set.ncard_le_ncard hsub hB) 1)

end BridgePiecePath

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SplicePieceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_after_pivotal_of_orientation (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (hb : ¬Conn G (ω \ {e}) x b) :
    Conn G (ω \ {e}) b z := by
  have hins : insert e (ω \ {e}) = ω := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases hqe : q = e <;> simp_all [he.1]
  obtain ⟨w,hw,hxw⟩ := he.2.1
  have hw' : w = z := Set.mem_singleton_iff.mp hw
  subst w
  rw [← hins,conn_insert_iff G _ e a b x z hab] at hxw
  rcases hxw with h | ⟨_,h⟩ | ⟨h,_⟩
  · exact (he.2.2 ⟨z,rfl,h⟩).elim
  · exact h
  · exact (hb h).elim

 
theorem SpliceTrace.internal_agreement (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ internalEdges G (cluster G ω x), q ∈ ωf ↔ q ∈ ω := by
  induction h with
  | stop => exact fun _ _ => Iff.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    intro q hq
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hbS : b ∉ S := hB hb
    have hqq : q ∈ internalEdges G (cluster G ω' x) := by
      rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
      exact fun v hv => Or.inl (hq v hv)
    rw [ih q hqq]
    change q ∈ internalEdges G S at hq
    have hh := (splice_internal_fields G S B e ω (η i) a b hab hbS hB).1
    exact Iff.of_eq (show (q ∈ ω') = (q ∈ ω) from by
      have := congrArg (fun A : Set E => q ∈ A) hh
      simpa only [Set.mem_inter_iff,hq,and_true] using this)

 
theorem SpliceTrace.head_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    cluster G (ωf \ {e}) x = cluster G ω x := by
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax hy he hab ha hb ht =>
    have hc := splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    rw [SpliceTrace.preserve_cut G x η y k i _ ωf rest ht e]
    · exact hc
    · intro l hil hlk
      rw [hc]
      exact hmax l hil hlk

 
theorem contactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (B : Set V) (hB : B.Finite) : (contactSet G ω B).Finite := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  apply (incidentSupport G hloc W).finite_toSet.subset
  rintro e ⟨_,a,b,hab,ha,_⟩
  apply (mem_incidentSupport G hloc W e).mpr
  refine ⟨a,?_,?_⟩
  · change a ∈ (W : Set V)
    rw [hWB]
    exact ha
  · simp [hab]

 

theorem goodForScale_piece (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω x L) (B : Set V) (hB : B.Finite)
    (hBC : B ⊆ cluster G ω x)
    (hconn : ∀ a ∈ B, ∀ b ∈ B, Conn G (ω ∩ internalEdges G B) a b)
    (hK : 0 < (contactSet G ω B).ncard) {a b : V} (ha : a ∈ B) (hb : b ∈ B) :
    (pivotalDistance G (ω ∩ internalEdges G B) a b : ℝ) ≤
      (contactSet G ω B).ncard*L := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  have hh := hg W (by simpa only [hWB] using hBC)
    (by simpa only [← Finset.mem_coe,hWB] using hconn)
    (by simpa only [hWB] using hK) a (by simpa only [← Finset.mem_coe,hWB] using ha)
    b (by simpa only [← Finset.mem_coe,hWB] using hb)
  simpa only [hWB] using hh

 
theorem slit_piece_connected (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (_hy : y ∉ S) :
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    ∀ a ∈ B, ∀ b ∈ B, Conn G (η ∩ internalEdges G B) a b := by
  intro B a ha b hb
  have hc := conn_restrict_cluster G (η ∩ internalEdges G Sᶜ) y ha
    (conn_trans G _ (conn_symm G _ ha) hb)
  apply conn_mono G ?_ hc
  exact fun _ h => ⟨h.1.1,h.2⟩

end SplicePieceGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceGapBound
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def traceHeadGap (G : BondGraph V E) (ωf : Set E) (x z : V)
    (e : E) (rest : List (ℕ × E)) : ℕ :=
  (match rest with
    | [] => (separatingBonds G ωf x z).card + 1
    | (_,f)::_ => bridgeIndex G ωf x z f) - bridgeIndex G ωf x z e

 

theorem SpliceTrace.head_gap_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j i M : ℕ)
    (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hCf : (cluster G ωf x).Finite)
    (hCi : (cluster G (η i) (y i)).Finite)
    (hM : (cluster G (η i) (y i)).ncard ≤ M)
    (L : ℝ) (hgood : GoodForScale G (η i) (y i) L) :
    let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
    let K := (contactSet G (η i) B).ncard
    let l := traceHeadGap G ωf x (y k) e rest
    1 ≤ K ∧ 1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1 + K*L := by
  have hfull := h
  cases h with
  | step j i ω e a b rest ωf hn _ _ _ hy he hab ha hb ht =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let K := (contactSet G (η i) B).ncard
    change 1 ≤ K ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧
      (traceHeadGap G ωf x (y k) e rest:ℝ) ≤ 1+K*L
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
    have hB : B.Finite := hCi.subset hBC
    have hKB : (contactSet G (η i) B).Finite := contactSet_finite G hloc (η i) B hB
    have heK : e ∈ contactSet G (η i) B :=
      ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,fun h => hBo h ha⟩
    have hK : 0 < K := (Set.ncard_pos hKB).mpr ⟨e,heK⟩
    have hBpos : 0 < B.ncard := (Set.ncard_pos hB).mpr ⟨b,hb⟩
    have hBM : B.ncard ≤ M := (Set.ncard_le_ncard hBC hCi).trans hM
    have hcluster : cluster G ω' x = S ∪ B :=
      splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hcut : cluster G (ωf \ {e}) x = S :=
      SpliceTrace.head_cut G x η y k j i ω ωf e rest hfull
    have hpe : OpenMarkedPivotal G ωf {y k} x e :=
      SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) hfull (i,e) (by simp)
    have hxa : Conn G (ωf \ {e}) x a := by
      change a ∈ cluster G (ωf \ {e}) x
      rw [hcut]
      exact ha
    have hxb : ¬Conn G (ωf \ {e}) x b := by
      change b ∉ cluster G (ωf \ {e}) x
      rw [hcut]
      exact hBo hb
    have hbits : ωf ∩ internalEdges G B = η i ∩ internalEdges G B := by
      have hii := (splice_internal_fields G S B e ω (η i) a b hab (hBo hb) hBo).2
      ext q
      by_cases hq : q ∈ internalEdges G B
      · have hq' : q ∈ internalEdges G (cluster G ω' x) := by
          rw [hcluster]
          exact fun v hv => Or.inr (hq v hv)
        have hiff := SpliceTrace.internal_agreement G x η y k i ω' ωf rest ht q hq'
        have hbit := congrArg (fun A : Set E => q ∈ A) hii
        simpa only [Set.mem_inter_iff,hq,and_true,hiff] using Iff.of_eq hbit
      · simp only [Set.mem_inter_iff,hq,and_false]
    have hconn := slit_piece_connected G (η i) S (y i) hy
    have finish (l : ℕ) (c : V) (hc : c ∈ B) (hl : 1 ≤ l)
        (hg : l ≤ 1 + pivotalDistance G (ωf ∩ internalEdges G B) b c) :
        1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1+K*L := by
      rw [hbits] at hg
      have hp := pivotalDistance_le_induced_card G (η i) B hB hb (b := c)
      have hg' : (l:ℝ) ≤ 1+(pivotalDistance G (η i ∩ internalEdges G B) b c:ℝ) := by
        exact_mod_cast hg
      have hgood' := goodForScale_piece G (η i) (y i) L hgood B hB hBC hconn hK hb hc
      refine ⟨hl,by omega,?_⟩
      change (l:ℝ) ≤ 1+(contactSet G (η i) B).ncard*L
      linarith
    refine ⟨hK,?_⟩
    cases rest with
    | nil =>
      have hfω : ωf = ω' := by cases ht; rfl
      have hdiff : cluster G ωf x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hfω,hcluster]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hyk : y k ∈ B := by
        have hz := SpliceTrace.endpoint G x η y k j ω ωf [(i,e)] hfull
        rw [hfω,hcluster] at hz
        exact hz.resolve_left hn
      have hconnz := conn_after_pivotal_of_orientation G ωf x (y k) hpe a b hab hxb
      have hp := conn_after_pivotal_internal G ωf x (y k) hpe a b hab hxa hxb hconnz
      have hg := bridge_terminal_gap_le_internal_distance G ωf x (y k) hCf hpe a b hab hxa hp
      rw [hdiff] at hg
      apply finish _ (y k) hyk _ hg
      have hcard : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
        Finset.card_filter_le _ _
      omega
    | cons q more =>
      obtain ⟨l,f⟩ := q
      have hcutf : cluster G (ωf \ {f}) x = S ∪ B := by
        rw [SpliceTrace.head_cut G x η y k i l ω' ωf f more ht,hcluster]
      have hss : cluster G (ωf \ {e}) x ⊂ cluster G (ωf \ {f}) x := by
        rw [hcut,hcutf]
        exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_left,fun heq =>
          hBo hb (heq.symm ▸ (show b ∈ S ∪ B from Or.inr hb))⟩
      have hfFin : (cluster G (ωf \ {f}) x).Finite :=
        hCf.subset (fun _ h => conn_mono G Set.sdiff_subset h)
      have hr : pivotalRank G ωf x e < pivotalRank G ωf x f := Set.ncard_lt_ncard hss hfFin
      have hpf : OpenMarkedPivotal G ωf {y k} x f :=
        SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::(l,f)::more) hfull (l,f) (by simp)
      obtain ⟨c,d,hcd,hxc,hxd,hdyk⟩ := openMarkedPivotal_oriented G ωf {y k} x hpf
      have hdy : Conn G (ωf \ {f}) d (y k) := by
        simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hdyk
      have hdiff : cluster G (ωf \ {f}) x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hcutf]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hc : c ∈ B := by
        have hfout := (pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hCf hpe hpf).mp hr
        have hcnot := ((mem_internalEdges_of_ends G _ f c d hcd).mp hfout).1
        rw [hcut] at hcnot
        change c ∈ cluster G (ωf \ {f}) x at hxc
        rw [hcutf] at hxc
        exact hxc.resolve_left hcnot
      have hp := conn_between_pivotals_internal G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxb (by change c ∈ cluster G (ωf \ {f}) x; rw [hcutf]; exact Or.inr hc)
      have hg := bridge_gap_le_internal_distance G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxd hdy hp
      rw [hdiff] at hg
      apply finish _ c hc _ hg
      have hind := bridgeIndex_interval_identity G ωf x (y k) hCf hpf hr
      omega

end SpliceGapBound

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.seam_data (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, j < q.1 ∧ q.1 ≤ k ∧ q.2 ∈ η q.1 ∧
      q.2 ∈ internalEdges G (cluster G (η q.1) (y q.1)) := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf _ hji hik _ _ he hab _ hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hb' : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
      exact ⟨hji,hik,he,(mem_internalEdges_of_ends G _ e a b hab).mpr
        ⟨(edge_cluster_sides G (η i) (y i) he hab).mpr hb',hb'⟩⟩
    · obtain ⟨hqi,hqk,hqe,hqC⟩ := ih q hq
      exact ⟨hji.trans hqi,hqk,hqe,hqC⟩

 
theorem SpliceTrace.head_index_lt (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hC : (cluster G ωf x).Finite) :
    ∀ q ∈ rest, bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) q.2 := by
  have hfull := h
  have hc := SpliceTrace.head_cut G x η y k j i ω ωf e rest h
  have hseams := SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) h
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax _ _ _ _ _ ht =>
    intro q hq
    obtain ⟨hqi,hqk,_,hqC⟩ := SpliceTrace.seam_data G x η y k i _ ωf rest ht q hq
    have hout : q.2 ∈ internalEdges G (cluster G (ωf \ {e}) x)ᶜ := by
      rw [hc]
      intro v hv hvS
      exact Set.disjoint_left.mp (hmax q.1 hqi hqk) (hqC v hv) hvS
    have hpe := hseams (i,e) (by simp)
    have hpq := hseams q (List.mem_cons_of_mem _ hq)
    exact bridgeIndex_lt_of_rank_lt G ωf x (y k) hpq
      ((pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hC hpe hpq).mpr hout)

 
noncomputable def gapSpliceCode (G : BondGraph V E) (ωf : Set E) (x z : V) :
    List (ℕ × E) → List (ℕ × ℕ)
  | [] => []
  | (i,e)::rest => (i,traceHeadGap G ωf x z e rest)::gapSpliceCode G ωf x z rest


theorem SpliceTrace.decode_gap_code (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (hC : (cluster G ωf x).Finite) :
    decodeGapOrdinals (separatingBonds G ωf x (y k)).card
      (gapSpliceCode G ωf x (y k) steps) = ordinalSpliceCode G ωf x (y k) steps := by
  induction steps generalizing j ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hlater := SpliceTrace.head_index_lt G x η y k j i ω ωf e rest h hC
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      have ih' := ih i _ ht
      simp only [gapSpliceCode,decodeGapOrdinals,ih',ordinalSpliceCode,List.map_cons]
      congr 2
      cases rest with
      | nil =>
        simp only [List.map_nil,traceHeadGap]
        have hle : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
          Finset.card_filter_le _ _
        omega
      | cons q qs =>
        obtain ⟨l,f⟩ := q
        have hle := hlater (l,f) (by simp)
        change bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) f at hle
        simp only [List.map_cons,traceHeadGap]
        omega

 
theorem SpliceTrace.input_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  apply SpliceTrace.input_unique_of_ordinalCode G x η₁ η₂ y₁ y₂ k j ω₁ ω₂ ωf
    c₁ c₂ ht₁ ht₂ hz hC _ θf he₁ he₂
  rw [← SpliceTrace.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ ht₁ hC,
    heq,hz,SpliceTrace.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ ht₂ hC]

end GapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_Replay
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SparseGapCode
attribute [local instance] Classical.propDecidable Classical.decEq



theorem sparseGapValue_zero (c : List (ℕ × ℕ)) (i : ℕ)
    (h : ∀ q ∈ c, i ≠ q.1) : sparseGapValue c i = 0 := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue,ite_eq_right (h (j,l) (by simp))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))


theorem sparseGapValue_injective (c d : List (ℕ × ℕ))
    (hc : c.Pairwise (fun q r => q.1 < r.1))
    (hd : d.Pairwise (fun q r => q.1 < r.1))
    (hpc : ∀ q ∈ c, 0 < q.2) (hpd : ∀ q ∈ d, 0 < q.2)
    (heq : ∀ i, sparseGapValue c i = sparseGapValue d i) : c = d := by
  induction c generalizing d with
  | nil =>
    cases d with
    | nil => rfl
    | cons q d =>
      obtain ⟨j,l⟩ := q
      have hh := heq j
      simp [sparseGapValue] at hh
      have := hpd (j,l) (by simp)
      omega
  | cons q c ih =>
    obtain ⟨i,l⟩ := q
    cases d with
    | nil =>
      have hh := heq i
      simp [sparseGapValue] at hh
      have := hpc (i,l) (by simp)
      omega
    | cons q d =>
      obtain ⟨j,m⟩ := q
      obtain ⟨hc0,hc1⟩ := List.pairwise_cons.mp hc
      obtain ⟨hd0,hd1⟩ := List.pairwise_cons.mp hd
      have hij : i = j := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hij | hji
        · have hz : sparseGapValue ((j,m)::d) i = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hne
            · have := hd0 q hq
              change j < q.1 at this
              omega
          have hh := heq i
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpc (i,l) (by simp)
          omega
        · have hz : sparseGapValue ((i,l)::c) j = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact Ne.symm hne
            · have := hc0 q hq
              change i < q.1 at this
              omega
          have hh := heq j
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpd (j,m) (by simp)
          omega
      subst j
      have hlm : l = m := by simpa [sparseGapValue] using heq i
      subst m
      congr 1
      apply ih d hc1 hd1
        (fun q hq => hpc q (List.mem_cons_of_mem _ hq))
        (fun q hq => hpd q (List.mem_cons_of_mem _ hq))
      intro r
      by_cases hr : r = i
      · subst r
        rw [sparseGapValue_zero c i (fun q hq => (hc0 q hq).ne),
          sparseGapValue_zero d i (fun q hq => (hd0 q hq).ne)]
      · simpa only [sparseGapValue,ite_eq_right hr] using heq r


theorem sparseGapArray_injective (k M : ℕ) (c d : List (ℕ × ℕ))
    (hc : ValidSparseGapCode k M c) (hd : ValidSparseGapCode k M d)
    (heq : sparseGapArray k M c hc = sparseGapArray k M d hd) : c = d := by
  apply sparseGapValue_injective c d hc.1 hd.1
    (fun q hq => (hc.2 q hq).2.2.1) (fun q hq => (hd.2 q hq).2.2.1)
  intro i
  by_cases hi : 1 ≤ i ∧ i ≤ k
  · have he := congrArg (fun f => (f ⟨i-1,by omega⟩).val) heq
    simpa only [sparseGapArray,show i-1+1 = i by omega] using he
  · rw [sparseGapValue_zero c i, sparseGapValue_zero d i]
    · intro q hq he
      have h := hd.2 q hq
      omega
    · intro q hq he
      have h := hc.2 q hq
      omega

 

theorem SpliceTrace.valid_gap_code (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ValidSparseGapCode k M (gapSpliceCode G ωf x (y k) steps) ∧
      ∀ q ∈ gapSpliceCode G ωf x (y k) steps, j < q.1 := by
  induction steps generalizing j ω with
  | nil => simp [ValidSparseGapCode,gapSpliceCode]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      obtain ⟨⟨hpair,hbounds⟩,hlater⟩ := ih i _ ht
      simp only [gapSpliceCode]
      refine ⟨⟨List.pairwise_cons.mpr ⟨?_,hpair⟩,?_⟩,?_⟩
      · exact hlater
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hi,hs.2.1,hg.2.1,hg.2.2.1⟩
        · exact hbounds q hq
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hs.1
        · exact hs.1.trans (hlater q hq)

end SparseGapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceContactMass
attribute [local instance] Classical.propDecidable Classical.decEq



theorem SpliceTrace.contact_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ) (hL : 1 ≤ L)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ∀ i, 1 ≤ traceContactCount G η y ωf x steps i ∧
      (traceContactCount G η y ωf x steps i : ℝ)⁻¹ ≤
        gapLetterWeight L (sparseGapValue (gapSpliceCode G ωf x (y k) steps) i) := by
  induction steps generalizing j ω with
  | nil => simp [traceContactCount,gapSpliceCode,sparseGapValue,gapLetterWeight]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    have hcut := h.head_cut G x η y k j i ω ωf e rest
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    have hk : seamContactCount G η y ωf x i e =
      (contactSet G (η i) (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))).ncard := by
      unfold seamContactCount
      rw [hcut]
    rw [← hk] at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      intro r
      by_cases hr : r = i
      · subst r
        simp only [traceContactCount,gapSpliceCode,sparseGapValue,if_true]
        refine ⟨hg.1,?_⟩
        rw [gapLetterWeight,ite_eq_right (by omega)]
        exact inverse_contact_weight_le _ _ L hg.1 hg.2.1 hL hg.2.2.2
      · simpa only [traceContactCount,gapSpliceCode,sparseGapValue,ite_eq_right hr] using ih i _ ht r



theorem SpliceTrace.code_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂) : c₁ = c₂ := by
  apply ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂)
  rw [← ht₁.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ hC,heq,hz,
    ht₂.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ hC]

end TraceContactMass

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteSpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def GraphSeparated (G : BondGraph V E) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬Adj G a b

end RemoteSpliceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq



def replayContacts (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    contactSet G (η i) B::replayContacts G x η y rest (spliceField G S B e ω (η i))

end RemoteReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeterministicReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def FollowsContactRule (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (steps : List (ℕ × E)) (ω : Set E) : Prop :=
  List.Forall₂ (fun q K => choose q.1 K = q.2) steps (replayContacts G x η y steps ω)

end DeterministicReplay

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq


def patchFirst (U τ : Set E) (s : SpliceState E) : SpliceState E :=
  (exchangeOn U s.1 τ,s.2)



theorem SpliceTrace.runMasks_first (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
    (runMasks (replayMasks G x η y steps ω) (ω,θ)).1 = ωf := by
  induction h with
  | stop => exact fun _ _ => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro θ hθ
    have hθi := hθ i hji hik
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change (runMasks (replayMasks G x η y rest ω') (exchangeState M i (ω,θ))).1 = ωf
    rw [hstep]
    apply ih θ'
    intro l hil hlk
    rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
    exact hθ l (hji.trans hil) hlk


end MaskExecution

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq



theorem replayMasks_indices (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) :
    (replayMasks G x η y c ω).map Prod.fst = c.map Prod.fst := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,List.map_cons,ih]

end JointWeight

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_ReferenceLaws
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

def jointOutput (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₁ y₂ : ℕ → V) (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E)) : JointSpliceState E :=
  (ωf,(runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2,
    (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2)

def jointRestored (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₂ : ℕ → V) (ω₁ ω₂ : Set E) (c₂ : List (ℕ × E)) : JointSpliceState E :=
  (exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂,η₁,η₂)



end FiniteJointMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectorySupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V) : ℕ → Set V
  | 0 => ∅
  | k+1 => trajectoryUnion G η y k ∪ cluster G (η (k+1)) (y (k+1))

theorem mem_trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k : ℕ) (v : V) : v ∈ trajectoryUnion G η y k ↔
      ∃ i, 1 ≤ i ∧ i ≤ k ∧ v ∈ cluster G (η i) (y i) := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    simp only [trajectoryUnion,Set.mem_union,ih]
    constructor
    · rintro (⟨i,hi,hik,hv⟩ | hv)
      · exact ⟨i,hi,by omega,hv⟩
      · exact ⟨k+1,by omega,by omega,hv⟩
    · rintro ⟨i,hi,hik,hv⟩
      by_cases he : i = k+1
      · exact Or.inr (he ▸ hv)
      · exact Or.inl ⟨i,hi,by omega,hv⟩

theorem trajectoryUnion_finite_cap (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k M : ℕ) (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (trajectoryUnion G η y k).Finite ∧ (trajectoryUnion G η y k).ncard ≤ k*M := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    obtain ⟨hf,hc⟩ := ih (fun i hi hik => hcaps i hi (by omega))
    obtain ⟨hf',hc'⟩ := hcaps (k+1) (by omega) (by omega)
    refine ⟨hf.union hf',?_⟩
    calc
      _ ≤ (trajectoryUnion G η y k).ncard + (cluster G (η (k+1)) (y (k+1))).ncard := Set.ncard_union_le ..
      _ ≤ k*M+M := Nat.add_le_add hc hc'
      _ = (k+1)*M := by ring

 

theorem SpliceTrace.added_subset_trajectory (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    cluster G ωf x \ cluster G ω x ⊆ trajectoryUnion G η y k := by
  induction h with
  | stop => exact fun _ hv => (hv.2 hv.1).elim
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    intro v hv
    by_cases hv' : v ∈ cluster G ω' x
    · rw [hC] at hv'
      have hvB := hv'.resolve_left hv.2
      exact (mem_trajectoryUnion G η y k v).mpr
        ⟨i,by omega,hik,conn_mono G Set.inter_subset_left hvB⟩
    · exact ih ⟨hv.1,hv'⟩



end TrajectorySupport

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
def hangingSide (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : Set V :=
  cluster G ω x \ cluster G (ω \ {e}) x

theorem hangingSide_finite (G : BondGraph V E) (ω : Set E) (x : V) (e : E)
    (hC : (cluster G ω x).Finite) : (hangingSide G ω x e).Finite := hC.subset Set.sdiff_subset



noncomputable def smallSeparatingBonds (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) : Finset E :=
  (separatingBonds G ω x z).filter fun e => (hangingSide G ω x e).ncard ≤ v

noncomputable def smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  (smallSeparatingBonds G ω x z v).biUnion fun e => (hangingSide_finite G ω x e hC).toFinset

end SmallHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHanging
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def graphNeighbors (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : Finset V := A.biUnion (neighbors G hloc)



noncomputable def nearHangingEndpoints (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  ((hangingSide_finite G ω x e hC).toFinset ∪ smallHangingThrough G ω x z v hC) ∪
    (graphNeighbors G hloc (hangingSide_finite G ω x e hC).toFinset).biUnion
      (fun a => smallHangingThrough G ω x a v hC)

end NearHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq


def finiteFieldSet (Q : Finset E) (ω : FiniteField Q) : Set E := (ω.val : Set E)

noncomputable def finiteFieldWeight (Q : Finset E) (p : ℝ) (ω : FiniteField Q) : ℝ :=
  bernoulliWeight Q ω.val p

@[simp] theorem domainBits_finiteFieldSet (Q : Finset E) (ω : FiniteField Q) :
    domainBits Q (finiteFieldSet Q ω) = ω.val := by
  ext e
  have hs := Finset.mem_powerset.mp ω.property
  simp only [mem_domainBits,finiteFieldSet,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hs h,h⟩⟩

theorem finiteFieldWeight_nonneg (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    0 ≤ finiteFieldWeight Q p ω := bernoulliWeight_nonneg _ _ p

theorem sum_finiteFieldWeight (Q : Finset E) (p : ℝ) :
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω = 1 := by
  rw [show (fun ω : FiniteField Q => finiteFieldWeight Q p ω) =
    (fun ω : FiniteField Q => bernoulliWeight Q ω.val p) from rfl,Finset.sum_coe_sort Q.powerset (fun ω => bernoulliWeight Q ω p)]
  simpa only [bernoulliPolynomial,bernoulliWeight,mul_one,one_mul] using bernoulliPolynomial_const Q 1 p

 

def finiteFieldFamily (Q : Finset E) (J : Finset ℕ) (η : ↥J → FiniteField Q) : ℕ → Set E :=
  fun i => if hi : i ∈ J then finiteFieldSet Q (η ⟨i,hi⟩) else ∅

@[simp] theorem finiteFieldFamily_at (Q : Finset E) (J : Finset ℕ)
    (η : ↥J → FiniteField Q) (i : ↥J) :
    finiteFieldFamily Q J η i = finiteFieldSet Q (η i) := by
  simp [finiteFieldFamily,i.property]

noncomputable def finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) : ℝ := ∏ i, finiteFieldWeight Q p (η i)

theorem finiteFamilyWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (η : ↥J → FiniteField Q) : 0 ≤ finiteFamilyWeight Q J p η :=
  Finset.prod_nonneg fun _ _ => finiteFieldWeight_nonneg Q p _

theorem sum_finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ) :
    ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η = 1 := by
  unfold finiteFamilyWeight
  rw [← Fintype.prod_sum]
  simp only [sum_finiteFieldWeight,Finset.prod_const_one]

theorem prod_fieldFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) :
    (∏ i ∈ J, bernoulliWeight Q (domainBits Q (finiteFieldFamily Q J η i)) p) =
      finiteFamilyWeight Q J p η := by
  rw [← Finset.prod_coe_sort J]
  simp only [finiteFieldFamily_at,domainBits_finiteFieldSet,finiteFamilyWeight,finiteFieldWeight]

abbrev FiniteJointData (Q : Finset E) (J₁ J₂ : Finset ℕ) :=
  FiniteField Q × (↥J₁ → FiniteField Q) × (↥J₂ → FiniteField Q)

def encodeFiniteJoint (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : FiniteJointData Q J₁ J₂) : JointSpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1,finiteFieldFamily Q J₂ s.2.2)

theorem finiteFieldSet_injective (Q : Finset E) : Function.Injective (finiteFieldSet Q) := by
  intro a b he
  exact Subtype.ext (Finset.coe_injective he)

theorem finiteFieldFamily_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (finiteFieldFamily Q J) := by
  intro a b he
  funext i
  apply finiteFieldSet_injective Q
  simpa only [finiteFieldFamily_at] using congrFun he i

end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def finiteJointDomain (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Finset (JointSpliceState E) := Finset.univ.image (encodeFiniteJoint Q J₁ J₂)

theorem exchangeOn_subset (M ω η Q : Set E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    exchangeOn M ω η ⊆ Q := by
  rintro e (⟨he,_⟩ | ⟨he,_⟩)
  · exact hω he
  · exact hη he

end FiniteReferenceFactor

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]


noncomputable def replaySeedFiber (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) : List (ℕ × E) → Set E → ℕ → Set unitInterval
  | [], _, _ => Set.univ
  | (j,e)::c, ω, i =>
    let S := cluster G ω x
    let B := cluster G (η j ∩ internalEdges G Sᶜ) (y j)
    if i = j then {t | chooseContact (fun _ => t) j (contactSet G (η j) B) = e}
    else replaySeedFiber G x η y c (spliceField G S B e ω (η j)) i

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_MomentBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSpliceState
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.runMasks_execution (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
      SpliceExecution G x (ω,θ) c (runMasks (replayMasks G x η y c ω) (ω,θ)) := by
  induction h with
  | stop => intro θ _; exact SpliceExecution.nil _
  | @step j i ω e a b c ωf hn hji hik hm hy he hab ha hb ht ih =>
    intro θ hθ
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hθi := hθ i hji hik
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change SpliceExecution G x (ω,θ) ((i,e)::c)
      (runMasks (replayMasks G x η y c ω') (exchangeState M i (ω,θ)))
    rw [hstep]
    refine SpliceExecution.cons (ω,θ) (ω',θ') _ (i,e) c ?_ ?_
    · refine ⟨y i,a,b,hy,?_,hab,ha,?_,?_⟩
      · simpa only [hθi] using he
      · simpa only [hθi] using hb
      · simpa only [hθi] using hstep.symm
    · apply ih θ'
      intro l hil hlk
      rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
      exact hθ l (hji.trans hil) hlk

abbrev FiniteSpliceData (Q : Finset E) (J : Finset ℕ) :=
  FiniteField Q × (↥J → FiniteField Q)

def encodeFiniteSplice (Q : Finset E) (J : Finset ℕ)
    (s : FiniteSpliceData Q J) : SpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J s.2)

noncomputable def finiteSpliceDomain (Q : Finset E) (J : Finset ℕ) : Finset (SpliceState E) :=
  Finset.univ.image (encodeFiniteSplice Q J)


theorem mem_finiteSpliceDomain_iff (Q : Finset E) (J : Finset ℕ) (s : SpliceState E) :
    s ∈ finiteSpliceDomain Q J ↔ s.1 ⊆ (Q : Set E) ∧
      (∀ i, s.2 i ⊆ (Q : Set E)) ∧ ∀ i ∉ J, s.2 i = ∅ := by
  constructor
  · intro hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨?_,?_,?_⟩
    · exact Finset.coe_subset.mpr (Finset.mem_powerset.mp a.1.property)
    · intro i
      by_cases hi : i ∈ J
      · simpa only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,finiteFieldSet] using
          Finset.coe_subset.mpr (Finset.mem_powerset.mp (a.2 ⟨i,hi⟩).property)
      · simp [encodeFiniteSplice,finiteFieldFamily,hi]
    · intro i hi
      simp [encodeFiniteSplice,finiteFieldFamily,hi]
  · rintro ⟨hω,hη,hz⟩
    let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
    have he (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
      ext e
      simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
      exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
    refine Finset.mem_image.mpr ⟨(desc s.1,fun i => desc (s.2 i)),Finset.mem_univ _,?_⟩
    apply Prod.ext (he s.1 hω)
    funext i
    by_cases hi : i ∈ J
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,he _ (hη i)]
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_right hi,hz i hi]

theorem exchangeState_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (i : ℕ) (hi : i ∈ J) (M : Set E) :
    exchangeState M i s ∈ finiteSpliceDomain Q J := by
  obtain ⟨hω,hη,hz⟩ := (mem_finiteSpliceDomain_iff Q J s).mp hs
  apply (mem_finiteSpliceDomain_iff Q J _).mpr
  refine ⟨exchangeOn_subset M _ _ _ hω (hη i),?_,?_⟩
  · intro l
    by_cases hli : l = i
    · simpa only [hli,exchangeState_at] using exchangeOn_subset M _ _ _ (hη i) hω
    · rw [exchangeState_away _ _ _ _ hli]
      exact hη l
  · intro l hl
    have hli : l ≠ i := by intro he; subst l; exact hl hi
    rw [exchangeState_away _ _ _ _ hli]
    exact hz l hl

theorem runMasks_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (ms : List (ℕ × Set E))
    (hJ : ∀ q ∈ ms, q.1 ∈ J) : runMasks ms s ∈ finiteSpliceDomain Q J := by
  induction ms generalizing s with
  | nil => exact hs
  | cons q ms ih =>
    apply ih _ (exchangeState_mem_finiteSpliceDomain Q J s hs q.1 (hJ q (by simp)) q.2)
    exact fun q hq => hJ q (by simp [hq])

end FiniteSpliceState

end Percolation

 
open MeasureTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteInverseLoad {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (t : SpliceState E) : ℝ :=
  ∑ a, if out a = t then mass a else 0

theorem finiteInverseLoad_nonneg {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (hm : ∀ a, 0 ≤ mass a) (t : SpliceState E) :
    0 ≤ finiteInverseLoad out mass t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hm a
  · exact le_refl 0



end FiniteSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq



theorem traceIndex_valid (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) :
    SpliceTrace G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 a.2.val
      (traceIndexOutput G x k Q A y a).1 ∧
    SpliceExecution G x a.1.val a.2.val (traceIndexOutput G x k Q A y a) := by
  have ht := ((mem_finiteTraceCodes_iff G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 Q a.2.val).mp
    a.2.property).2
  have hf := ht.runMasks_first G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
    a.1.val.2 (by intros; rfl)
  refine ⟨?_,?_⟩
  · simpa only [traceIndexOutput,hf] using ht
  · exact ht.runMasks_execution G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
      a.1.val.2 (by intros; rfl)

theorem traceIndex_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexInput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ he
  have hah : a = b := Subtype.ext (congrArg Prod.fst he)
  subst b
  have hcd : c = d := Subtype.ext (congrArg Prod.snd he)
  subst d
  rfl

theorem traceIndexOutput_mem (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (a : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G x k Q A y a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) := by
  apply runMasks_mem_finiteSpliceDomain Q (Finset.Icc 1 k) a.1.val (hA a.1.property)
  intro q hq
  have hmap : q.1 ∈ (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1).map Prod.fst :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [replayMasks_indices] at hmap
  obtain ⟨r,hr,her⟩ := List.mem_map.mp hmap
  have h := (traceIndex_valid G x k Q A y a).1.seam_data G x a.1.val.2 (y a.1.val)
    k 0 a.1.val.1 _ a.2.val r hr
  exact her ▸ Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩



end FiniteForwardDensity

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteRootLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteRootLoad (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) (ω : FiniteField Q) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η *
    f (finiteFieldSet Q ω,finiteFieldFamily Q J η)

theorem finiteRootLoad_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (hf : ∀ s ∈ finiteSpliceDomain Q J, 0 ≤ f s)
    (ω : FiniteField Q) : 0 ≤ finiteRootLoad Q J p f ω := by
  apply Finset.sum_nonneg
  intro η _
  apply mul_nonneg (finiteFamilyWeight_nonneg Q J p η)
  exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)

theorem finiteRootLoad_le (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (C : ℝ)
    (hf : ∀ s ∈ finiteSpliceDomain Q J, f s ≤ C)
    (ω : FiniteField Q) : finiteRootLoad Q J p f ω ≤ C := by
  calc
    _ ≤ ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * C := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_left _ (finiteFamilyWeight_nonneg Q J p η)
      exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)
    _ = C := by rw [← Finset.sum_mul,sum_finiteFamilyWeight,one_mul]


end FiniteRootLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePairLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 
def pairSpliceOutput (s t : SpliceState E) : JointSpliceState E := (s.1,s.2,t.2)

end FinitePairLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteFamilyIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFamilyIntegral (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : (ℕ → Set E) → ℝ) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * f (finiteFieldFamily Q J η)

end FiniteFamilyIntegral

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_TrajectoryMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFieldIntegral (Q : Finset E) (p : ℝ) (f : Set E → ℝ) : ℝ :=
  ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * f (finiteFieldSet Q ω)



theorem oldPathWeight_support (G : BondGraph V E) (k M : ℕ) (L : ℝ)
    (q : Set E → V → V → ℝ)
    (hs : ∀ ω a b, q ω a b ≠ 0 → b ∈ cluster G ω a ∧
      (cluster G ω a).Finite ∧ (cluster G ω a).ncard ≤ M ∧ GoodForScale G ω a L)
    (y : ℕ → V) (η : ℕ → Set E) (hy : oldPathWeight k q y η ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ k → y (i-1) ∈ cluster G (η i) (y i) ∧
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M ∧
      GoodForScale G (η i) (y i) L := by
  intro i hi hik
  apply hs
  have h := (Finset.prod_ne_zero_iff.mp hy) ⟨i, Finset.mem_Icc.mpr ⟨hi,hik⟩⟩ (Finset.mem_univ _)
  exact h

end OldPathWeight

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}


theorem oldRunVertices_succ_of_le (k : ℕ) (z : W) (y : Fin (k+1) → W)
    (i : ℕ) (hi : i ≤ k) :
    oldRunVertices (k+1) z y i = oldRunVertices k (y 0) (Fin.tail y) i := by
  simp only [oldRunVertices, ite_eq_left hi]

 

theorem oldPathWeight_oldRunVertices (k : ℕ) (q : Set E → W → W → ℝ)
    (η : ℕ → Set E) (z : W) (y : Fin k → W) :
    oldPathWeight k q (oldRunVertices k z y) η =
      oldRunWeight (fun i => q (η i)) k z y := by
  induction k generalizing z with
  | zero =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 0)
      (fun i => q (η i) (oldRunVertices 0 z y i) (oldRunVertices 0 z y (i-1)))]
    simp [oldRunWeight]
  | succ k ih =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 (k+1))
      (fun i => q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))),
      Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k,
        q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))) =
        oldPathWeight k q (oldRunVertices k (y 0) (Fin.tail y)) η := by
      unfold oldPathWeight
      rw [Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q (η i) (oldRunVertices k (y 0) (Fin.tail y) i)
          (oldRunVertices k (y 0) (Fin.tail y) (i-1)))]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he, ih, oldRunVertices_last, Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _), oldRunVertices_last]
    exact mul_comm _ _

end FiniteOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
noncomputable def finiteOldKernel (Q : Finset E) (p : ℝ)
    (q : Set E → W → W → ℝ) (a b : W) : ℝ :=
  finiteFieldIntegral Q p (fun ω => q ω a b)

end IndependentOldRun

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedCodeFiber
attribute [local instance] Classical.propDecidable Classical.decEq



theorem finite_choice_fiber_le {A B C P : Type*} [Fintype A] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p)
    (hrow : ∀ c, ∑ p, q c p ≤ 1) (b : B) :
    (∑ a, if f a = b then q (ctx a) (choice a) else 0) ≤ 1 := by
  let J := {a : A // f a = b}
  by_cases hne : Nonempty J
  · let a₀ : J := Classical.choice hne
    have hc (a : J) : ctx a.val = ctx a₀.val := hctx _ _ (a.property.trans a₀.property.symm)
    have hi : Function.Injective (fun a : J => choice a.val) := by
      intro a a' he
      apply Subtype.ext
      apply hir
      exact Prod.ext (hctx _ _ (a.property.trans a'.property.symm))
        (Prod.ext he (a.property.trans a'.property.symm))
    have hb := sum_comp_le_sum_of_injective (fun a : J => choice a.val) hi
      (q (ctx a₀.val)) (hq _)
    have he : (∑ a, if f a = b then q (ctx a) (choice a) else 0) =
        ∑ a : J, q (ctx a) (choice a) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro a; simp) _
    rw [he]
    simpa only [hc] using hb.trans (hrow (ctx a₀.val))
  · have hn (a : A) : f a ≠ b := fun h => hne ⟨⟨a,h⟩⟩
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,zero_le_one]

 

theorem finite_weighted_code_mass_le {A B C P : Type*} [Fintype A] [Fintype B] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p) (hrow : ∀ c, ∑ p, q c p ≤ 1)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, q (ctx a) (choice a) * w (f a)) ≤ ∑ b, w b := by
  rw [finite_sum_group_weight]
  apply Finset.sum_le_sum
  intro b _
  calc
    _ ≤ w b * 1 := mul_le_mul_of_nonneg_left
      (finite_choice_fiber_le f ctx choice hir hctx q hq hrow b) (hw b)
    _ = w b := mul_one _

end WeightedCodeFiber
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedInverseLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteInverseLoad_weighted_le {I P : Type*} [Fintype I] [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (choice : I → P) (hir : Function.Injective (fun a => (inp a,choice a,steps a)))
    (q : SpliceState E → P → ℝ) (hq : ∀ s b, 0 ≤ q s b)
    (hrow : ∀ s, ∑ b, q s b ≤ 1)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (t : SpliceState E) :
    finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t ≤
      inverseCodeMass M L ^ k := by
  let J := {a : I // out a = t}
  let c (a : J) := gapSpliceCode G (out a.val).1 x z (steps a.val)
  have hvalid (a : J) : ValidSparseGapCode k M (c a) := by
    have hv := (htrace a.val).valid_gap_code G hloc x (inp a.val).2 (y a.val) k 0 M
      (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L (hgood a.val)
    simpa only [c,hz a.val] using hv.1
  let arr (a : J) := sparseGapArray k M (c a) (hvalid a)
  let ctx (a : J) := (inp a.val,steps a.val)
  have hc (a b : J) (he : arr a = arr b) : ctx a = ctx b := by
    have ho : out a.val = out b.val := a.property.trans b.property.symm
    have hcode : c a = c b := sparseGapArray_injective k M (c a) (c b)
      (hvalid a) (hvalid b) he
    have htB : SpliceTrace G x (inp b.val).2 (y b.val) k 0
        (inp b.val).1 (steps b.val) (out a.val).1 := by
      rw [ho]
      exact htrace b.val
    have heB : SpliceExecution G x (inp b.val) (steps b.val) (out a.val) := ho.symm ▸ hex b.val
    have hg : gapSpliceCode G (out a.val).1 x (y a.val k) (steps a.val) =
        gapSpliceCode G (out a.val).1 x (y a.val k) (steps b.val) := by
      simpa only [c,hz a.val,ho] using hcode
    have hze : y a.val k = y b.val k := (hz a.val).trans (hz b.val).symm
    have hs := (htrace a.val).code_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg
    have hi := (htrace a.val).input_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg (out a.val).2 (hex a.val) heB
    exact Prod.ext hi hs
  have hi : Function.Injective (fun a : J => (ctx a,choice a.val,arr a)) := by
    intro a b he
    apply Subtype.ext
    apply hir
    have hec := congrArg Prod.fst he
    have hin : inp a.val = inp b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.1) hec
    have hst : steps a.val = steps b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.2) hec
    exact Prod.ext hin (Prod.ext (congrArg (fun z => z.2.1) he) hst)
  let w (b : Fin k → Fin (M+1)) := ∏ i, gapLetterWeight L (b i).val
  have hb := finite_weighted_code_mass_le arr ctx (fun a : J => choice a.val) hi hc
    (fun s b => q s.1 b) (fun s => hq s.1) (fun s => hrow s.1) w
    (fun b => Finset.prod_nonneg (fun i _ => gapLetterWeight_nonneg L (by linarith) _))
  change (∑ a : J, q (inp a.val) (choice a.val) * w (arr a)) ≤ ∑ b, w b at hb
  have he : finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t =
      ∑ a : J, q (inp a.val) (choice a.val) * ∏ i : Fin k,
      (traceContactCount G (inp a.val).2 (y a.val) (out a.val).1 x (steps a.val) (i.val+1):ℝ)⁻¹ := by
    rw [finiteInverseLoad,← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro a; simp) _
  rw [he]
  calc
    _ ≤ ∑ a : J, q (inp a.val) (choice a.val) * w (arr a) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hq _ _)
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      have h := ((htrace a.val).contact_weight_bound G hloc x (inp a.val).2 (y a.val)
        k 0 M (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L hL
        (hgood a.val) (i.val+1)).2
      simpa only [w,arr,sparseGapArray,c,hz a.val] using h
    _ ≤ ∑ b, w b := hb
    _ = _ := total_gap_code_mass k M L

end WeightedInverseLoad
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}



def choiceTraceCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : List (ℕ × E) :=
  traceIndexCode G x k Q (A a.1) (y a.1) a.2

theorem choiceTrace_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteChoiceTraceIndex G x k Q A y =>
      (choiceTraceInput G x k Q A y a,a.1,choiceTraceCode G x k Q A y a)) := by
  rintro ⟨r,a⟩ ⟨r',b⟩ he
  have hr : r = r' := congrArg (fun z => z.2.1) he
  subst r'
  have hin : traceIndexInput G x k Q (A r) (y r) a =
      traceIndexInput G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.1) he
  have hcode : traceIndexCode G x k Q (A r) (y r) a =
      traceIndexCode G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.2.2) he
  have hab : a = b := traceIndex_injective G x k Q (A r) (y r) (Prod.ext hin hcode)
  subst b
  rfl

noncomputable def finiteChoiceForwardLoad [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) : SpliceState E → ℝ :=
  finiteInverseLoad (choiceTraceOutput G x k Q A y) (choiceTraceMass G x k Q A y q)

 
theorem finiteChoiceForwardLoad_bounds [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (hq : ∀ s r, 0 ≤ q s r)
    (hrow : ∀ s, ∑ r, q s r ≤ 1)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hz : ∀ r s, s ∈ A r → y r s k = z)
    (hgood : ∀ r s, s ∈ A r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y r s i)).Finite ∧
      (cluster G (s.2 i) (y r s i)).ncard ≤ M ∧ GoodForScale G (s.2 i) (y r s i) L)
    (t : SpliceState E) :
    0 ≤ finiteChoiceForwardLoad G x k Q A y q t ∧
      finiteChoiceForwardLoad G x k Q A y q t ≤ inverseCodeMass M L ^ k := by
  constructor
  · apply finiteInverseLoad_nonneg
    intro a
    exact mul_nonneg (hq _ _) (Finset.prod_nonneg (fun _ _ => by positivity))
  · apply finiteInverseLoad_weighted_le G hloc x z k M L hL
      (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
      (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val) Sigma.fst
      (choiceTrace_injective G x k Q A y) q hq hrow
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
      (fun a => hz a.1 _ a.2.1.property) _
      (fun a => hgood a.1 _ a.2.1.property) t
    intro a
    have hs := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp
      (traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2)
    exact cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs.1) x



end ChoiceForwardDensity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def auxiliaryTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ := ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p



noncomputable def endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (z : V) : ℝ :=
  ∑ a, if (out a).1 = ω ∧ endpoint a = z then auxiliaryTupleWeight Q J p (out a) * m a else 0


theorem finiteRootLoad_eq_sum {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) (ω : FiniteField Q) :
    finiteRootLoad Q J p (finiteInverseLoad out m) ω =
      ∑ a, if (out a).1 = finiteFieldSet Q ω then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [finiteRootLoad,finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨⟨r,η⟩,_,ha⟩ := Finset.mem_image.mp (hs a)
  change (finiteFieldSet Q r,finiteFieldFamily Q J η) = out a at ha
  rw [← ha]
  have he (θ : ↥J → FiniteField Q) :
      (finiteFieldSet Q r,finiteFieldFamily Q J η) = (finiteFieldSet Q ω,finiteFieldFamily Q J θ) ↔
      r = ω ∧ η = θ := by
    constructor
    · intro h
      exact ⟨finiteFieldSet_injective Q (congrArg Prod.fst h),
        finiteFieldFamily_injective Q J (congrArg Prod.snd h)⟩
    · rintro ⟨rfl,rfl⟩; rfl
  simp only [he]
  by_cases hr : r = ω
  · subst r
    simp only [true_and,if_true,Finset.sum_ite_eq,Finset.mem_univ]
    rw [auxiliaryTupleWeight,prod_fieldFamilyWeight]
  · have hr' : finiteFieldSet Q r ≠ finiteFieldSet Q ω := fun h => hr (finiteFieldSet_injective Q h)
    simp [hr,hr']



end EndpointRootMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem mem_reachBall_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (x y : V) (n : ℕ) :
    a y ∈ reachBall G (a x) n ↔ y ∈ reachBall G x n := by
  constructor
  · intro h
    simpa only [Equiv.symm_apply_apply] using mem_reachBall_aut G (isAut_symm G ha) h
  · exact mem_reachBall_aut G ha

 
def transportCut (G : BondGraph V E) (n : ℕ) (x y : V) : Prop :=
  y ∈ reachBall G x n ∧ x ∈ reachBall G y n

end NonnegativeTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteTrajectoryMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]



noncomputable def finiteTrajectoryMass (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (a : V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
      oldRunWeight (fun i => q (η i)) k z y else 0)

noncomputable def finiteTrajectoryHit (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty then
      oldRunWeight (fun i => q (η i)) k z y else 0)

end FiniteTrajectoryMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Transport_EndpointKernels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceSeparatedMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P₁ P₂ : Type*} [Fintype P₁] [Fintype P₂]

 
noncomputable def finiteChoiceSeparatedPairMass
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ) : ℝ :=
  ∑ a : FiniteChoiceTraceIndex G x k Q A₁ (fun r s => y₁ r s.2),
    ∑ b : FiniteChoiceTraceIndex G x k Q A₂ (fun r s => y₂ r s.2),
    if (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 =
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b).1 ∧
      choiceTraceCode G x k Q A₁ (fun r s => y₁ r s.2) a ≠ [] ∧
      choiceTraceCode G x k Q A₂ (fun r s => y₂ r s.2) b ≠ [] ∧
      GraphSeparated G
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x)
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₂ (fun r s => y₂ r s.2) b).1 x)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a)
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b)) *
      choiceTraceMass G x k Q A₁ (fun r s => y₁ r s.2) (fun s r => m₁ r s.2) a *
      choiceTraceMass G x k Q A₂ (fun r s => y₂ r s.2) (fun s r => m₂ r s.2) b else 0

 
noncomputable def finiteChoiceHit (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : ℝ)
    (y : P₁ → (ℕ → Set E) → ℕ → V) (m : P₁ → (ℕ → Set E) → ℝ) (B : Set V) : ℝ :=
  ∑ r, finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (B ∩ trajectoryUnion G η (y r η) k).Nonempty then m r η else 0)



end ChoiceSeparatedMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

structure LocalEndpointRule (G : BondGraph V E) (hloc : LocallyFinite G)
    (O : Set V) (M : ℕ) (L : ℝ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  row_le_one : ∀ ω x, (∑' y, mass ω x y) ≤ 1
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem outside_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hfin M hcap hc)

theorem summable_mass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    Summable (q.mass ω x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.outside_ball_zero ω x y
  simpa only [Set.Finite.mem_toFinset] using hy



noncomputable def kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

end LocalEndpointRule
end LocalEndpointRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



noncomputable def successProbability (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, q.kernel p x y

end LocalEndpointRule
end LocalEndpointKernel

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointSchur
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}


noncomputable def normalizedKernel (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x y : V) : ℝ :=
  (q.successProbability p o)⁻¹ * q.kernel p x y



end LocalEndpointRule
end EndpointSchur

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteFieldEquiv (Q : Finset E) : FiniteField Q ≃ Set (Q : Set E) where
  toFun ω := Subtype.val ⁻¹' finiteFieldSet Q ω
  invFun η := ⟨η.toFinset.map ⟨Subtype.val,Subtype.val_injective⟩, by
    apply Finset.mem_powerset.mpr
    intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp he
    exact a.property⟩
  left_inv ω := by
    apply Subtype.ext
    apply Finset.coe_injective
    ext e
    simp only [Finset.coe_map,Set.mem_image,finiteFieldSet,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,rfl⟩
      have ha' : a ∈ (Subtype.val ⁻¹' (ω.val : Set E) : Set (Q : Set E)) := Set.mem_toFinset.mp ha
      exact ha'
    · intro he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,Set.mem_toFinset.mpr he,rfl⟩
  right_inv η := by
    ext e
    simp only [Set.mem_preimage,finiteFieldSet,Finset.coe_map,Set.coe_toFinset,
      Set.mem_image,Function.Embedding.coeFn_mk,Subtype.val_injective.eq_iff,exists_eq_right]

@[simp] theorem finiteFieldEquiv_apply (Q : Finset E) (ω : FiniteField Q) :
    finiteFieldEquiv Q ω = Subtype.val ⁻¹' finiteFieldSet Q ω := rfl

@[simp] theorem finiteFieldEquiv_image (Q : Finset E) (ω : FiniteField Q) :
    Subtype.val '' finiteFieldEquiv Q ω = finiteFieldSet Q ω := by
  rw [finiteFieldEquiv_apply]
  apply Set.image_preimage_eq_of_subset
  intro e he
  exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩



end FiniteLocalIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GoodnessCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem openMarkedPivotal_pair_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) (e : E) :
    OpenMarkedPivotal G (b ⁻¹' ω) {y} x e ↔
      OpenMarkedPivotal G ω {a y} (a x) (b e) := by
  have he : (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  simp only [OpenMarkedPivotal,MarkedEvent,Set.mem_singleton_iff,exists_eq_left,
    Set.mem_preimage,he,conn_aut_iff G hab]

theorem pivotalDistance_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    pivotalDistance G (b ⁻¹' ω) x y = pivotalDistance G ω (a x) (a y) := by
  have he : {e | OpenMarkedPivotal G (b ⁻¹' ω) {y} x e} =
      b ⁻¹' {e | OpenMarkedPivotal G ω {a y} (a x) e} := by
    ext e
    exact openMarkedPivotal_pair_aut G hab ω x y e
  rw [pivotalDistance,he,Set.ncard_preimage_of_injective_subset_range b.injective]
  · rfl
  · exact fun e _ => b.surjective e

theorem goodForScale_aut_pullback (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω (a x) L) : GoodForScale G (b ⁻¹' ω) x L := by
  intro W hW hconn hpos u hu v hv
  let W' := W.map a.toEmbedding
  have hpre : a ⁻¹' (W' : Set V) = (W : Set V) := by
    ext z
    simp [W']
  have hcfg : b ⁻¹' (ω ∩ internalEdges G (W' : Set V)) =
      (b ⁻¹' ω) ∩ internalEdges G (W : Set V) := by
    rw [Set.preimage_inter,← internalEdges_aut_preimage G hab,hpre]
  have hcontact : (contactSet G (b ⁻¹' ω) (W : Set V)).ncard =
      (contactSet G ω (W' : Set V)).ncard := by
    rw [← hpre,contactSet_aut_preimage G hab,
      Set.ncard_preimage_of_injective_subset_range b.injective]
    exact fun e _ => b.surjective e
  have hW' : (W' : Set V) ⊆ cluster G ω (a x) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz
    exact (conn_aut_iff G hab ω x w).mp (hW hw)
  have hc' : ∀ w ∈ W', ∀ z ∈ W', Conn G (ω ∩ internalEdges G (W' : Set V)) w z := by
    intro w hw z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hz
    apply (conn_aut_iff G hab _ u v).mp
    rw [hcfg]
    exact hconn u hu v hv
  have H := hg W' hW' hc' (by rwa [← hcontact]) (a u)
    (Finset.mem_map.mpr ⟨u,hu,rfl⟩) (a v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
  rw [← pivotalDistance_aut_preimage G hab,hcfg,← hcontact] at H
  exact H

theorem goodForScale_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ) :
    GoodForScale G (b ⁻¹' ω) x L ↔ GoodForScale G ω (a x) L := by
  constructor
  · intro h
    have H := goodForScale_aut_pullback G (isAut_symm G hab) (b ⁻¹' ω) (a x) L
      (by simpa only [Equiv.symm_apply_apply] using h)
    simpa only [← Set.preimage_comp,Equiv.self_comp_symm,Set.preimage_id_eq,id_eq] using H
  · exact goodForScale_aut_pullback G hab ω x L

end GoodnessCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

def CappedGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L

theorem cappedGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q : Set E)) x M L := by
  have he (η : Set E) : CappedGoodness G η x M L ↔
      ((cluster G η x).Finite ∧ (cluster G η x).ncard ≤ M) ∧ ¬CappedBadGoodness G η x M L := by
    constructor
    · rintro ⟨hf,hM,hg⟩
      exact ⟨⟨hf,hM⟩,fun h => h.2.2 hg⟩
    · rintro ⟨⟨hf,hM⟩,hbad⟩
      refine ⟨hf,hM,?_⟩
      by_contra hn
      exact hbad ⟨hf,hM,hn⟩
  dsimp only
  have hbad := cappedBadGoodness_local G hloc x M L ω
  have hcap := capped_cluster_local G hloc x M ω
  dsimp only at hbad hcap
  rw [he,he,hbad,hcap]

theorem cappedGoodness_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    CappedGoodness G (b ⁻¹' ω) x M L ↔ CappedGoodness G ω (a x) M L := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [CappedGoodness,hf,hn,goodForScale_aut_iff G hab]

theorem incidentSupport_ball_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) {r R : ℕ} (h : r ≤ R) :
    incidentSupport G hloc (finite_reachBall hloc x r).toFinset ⊆
      incidentSupport G hloc (finite_reachBall hloc x R).toFinset := by
  apply incidentSupport_mono
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz ⊢
  exact reachBall_mono_local G x h hz

end CappedGoodLocality

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq



structure CappedLocalLoad (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (M : ℕ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def row (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y

theorem row_locality (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) :
    q.row ω x = q.row
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem row_covariance (q : CappedLocalLoad G hloc O M) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) : q.row (b ⁻¹' ω) x = q.row ω (a x) := by
  unfold row
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _



noncomputable def truncate (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b) (L : ℝ) :
    LocalEndpointRule G hloc O M L where
  mass ω x y := if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then b⁻¹ * q.mass ω x y else 0
  radius := max q.radius M
  nonneg ω x y := by split_ifs; exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y); rfl
  row_le_one ω x := by
    by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
    · simp only [h,and_self,if_true,tsum_mul_left]
      exact (mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hb.le)).trans_eq (inv_mul_cancel₀ hb.ne')
    · simp only [h,if_false,tsum_zero,zero_le_one]
  support ω x y h := by
    split_ifs at h with hkeep
    · have hm : q.mass ω x y ≠ 0 := fun he => h (by rw [he,mul_zero])
      obtain ⟨hx,hy,hc,_,_⟩ := q.support ω x y hm
      exact ⟨hx,hy,hc,hkeep.2⟩
    · exact (h rfl).elim
  locality ω x y := by
    let S := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    have hm := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.mass η x y) (q.locality · x y) ω
    have hr := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.row η x) (q.row_locality · x) ω
    have hg := finite_prop_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_right q.radius M))
      (fun η => CappedGoodness G η x M L) (fun η => cappedGoodness_local G hloc η x M L) ω
    simp only [hm,hr,hg]
    rfl
  covariance a c hac ω x y := by
    simp only [q.row_covariance a c hac,q.covariance a c hac,cappedGoodness_aut_iff G hac]

end CappedLocalLoad
end CappedLocalLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CategoricalAmplificationInput
attribute [local instance] Classical.propDecidable Classical.decEq



namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) : ℝ :=
  oldRunWeight (fun i a b => q.mass (s.2 i) a.val b.val) k z r

theorem amplificationWeight_eq (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B k z s r = oldPathWeight k q.mass (amplificationVertices B k z r) s.2 := by
  exact (oldPathWeight_oldRunVertices k (fun ω a b => q.mass ω a.val b.val) s.2 z r).symm

theorem amplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    0 ≤ q.amplificationWeight B k z s r :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun i a b => q.nonneg (s.2 i) a.val b.val) k z r

theorem amplificationWeight_row (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) :
    (∑ r, q.amplificationWeight B k z s r) ≤ 1 := by
  have hr (i : ℕ) (a : ↥B) : (∑ b : ↥B, q.mass (s.2 i) a.val b.val) ≤ 1 := by
    rw [Finset.sum_coe_sort B]
    exact ((q.summable_mass _ _).sum_le_tsum B (fun y _ => q.nonneg _ _ y)).trans (q.row_le_one _ _)
  simpa only [one_pow,amplificationWeight] using sum_oldRunWeight_le
    (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun _ a b => q.nonneg _ a.val b.val) 1 zero_le_one hr k z

 

noncomputable def amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) : Finset (SpliceState E) :=
  (finiteSpliceDomain Q (Finset.Icc 1 k)).filter fun s =>
    x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0

theorem mem_amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    s ∈ q.amplificationInputs Q B x k n z r ↔
      s ∈ finiteSpliceDomain Q (Finset.Icc 1 k) ∧
      x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0 :=
  Finset.mem_filter

theorem amplificationInputs_subset (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) :
    q.amplificationInputs Q B x k n z r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  Finset.filter_subset _ _

theorem amplificationInputs_chain (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) :
    ∀ i, 1 ≤ i → i ≤ k →
      Conn G (s.2 i) (amplificationVertices B k z r i) (amplificationVertices B k z r (i-1)) ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).Finite ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).ncard ≤ M ∧
      GoodForScale G (s.2 i) (amplificationVertices B k z r i) L := by
  apply oldPathWeight_support G k M L q.mass
  · intro ω a b h
    exact (q.support ω a b h).2.2
  · exact (q.amplificationWeight_eq B k z s r) ▸ ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.2

 

theorem amplificationTrace_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) (c : List (ℕ × E)) (ωf : Set E)
    (ht : SpliceTrace G x s.2 (amplificationVertices B k z r) k 0 s.1 c ωf) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ωf x z.val ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ 2*n+k*M := by
  obtain ⟨hdom,hx,hz,_,hbin,_,_⟩ := (q.mem_amplificationInputs Q B x k n z r s).mp hs
  have hc := q.amplificationInputs_chain Q B x k n z r s hs
  have hroot : (cluster G s.1 x).Finite :=
    cluster_finite_of_finite_edges G (Q.finite_toSet.subset
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp hdom).1) x
  obtain ⟨hf,hcap⟩ := trajectoryUnion_finite_cap G s.2 (amplificationVertices B k z r) k M
    (fun i hi hik => ⟨(hc i hi hik).2.1,(hc i hi hik).2.2.1⟩)
  have hsub : cluster G ωf x ⊆ cluster G s.1 x ∪ trajectoryUnion G s.2 (amplificationVertices B k z r) k := by
    intro v hv
    by_cases hv' : v ∈ cluster G s.1 x
    · exact Or.inl hv'
    · exact Or.inr (ht.added_subset_trajectory G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c ⟨hv,hv'⟩)
  refine ⟨hx,hz,?_,(hroot.union hf).subset hsub,?_⟩
  · simpa only [amplificationVertices,oldRunVertices_last,cluster,Set.mem_ofPred_eq] using
      ht.endpoint G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c
  · exact (Set.ncard_le_ncard hsub (hroot.union hf)).trans
      ((Set.ncard_union_le ..).trans (Nat.add_le_add (by omega) hcap))

end LocalEndpointRule
end CategoricalAmplificationInput

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Amplification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def restrictFiniteField (Q : Finset E) (ω : Set E) : FiniteField Q :=
  ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩

@[simp] theorem finiteFieldSet_restrict (Q : Finset E) (ω : Set E) :
    finiteFieldSet Q (restrictFiniteField Q ω) = ω ∩ (Q : Set E) := by
  ext e
  simp [restrictFiniteField,domainBits,finiteFieldSet,and_comm]

@[simp] theorem restrictFiniteField_fieldSet (Q : Finset E) (ω : FiniteField Q) :
    restrictFiniteField Q (finiteFieldSet Q ω) = ω := by
  apply Subtype.ext
  exact domainBits_finiteFieldSet Q ω

theorem cluster_restrict_of_cap (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (C : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x C).toFinset ⊆ Q)
    (hf : (cluster G (ω ∩ (Q : Set E)) x).Finite)
    (hC : (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ C) :
    cluster G (ω ∩ (Q : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have ha := finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hf C hC ih
      have heQ := hQ ((mem_incidentSupport G hloc _ e).mpr
        ⟨a,by simpa only [Set.Finite.mem_toFinset] using ha,by simp [hab]⟩)
      exact ih.tail ⟨e,⟨he,heQ⟩,hab⟩

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

noncomputable def amplificationMarginal (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
      (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z)) (restrictFiniteField Q ω)

theorem amplificationMarginal_local (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q B x k n z p ω =
      q.amplificationMarginal Q B x k n z p (ω ∩ (Q : Set E)) := by
  unfold amplificationMarginal
  congr 1
  apply (finiteFieldSet_injective Q)
  simp only [finiteFieldSet_restrict,Set.inter_assoc,Set.inter_self]

theorem amplificationMarginal_bounds (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationMarginal Q B x k n z p ω ∧
      q.amplificationMarginal Q B x k n z p ω ≤ inverseCodeMass M L ^ k := by
  have hb := finiteChoiceForwardLoad_bounds G hloc x z.val k M L hL Q
    (q.amplificationInputs Q B x k n z) (fun r _ => amplificationVertices B k z r)
    (q.amplificationWeight B k z) (q.amplificationWeight_nonneg B k z)
    (q.amplificationWeight_row B k z) (q.amplificationInputs_subset Q B x k n z)
    (fun _ _ _ => congrArg Subtype.val (oldRunVertices_last ..))
    (fun r s hs i hi hik => (q.amplificationInputs_chain Q B x k n z r s hs i hi hik).2)
  exact ⟨finiteRootLoad_nonneg _ _ p _ (fun s _ => (hb s).1) _,
    finiteRootLoad_le _ _ p _ _ (fun s _ => (hb s).2) _⟩

theorem amplificationMarginal_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G (ω ∩ (Q : Set E)) x z.val ∧
      (cluster G (ω ∩ (Q : Set E)) x).Finite ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ 2*n+k*M := by
  let A := q.amplificationInputs Q B x k n z
  let y := fun r (_ : SpliceState E) => amplificationVertices B k z r
  let I := FiniteChoiceTraceIndex G x k Q A y
  let out := choiceTraceOutput G x k Q A y
  have ho (a : I) : out a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    traceIndexOutput_mem G x k Q (A a.1) (y a.1) (q.amplificationInputs_subset Q B x k n z a.1) a.2
  have he := finiteRootLoad_eq_sum Q (Finset.Icc 1 k) p out
    (choiceTraceMass G x k Q A y (q.amplificationWeight B k z)) ho (restrictFiniteField Q ω)
  have ha : ∃ a : I, (out a).1 = ω ∩ (Q : Set E) := by
    by_contra hn
    push Not at hn
    apply h
    change finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out _) _ = 0
    rw [he,finiteFieldSet_restrict]
    simp only [hn,if_false,Finset.sum_const_zero]
  obtain ⟨a,ha⟩ := ha
  have ht := (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1
  have hs := q.amplificationTrace_support Q B x k n z a.1 a.2.1.val a.2.1.property
    (choiceTraceCode G x k Q A y a) (out a).1 ht
  rwa [ha] at hs

theorem amplificationMarginal_physical_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n+k*M)).toFinset ⊆ Q)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ω x z.val ∧ (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ 2*n+k*M := by
  obtain ⟨hx,hz,hc,hf,hcap⟩ := q.amplificationMarginal_support Q B x k n z p ω h
  have he := cluster_restrict_of_cap G hloc Q ω x (2*n+k*M) hQ hf hcap
  exact ⟨hx,hz,conn_mono G Set.inter_subset_left hc,he ▸ hf,he ▸ hcap⟩



end LocalEndpointRule
end AmplificationMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMeanKernel
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteBinConnection (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (n : ℕ) (y : V) : ℝ := finiteFieldIntegral Q p (fun ω =>
      if n ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < 2*n ∧ y ∈ cluster G ω x then 1 else 0)

end AmplificationMeanKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def binConnectionMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  if (cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n ∧ Conn G ω x y then 1 else 0

noncomputable def binConnection (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binConnectionMass G n ω x y ∂law p

end BinConnection

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitBinOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem isAut_trans (G : BondGraph V E) {a c : V ≃ V} {b d : E ≃ E}
    (hab : IsAut G a b) (hcd : IsAut G c d) : IsAut G (a.trans c) (b.trans d) := by
  intro e
  change G (d (b e)) = (G e).map (c ∘ a)
  rw [hcd,hab,Sym2.map_map]

theorem mem_vertexOrbit_aut_iff (G : BondGraph V E) (o : V) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) : a x ∈ vertexOrbit G o ↔ x ∈ vertexOrbit G o := by
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G hab),?_⟩
    simp only [Equiv.trans_apply,hc,Equiv.symm_apply_apply]
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd hab,rfl⟩


noncomputable def orbitBinConnection (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : ℝ :=
  if x ∈ vertexOrbit G o ∧ y ∈ vertexOrbit G o then binConnection G p n x y else 0

noncomputable def binOrbitRow (G : BondGraph V E) (p : unitInterval) (o : V) (n : ℕ) : ℝ :=
  ∑' y, orbitBinConnection G p o n o y

end OrbitBinOperator

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterVisitKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def conditionalSuccess (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y



noncomputable def clusterVisitMass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) : ℝ :=
  if a ∈ cluster G ω x then q.conditionalSuccess ω x else 0

noncomputable def clusterVisitKernel (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x a : V) : ℝ := ∫ ω, q.clusterVisitMass ω x a ∂law p

end LocalEndpointRule
end ClusterVisitKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section VisitEnvelope
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

noncomputable def visitEnvelope (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) : ℕ → V → V → ℝ
  | 0, _, _ => 0
  | k+1, x, a => q.successProbability p o ^ k * q.clusterVisitKernel p x a +
      ∑' y, q.kernel p x y * q.visitEnvelope o p k y a

end LocalEndpointRule
end VisitEnvelope

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Splicing_EndpointMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq



namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def allAmplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) : ℝ :=
  oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k r.1 r.2

noncomputable def allAmplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ)
    (r : ↥B × (Fin k → ↥B)) : Finset (SpliceState E) :=
  q.amplificationInputs Q B x k n r.1 r.2

end LocalEndpointRule
end AllEndpointHit

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointSeparated
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWindowMass (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (lo hi : ℕ) : ℝ :=
  finiteFieldIntegral Q p (fun ω => if (cluster G ω x).Finite ∧
    lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi then 1 else 0)

end AllEndpointSeparated

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq


namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

abbrev AmplificationIndex (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) :=
  FiniteChoiceTraceIndex G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationOutput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceOutput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationInput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceInput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationCode (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → List (ℕ × E) :=
  choiceTraceCode G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → ℝ :=
  choiceTraceMass G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)

noncomputable def amplificationRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) : ℝ :=
  ∑ z : ↥B, q.amplificationMarginal Q B x k n z p ω

end LocalEndpointRule
end AllEndpointMarginal

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointNil
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationNilRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteInverseLoad (q.amplificationOutput Q B x k n)
      (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)) ω



end LocalEndpointRule
end AllEndpointNil

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNear
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationAdded (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) : Set V :=
  cluster G (q.amplificationOutput Q B x k n a).1 x \ cluster G (q.amplificationInput Q B x k n a).1 x

noncomputable def amplificationNearPairMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) : ℝ :=
  ∑ a : q.AmplificationIndex Q B x k n, ∑ b : q.AmplificationIndex Q B x k n,
    if (q.amplificationOutput Q B x k n a).1 = (q.amplificationOutput Q B x k n b).1 ∧
      q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
      ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (q.amplificationOutput Q B x k n a) (q.amplificationOutput Q B x k n b)) *
        q.amplificationMass Q B x k n a * q.amplificationMass Q B x k n b else 0



end LocalEndpointRule
end AllEndpointNear

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteThreeClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def commonRootPairMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (m : I → ℝ) (P : I → I → Prop) : ℝ :=
  ∑ a, ∑ b, if (out a).1 = (out b).1 ∧ P a b then
    jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b else 0



end FiniteThreeClass

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Covariance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteFieldCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteFieldAutEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : FiniteField Q ≃ FiniteField Q' :=
  (Equiv.finsetCongr b).subtypeEquiv (fun ω => by
    simp only [Finset.mem_powerset]
    change ω ⊆ Q ↔ ω.map b.toEmbedding ⊆ Q'
    rw [finset_aut_eq_map b Q Q' hQ,Finset.map_subset_map])

@[simp] theorem finiteFieldSet_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : FiniteField Q) :
    finiteFieldSet Q' (finiteFieldAutEquiv b Q Q' hQ ω) = edgeFieldEquiv b (finiteFieldSet Q ω) := by
  change (ω.val.map b.toEmbedding : Set E) = b.symm ⁻¹' (ω.val : Set E)
  rw [Finset.coe_map]
  exact b.image_eq_preimage_symm _

@[simp] theorem finiteFieldWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (p : ℝ) (ω : FiniteField Q) :
    finiteFieldWeight Q' p (finiteFieldAutEquiv b Q Q' hQ ω) = finiteFieldWeight Q p ω := by
  change p^(ω.val.map b.toEmbedding).card * (1-p)^(Q'.card-(ω.val.map b.toEmbedding).card) = _
  simp only [Finset.card_map,finset_aut_eq_map b Q Q' hQ]
  rfl

noncomputable def finiteFamilyEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) :
    (↥J → FiniteField Q) ≃ (↥J → FiniteField Q') :=
  Equiv.piCongrRight fun _ => finiteFieldAutEquiv b Q Q' hQ

@[simp] theorem finiteFieldFamily_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (η : ↥J → FiniteField Q) (i : ℕ) :
    finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) i =
      edgeFieldEquiv b (finiteFieldFamily Q J η i) := by
  unfold finiteFieldFamily
  split_ifs with hi
  · exact finiteFieldSet_aut_map b Q Q' hQ (η ⟨i,hi⟩)
  · rfl

@[simp] theorem finiteFamilyWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ) (η : ↥J → FiniteField Q) :
    finiteFamilyWeight Q' J p (finiteFamilyEquiv b Q Q' hQ J η) = finiteFamilyWeight Q J p η := by
  apply Finset.prod_congr rfl
  intro i _
  exact finiteFieldWeight_aut_map b Q Q' hQ p (η i)

@[simp] theorem restrictFiniteField_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    restrictFiniteField Q' (edgeFieldEquiv b ω) = finiteFieldAutEquiv b Q Q' hQ (restrictFiniteField Q ω) := by
  apply finiteFieldSet_injective Q'
  rw [finiteFieldSet_aut_map,finiteFieldSet_restrict,finiteFieldSet_restrict]
  ext e
  change (b.symm e ∈ ω ∧ e ∈ Q') ↔ (b.symm e ∈ ω ∧ b.symm e ∈ Q)
  rw [hQ (b.symm e),b.apply_symm_apply]

 

theorem finiteRootLoad_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ)
    (f f' : SpliceState E → ℝ) (hf : ∀ s, f' (spliceStateEquiv b s) = f s)
    (ω : FiniteField Q) :
    finiteRootLoad Q' J p f' (finiteFieldAutEquiv b Q Q' hQ ω) = finiteRootLoad Q J p f ω := by
  unfold finiteRootLoad
  rw [← (finiteFamilyEquiv b Q Q' hQ J).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [finiteFamilyWeight_aut_map,finiteFieldSet_aut_map]
  have he : finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) =
      fun i => edgeFieldEquiv b (finiteFieldFamily Q J η i) :=
    funext (finiteFieldFamily_aut_map b Q Q' hQ J η)
  rw [he]
  exact congrArg (fun t => finiteFamilyWeight Q J p η * t)
    (hf (finiteFieldSet Q ω,finiteFieldFamily Q J η))

end FiniteFieldCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ChoiceIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P P' : Type*}

theorem finiteChoiceForwardLoad_aut_map [Fintype P] [Fintype P']
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))
    (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r) (s : SpliceState E) :
    finiteChoiceForwardLoad G (a x) k Q' A' y' q' (spliceStateEquiv b s) =
      finiteChoiceForwardLoad G x k Q A y q s := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [← (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [FiniteChoiceTraceIndexEquiv.output,FiniteChoiceTraceIndexEquiv.mass G hab x k Q Q' hQ e A A' hA y y' hy q q' hq]
  simp only [(spliceStateEquiv b).injective.eq_iff]

end ChoiceIndexCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceInput
attribute [local instance] Classical.propDecidable Classical.decEq

theorem edgeField_subset_aut_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    edgeFieldEquiv b ω ⊆ (Q' : Set E) ↔ ω ⊆ (Q : Set E) := by
  constructor
  · intro h e he
    exact (hQ e).mpr (h (by simpa using he : b e ∈ edgeFieldEquiv b ω))
  · intro h e he
    have hh := (hQ (b.symm e)).mp (h he)
    simpa only [b.apply_symm_apply,Finset.mem_coe] using hh

theorem finiteSpliceDomain_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (s : SpliceState E) :
    spliceStateEquiv b s ∈ finiteSpliceDomain Q' J ↔ s ∈ finiteSpliceDomain Q J := by
  rw [mem_finiteSpliceDomain_iff,mem_finiteSpliceDomain_iff]
  change (edgeFieldEquiv b s.1 ⊆ (Q':Set E) ∧
    (∀ i,edgeFieldEquiv b (s.2 i) ⊆ (Q':Set E)) ∧ ∀ i ∉ J,edgeFieldEquiv b (s.2 i)=∅) ↔ _
  have hz (η : Set E) : edgeFieldEquiv b η = ∅ ↔ η = ∅ := by
    change edgeFieldEquiv b η = edgeFieldEquiv b ∅ ↔ _
    exact (edgeFieldEquiv b).injective.eq_iff
  simp only [edgeField_subset_aut_iff b Q Q' hQ,hz]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem mass_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.mass (edgeFieldEquiv b ω) (a x) (a y) = q.mass ω x y := by
  simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply] using
    q.covariance a.symm b.symm (isAut_symm G hab) ω (a x) (a y)

theorem amplificationWeight_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B' k (finiteVertexEquiv a B B' hB z) (spliceStateEquiv b s)
      (finiteRunEquiv a B B' hB k r) = q.amplificationWeight B k z s r := by
  apply oldRunWeight_map (finiteVertexEquiv a B B' hB)
  intro i v w
  exact q.mass_aut_map hab (s.2 i) v.val w.val

theorem amplificationInputs_aut_map_iff (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    spliceStateEquiv b s ∈ q.amplificationInputs Q' B' (a x) k n
      (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) ↔
      s ∈ q.amplificationInputs Q B x k n z r := by
  rw [q.mem_amplificationInputs,q.mem_amplificationInputs]
  have hn : (cluster G (edgeFieldEquiv b s.1) (a x)).ncard = (cluster G s.1 x).ncard := by
    rw [cluster_edgeFieldEquiv G hab,← a.image_eq_preimage_symm,Set.ncard_image_of_injective _ a.injective]
  change (spliceStateEquiv b s ∈ finiteSpliceDomain Q' (Finset.Icc 1 k) ∧
    a x ∈ vertexOrbit G o ∧ a z.val ∈ vertexOrbit G o ∧
    n ≤ (cluster G (edgeFieldEquiv b s.1) (a x)).ncard ∧
    (cluster G (edgeFieldEquiv b s.1) (a x)).ncard < 2*n ∧
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) 0 ∈
      cluster G (edgeFieldEquiv b s.1) (a x) ∧ _) ↔ _
  rw [finiteSpliceDomain_aut_map_iff b Q Q' hQ,mem_vertexOrbit_aut_iff G o hab,
    mem_vertexOrbit_aut_iff G o hab,hn,amplificationVertices_aut_map,
    cluster_edgeFieldEquiv G hab,q.amplificationWeight_aut_map hab B B' hB]
  simp only [Set.mem_preimage,Equiv.symm_apply_apply]

end LocalEndpointRule
end AmplificationCovarianceInput

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q' B' (a x) k n (finiteVertexEquiv a B B' hB z) p (edgeFieldEquiv b ω) =
      q.amplificationMarginal Q B x k n z p ω := by
  unfold amplificationMarginal
  rw [restrictFiniteField_aut_map b Q Q' hQ]
  apply finiteRootLoad_aut_map
  intro s
  apply finiteChoiceForwardLoad_aut_map G hab x k Q Q' hQ (finiteRunEquiv a B B' hB k)
  · intro r s
    exact (q.amplificationInputs_aut_map_iff o hab Q Q' hQ B B' hB x k n z r s).symm
  · intro r s i
    exact amplificationVertices_aut_map a B B' hB k z r i
  · intro s r
    exact q.amplificationWeight_aut_map hab B B' hB k z s r

end LocalEndpointRule

theorem mem_incidentSupport_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (e : E) :
    b e ∈ incidentSupport G hloc B' ↔ e ∈ incidentSupport G hloc B := by
  rw [finset_aut_eq_map a B B' hB,incidentSupport_aut G hloc hab]
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem finiteBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) (R : ℕ) :
    y ∈ (finite_reachBall hloc x R).toFinset ↔ a y ∈ (finite_reachBall hloc (a x) R).toFinset := by
  simpa only [Set.Finite.mem_toFinset] using (mem_reachBall_aut_iff G hab x y R).symm

theorem localBondBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (R : ℕ) (e : E) :
    e ∈ incidentSupport G hloc (finite_reachBall hloc x R).toFinset ↔
      b e ∈ incidentSupport G hloc (finite_reachBall hloc (a x) R).toFinset :=
  (mem_incidentSupport_aut_iff G hloc hab _ _ (fun y => finiteBall_aut_iff G hloc hab x y R) e).symm

end AmplificationCovarianceMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationLoad
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

def amplificationRadius (q : LocalEndpointRule G hloc O M L) (k n : ℕ) : ℕ :=
  2*n+k*M+max q.radius M

noncomputable def amplificationBall (_q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset V :=
  (finite_reachBall hloc x (2*n+k*M)).toFinset

noncomputable def amplificationBonds (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset E :=
  incidentSupport G hloc (finite_reachBall hloc x (q.amplificationRadius k n)).toFinset

 

noncomputable def amplifiedMass (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) : ℝ :=
  if hz : z ∈ q.amplificationBall k n x then
    q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω / n
  else 0

theorem amplifiedMass_nonneg (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) : 0 ≤ q.amplifiedMass k n p ω x z := by
  unfold amplifiedMass
  split_ifs
  · exact div_nonneg (q.amplificationMarginal_bounds hL _ _ _ _ _ _ _ _).1 (Nat.cast_nonneg _)
  · exact le_rfl

theorem amplifiedMass_support (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) (h : q.amplifiedMass k n p ω x z ≠ 0) :
    x ∈ O ∧ z ∈ O ∧ Conn G ω x z ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ 2*n+k*M := by
  unfold amplifiedMass at h
  split_ifs at h with hz
  · apply q.amplificationMarginal_physical_support (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω
    · exact incidentSupport_ball_mono G hloc x (Nat.le_add_right (2*n+k*M) (max q.radius M))
    · intro he
      exact h (by rw [he,zero_div])
  · exact (h rfl).elim

theorem amplifiedMass_local (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) :
    q.amplifiedMass k n p ω x z =
      q.amplifiedMass k n p (ω ∩ (q.amplificationBonds k n x : Set E)) x z := by
  unfold amplifiedMass
  split_ifs
  · exact congrArg (fun t : ℝ => t / n) (q.amplificationMarginal_local _ _ _ _ _ _ _ _)
  · rfl

theorem amplifiedMass_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) :
    q.amplifiedMass k n p (edgeFieldEquiv b ω) (a x) (a z) = q.amplifiedMass k n p ω x z := by
  have hB (y : V) : y ∈ q.amplificationBall k n x ↔ a y ∈ q.amplificationBall k n (a x) :=
    finiteBall_aut_iff G hloc hab x y (2*n+k*M)
  have hQ (e : E) : e ∈ q.amplificationBonds k n x ↔ b e ∈ q.amplificationBonds k n (a x) :=
    localBondBall_aut_iff G hloc hab x (q.amplificationRadius k n) e
  unfold amplifiedMass
  by_cases hz : z ∈ q.amplificationBall k n x
  · simp only [dite_eq_left hz,dite_eq_left ((hB z).mp hz)]
    exact congrArg (fun t : ℝ => t / n)
      (q.amplificationMarginal_aut_map o hab _ _ hQ _ _ hB x k n ⟨z,hz⟩ p ω)
  · simp only [dite_eq_right hz,dite_eq_right (mt (hB z).mpr hz)]

 

noncomputable def amplificationLoad (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) :
    CappedLocalLoad G hloc (vertexOrbit G o) (2*n+k*M) where
  mass := q.amplifiedMass k n p
  radius := q.amplificationRadius k n
  nonneg := q.amplifiedMass_nonneg hL k n p
  support := q.amplifiedMass_support k n p
  locality := q.amplifiedMass_local k n p
  covariance := by
    intro a b hab ω x z
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply,Equiv.symm_symm] using
      q.amplifiedMass_aut_map o (isAut_symm G hab) k n p ω (a x) (a z)

end LocalEndpointRule
end CanonicalAmplificationLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def kernel (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

end CappedLocalLoad


end AmplificationLoadOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Connections
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterWindow (G : BondGraph V E) (x : V) (lo hi : ℕ) (ω : Set E) : Prop :=
  (cluster G ω x).Finite ∧ lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi

noncomputable def clusterWindowProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : ℝ := (law p).real {ω | ClusterWindow G x lo hi ω}

end ClusterWindowLaw
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def cappedConnectionMass (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : ℝ :=
  if CappedGoodness G ω x M L ∧ Conn G ω x y then c*S x y/twoPoint G p x y else 0

theorem cappedConnectionMass_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c) (hS : ∀ x y, 0 ≤ S x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : 0 ≤ cappedConnectionMass G p S c M L ω x y := by
  unfold cappedConnectionMass
  split_ifs
  · exact div_nonneg (mul_nonneg hc (hS x y)) (twoPoint_nonneg G p x y)
  · rfl

theorem cappedConnectionMass_support (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V)
    (h : cappedConnectionMass G p S c M L ω x y ≠ 0) :
    S x y ≠ 0 ∧ CappedGoodness G ω x M L ∧ Conn G ω x y := by
  unfold cappedConnectionMass at h
  split_ifs at h with hh
  · refine ⟨?_,hh⟩
    intro hz
    simp only [hz,mul_zero,zero_div] at h
    exact h rfl
  · exact (h rfl).elim

theorem cappedConnectionMass_le (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : cappedConnectionMass G p S c M L ω x y ≤ S x y := by
  by_cases hs : S x y = 0
  · simp only [cappedConnectionMass,hs,mul_zero,zero_div,ite_self,le_refl]
  · unfold cappedConnectionMass
    split_ifs
    · apply (div_le_iff₀ (hc.trans_le (hτ x y hs))).mpr
      exact (mul_le_mul_of_nonneg_right (hτ x y hs) (hS x y)).trans_eq (mul_comm _ _)
    · exact hS x y

theorem cappedConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  change cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y
  have hg := cappedGoodness_local G hloc ω x M L
  change CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q:Set E)) x M L at hg
  unfold cappedConnectionMass
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h,hxy⟩
    have h' := hg.mp h
    have he := cluster_restrict_of_cap G hloc Q ω x M (Finset.Subset.refl _) h'.1 h'.2.1
    refine ⟨h',?_⟩
    change y ∈ cluster G (ω ∩ (Q:Set E)) x
    rw [he]
    exact hxy
  · rintro ⟨h,hxy⟩
    exact ⟨hg.mpr h,conn_mono G Set.inter_subset_left hxy⟩

theorem cappedConnectionMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b)
    (hS : ∀ x y, S (a x) (a y) = S x y) (ω : Set E) (x y : V) :
    cappedConnectionMass G p S c M L (b ⁻¹' ω) x y = cappedConnectionMass G p S c M L ω (a x) (a y) := by
  simp only [cappedConnectionMass,cappedGoodness_aut_iff G hab,conn_aut_iff G hab,
    hS,twoPoint_aut G p hab]

noncomputable def connectionAdjustedRule [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ O ∧ y ∈ O)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L : ℝ) : LocalEndpointRule G hloc O M L where
  mass := cappedConnectionMass G p S c M L
  radius := M
  nonneg := cappedConnectionMass_nonneg G p S c hc.le hS M L
  support := by
    intro ω x y h
    obtain ⟨hs,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y h
    exact ⟨(hO x y hs).1,(hO x y hs).2,hxy,hg⟩
  locality := fun ω x y => cappedConnectionMass_local G hloc p S c M L ω x y
  covariance := fun a b hab ω x y => cappedConnectionMass_covariant G p S c M L a b hab (hcov a b hab) ω x y
  row_le_one := by
    intro ω x
    have hs : Summable (cappedConnectionMass G p S c M L ω x) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
      intro y hy
      by_contra hn
      obtain ⟨_,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y hn
      apply hy
      simp only [Set.Finite.mem_toFinset]
      exact finite_cluster_subset_reachBall G ω x hg.1 M hg.2.1 hxy
    exact (hs.tsum_le_tsum (cappedConnectionMass_le G p S c hc hS hτ M L ω x) (hSsum x)).trans (hrow x)

end ConnectionAdjustedRule

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinOrbitRowMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binSizeMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, binConnectionMass G n ω x y

noncomputable def binOrbitRowMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, if y ∈ vertexOrbit G x then binConnectionMass G n ω x y else 0

end BinOrbitRowMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitTransportMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  binConnectionMass G n ω x y * binOrbitRowMass G n ω y / binSizeMass G n ω x

end BinOrbitTransport

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ScaleBudget
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedBinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitTransport (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binOrbitTransportMass G n ω x y ∂law p

end AveragedBinOrbitTransport

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitDyadicScales
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def weightedWindowProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (a b : ℕ) : ℝ :=
  ∑ i, weight i * clusterWindowProbability G p (root i) a b

noncomputable def dyadicBinProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (j : ℕ) : ℝ :=
  weightedWindowProbability G p root weight (2^j) (2^(j+1))



end OrbitDyadicScales

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfile

 

structure EndpointProfile (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (s : ℝ) where
  cap : ℕ
  rule : LocalEndpointRule G hloc (vertexOrbit G o) cap ((cap:ℝ)^s)
  success_pos : 0 < rule.successProbability p o
  op : Hilbert V →L[ℂ] Hilbert V
  norm_pos : 0 < ‖op‖
  coeff : ∀ x y, matrixCoeff op x y = (rule.normalizedKernel o p x y : ℂ)

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

noncomputable def U (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/q.rule.successProbability p o)
noncomputable def m (q : EndpointProfile G hloc p o s) : ℝ := Real.log q.cap
noncomputable def H (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/‖q.op‖)
noncomputable def cost (q : EndpointProfile G hloc p o s) (ξ : ℝ) : ℝ := q.U+(s+ξ)*q.m

end EndpointProfile

end EndpointProfile

end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_Resampling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryPivotal
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ShortClosedBoundary (G : BondGraph V E) (ω : Set E) (x z : V) (M : ℕ) (e : E) : Prop :=
  e ∉ ω ∧ ¬Conn G ω x z ∧ ∃ a b : V, ∃ l : List E,
    G e = s(a,b) ∧ Along G x l a ∧ (∀ f ∈ l, f ∈ ω) ∧ l.length < M ∧ Conn G ω b z

end ShortBoundaryPivotal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryCounting
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def firstOpenBridgeCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M)).card

noncomputable def shortClosedBoundaryCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (ShortClosedBoundary G ω x z M)).card

end ShortBoundaryCounting

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClusterResampling
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def resampleClusterAt (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) : Finset E :=
  exteriorBonds G ω W ∪ (η ∩ (Q \ exteriorBonds G Q W))



end ClusterResampling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ResampledBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def resampleRootCluster (G : BondGraph V E) (Q : Finset E)
    (z : V) (ω η : Finset E) : Finset E :=
  resampleClusterAt G Q (cluster G ω z) ω η


end ResampledBoundary
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedSelectorBound
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def restrictedSusceptibility (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : ℝ :=
  ∑' y, (law p).real {ω | Conn G (ω ∩ S) x y}

end RestrictedSelectorBound
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq

 
def intrinsicBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) : Set V :=
  {y | ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ ω}

theorem mem_intrinsicBall_self (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    x ∈ intrinsicBall G ω x M := ⟨[],.nil x,Nat.zero_le _,by simp⟩

theorem intrinsicBall_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ reachBall G x M := by
  rintro y ⟨l,hl,hlen,_⟩
  exact reachBall_mono G x hlen hl.mem_reachBall

end IntrinsicBall
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_exists_max (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    ∃ z ∈ intrinsicBall G ω x M, ∀ y ∈ intrinsicBall G ω x M, f y ≤ f z :=
  Set.exists_max_image _ f ((finite_reachBall hloc x M).subset
    (intrinsicBall_subset_reachBall G ω x M)) ⟨x,mem_intrinsicBall_self G ω x M⟩

noncomputable def intrinsicMaximizer (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) : V :=
  Classical.choose (intrinsicBall_exists_max G hloc ω x M f)

noncomputable def intrinsicPotentialMax (G : BondGraph V E) (ω : Set E)
    (x : V) (M : ℕ) (f : V → ℝ) : ℝ := sSup (f '' intrinsicBall G ω x M)

noncomputable def intrinsicBondSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) : Finset E :=
  (incidentSupport G hloc (finite_reachBall hloc x M).toFinset).filter (· ∈ S)

end IntrinsicMaximum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def inducedSusceptibility (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : ℝ :=
  if x ∈ D then restrictedSusceptibility G (internalEdges G D) p x else 0

end MaximalSusceptibility
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletedDomainPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) : ℝ :=
  ∑ a ∈ ((finite_reachBall hloc x M).toFinset.filter (· ∉ D)),
    ∑ b ∈ neighbors G hloc a, inducedSusceptibility G D p b

noncomputable def deletedLocalPotential (G : BondGraph V E) (D : Set V) (p : unitInterval)
    (ω : Set E) (x : V) (M : ℕ) : ℝ :=
  if x ∈ D then intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) else 0

end DeletedDomainPotential
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointDifference
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)

noncomputable def kernelDifference (p r : unitInterval) (x y : V) : ℝ :=
  |q.normalizedKernel o p x y - q.normalizedKernel o r x y|
noncomputable def differenceRow (p r : unitInterval) : ℝ := ∑' y, q.kernelDifference o p r o y

end LocalEndpointRule
end EndpointDifference
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def clusterMass (G : BondGraph V E) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if Conn G ω x y then 1 else 0

end ClusterMassMoments
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinClusterSlice
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binClusterSlice (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if h : ClusterWindow G x n (2*n) ω then h.1.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

end BinClusterSlice
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinDiagonalClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitClass (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if x ∈ vertexOrbit G o then binClusterSlice G o n ω x else ∅

end BinDiagonalClass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalMass (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) : ℝ :=
  finiteClassTransport (binOrbitClass G o n ω) (fun x => binSizeMass G n ω x ^ 2) K x y

end BinDiagonalTransport
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_ExteriorMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalKernel (G : BondGraph V E) (p : unitInterval)
    (o : V) (n : ℕ) (K : V → V → ℝ) (x y : V) : ℝ :=
  ∫ ω, binDiagonalMass G o n K ω x y ∂law p

end BinDiagonalLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicDiagonalStrata
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullOrbitClass (G : BondGraph V E) (o : V) (ω : Set E) (x : V) : Finset V :=
  if h : (cluster G ω x).Finite then h.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

noncomputable def diagonalLossMass (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (ω : Set E) (x : V) : ℝ :=
  ((cluster G ω x).ncard:ℝ)^2 * ∑ z ∈ fullOrbitClass G o ω x, K x z

end DyadicDiagonalStrata
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalSeries
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def diagonalLossTerm (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x y : V) (ω : Set E) : ℝ :=
  if y ∈ vertexOrbit G o ∧ Conn G ω x y then K x y*((cluster G ω x).ncard:ℝ)^2 else 0

end DiagonalSeries
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def freshExteriorMoment (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ :=
  ((cluster G ω x).ncard:ℝ) * inducedSusceptibility G (cluster G ω x)ᶜ p y

end FreshExteriorMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def distinctClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) ∂law p

noncomputable def neighborClusterMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : ℝ :=
  ∑ y ∈ neighbors G hloc x, distinctClusterMoment G p x y

noncomputable def rootNeighborMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * neighborClusterMoment G hloc p (root i)

end DistinctClusterMoments
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_DistinctMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedBoundaryPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exposedVertexPotential (G : BondGraph V E) (p : unitInterval)
    (x a b : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then freshExteriorMoment G p a b ω else 0

end ExposedBoundaryPotential
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectedMomentLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def connectedClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) ∂law p

end ConnectedMomentLoss
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section MapScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

noncomputable def potentialScale (q : EndpointProfile G hloc p₀ o s) (p : unitInterval) : ℝ :=
  (q.rule.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*q.cap)

noncomputable def geometricScale (q : EndpointProfile G hloc p₀ o s) : ℝ := 2*q.potentialScale p₀

end EndpointProfile
end MapScaleBudget
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Susceptibility
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

def orientedPivotalEvent (G : BondGraph V E) (x y a b : V) : Set (Set E) :=
  {ω | Conn G ω x a ∧ Conn G ω b y ∧ ¬ Conn G ω a b}

end OrientedPivotalConnections
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def pivotalTransportMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : ℝ :=
  ∑ b ∈ neighbors G hloc a, ∑' y, (law p).real (orientedPivotalEvent G x y a b)

end PivotalTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section FiniteRootPivotalApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteRootPivotalMass (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (Q : Finset E) (F : Finset V) : ℝ :=
  ∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))

end FiniteRootPivotalApproximation
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_FractionalMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededEdgeSearch
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seededEdgeSearch (G : BondGraph V E) (x : V) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, R => .done (decide (x ∈ R))
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .query t.1 (seededEdgeSearch G x n (Q.erase t.1) R)
        (seededEdgeSearch G x n (Q.erase t.1) (insert t.2.2 R))
    else .done (decide (x ∈ R))

end SeededEdgeSearch
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RandomizedDecisionCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSeedProbability (G : BondGraph V E) (F : Finset V)
    (ω : Finset E) (x : V) (h : ℝ) : ℝ :=
  bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h

end RandomizedDecisionCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterTailIndicator (G : BondGraph V E) (x : V) (n : ℕ)
    (ω : Finset E) : ℝ := if n ≤ (finiteRootComponent G ω x).card then 1 else 0

noncomputable def finiteClusterTail (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (finiteClusterTailIndicator G x n) p

end ClusterTailCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Exploration_TailBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceExploration
attribute [local instance] Classical.propDecidable Classical.decEq

 

def IncidencePending (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ G t.1 = s(t.2.1,t.2.2)

noncomputable def incidencePick (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : IncidencePending G Q R) : E × V × V := Classical.choose h

noncomputable def incidenceSearch (G : BondGraph V E) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : IncidencePending G Q R then
      let t := incidencePick G Q R hc
      .query t.1 (incidenceSearch G n (Q.erase t.1) R)
        (incidenceSearch G n (Q.erase t.1) (insert t.2.2 R))
    else .done false



structure IncidenceInvariant (G : BondGraph V E) (Q ω : Finset E) (R C : Finset V) : Prop where
  discovered : R ⊆ C
  closed : ∀ a ∈ C, ∀ e ∈ ω, ∀ b, G e = s(a,b) → b ∈ C
  reachable : ∀ y ∈ C, ∃ r ∈ R, Conn G ((ω ∩ Q : Finset E):Set E) r y

end IncidenceExploration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorExplorationLaw
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def exteriorSearchScore (G : BondGraph V E) (n : ℕ) (Q : Finset E)
    (x v : V) (p : ℝ) (ω : Finset E) : ℝ :=
  let W := finiteRootComponent G ω x
  if v ∈ W then 0 else
    (incidenceSearch G n (exteriorBonds G Q (W:Set V)) {v}).score p (exteriorBonds G ω (W:Set V))

end ExteriorExplorationLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClosedClusterContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def contactBonds (G : BondGraph V E) (Q : Finset E) (A B : Finset V) : Finset E :=
  Q.filter (fun e => ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b))

end ClosedClusterContacts
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_LargeContacts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactBinFirstMoment
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterContactBin (G : BondGraph V E) (Q : Finset E)
    (x v : V) (n m : ℕ) (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x v ∧
    n ≤ min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ∧
    min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m
  then (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card else 0



end ContactBinFirstMoment
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def fullContactBin (G : BondGraph V E) (x v : V) (n m : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ n ≤ min (cluster G ω x).ncard (cluster G ω v).ncard ∧
    min (cluster G ω x).ncard (cluster G ω v).ncard ≤ m
  then clusterContactCount G ω x v else 0

end InfiniteContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterAveragingKernel (G : BondGraph V E) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Conn G ω x y then ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ else 0

end ClusterAveraging
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PositiveClusterPairs
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairKernel (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b then J a b else 0

 

noncomputable def clusterPairDensity (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
    ∑' y, ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ * (if ¬Conn G ω x y then F x y else 0)

noncomputable def clusterPairFunctional (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F : Set E → V → V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, clusterPairDensity G ω (F ω) (root i) ∂law p

end PositiveClusterPairs
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairReversal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMass (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ * ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
    (if ¬Conn G ω x y then F x y else 0)

end PairReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_ContactTrace
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section IndexedEdgeKernel
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def indexedEdgeKernel (G : BondGraph V E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if G e = s(x,y) then 1 else 0

end IndexedEdgeKernel
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLarge (G : BondGraph V E) (L : ℕ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min (cluster G ω x).ncard (cluster G ω y).ncard then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

end ContactSquareTrace
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactRealCutoff
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLargeReal (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

end ContactRealCutoff
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteClusterKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWeight (G : BondGraph V E) (f : V → ℝ)
    (x : V) (ω : Finset E) : ℝ := ∑ y ∈ finiteRootComponent G ω x, f y

noncomputable def finitePairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (ω : Finset E) (x y : V) : ℝ :=
  ∑ a ∈ finiteRootComponent G ω x, finiteClusterWeight G (J a) y ω

end FiniteClusterKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallFinitePairKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSmallPairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (L : ℝ) (x y : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L ∧ ¬Conn G (ω:Set E) x y then finitePairKernel G J ω x y else 0

noncomputable def finiteSmallClusterSize (G : BondGraph V E) (L : ℝ) (x : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L then (finiteRootComponent G ω x).card else 0


end SmallFinitePairKernel
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def smallPairKernel (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (x y : V) (ω : Set E) : ℝ≥0∞ :=
  if ((cluster G ω x).ncard:ℝ) < L ∧ ¬Conn G ω x y then clusterPairKernel G ω J x y else 0

end SmallKernelLimit
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairMeasure
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMeasure [MeasurableSpace V]
    {ι : Type*} [MeasurableSpace ι] (G : BondGraph V E) (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ) : Measure (Set E × (ι × V)) :=
  ((law p).prod Measure.count).withDensity (fun t => ENNReal.ofReal (weight t.2.1) *
    clusterPairMass G t.1 (fun _ _ => 1) (root t.2.1) t.2.2)

end PairMeasure
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_RussoRows
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section LargeContactCauchySchwarz
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def largeContactKernel (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    clusterPairKernel G ω (indexedEdgeKernel G) x y else 0

end LargeContactCauchySchwarz
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionRussoContacts
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClosedContact (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x y then
    (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω y)).card else 0

end ConnectionRussoContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactError
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterSupportIn (G : BondGraph V E) (Q : Finset E) (ω : Set E) (x : V) : Prop :=
  ∀ a, Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q

noncomputable def contactApproxError (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (x y : V) (ω : Set E) : ℝ :=
  if ClusterSupportIn G Q ω x ∧ ClusterSupportIn G Q ω y then 0
  else (d:ℝ)*(cluster G ω x).ncard

end UniformContactError
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoDiagram (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, indexedEdgeKernel G a b *
    (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b})

end RussoDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoMajorant
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoSlope (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  realContactExpectation G x y t / (1-t)

noncomputable def russoMajorant (G : BondGraph V E) (b : unitInterval) (x y : V) : ℝ :=
  (russoDiagram G b x y).toReal / (1-(b:ℝ))

end RussoMajorant
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RealTriangle
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangleTerm (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t

noncomputable def realTriangleSlope (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  russoSlope G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * russoSlope G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * russoSlope G ab.2 x t

noncomputable def triangleMajorant (G : BondGraph V E) (b : unitInterval) (x : V) (ab : V×V) : ℝ :=
  russoMajorant G b x ab.1 * twoPoint G b ab.1 ab.2 +
  twoPoint G b x ab.1 * russoMajorant G b ab.1 ab.2 +
  russoMajorant G b x ab.2 * twoPoint G b ab.2 ab.1

end RealTriangle
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TriangleDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangle (G : BondGraph V E) (x : V) (t : ℝ) : ℝ :=
  ∑' ab, realTriangleTerm G x ab t

noncomputable def rootTriangle (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * realTriangle G (root i) t

end TriangleDerivative
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_TraceBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TraceSquareRoot
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rootTriangleSqrt (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ := Real.sqrt (rootTriangle G root weight t)

end TraceSquareRoot
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def maxSusceptibility (G : BondGraph V E) (p : unitInterval) : ℝ :=
  sSup (Set.range (susceptibility G p))

end NormRatio
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorMonotonicity
attribute [local instance] Classical.propDecidable Classical.decEq

 

def corridorCounted (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) : Prop :=
  Conn G (ω ∩ internalEdges G D) x y ∧
    (∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y) ∧
    Disjoint blockers (ω ∩ internalEdges G D)

end CorridorMonotonicity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq


abbrev RawCorridor (G : BondGraph V E) (k : ℕ) :=
  Σ x y : V, HoldingWalk (openSimpleGraph G Set.univ) k x y

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def base (w : RawCorridor G k) : V := w.1
def endpoint (w : RawCorridor G k) : V := w.2.1
noncomputable def path (w : RawCorridor G k) :
    (openSimpleGraph G Set.univ).Walk w.base w.endpoint := w.2.2.erase
noncomputable def interior (w : RawCorridor G k) : Finset V :=
  w.path.support.toFinset \ {w.base,w.endpoint}
def retained (w : RawCorridor G k) : Set E := {e | G e ∈ w.path.edges}
noncomputable def blockers (w : RawCorridor G k) : Set E :=
  {e | ∃ z ∈ w.interior, z ∈ G e} \ w.retained
noncomputable def probability (P : V → V → ℝ) (w : RawCorridor G k) : ℝ := w.2.2.mass P
noncomputable def weight (P : V → V → ℝ) (p : ℝ) (w : RawCorridor G k) : ℝ :=
  w.probability P * (p^w.path.length)⁻¹ * ((1-p)^w.blockers.ncard)⁻¹

theorem retained_finite (hG : Function.Injective G) (w : RawCorridor G k) : w.retained.Finite :=
  (List.finite_toSet w.path.edges).preimage hG.injOn

theorem blockers_finite (hloc : LocallyFinite G) (w : RawCorridor G k) : w.blockers.Finite := by
  apply Set.Finite.subset (s := (incidentSupport G hloc w.interior : Set E)) (Finset.finite_toSet _)
  intro e he
  exact (mem_incidentSupport G hloc w.interior e).mpr he.1

end RawCorridor
end LiteralCorridors
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PublishedConsequences
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

structure PublishedSimpleGraph (G : BondGraph V E) : Prop where
  injective : Function.Injective G
  loopless : ∀ e x, G e ≠ s(x, x)
  connected : Connected G
  locallyFinite : LocallyFinite G
  quasiTransitive : QuasiTransitive G

noncomputable def criticalFiniteTail (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V) (n : ℕ) : ℝ :=
  (law (pc G) {ω | ω ∈ A x n ∧ (cluster G ω x).Finite}).toReal

def HutchcroftCriticalVolumeInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    PowerTail (criticalFiniteTail G (volumeEvent G) x) (1 / 2)

def HutchcroftCriticalRadiiInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    PowerTail (criticalFiniteTail G (intrinsicRadiusEvent G) x) 1 ∧
    PowerTail (criticalFiniteTail G (extrinsicRadiusEvent G) x) 1

def HutchcroftFirstMomentInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ p : unitInterval, p < pc G → (pc G : ℝ) - p < δ →
        c / ((pc G : ℝ) - p) ≤ ∫ ω, ((cluster G ω x).ncard : ℝ) ∂law p ∧
        (∫ ω, ((cluster G ω x).ncard : ℝ) ∂law p) ≤ C / ((pc G : ℝ) - p)

def TrianglePercolationProbabilityInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → (∀ x, triangleDiagram G (pc G) x < ⊤) →
    PercolationProbabilityLaw G

end BenjaminiSchramm
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Corridors
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def calibrationEvent (w : RawCorridor G k) : Set (Set E) :=
  {ω | w.retained ⊆ ω ∧ Disjoint w.blockers ω}

end RawCorridor
end ExactCorridorPattern
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorContraction
attribute [local instance] Classical.propDecidable Classical.decEq



namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exterior (w : RawCorridor G k) (ω : Set E) : Set E :=
  ω ∩ internalEdges G (w.interior : Set V)ᶜ

def attachment (w : RawCorridor G k) (ω : Set E) : Set V :=
  {z | z ∈ w.path.support ∨ Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z}

end RawCorridor
end CorridorContraction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CorridorBKCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exteriorOrientations (w : RawCorridor G k) (x y : V) : Set (Set E) :=
  orientedPivotalEvent G x y w.base w.endpoint ∪ orientedPivotalEvent G x y w.endpoint w.base

end RawCorridor
end CorridorBKCalibration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSum
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

def counted (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) : Prop :=
  3 ≤ w.path.length ∧ (∀ z ∈ w.path.support, z ∈ D) ∧
    corridorCounted G w.retained w.blockers D ω x y

end RawCorridor

end CorridorSum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualCorridorPenalty
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def corridorPenaltyTerm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    {k : ℕ} (D : Set V) (ω : Set E) (x y : V) (w : RawCorridor G k) : ℝ :=
  if w.counted D ω x y then w.weight P p else 0

noncomputable def corridorPenalty (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  ∑' w : RawCorridor G k, corridorPenaltyTerm G P p D ω x y w

end ActualCorridorPenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def deformedConnection (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then
    Real.exp (-t * corridorPenalty G P p k D ω x y) else 0

noncomputable def deformedKernel (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : ℝ :=
  ∫ ω, deformedConnection G P p k t D ω x y ∂law p

end ActualWeightedConnections
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_ClusterProducts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedBondNeighborhood (G : BondGraph V E) (A : Set V) : Set V :=
  {z | z ∈ A ∨ ∃ e, z ∈ G e ∧ ∃ a ∈ G e, a ∈ A}

def SimpleVisit (G : BondGraph V E) (S : Set E) (A : Set V) (x y : V) : Prop :=
  ∃ q : (openSimpleGraph G S).Walk x y, q.IsPath ∧ ∃ z ∈ q.support, z ∈ A

end DeletionGeometry
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) : ℝ :=
  ∑' y, deformedKernel G P p k t D x y

end DeformedSusceptibility
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, deformedConnection G P p k t D ω x y

end ExteriorWeightedConnections
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactComponentRestriction
attribute [local instance] Classical.propDecidable Classical.decEq

 
def OpenClosed (G : BondGraph V E) (ω : Set E) (A : Set V) : Prop :=
  ∀ e ∈ ω, ∀ z ∈ G e, z ∈ A → ∀ a ∈ G e, a ∈ A

end ExactComponentRestriction
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedFreshExteriorMoment (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) (ω : Set E) : ℝ :=
  deformedClusterMass G P p k t D ω x *
    deformedSusceptibility G P p k t (D \ cluster G (ω ∩ internalEdges G D) x) y

end FreshWeightedMass
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Derivatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizeWeightedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def sizeMembership (G : BondGraph V E) (x a : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0

noncomputable def sizeWeightedConnectionPotential (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ := ∑' a, sizeMembership G x a ω * twoPoint G p y a

end SizeWeightedPotential
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LiteralDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedDerivativeMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y

end LiteralDeformationDerivative
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_Calibration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorLegObservable
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exteriorLegProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) : ℝ :=
  if ¬Conn G (w.exterior ω) w.base w.endpoint then
    deformedConnection G P p k t (w.interior : Set V)ᶜ ω x w.base *
      deformedConnection G P p k t (w.interior : Set V)ᶜ ω w.endpoint y else 0

end ExteriorLegObservable
end Percolation


namespace Percolation
universe u u' u'' v
section GraphAutWalks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {E : Type v}

theorem openSimpleGraph_univ_adj (G : BondGraph V E) (x y : V) :
    (openSimpleGraph G Set.univ).Adj x y ↔ x ≠ y ∧ Adj G x y := by
  simp only [openSimpleGraph,Adj,Set.mem_univ,true_and]

def autSimpleGraph (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) :
    openSimpleGraph G Set.univ ≃g openSimpleGraph G Set.univ where
  toEquiv := a
  map_rel_iff' := by
    intro x y
    simp only [openSimpleGraph_univ_adj,a.injective.ne_iff]
    exact and_congr_right (fun _ => ⟨fun h => by simpa using adj_aut G (isAut_symm G hab) h,
      adj_aut G hab⟩)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
def autEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) : RawCorridor G k ≃ RawCorridor G k :=
  rawWalkEquiv (autSimpleGraph G hab) k

end RawCorridor
end GraphAutWalks
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Deformation_AveragedDecrease
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def corridorDerivativeContribution (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) : ℝ :=
  ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
    deformedConnection G P p k t Set.univ ω x y ∂law p

end DeformationCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DerivativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def derivativeTransportMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (x u : V) : ℝ :=
  ∑' w : RawFrom (openSimpleGraph G Set.univ) k u,
    ∑' y, corridorDerivativeContribution G P p t ⟨u,w⟩ x y

end DerivativeTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedDerivative
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]



noncomputable def averagedDeformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * deformedSusceptibility G P p k t Set.univ (root i)

end AveragedDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathAverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

noncomputable def rawPathAverage (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (f : RawCorridor G k → ℝ) : ℝ :=
  ∑ i, weight i * ∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i),
    w.2.mass P * f ⟨root i,w⟩

noncomputable def retainedSusceptibilityProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) : ℝ :=
  if 3 ≤ w.path.length then
    deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.base *
      deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.endpoint
  else 0

end PathAverage
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 
def segmentOrbit (G : BondGraph V E) (γ : I → V) : Set (I → V) :=
  {s | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ s = a ∘ γ}

omit [Fintype I] in
theorem segmentOrbit_aut_iff (G : BondGraph V E) (γ s : I → V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    a ∘ s ∈ segmentOrbit G γ ↔ s ∈ segmentOrbit G γ := by
  constructor
  · rintro ⟨c,d,hcd,he⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G h),?_⟩
    funext i
    have hh := congrFun he i
    simpa only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using congrArg a.symm hh
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd h,rfl⟩

theorem finite_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    {s ∈ segmentOrbit G γ | s i = x}.Finite := by
  apply (Set.Finite.pi' (fun _ : I => finite_reachBall hloc x n)).subset
  rintro s ⟨⟨a,b,hab,rfl⟩,hx⟩ j
  have hh := mem_reachBall_aut G hab (hdiam i j)
  change a (γ i) = x at hx
  simpa only [hx,Function.comp_apply] using hh

noncomputable def segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) : Finset (I → V) :=
  (finite_segmentAnchors G hloc γ n hdiam i x).toFinset

theorem mem_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) (s : I → V) :
    s ∈ segmentAnchors G hloc γ n hdiam i x ↔ s ∈ segmentOrbit G γ ∧ s i = x := by
  exact Set.Finite.mem_toFinset _

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]



noncomputable def anchoredPositionKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) : ℝ :=
  ∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
    if y = s j then ((segmentAnchors G hloc γ n hdiam i x).card : ℝ)⁻¹ else 0

end AnchoredPositionKernels
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_Labels
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledEscapeExperiment

 

structure EscapeLabel (G : BondGraph V E) (γ : I → V) (endpoint negative : I) (L m : ℕ) where
  first : I → V
  first_mem : first ∈ segmentOrbit G γ
  last : I → V
  last_mem : last ∈ segmentOrbit G γ
  middle : HoldingWalk (openSimpleGraph G Set.univ) L (first endpoint) (last endpoint)
  leftTail : RawFrom (openSimpleGraph G Set.univ) m (first negative)
  rightTail : RawFrom (openSimpleGraph G Set.univ) m (last negative)

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def reverse (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := ξ.last
  first_mem := ξ.last_mem
  last := ξ.first
  last_mem := ξ.first_mem
  middle := ξ.middle.reverse
  leftTail := ξ.rightTail
  rightTail := ξ.leftTail

theorem reverse_reverse (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.reverse = ξ := by
  cases ξ
  simp only [reverse,HoldingWalk.reverse_reverse]

noncomputable def mass (P : V → V → ℝ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.middle.mass P * ξ.leftTail.2.mass P * ξ.rightTail.2.mass P



def reverseRootedEquiv (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = y ∧ ξ.last center = x} where
  toFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  invFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  left_inv ξ := Subtype.ext (reverse_reverse ξ.1)
  right_inv ξ := Subtype.ext (reverse_reverse ξ.1)

end EscapeLabel
end LabeledEscapeExperiment
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def RootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) : Type (max u w) :=
  Σ s : (segmentAnchors G hloc γ n hdiam center x),
    Σ mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
      Σ h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg)

noncomputable def labelFromCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  have hsm := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).1
  have hsx := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).2
  have hhm := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).1
  have hhz := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).2
  subst z
  exact ⟨⟨s,hsm,h,hhm,mid,α,β⟩,hsx⟩

noncomputable def labelToCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}) :
    RootedLabelCode G hloc γ n hdiam center ep neg L m x :=
  ⟨⟨ξ.1.first,(mem_segmentAnchors G hloc γ n hdiam center x ξ.1.first).mpr ⟨ξ.1.first_mem,ξ.2⟩⟩,
    ⟨ξ.1.last ep,ξ.1.middle⟩,
    ⟨ξ.1.last,(mem_segmentAnchors G hloc γ n hdiam ep (ξ.1.last ep) ξ.1.last).mpr ⟨ξ.1.last_mem,rfl⟩⟩,
    ξ.1.leftTail,ξ.1.rightTail⟩

noncomputable def rootedLabelEquiv (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} ≃
      RootedLabelCode G hloc γ n hdiam center ep neg L m x where
  toFun := labelToCode G hloc γ n hdiam center ep neg L m x
  invFun := labelFromCode G hloc γ n hdiam center ep neg L m x
  left_inv ξ := by
    cases ξ with
    | mk ξ hξ => cases ξ; rfl
  right_inv c := by
    rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
    have hh' := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
    obtain ⟨hhm,hhz⟩ := hh'
    subst z
    rfl

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def segmentReturnMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V) : ℝ :=
  ∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
    if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0

end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]



noncomputable def escapeLabelProbability (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.mass (walkKernel G hloc a) /
    (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep))

end LabeledNormalization
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def autMap {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := a ∘ ξ.first
  first_mem := (segmentOrbit_aut_iff G γ ξ.first hab).mpr ξ.first_mem
  last := a ∘ ξ.last
  last_mem := (segmentOrbit_aut_iff G γ ξ.last hab).mpr ξ.last_mem
  middle := ξ.middle.map (autSimpleGraph G hab).toHom
  leftTail := ⟨a ξ.leftTail.1,ξ.leftTail.2.map (autSimpleGraph G hab).toHom⟩
  rightTail := ⟨a ξ.rightTail.1,ξ.rightTail.2.map (autSimpleGraph G hab).toHom⟩

theorem autMap_trans {a c : V ≃ V} {b d : E ≃ E} (hab : IsAut G a b) (hcd : IsAut G c d)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap hcd (autMap hab ξ) = autMap (isAut_trans G hab hcd) ξ := by
  cases ξ
  dsimp only [autMap,autSimpleGraph]
  simp only [HoldingWalk.map_map]
  rfl

theorem autMap_refl (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_refl G) ξ = ξ := by
  cases ξ with
  | mk f hf l hl mid α β =>
    change EscapeLabel.mk f hf l hl (mid.map SimpleGraph.Hom.id)
      ⟨α.1,α.2.map SimpleGraph.Hom.id⟩ ⟨β.1,β.2.map SimpleGraph.Hom.id⟩ = _
    simp only [HoldingWalk.map_id]

theorem autMap_symm {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_symm G hab) (autMap hab ξ) = ξ := by
  rw [autMap_trans]
  have ha : a.trans a.symm = Equiv.refl V := by ext x; exact a.symm_apply_apply x
  have hb : b.trans b.symm = Equiv.refl E := by ext x; exact b.symm_apply_apply x
  generalize hp : isAut_trans G hab (isAut_symm G hab) = h
  clear hp
  revert h
  rw [ha,hb]
  intro h
  exact autMap_refl ξ

end EscapeLabel
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def labelEndpointEquiv (center : I) (x : V) :
    (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) ≃
      {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} where
  toFun ξ := ⟨ξ.2.1,ξ.2.2.1⟩
  invFun ξ := ⟨ξ.1.last center,ξ.1,ξ.2,rfl⟩
  left_inv ξ := by rcases ξ with ⟨y,ξ,hx,hy⟩; subst y; rfl
  right_inv ξ := rfl

def labelAutPairEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = a x ∧ ξ.last center = a y} where
  toFun ξ := ⟨EscapeLabel.autMap hab ξ.1,congrArg a ξ.2.1,congrArg a ξ.2.2⟩
  invFun ξ := ⟨EscapeLabel.autMap (isAut_symm G hab) ξ.1,by
    change a.symm (ξ.1.first center) = x ∧ a.symm (ξ.1.last center) = y
    rw [ξ.2.1,ξ.2.2,a.symm_apply_apply,a.symm_apply_apply]
    exact ⟨rfl,rfl⟩⟩
  left_inv ξ := Subtype.ext (EscapeLabel.autMap_symm hab ξ.1)
  right_inv ξ := Subtype.ext (EscapeLabel.autMap_symm (isAut_symm G hab) ξ.1)

noncomputable def escapeLabelTransport (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) : ℝ :=
  ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}, B ξ.1

end LabeledTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GeodesicSegments
attribute [local instance] Classical.propDecidable Classical.decEq

 

def geodesicSegment (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) : Fin (N+1) → V :=
  fun i => q.getVert i

theorem segmentOrbit_adj (G : BondGraph V E) {I : Type*} (γ s : I → V)
    (hs : s ∈ segmentOrbit G γ) (i j : I) (hij : (openSimpleGraph G Set.univ).Adj (γ i) (γ j)) :
    (openSimpleGraph G Set.univ).Adj (s i) (s j) := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact (autSimpleGraph G hab).map_rel_iff.mpr hij

end GeodesicSegments
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_CollisionTails
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

theorem orbitSegment_consecutive (G : BondGraph V E) (J : ℕ) (γ s : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hs : s ∈ segmentOrbit G γ) :
    ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (s i.castSucc) (s i.succ) :=
  fun i => segmentOrbit_adj G γ s hs _ _ (hγ i)

 

def escapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) ((J+L)+J)
      (ξ.first (segmentCenter J)) (ξ.last (segmentCenter J)) :=
  (positiveStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append
    (ξ.middle.append (positiveStem _ J ξ.last
      (orbitSegment_consecutive G J γ ξ.last hγ ξ.last_mem)).reverse)

end IntrinsicVisibleBlocks
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootedRawProjection
attribute [local instance] Classical.propDecidable Classical.decEq

def rootedEscapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact ⟨ξ.last (segmentCenter J),escapeLabelRaw G J L m γ hγ ξ⟩

end RootedRawProjection
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelDeletionDiagram
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

noncomputable def kernelTriangleDiagonal (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (u : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, ∑' z, law p {ω | Conn G ω u a} * K a b *
    law p {ω | Conn G ω b z} * law p {ω | Conn G ω u z}

noncomputable def kernelDeletionDiagram (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, ∑' z, K a b * law p {ω | Conn G ω b z} *
    law p {ω | Conn G ω x a ∧ Conn G ω x z}

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorConnection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exteriorSusceptibility (G : BondGraph V E) (p : unitInterval)
    (x b : V) (ω : Set E) : ℝ :=
  freshExteriorMoment G p x b ω / (cluster G ω x).ncard

noncomputable def exteriorConnectionMoment (G : BondGraph V E) (p : unitInterval)
    (x a b : V) : ℝ≥0∞ :=
  ∫⁻ ω, if Conn G ω x a then ENNReal.ofReal (exteriorSusceptibility G p x b ω)
    else 0 ∂law p

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_KernelExterior
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def kernelExteriorPotential (G : BondGraph V E) (p : unitInterval)
    (K : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, K a b * exteriorConnectionMoment G p x a b

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Score
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decision-tree scores and influences for two-cluster events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterScore (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : ℝ) (ω : Finset E) : ℝ :=
  ∑ e ∈ incidentBonds G Q (finiteRootComponent G ω x), ((if e ∈ ω then 1 else 0)-p)


end Percolation

 

 

open MeasureTheory ProbabilityTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteDensity (G : BondGraph V E) (n : ℕ) (x : V) (ω : Finset E) : ℝ :=
  cappedDensity n (finiteRootComponent G ω x).card

noncomputable def finiteDensityInfluence (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Finset E) : ℝ :=
  if e ∈ ω then 0 else finiteDensity G n x ω - finiteDensity G n x (insert e ω)

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Transport
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite-volume two-cluster limits and transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterDensity (G : BondGraph V E) (n : ℕ) (x : V) (ω : Set E) : ℝ :=
  cappedDensity n (cluster G ω x).ncard

noncomputable def densityInfluence (G : BondGraph V E) (n : ℕ) (x : V)
    (e : E) (ω : Set E) : ℝ :=
  if e ∈ ω then 0 else clusterDensity G n x ω - clusterDensity G n x (insert e ω)

end Percolation

 

 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def boundaryDensityInfluence (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  ∑' e, if y ∈ G e then ENNReal.ofReal (densityInfluence G n y e ω) else 0

noncomputable def localDensityLoss (G : BondGraph V E) (n : ℕ)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  (cluster G ω y).ncard * boundaryDensityInfluence G n ω y

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_TwoCluster_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative two-cluster probability bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

 

def twoLargeEvent (G : BondGraph V E) (a b : V) (n : ℕ) : Set (Set E) :=
  {ω | ¬Conn G ω a b ∧ ω ∈ clusterLarge G a n ∧ ω ∈ clusterLarge G b n}

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PositiveEscapes
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

def firstEscapeCollision (G : BondGraph V E) (J m L : ℕ) (x y : V)
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (tail : RawFrom (openSimpleGraph G Set.univ) m x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L y) (h : I → V) : Prop :=
  (((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
    (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)) ∨
  ((∃ st : Fin (J+1) × Fin (J+1), h (j st.1) = neg st.2) ∨
    (∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h (j ij.2)))

end CombinedRawAvoidance
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FirstLabeledMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelFirstEscapeCollision (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  firstEscapeCollision G J m L (ξ.first neg) (ξ.first ep)
    (fun t => ξ.first (posIdx t)) (fun t => ξ.first (negIdx t)) suffixIdx
    ξ.leftTail ⟨ξ.last ep,ξ.middle⟩ ξ.last

end FirstLabeledMarginal
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_SelectionBounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelPotentialFailure (G : BondGraph V E) (p : unitInterval) (γ : I → V)
    (ep neg : I) (L m : ℕ)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.leftTail.1 b) ∨
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.rightTail.1 b)

end FullPotentialTests
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Escape_PathSelection
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


def labelLeftEscape (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) (m+J)
      (ξ.first (segmentCenter J)) ξ.leftTail.1 :=
  (negativeStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append ξ.leftTail.2

 
def labelCorridor (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) : RawCorridor G ((J+L)+J) :=
  ⟨ξ.first (segmentCenter J), ξ.last (segmentCenter J), escapeLabelRaw G J L m γ hγ ξ⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}


noncomputable def neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) : Finset V :=
  w.interior ∪ w.interior.biUnion (neighbors G hloc)


def HasEscape (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) (x : V) : Prop :=
  ∃ z, ∃ q : (openSimpleGraph G Set.univ).Walk x z,
    q.IsPath ∧ q.length ≤ j ∧ (∀ v ∈ q.support, v ∉ w.interior) ∧
      (∑ b ∈ w.neighborhood hloc, twoPoint G p z b) ≤ t

 
def Selected (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) : Prop :=
  3 ≤ w.path.length ∧ w.HasEscape hloc p j t w.base ∧ w.HasEscape hloc p j t w.endpoint

end RawCorridor

 

noncomputable def spineVertices (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset ∪
    Finset.univ.image (h ∘ segmentPositiveIndex J)

noncomputable def spineNeighborhood (G : BondGraph V E) (hloc : LocallyFinite G) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  let W := spineVertices G J L s mid h
  W ∪ W.biUnion (neighbors G hloc)

end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Automorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally compact graph automorphism groups and unimodular root data. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Topology
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}

 
def graphAut (G : BondGraph V E) : Subgroup (Equiv.Perm V) where
  carrier := vertexAut G
  one_mem' := ⟨Equiv.refl E, isAut_refl G⟩
  mul_mem' := by
    rintro a c ⟨b,hb⟩ ⟨d,hd⟩
    exact ⟨d.trans b, isAut_trans G hd hb⟩
  inv_mem' := by
    rintro a ⟨b,hb⟩
    exact ⟨b.symm,isAut_symm G hb⟩

 

theorem mem_vertexAut_iff (G : BondGraph V E) (hG : Function.Injective G)
    (a : Equiv.Perm V) :
    a ∈ vertexAut G ↔ ∀ x y, Adj G (a x) (a y) ↔ Adj G x y := by
  constructor
  · rintro ⟨b,hb⟩ x y
    exact ⟨fun h => by simpa using adj_aut G (isAut_symm G hb) h,adj_aut G hb⟩
  · intro ha
    have he (s : Sym2 V) : s ∈ Set.range G ↔ s.map a ∈ Set.range G := by
      induction s using Sym2.inductionOn with
      | _ x y => exact (ha x y).symm
    let a₂ : Equiv.Perm (Sym2 V) :=
      ⟨Sym2.map a,Sym2.map a.symm,
        fun s => by simp only [Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq],
        fun s => by simp only [Sym2.map_map,Equiv.self_comp_symm,Sym2.map_id',id_eq]⟩
    let e : E ≃ Set.range G := Equiv.ofInjective G hG
    let b : E ≃ E := (e.trans (a₂.subtypeEquiv he)).trans e.symm
    refine ⟨b,?_⟩
    intro z
    have hb : e (b z) = a₂.subtypeEquiv he (e z) := by
      exact e.apply_symm_apply _
    exact congrArg Subtype.val hb

 

abbrev graphOrbitType (G : BondGraph V E) := Quotient (MulAction.orbitRel (graphAut G) V)

instance graphOrbitType_nonempty [Nonempty V] (G : BondGraph V E) :
    Nonempty (graphOrbitType G) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩

noncomputable def graphOrbitRoot (G : BondGraph V E) : graphOrbitType G → V := Quotient.out

section Topology
variable [TopologicalSpace V] [DiscreteTopology V]

theorem isClosed_vertexAut (G : BondGraph V E) (hG : Function.Injective G) :
    IsClosed (vertexAut G) := by
  have h (x y : V) : IsClosed {a : Equiv.Perm V | Adj G (a x) (a y) ↔ Adj G x y} := by
    have hf : Continuous (fun a : Equiv.Perm V => (a x,a y)) :=
      (PointwisePerm.continuous_apply x).prodMk (PointwisePerm.continuous_apply y)
    exact (isClosed_discrete {p : V × V | Adj G p.1 p.2 ↔ Adj G x y}).preimage hf
  convert isClosed_iInter (fun x => isClosed_iInter (h x)) using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,mem_vertexAut_iff G hG]

 
theorem isCompact_vertexStabilizer (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) :
    IsCompact {a : Equiv.Perm V | a ∈ vertexAut G ∧ a x = x} := by
  apply PointwisePerm.isCompact_of_finite_images _
    ((isClosed_vertexAut G hG).inter (PointwisePerm.isClosed_fixed x x))
  · intro y
    obtain ⟨n,hn⟩ := exists_mem_reachBall (hconn x y)
    apply (finite_reachBall hloc x n).subset
    rintro z ⟨a,⟨⟨b,hb⟩,hx⟩,rfl⟩
    change a x = x at hx
    simpa only [hx] using mem_reachBall_aut G hb hn
  · intro y
    obtain ⟨n,hn⟩ := exists_mem_reachBall (hconn x y)
    apply (finite_reachBall hloc x n).subset
    rintro z ⟨a,⟨⟨b,hb⟩,hx⟩,rfl⟩
    have hx' : a.symm x = x := by rw [Equiv.symm_apply_eq,hx]
    simpa only [hx'] using mem_reachBall_aut G (isAut_symm G hb) hn

 
omit [DiscreteTopology V] in
theorem graphAut_continuous_apply (G : BondGraph V E) (x : V) :
    Continuous (fun g : graphAut G => g • x) :=
  (PointwisePerm.continuous_apply x).comp continuous_subtype_val

theorem graphAut_isOpen_stabilizer (G : BondGraph V E) (x : V) :
    IsOpen (actionStabilizer (H := graphAut G) x) :=
  (isOpen_discrete ({x} : Set V)).preimage (graphAut_continuous_apply G x)

theorem graphAut_isCompact_stabilizer (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) :
    IsCompact (actionStabilizer (H := graphAut G) x) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert isCompact_vertexStabilizer G hG hconn hloc x using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨g.property,hg⟩
  · rintro ⟨ha,hax⟩
    exact ⟨⟨a,ha⟩,hax,rfl⟩

 

theorem graphAut_locallyCompact [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    LocallyCompactSpace (graphAut G) := by
  let x : V := Classical.arbitrary V
  have hK := graphAut_isCompact_stabilizer G hG hconn hloc x
  have hKo := graphAut_isOpen_stabilizer G x
  have hw : WeaklyLocallyCompactSpace (graphAut G) := by
    refine ⟨fun g => ?_⟩
    refine ⟨(fun h : graphAut G => g * h) '' actionStabilizer (H := graphAut G) x,
      hK.image (continuous_const.mul continuous_id),?_⟩
    have h1 : actionStabilizer (H := graphAut G) x ∈ nhds (1 : graphAut G) :=
      hKo.mem_nhds (one_smul _ _)
    have he := (Homeomorph.mulLeft g).map_nhds_eq (1 : graphAut G)
    change Filter.map (fun h : graphAut G => g * h) (nhds 1) = nhds (g * 1) at he
    rw [mul_one] at he
    rw [←he]
    exact Filter.image_mem_map h1
  let := hw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance graphAutSecondCountable [Countable V] (G : BondGraph V E) :
    SecondCountableTopology (graphAut G) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance graphAutMeasurableSpace (G : BondGraph V E) : MeasurableSpace (graphAut G) :=
  borel (graphAut G)

instance graphAutBorelSpace (G : BondGraph V E) : BorelSpace (graphAut G) := ⟨rfl⟩

 
noncomputable def graphHaar [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) :
    Measure (graphAut G) := by
  letI := graphAut_locallyCompact G hG hconn hloc
  exact Measure.haar

end Topology
end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical boundedness of the percolation operator under unimodularity and simple edge indexing. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal





namespace Percolation
open MeasureTheory
universe u v
variable {V : Type u} {E : Type v}

 

noncomputable def AutUnimodular [Nonempty V] (G : BondGraph V E)
    (hG : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G) : Prop :=
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  (graphHaar G hG hconn hloc).IsMulRightInvariant



end Percolation



end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Graph
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision of indexed bond graphs and its basic geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory

theorem subdivision_injective (G : BondGraph V E) : Function.Injective (subdivision G) := by
  intro ⟨⟨e,x⟩,hx⟩ ⟨⟨f,y⟩,hy⟩ h
  simp only [subdivision,Sym2.eq_iff] at h
  rcases h with ⟨hxy,hef⟩ | ⟨hbad,_⟩
  · have h₁ : x = y := Sum.inl.inj hxy
    have h₂ : e = f := Sum.inr.inj hef
    subst y; subst f; rfl
  · cases hbad

theorem subdivision_locallyFinite (G : BondGraph V E) (hloc : LocallyFinite G) :
    LocallyFinite (subdivision G) := by
  classical
  intro z
  cases z with
  | inl x =>
    apply Set.Finite.of_finite_image (f := fun e : SubdivisionEdge G => e.val.1)
    · apply (hloc x).subset
      rintro e ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : x = y := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro e he f hf hef
      apply Subtype.ext
      apply Prod.ext hef
      have hx : x = e.val.2 := by simpa [subdivision] using he
      have hy : x = f.val.2 := by simpa [subdivision] using hf
      exact hx.symm.trans hy
  | inr e =>
    apply Set.Finite.of_finite_image (f := fun f : SubdivisionEdge G => f.val.2)
    · apply (Sym2.toFinset (G e)).finite_toSet.subset
      rintro x ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : e = f := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro f hf g hg hfg
      apply Subtype.ext
      apply Prod.ext _ hfg
      have h₁ : e = f.val.1 := by simpa [subdivision] using hf
      have h₂ : e = g.val.1 := by simpa [subdivision] using hg
      exact h₁.symm.trans h₂

theorem subdivision_connected (G : BondGraph V E) (hconn : Connected G) :
    Connected (subdivision G) := by
  have hold (x y : V) : Relation.ReflTransGen (Adj (subdivision G)) (.inl x) (.inl y) := by
    induction hconn x y with
    | refl => exact .refl
    | @tail y z hxy hyz ih =>
      obtain ⟨e,he⟩ := hyz
      exact (ih.tail ((subdivision_adj_inl_inr G y e).mpr (by simp [he]))).tail
        ((subdivision_adj_inr_inl G e z).mpr (by simp [he]))
  have attach (z : V ⊕ E) : ∃ x : V, Relation.ReflTransGen (Adj (subdivision G)) z (.inl x) := by
    cases z with
    | inl x => exact ⟨x,.refl⟩
    | inr e =>
      exact ⟨(G e).out.1,Relation.ReflTransGen.single
        ((subdivision_adj_inr_inl G e _).mpr (G e).out_fst_mem)⟩
  have rev {a b : V ⊕ E} (h : Relation.ReflTransGen (Adj (subdivision G)) a b) :
      Relation.ReflTransGen (Adj (subdivision G)) b a := by
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact (Relation.ReflTransGen.single (adj_symm _ hab)).trans ih
  intro z w
  obtain ⟨x,hx⟩ := attach z
  obtain ⟨y,hy⟩ := attach w
  exact hx.trans ((hold x y).trans (rev hy))

 
theorem incidence_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (e : E) (x : V) : a x ∈ G (b e) ↔ x ∈ G e := by
  rw [hab e]
  simp only [Sym2.mem_map,a.injective.eq_iff,exists_eq_right]

 
noncomputable def subdivisionAutEdges (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) : SubdivisionEdge G ≃ SubdivisionEdge G :=
  (b.prodCongr a).subtypeEquiv (fun p => (incidence_aut_iff G hab p.1 p.2).symm)

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Subdivision_Coupling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupling percolation on a graph with percolation on its subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def subdivisionOpen (G : BondGraph V E) (ν : Set (E × Bool)) :
    Set (SubdivisionEdge G) := halfBit G ⁻¹' ν

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_Cayley
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

def PublishedPhaseInput {V E : Type*} (G : BondGraph V E) : Prop :=
  ∀ p : unitInterval, pc G < p → p < pu G →
    ∀ᵐ ω ∂law p, (infiniteClusters G ω).Infinite

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation

namespace ClusterDeletion
variable {V : Type*}

noncomputable def residual (H : SimpleGraph V) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact if s ∉ roots (delete H U) S then
    F (component (delete H (roots (delete H U) S)) s) -
      F (component (delete H (roots (delete H U) S ∪ U)) s)
  else 0

end ClusterDeletion
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_DeleteBot
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}
@[simp] lemma delete_bot (U : Set V) : delete (⊥ : SimpleGraph V) U = ⊥ := by
  ext v w
  simp [delete]
@[simp] lemma component_bot (s : V) : component (⊥ : SimpleGraph V) s = {s} := by
  ext v
  simp [component, SimpleGraph.reachable_bot, eq_comm]
@[simp] lemma roots_bot (S : Set V) : roots (⊥ : SimpleGraph V) S = S := by
  ext v
  simp [roots, SimpleGraph.reachable_bot]
end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

namespace SearchTree
variable {E R : Type*}
def run : SearchTree E R → (E → Bool) → R
  | .done r, _ => r
  | .ask e l r, ω => if ω e then run r ω else run l ω

def reads : SearchTree E R → (E → Bool) → List E
  | .done _, _ => []
  | .ask e l r, ω => e :: if ω e then reads r ω else reads l ω

def Valid [DecidableEq E] : SearchTree E R → Finset E → Prop
  | .done _, _ => True
  | .ask e l r, used => e ∉ used ∧ l.Valid (insert e used) ∧ r.Valid (insert e used)

end SearchTree

end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Exhaustive
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def Exhaustive (G : BondGraph V E) (order : List (Dart V E)) : Prop :=
  ∀ v e t, G.ends e = s(v,t) → (v,e,t) ∈ order

def Frontier (G : BondGraph V E) (st : State V E) (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

def ReadConsistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def score (p : ℝ) (F : Set E → Prop) :
    SearchTree E R → (E → Prop → ℝ) → Set E → ℝ
  | .done _, _, _ => 0
  | .ask e l r, w, ω =>
      (if openPivot F e ω then (1-p)*delta w F e else 0) +
      if ω e then score p F r (pin w e True) ω else score p F l (pin w e False) ω

noncomputable def PhaseAdmissible {V : Type*} (G : BondGraph V E) (s : V) (p : ℝ) :
    SearchTree E R → (E → Prop → ℝ) → Prop
  | .done _, _ => True
  | .ask e l r, w =>
      w e False = 1-p ∧ w e True = p ∧
      (∃ v b, G.ends e = s(v,b) ∧
        ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) ∧
      PhaseAdmissible G s p l (pin w e False) ∧
      PhaseAdmissible G s p r (pin w e True)

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def SupportedTails (G : BondGraph V E) (s : V) (w : E → Prop → ℝ)
    (stack : List (Dart V E)) : Prop :=
  ∀ d ∈ stack, ∀ ω, density w ω ≠ 0 → (G.openGraph ω).Reachable s d.1

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ListScore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def listScore (p : ℝ) (F : Set E → Prop) (ω : Set E) :
    List E → (E → Prop → ℝ) → ℝ
  | [], _ => 0
  | e::es, w => (if openPivot F e ω then (1-p)*delta w F e else 0) +
      listScore p F ω es (pin w e (ω e))

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PhaseFrontier
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def PhaseFrontier (G : BondGraph V E) (A : Set V) (st : State V E)
    (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, v ∉ A → ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PrefixState
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def PrefixState (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) : Prop :=
  a ∈ st.reached ∧ ∀ ω : Set E, density w ω ≠ 0 →
    (∀ v ∈ st.reached, (G.openGraph {e | e ∈ st.read ∧ e ∈ ω}).Reachable a v) ∧
    ReadConsistent G st (fun e => decide (ω e))

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_TargetSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def targetSearch (G : BondGraph V E) (B : Set V)
    (order : List (Dart (Option V) E)) (a : V) : SearchTree E (State (Option V) E) :=
  search (G.wireTargets B) order (collapseTarget B a) {none}

def GoodDarts (G : BondGraph V E) (ds : List (Dart V E)) : Prop :=
  ∀ d ∈ ds, G.ends d.2.1 = s(d.1,d.2.2)

noncomputable def mapDart (B : Set V) (d : Dart V E) : Dart (Option V) E :=
  (collapseTarget B d.1,d.2.1,collapseTarget B d.2.2)
noncomputable def mapState (B : Set V) (st : State V E) : State (Option V) E :=
  ⟨st.reached.image (collapseTarget B),st.read⟩

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def terminalProbability (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => prob w F
  | .ask e l r => if ω e then r.terminalProbability F (pin w e True) ω
      else l.terminalProbability F (pin w e False) ω

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AncestryForest
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

namespace Forest
variable (F : Forest)

def root (F : Forest) (n : ℕ) : ℕ :=
  if _h : n < 2 then n else F.root (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

end Forest
end CriticalPercolation.InterpolationForest

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedPivotWeight
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def closedPivotWeight (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  if ¬ω e ∧ openPivot F e (Function.update ω e True) then p*T.queryDelta F w ω e else 0

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_ReverseGuess
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def reverseMass (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    b/(1+s+b)^2 + if ω f then r.reverseMass p F (pin w f True) ω (s+b)
      else l.reverseMass p F (pin w f False) ω (s+b)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryTree
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation
open FiniteEntropy

universe u

namespace QueryTree
variable {E : Type u}

instance leafFintype : (t : QueryTree E) → Fintype t.Leaf
  | .stop => inferInstanceAs (Fintype PUnit)
  | .ask _ left right => @instFintypeSum _ _ left.leafFintype right.leafFintype

def reads : (t : QueryTree E) → (E → Bool) → List E
  | .stop, _ => []
  | .ask e left right, ω => e :: if ω e then right.reads ω else left.reads ω

def Valid [DecidableEq E] : QueryTree E → Finset E → Prop
  | .stop, _ => True
  | .ask e left right, used => e ∉ used ∧ left.Valid (insert e used) ∧ right.Valid (insert e used)

noncomputable def reference (p : ℝ) : (t : QueryTree E) → t.Leaf → ℝ
  | .stop, _ => 1
  | .ask _ left _, Sum.inl x => (1-p)*left.reference p x
  | .ask _ _ right, Sum.inr x => p*right.reference p x

noncomputable def charge (F : ℝ → ℝ) : (t : QueryTree E) → (t.Leaf → ℝ) → ℝ
  | .stop, _ => 0
  | .ask _ left right, P =>
      let l := ∑ x, P (Sum.inl x)
      let r := ∑ x, P (Sum.inr x)
      (l+r)*F (r/(l+r)) + left.charge F (fun x => P (Sum.inl x)) +
        right.charge F (fun x => P (Sum.inr x))

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Node
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

instance nodeFintype : (t : QueryTree E) → Fintype t.Node
  | .stop => inferInstanceAs (Fintype PEmpty)
  | .ask _ l r => @instFintypeSum _ _ (inferInstanceAs (Fintype PUnit))
      (@instFintypeSum _ _ l.nodeFintype r.nodeFintype)

def bit : (t : QueryTree E) → t.Node → E
  | .stop, n => PEmpty.elim n
  | .ask e _ _, .inl _ => e
  | .ask _ l _, .inr (.inl n) => l.bit n
  | .ask _ _ r, .inr (.inr n) => r.bit n

def response : (t : QueryTree E) → t.Node → t.Leaf → Option Bool
  | .stop, n, _ => PEmpty.elim n
  | .ask _ _ _, .inl _, .inl _ => some false
  | .ask _ _ _, .inl _, .inr _ => some true
  | .ask _ l _, .inr (.inl n), .inl x => l.response n x
  | .ask _ _ _, .inr (.inl _), .inr _ => none
  | .ask _ _ _, .inr (.inr _), .inl _ => none
  | .ask _ _ r, .inr (.inr n), .inr x => r.response n x

noncomputable def nodeMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if (t.response n x).isSome then P x else 0

noncomputable def nodeTrueMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if t.response n x = some true then P x else 0

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Visits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*}

def visits (t : QueryTree E) (n : t.Node) (ω : E → Bool) : Bool :=
  (t.response n (t.run ω)).isSome

end CriticalPercolation.QueryTree

namespace CriticalPercolation
universe u v w

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

def bare : MarkedTree E A → QueryTree E
  | .stop => .stop
  | .ask e _ l r => .ask e l.bare r.bare

def nodeLabel : (t : MarkedTree E A) → t.bare.Node → A
  | .stop, n => PEmpty.elim n
  | .ask _ a _ _, .inl _ => a
  | .ask _ _ l _, .inr (.inl n) => l.nodeLabel n
  | .ask _ _ _ r, .inr (.inr n) => r.nodeLabel n

def map (f : A → B) : MarkedTree E A → MarkedTree E B
  | .stop => .stop
  | .ask e a l r => .ask e (f a) (l.map f) (r.map f)

end MarkedTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Select
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

def pathNodes : (t : QueryTree E) → (E → Bool) → List t.Node
  | .stop, _ => []
  | .ask e l r, ω => .inl PUnit.unit ::
      if ω e then (r.pathNodes ω).map (Sum.inr ∘ Sum.inr)
      else (l.pathNodes ω).map (Sum.inr ∘ Sum.inl)

def marked : (t : QueryTree E) → MarkedTree E t.Node
  | .stop => .stop
  | .ask e l r => .ask e (.inl PUnit.unit)
      (l.marked.map (Sum.inr ∘ Sum.inl)) (r.marked.map (Sum.inr ∘ Sum.inr))

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_LocalNode
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree

variable {E I : Type*} (t : I → QueryTree E)

abbrev LocalNode := (i : I) × (t i).Node

def coord (a : LocalNode t) : E := (t a.1).bit a.2

def algorithm (i : I) : MarkedTree E (LocalNode t) :=
  (t i).marked.map (Sigma.mk i)

def raw (order : List I) : MarkedTree E (LocalNode t) :=
  sequence (order.map (algorithm t))

variable [DecidableEq E] [Fintype E]
def combined (order : List I) : MarkedTree E (LocalNode t) :=
  (raw t order).cached (fun _ => none)

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Uniform01
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

noncomputable def law : Measure (I → ℝ) := Measure.pi fun _ => uniform01

instance instIsProbabilityMeasureForallRealLaw : IsProbabilityMeasure (law (I := I)) := by
  unfold law
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_AeEvalNe
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

instance instNullSingletonClassRealUniform01 : NullSingletonClass uniform01 := by
  unfold uniform01
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_OrderMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

noncomputable def orderMass (o : Order I) : ℝ := ∫ _u in cell o, (1:ℝ) ∂law
noncomputable def orderWeight (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, endpointKernel (u i) ∂law
noncomputable def orderSquare (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, (endpointKernel (u i))^2 ∂law

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Users
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype I]

noncomputable instance (priority := 2000) localNodeDecidable (t : I → QueryTree E) :
    DecidableEq (LocalNode t) := Classical.decEq _

noncomputable def users (t : I → QueryTree E) (ω : E → Bool) (e : E) : Finset I :=
  Finset.univ.filter (fun i => e ∈ (t i).reads ω)

noncomputable def otherUsers (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E) :
    Finset {j : I // j ≠ i} := (users t ω e).subtype (fun j => j ≠ i)

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_InputMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def inputMass (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) : ℝ :=
  t.nodeMass (pushMass t.run P) n
noncomputable def inputNumerator (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ)
    (n : t.Node) : ℝ := t.nodeTrueMass (pushMass t.run P) n - p*t.inputMass P n

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_GlobalNode
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy FiniteProduct

variable {E I : Type*} [Fintype E] [Fintype I]

abbrev GlobalNode (t : I → QueryTree E) := (o : Order I) × (combined t o.val).bare.Node

noncomputable abbrev globalTag (t : I → QueryTree E) (x : GlobalNode t) : LocalNode t :=
  (combined t x.1.val).nodeLabel x.2

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def Consistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

def Sound (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ v ∈ st.reached, ∃ s ∈ S, (G.openGraph {e | ω e = true}).Reachable s v

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteEntropy FiniteProduct

variable {V E I : Type*} [Fintype E] [Fintype I]

noncomputable def clusterUsers (G : BondGraph V E) (a b : I → V) (ω : E → Bool)
    (v : V) : Finset I :=
  Finset.univ.filter (fun i => (G.openGraph {e | ω e = true}).Reachable (a i) v ∨
    (G.openGraph {e | ω e = true}).Reachable (b i) v)

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z I M : Type*} [Fintype X] [Fintype Y] [Fintype Z]

noncomputable def conditionalMass (P : X → ℝ) (u : X → Y) (v : X → Z)
    (y : Y) (z : Z) : ℝ :=
  pushMass (fun x => (u x,v x)) P (y,z) / pushMass u P y

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

 def Available (G : BondGraph V E) (v : V) (st : State E) (e : E) : Prop :=
  e ∉ st.read ∧ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v)

 def compile (G : BondGraph V E) (v : V) : ℕ → State E → SearchTree E (State E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, Available G v st e then
      let e := h.choose
      .ask e (compile G v n (st.closed e)) (compile G v n (st.open e))
    else .done st

 def Good (G : BondGraph V E) (v : V) (ω : Set E) (st : State E) : Prop :=
  st.opened ⊆ st.read ∧
  (∀ e ∈ st.read, e ∈ st.opened ↔ e ∈ ω) ∧
  ∀ e ∈ st.read, e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v)

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_QueryMartingale
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

def queryCount : SearchTree E R → (E → Prop) → ℕ
  | .done _, _ => 0
  | .ask e l r, ω => 1 + if ω e then queryCount r ω else queryCount l ω

def centeredSum (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then (1-p)+centeredSum p r ω else -p+centeredSum p l ω

def truncate : SearchTree E R → ℕ → SearchTree E Unit
  | _, 0 => .done ()
  | .done _, _+1 => .done ()
  | .ask e l r, n+1 => .ask e (truncate l n) (truncate r n)

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

variable [Fintype E]
 def tree (G : BondGraph V E) (v : V) : SearchTree E (State E) :=
  compile G v (Fintype.card E + 1) ⟨∅,∅⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

def criticalModel (G : BondGraph V E) : CriticalPercolation.BondGraph V E := ⟨G⟩

theorem criticalModel_quasiTransitive (G : BondGraph V E) (hqt : QuasiTransitive G) :
    (criticalModel G).QuasiTransitive := by
  obtain ⟨S, hS⟩ := hqt
  refine ⟨S, S.finite_toSet, ?_⟩
  intro x
  obtain ⟨o, ho, a, b, hab, hax⟩ := hS x
  exact ⟨o, ho, ⟨a, b, hab⟩, hax⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorSeparation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Corridor

def source (e : Edge) : Site := e.1
def target (e : Edge) : Site := if e.2 then e.1+(1,0) else e.1+(0,1)
def endpoints (e : Edge) : Set Site := {source e,target e}

def box (j h : ℝ) (v : Site) : Set Point := {x |
    |x.1-((v.1 : ℝ)+v.2)|≤j ∧ |x.2-((v.1 : ℝ)-v.2)|≤j+h}

def tube (h : ℝ) (e : Edge) : Set Point := {x |
    (e.1.1 : ℝ)+e.1.2≤x.1 ∧ x.1≤(e.1.1 : ℝ)+e.1.2+1 ∧
    if e.2 then |x.2-(x.1-2*(e.1.2 : ℝ))|≤h
    else |x.2-(2*(e.1.1 : ℝ)-x.1)|≤h}

def domain (j h : ℝ) (e : Edge) : Set Point :=
  box j h (source e)∪box j h (target e)∪tube h e

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def graphBox (v : Site) : Set V := ξ ⁻¹' box j h v
def graphDomain (e : Edge) : Set V := ξ ⁻¹' domain j h e
def boxEdges (v : Site) : Set E := G.inducedEdges (graphBox ξ j h v)
def corridorEdges (e : Edge) : Set E := G.inducedEdges (graphDomain ξ j h e)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_Weight
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

def probability (p : ℝ) (F : Set E → Prop) : ℝ :=
  expect (fun _ : E => weight p) (fun ω => if F ω then 1 else 0)

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Link2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness

open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

def reachesTarget (o : V) (T : Set V) (ω : Set E) : Prop :=
  o ∈ roots (G.openGraph ω) T

def boundaryReach (R : Set V) (H : SimpleGraph V) (o : V) (e : E) : Prop :=
  ∃ x y, G.ends e = s(x,y) ∧ x ∉ R ∧ y ∈ R ∧ H.Reachable o x

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BoundaryCount
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule2
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {V E : Type*} [Fintype E] (G : BondGraph V E)

def boundaryCount (o : V) (R : Set V) (H : SimpleGraph V) : ℝ :=
  ∑ e, if boundaryReach G R H o e then 1 else 0

def boundaryFlux (p : ℝ) (o : V) (R : Set V) : ℝ :=
  p * expect (fun _ : E => weight p)
    (fun ω => boundaryCount G o R (delete (G.openGraph ω) R))

end CriticalPercolation.Sharpness
end
end CurrentModule2

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SharpnessPhi
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule6
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*}

variable (G : BondGraph V E)

def phi (p : unitInterval) (o : V) (S : Set V) : ℝ :=
  (p : ℝ) * ∑' e, (G.law p).real
    {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DeleteImageIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule9
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

noncomputable def deleteImageIso (φ : G.Aut) (ω : Set E) (S : Set V) :
    delete (G.openGraph ω) S ≃g delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S) where
  toEquiv := φ.vertex
  map_rel_iff' := by
    intro x y
    change ((G.openGraph (φ.edge '' ω)).Adj (φ.vertex x) (φ.vertex y) ∧
      φ.vertex x ∉ φ.vertex '' S ∧ φ.vertex y ∉ φ.vertex '' S) ↔ _
    simp only [BondGraph.Aut.adj_map,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
    rfl

end CriticalPercolation.Sharpness
end
end CurrentModule9

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_CutInside
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule3
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def cutInside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.1 else (G.ends e).out.2

def cutOutside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.2 else (G.ends e).out.1

def IsCut (S : Set V) (e : E) : Prop := cutInside G S e ∈ S ∧ cutOutside G S e ∉ S

def internalIncident (S C : Set V) : Set E :=
  {e | e ∈ G.incidentEdges C ∧ ∀ v ∈ G.ends e, v ∈ S}

def internalCluster (S : Set V) (o : V) (ω : Set E) : Set V :=
  component (delete (G.openGraph ω) Sᶜ) o

end CriticalPercolation.Sharpness
end
end CurrentModule3

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_Leak
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule4
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype E]

variable (G : BondGraph V E)

def leak (S C : Set V) (e : E) (v : V) (ω : Set E) : ℝ :=
  if IsCut G S e ∧ cutInside G S e ∈ C then
    if e ∈ ω ∧ (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0
  else 0

end CriticalPercolation.Sharpness
end
end CurrentModule4

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_TwoPoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

def twoPoint (p : unitInterval) (o v : V) : ℝ := (G.law p).real (G.hitEvent o {v})

end CriticalPercolation.Sharpness
end
end CurrentModule10

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterMassInfinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def size (ω : Set E) (v : V) : ℕ := (G.cluster ω v).ncard

def mass (s : ℕ) (ω : Set E) (v : V) : ℝ := cappedMass s (size G ω v) / size G ω v

def rootSum (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑' e, if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0

def rootDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * rootSum G p ω v

def rootAbsolute (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * |rootSum G p ω v|

def edgeMass (s : ℕ) (ω : Set E) (e : E) : ℝ :=
  cappedMass s (size G ω (G.ends e).out.1) +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else cappedMass s (size G ω (G.ends e).out.2)

def edgeDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  coefficient p ω e * edgeMass G s ω e

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedQuery
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*}

def weightedSum (a : E → ℝ) (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then a e*(1-p)+weightedSum a p r ω
      else -a e*p+weightedSum a p l ω

def quadraticCost (a : E → ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => (a e)^2 + if ω e then quadraticCost a r ω else quadraticCost a l ω

def takeQuadratic (a : E → ℝ) : SearchTree E R → ℝ → SearchTree E Unit
  | .done _, _ => .done ()
  | .ask e l r, B => if (a e)^2 ≤ B then
      .ask e (takeQuadratic a l (B-(a e)^2)) (takeQuadratic a r (B-(a e)^2))
      else .done ()

end CriticalPercolation.SearchTree
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorNormalization
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

def timeCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)+v.2)*T
def heightCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)-v.2)*T/4
def normalized (t z : V → ℝ) (T : ℝ) : V → Point := fun x => (t x/T,4*z x/T)
def localTime (t : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => t x-timeCenter T v
def localHeight (z : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => z x-heightCenter T v

def mark (t z : V → ℝ) (T ρ : ℝ) (v : Site) : Set V :=
  {x | 0≤localTime t T v x ∧ localTime t T v x≤ρ ∧ |localHeight z T v x|≤210}

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterTransportGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def small (r : ℕ) (ω : Set E) (v : V) : Prop :=
  ∀ x ∈ G.cluster ω v, ∀ y ∈ G.cluster ω v, y ∈ G.vertexBall x r

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterTransportSums
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def weight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then mass G s ω v else 0

def transport (r s : ℕ) (p : ℝ) (ω : Set E) (v : V) (e : E) : ℝ :=
  if e ∈ G.incidentEdges (G.cluster ω v) then weight G r s ω v * coefficient p ω e else 0

def clusterWeight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then cappedMass s (size G ω v) else 0

def truncatedEdgeMass (r s : ℕ) (ω : Set E) (e : E) : ℝ :=
  clusterWeight G r s ω (G.ends e).out.1 +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else clusterWeight G r s ω (G.ends e).out.2

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterTransportFinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

def expectedTransport (r s : ℕ) (p : unitInterval) (u : V) (e : E) : ℝ :=
  ∫ ω, transport G r s p ω u e ∂G.law p

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_LatticeGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open Boundary

def slotSite (n : ℕ) : Site := ((Nat.unpair n).1,(Nat.unpair n).2)

def incoming (n : ℕ) (S : Finset Site) : Option Edge :=
  if (slotSite n-(1,0))∈S then some (slotSite n-(1,0),true)
  else if (slotSite n-(0,1))∈S then some (slotSite n-(0,1),false) else none

structure GrowthState where
  good : Finset Site
  seen : Finset Edge

def GrowthState.initial : GrowthState := ⟨{(0,0)},∅⟩

def GrowthState.advance (n : ℕ) (S : GrowthState) (b : Bool) : GrowthState where
  good := if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good
  seen := S.seen∪(incoming n S.good).toFinset

lemma GrowthState.seen_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.seen⊆(S.advance n b).seen := Finset.subset_union_left

def GrowthState.Valid (n : ℕ) (S : GrowthState) : Prop :=
  (0,0)∈S.good ∧
  (∀ v∈S.good, quadrant v ∧ (v=(0,0) ∨ gridSlot v<n)) ∧
  (∀ e∈S.seen, source e∈S.good ∧ gridSlot (target e)<n)

def GrowthState.Covered (S : GrowthState) : Prop :=
  ∀ v∈S.good, v=(0,0) ∨ ∃ e∈S.seen, target e=v

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_GrowthHistoryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph Boundary

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def revealed (S : GrowthState) : Set E :=
  boxEdges G ξ j h (0,0)∪⋃ e∈S.seen, corridorEdges G ξ j h e

lemma revealed_mono {S T : GrowthState} (hST : S.seen⊆T.seen) :
    revealed G ξ j h S⊆revealed G ξ j h T := by
  apply Set.union_subset_union_right
  intro b hb
  obtain ⟨e,he,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.mem_iUnion₂.mpr ⟨e,hST he,hb⟩

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GrowthProcess
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure Scheme (V E : Type*) where
  graph : BondGraph V E
  coordinate : V → Point
  j : ℝ
  h : ℝ
  seed : Set V
  mark : Site → Set V
  parameter : E → unitInterval
  delta : ℝ

namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def block (S : GrowthState) : Set E := revealed P.graph P.coordinate P.j P.h S

def edgeDomain (e : Edge) : Set E := corridorEdges P.graph P.coordinate P.j P.h e

def enlarged (n : ℕ) (S : GrowthState) : Set E := P.block (S.advance n false)

def hit (v : Site) (R : Set E) : Set (Set E) := P.graph.restrictedSeed P.seed (P.mark v) R

def incomingHit (n : ℕ) (S : GrowthState) : Set (Set E) := P.hit (slotSite n) (P.enlarged n S)

def nextHit (n : ℕ) (S : GrowthState) (b : Bool) : Set (Set E) :=
  P.hit (target (slotSite n,b)) (P.enlarged n S∪P.edgeDomain (slotSite n,b))

def accepted (n : ℕ) (S : GrowthState) : Set (Set E) :=
  (predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
    (P.nextHit n S true) (P.nextHit n S false) P.delta)ᶜ

lemma accepted_measurable (n : ℕ) (S : GrowthState) :
    MeasurableSet[blockSigma (P.enlarged n S)] (P.accepted n S) :=
  (measurableSet_predictionFailure P.parameter (P.enlarged n S) _ _ _
    (P.graph.measurableSet_restrictedSeed _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
    (P.graph.restrictedSeed_measurable _ _ _) P.delta).compl

def rule : DecisionRule E GrowthState where
  initial := GrowthState.initial
  block := P.block
  further := P.enlarged
  contained n S := revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)
  active n S := (incoming n S.good).isSome
  accept := P.accepted
  measurable := P.accepted_measurable
  update := GrowthState.advance
  block_update _ _ _ := rfl

def rootEvent : Set (Set E) := {ω | ∀ b : Bool,
  1-P.delta ≤ (blockProbability P.parameter (P.block GrowthState.initial)
    (P.hit (target ((0,0),b)) (P.block GrowthState.initial∪P.edgeDomain ((0,0),b))) ω).toReal}

end Scheme
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_StoredPrediction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def Stable (n : ℕ) (S : GrowthState) (ω : Set E) : Prop :=
  (∀ v∈S.good, ω∈P.hit v (P.block S)) ∧
  (∀ e : Edge, source e∈S.good → n ≤ gridSlot (target e) →
    1-P.delta ≤ (blockProbability P.parameter (P.block S)
      (P.hit (target e) (P.block S∪P.edgeDomain e)) ω).toReal)

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ActualGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def actual (n : ℕ) (ω : Set E) : GrowthState := P.rule.state n (P.rule.codeOf n ω)

def allGood (ω : Set E) : Set Site := ⋃ n, ((P.actual n ω).good : Set Site)

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CoordinateScheme
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure CoordinateData (V E : Type*) where
  graph : BondGraph V E
  origin : V
  time : V → ℝ
  height : V → ℝ
  J : ℝ
  L : ℕ
  R : ℕ
  m : ℕ
  D : ℕ
  k : ℕ
  M : ℕ
  VM : ℕ
  e : ℝ
  rho : ℝ
  kappa : ℝ
  eta : ℝ
  delta : ℝ
  contour : ℝ
  pc : unitInterval
  p : unitInterval

namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)

def T : ℝ := C.L+1/2

def scheme : Scheme V E where
  graph := C.graph
  coordinate := normalized C.time C.height C.T
  j := C.J/C.T
  h := 2520/C.T
  seed := C.graph.vertexBall C.origin C.m
  mark := Corridor.mark C.time C.height C.T C.rho
  parameter := fun _ => C.p
  delta := C.delta

structure Bounds : Prop where
  connected : C.graph.fullGraph.Connected
  locallyFinite : C.graph.LocallyFinite
  time_origin : C.time C.origin=0
  height_origin : C.height C.origin=0
  time_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.time u-C.time v|≤C.rho
  height_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.height u-C.height v|≤C.rho
  J_lower : 26200<C.J
  L_lower : 10*(C.J+210)<C.L
  e_pos : 0<C.e
  rho_nonneg : 0≤C.rho
  e_small : (C.L+3)*C.e<1/100
  rho_small : (C.R+C.m+1)*C.rho<C.e/10
  R_gt : C.m<C.R
  pc_pos : 0<(C.pc : ℝ)
  pc_lt : (C.pc : ℝ)<1
  p_lower : (C.pc : ℝ)/2≤C.p
  p_upper : (C.p : ℝ)≤C.pc
  degree : ∀ v, (C.graph.incidentEdges {v}).ncard≤C.D
  M_pos : 0<C.M
  M_bound : ∀ v, (C.graph.vertexBall v (4*C.m+2)).ncard≤C.M
  VM_bound : ∀ v, (C.graph.vertexBall v C.m).ncard≤C.VM
  kappa_pos : 0<C.kappa
  kappa_le : C.kappa≤1
  eta_nonneg : 0≤C.eta
  eta_small : C.eta≤C.kappa*(C.kappa/4)/(4*(Real.log (4/C.kappa)+1))
  k_large : C.M*⌈Real.log (4/C.kappa)/((C.pc : ℝ)/2)^(C.m+1+C.VM)⌉₊≤C.k
  R_large : 4/(C.kappa*(1-(C.pc : ℝ))^(C.D*C.k))<(C.R : ℝ)-C.m
  delta_pos : 0<C.delta
  root_error : 2*(C.eta+C.L*C.kappa)<C.delta
  contour_nonneg : 0≤C.contour
  contour_small : 8*C.contour<1
  test_error : C.delta+2*((C.L+1)*C.kappa)/C.delta≤C.contour^4

end CoordinateData
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousTransport
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]
open ActionOrbitTransport

lemma pair_fiber_eq_suborbit (x y : X) :
    {w : X | pairOrbit G X x w=pairOrbit G X x y}=stabilizerOrbit G X x y := by
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm,pairOrbit_eq,mem_stabilizerOrbit]

variable (ht : ∀ x y : X, ∃ g : G, g • x=y)
  (hf : ∀ x y : X, (stabilizerOrbit G X x y).Finite)
  (hu : ∀ x y : X, suborbitCard G X x y=suborbitCard G X y x)

include ht hf in
lemma pair_row_finite (o b x : X) :
    {y : X | pairOrbit G X x y=pairOrbit G X o b}.Finite := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←smul_pairOrbit G X g o b]
  simpa only [pair_fiber_eq_suborbit] using hf (g • o) (g • b)

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousAverage
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma suborbit_finite (x y : X) : (stabilizerOrbit W.Aut X x y).Finite := by
  obtain ⟨p,_,_⟩ := W.connected.exists_path_of_dist x y
  apply (W.around x p.length).finite_toSet.subset
  intro z hz
  obtain ⟨g,hgx,rfl⟩ := (mem_stabilizerOrbit W.Aut X).mp hz
  change g x=x at hgx
  change g y∈W.around x p.length
  apply W.mem_around.mpr
  simpa only [hgx] using GraphTopology.iso_reachBall W.graph g (show y∈GraphTopology.reachBall W.graph x p.length from ⟨p,le_rfl⟩)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

def ratio (x y : X) : ℝ := (suborbitCard W.Aut X x y : ℝ)/(suborbitCard W.Aut X y x : ℝ)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicBallGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def intrinsicBallPolynomial (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ) : ℝ → ℝ :=
  bernoulliPolynomial (intrinsicBondSupport G hloc S x r)
    (fun ω => if y ∈ intrinsicBall G ((ω : Set E) ∩ S) x r then 1 else 0)

noncomputable def intrinsicBallMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : ℝ) : ℝ :=
  ∑ y ∈ (finite_reachBall hloc x r).toFinset, intrinsicBallPolynomial G hloc S x y r p

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicBallExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def ballIncidentEdges (G : BondGraph V E) (B : Set V) : Set E :=
  {e | ∃ a ∈ B, a ∈ G e}

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def intrinsicSphere (G : BondGraph V E) (ω : Set E) (x : V) (n : ℕ) : Set V :=
  {y | Conn G ω x y ∧ (openSimpleGraph G ω).dist x y = n}

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def thinSphereCell (G : BondGraph V E) (S : Set E) (x : V) (r k j : ℕ)
    (U W : Finset V) : Set (Set E) :=
  {ω | r ≤ j ∧ j ≤ 2*r ∧ intrinsicBall G (ω ∩ S) x (j-1) = U ∧
    intrinsicBall G (ω ∩ S) x j = W ∧
    (intrinsicSphere G (ω ∩ S) x j).ncard ≤ k ∧
    ∀ i, r ≤ i → i < j → k < (intrinsicSphere G (ω ∩ S) x i).ncard}

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ThinSphereStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def domainRadiusEvent (G : BondGraph V E) (S : Set E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ω ∩ S ∈ intrinsicRadiusEvent G x n}

def activeThinSphereCell (G : BondGraph V E) (S : Set E) (x : V) (r k j : ℕ)
    (U W : Finset V) : Set (Set E) :=
  thinSphereCell G S x r k j U W ∩ domainRadiusEvent G S x r

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BallSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def ballSnapshotCell (G : BondGraph V E) (x : V) (j : ℕ) (U W : Finset V) : Set (Set E) :=
  {ω | intrinsicBall G ω x (j-1) = U ∧ intrinsicBall G ω x j = W}

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedGhost
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

lemma ghostKernel_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    0 ≤ ghostKernel h x := by
  apply sub_nonneg.mpr
  exact (Real.exp_le_one_iff).mpr (by nlinarith)

lemma ghostKernel_le_one (h x : ℝ) : ghostKernel h x ≤ 1 := by
  exact sub_le_self _ (Real.exp_pos _).le

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def quarterTiltedClusterMass (G : BondGraph V E) (h : V → ℝ)
    (ω : Set E) (o : V) : ℝ≥0∞ :=
  ∑' x, if Conn G ω o x then ENNReal.ofReal (Real.exp (h x / 4)) else 0

noncomputable def modularLayerCount (G : BondGraph V E) (h : V → ℝ)
    (ω : Set E) (o : V) (k : ℤ) : ℝ≥0∞ :=
  ∑' x : {x : V // ⌊h x⌋ = k}, if Conn G ω o x then 1 else 0

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def modularHeight (G : BondGraph V E) (o x : V) : ℝ :=
  Real.log ((criticalModel G).modularRatio x o)

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SelectedLayerVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] (G : BondGraph V E)

def firstLayerHitAt (I : Set E) (x : V) (A : Set V) (z : V) : Set (Set E) :=
  {ω | Conn G (ω ∩ I) x z ∧ z ∈ A ∧ ∀ w ∈ A,
    Conn G (ω ∩ I) x w → Encodable.encode z ≤ Encodable.encode w}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshSlabCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def lowerCrossingBlock (f : V → ℝ) (a b R : ℝ) : Set E :=
  internalEdges G {v | a ≤ f v ∧ f v ≤ b+R} ∩ (internalEdges G {v | b ≤ f v})ᶜ

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def lowerFrontierCell (I J : Set E) (x : V) (S F : Set V) : Set (Set E) :=
  {ω | cluster G (ω ∩ I) x = S ∧ openFrontier G (ω ∩ J) S = F}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteEnergyModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {E : Type*}

def finiteModification (F : Finset E) (B : Set (Set E)) : Set (Set E) :=
  ⋃ σ : Set (F : Set E), (forceOn (F : Set E) (Subtype.val '' σ)) ⁻¹' B

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostField
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

def ghostRate (h x : ℝ≥0) : unitInterval :=
  ⟨ghostKernel h x, ghostKernel_nonneg h.2 x.2, ghostKernel_le_one h x⟩

def ghostFieldLaw {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) : Measure (Set V) :=
  CriticalPercolation.BernoulliProduct.law (fun v => ghostRate h (w v))

instance ghostFieldLaw_probability {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) :
    IsProbabilityMeasure (ghostFieldLaw h w) := by
  unfold ghostFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostBondBK
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V E T : Type*} (G : BondGraph V E) (x : V) (vertex : T → V)

def finiteGhostConnection (m : Set T) : Set (Set E) :=
  {ω | ∃ i ∈ m, Conn G ω x (vertex i)}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def GhostBridgePivotal (ω : Set E) (m n : Set V) (x : V) (e : E) (u v : V) : Prop :=
  e ∈ ω ∧ G e = s(u,v) ∧ Conn G (ω \ {e}) x u ∧ ¬Conn G (ω \ {e}) x v ∧
    Disjoint (cluster G (ω \ {e}) x) m ∧ Disjoint (cluster G (ω \ {e}) x) n ∧
      (ω \ {e}) ∈ DisjointOccurrence (finiteGhostConnection G v id m)
        (finiteGhostConnection G v id n)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def averagedQuarterBridge (p : unitInterval) (x : V) (h : ℝ≥0)
    (e : E) (u v : V) (S : Finset V) : ℝ≥0∞ :=
  ∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
    cluster G (ω \ {e}) x = (S : Set V)}
    ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)
    ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakClusterCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def restrictedSetHit (I : Set E) (A T : Set V) : Set (Set E) :=
  {ω | ∃ v ∈ A, ∃ t ∈ T, Conn G (ω ∩ I) v t}

def peakConnectionCell (I J : Set E) (u w : V) (S T : Set V) : Set (Set E) :=
  {ω | cluster G (ω ∩ I) u=S ∧
    Conn G ((ω ∩ J) ∩ internalEdges G S) u w ∧ Disjoint S T}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HeightMaximumSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def heightMaximumSlice (D : Set E) (f : V → ℝ) (s : ℝ) (n : ℕ) (x : V) : Set (Set E) :=
  (restrictedHit G D x {z | s*((n : ℝ)+1) ≤ f z})ᶜ ∩
    restrictedHit G D x {z | s*n ≤ f z}

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_IntrinsicConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def longConnectionEvent (G : BondGraph V E) (x y : V) (n : ℕ) : Set (Set E) :=
  {ω | Conn G ω x y ∧ n ≤ (openSimpleGraph G ω).dist x y}

def intrinsicSphereEvent (G : BondGraph V E) (x z : V) (j : ℕ) : Set (Set E) :=
  {ω | z ∈ intrinsicSphere G ω x j}

def snapshotFrontierCell (G : BondGraph V E) (x z : V) (j : ℕ)
    (a : Finset V × Finset V) : Set (Set E) :=
  if z ∈ a.2 \ a.1 then ballSnapshotCell G x j a.1 a.2 else ∅

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def newLayerCount (I J : Set E) (A : Set V) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if y ∈ A ∧ ¬Conn G (ω ∩ I) x y ∧ Conn G (ω ∩ J) x y then 1 else 0

end Percolation.BenjaminiSchramm

end

end OAI
end


