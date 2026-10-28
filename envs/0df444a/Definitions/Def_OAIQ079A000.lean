-- Prove2me | Definitions.Def_OAIQ079A000
-- name    : OAIQ079A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:38:18.642847+00:00
-- url     : https://prove2.me/theorems/d65bcd64-894b-4d7d-b0ed-4e6f2f7aa082
-- title:
--   Definitions bundle OAIQ079A000 of the split of OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 735 declarations of OpenAI's Lean: 501 definitions, 8 inductive types or structures, 14 instances and 212 theorems. The definitions and types are `OAI.CubicTorus.ActualBoundaryGraph`, `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.BoundaryFlatAt`, `OAI.CubicTorus.BoundaryNormalChart`, `OAI.CubicTorus.CenteredJacobiChart`, `OAI.CubicTorus.CenteredJacobiChart.ambientGradient`, `OAI.CubicTorus.CenteredJacobiChart.parameter`, `OAI.CubicTorus.CenteredJacobiChart.planarGradient`, `OAI.CubicTorus.CenteredJacobiChart.value`, `OAI.CubicTorus.CenteredJacobiChart.weight`, `OAI.CubicTorus.CenteredJacobiChart.weightedGradient`, `OAI.CubicTorus.CenteredJacobiChart.weightedValue`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.CornerRootData`, `OAI.CubicTorus.CoverC1BoundaryAt`, `OAI.CubicTorus.HasCutoffSaturation`, `OAI.CubicTorus.HasNormalizedCMCCharts`, `OAI.CubicTorus.HasPlanarWeakGradient`, `OAI.CubicTorus.HolderJet`, `OAI.CubicTorus.HolderNear`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.IsPositiveNodalPiece`, `OAI.CubicTorus.LatticeIsometry`, `OAI.CubicTorus.LatticeIsometry.addHom`, `OAI.CubicTorus.LatticeIsometry.normalMap`, `OAI.CubicTorus.LatticeIsometry.pullback`, `OAI.CubicTorus.LatticeIsometry.symm`, `OAI.CubicTorus.LinearCMCEquation`, `OAI.CubicTorus.LinearCMCEquationNear`, `OAI.CubicTorus.MovingCenter.InteriorCenter`, `OAI.CubicTorus.MovingCenter.bundleOrientedExcess`, `OAI.CubicTorus.MovingCenter.cubeBall`, `OAI.CubicTorus.MovingCenter.radialBump`, `OAI.CubicTorus.MovingCenter.radialCore`, `OAI.CubicTorus.MovingCenter.radialSquared`, `OAI.CubicTorus.Nesting.cutoff`, `OAI.CubicTorus.Nesting.ell`, `OAI.CubicTorus.Nesting.lambda`, `OAI.CubicTorus.Nesting.rawWeight` and 469 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CubicTorus_Compactness_BVLocalTranslation`, `CubicTorus_Compactness_BVWeyl`, `CubicTorus_Compactness_GraphMollifier`, `CubicTorus_Curvature_CMCFrameOperator`, `CubicTorus_Curvature_CmcStretch`, `CubicTorus_Curvature_LinearCMCEquation`, `CubicTorus_Curvature_LinearCMCEquationNear`, `CubicTorus_Curvature_NormalCurvatureScalar`, `CubicTorus_Curvature_SurfaceJacobiLocalization`, `CubicTorus_Curvature_TorusC2CMCAt`, `CubicTorus_Estimates_BVAnnulusSelection`, `CubicTorus_Estimates_BVBallCalibration`, `CubicTorus_Estimates_BVBallProbability`, `CubicTorus_Estimates_BVGraphEnergy`, `CubicTorus_Estimates_BVGraphRescaling`, `CubicTorus_Estimates_BVInteriorMultiplier`, `CubicTorus_Estimates_BVLocalScaling`, `CubicTorus_Estimates_BVOneDimensionalHat`, `CubicTorus_Estimates_BVPlanarLocalModels`, `CubicTorus_Estimates_BVRadial`, `CubicTorus_Estimates_BVSharpUpperBound`, `CubicTorus_Estimates_BVTriangleRegion`, `CubicTorus_Estimates_ChainAcceleration`, `CubicTorus_Estimates_ChainMass`, `CubicTorus_Estimates_CirclePeriodize`, `CubicTorus_Estimates_ConeSlopeReciprocalArea`, `CubicTorus_Estimates_CoordinatePlaneRays`, `CubicTorus_Estimates_CorrectedChain`, `CubicTorus_Estimates_DifferenceStep`, `CubicTorus_Estimates_GraphInverseMetric`, `CubicTorus_Estimates_HolderNear`, `CubicTorus_Estimates_LatticeHeightHom`, `CubicTorus_Estimates_PlanarRadialArea`, `CubicTorus_Estimates_PlaneQuadraticWeight`, `CubicTorus_Estimates_PlaneScaleEquiv`, `CubicTorus_Estimates_PlaneWeakGradient`, `CubicTorus_Estimates_RadialSectionArea`, `CubicTorus_Estimates_SliceJensenWeight`, `CubicTorus_Estimates_SmoothScalarSeparatedTrunc`, `CubicTorus_Estimates_SurfaceJet`, `CubicTorus_Estimates_TorusCoordinatePermute`, `CubicTorus_Estimates_TubeCalibration`, `CubicTorus_Estimates_UnitAngle`, `CubicTorus_Main`, `CubicTorus_Profiles_AxisCircleLebesgue`, `CubicTorus_Profiles_CMCSecantSymbol`, `CubicTorus_Profiles_CenteredJacobiChart`, `CubicTorus_Profiles_FirstSeamFunction`, `CubicTorus_Profiles_FourStarScalarGrid`, `CubicTorus_Profiles_MinimizerFirstTransitionTube`, `CubicTorus_Profiles_NestingBaseline`, `CubicTorus_Profiles_NestingEndpointBound`, `CubicTorus_Profiles_NodalTorusScalar`, `CubicTorus_Profiles_NormalMap`, `CubicTorus_Profiles_NormalTransverseLength`, `CubicTorus_Profiles_NormalizedCMCCharts`, `CubicTorus_Profiles_OctantVertex`, `CubicTorus_Profiles_PlanarRadialDownset`, `CubicTorus_Profiles_PlanarWeakGradient`, `CubicTorus_Profiles_SectionExtentBounds`, `CubicTorus_Profiles_SharpSectionWeight`, `CubicTorus_Profiles_SiblingCmcSecant`, `CubicTorus_Profiles_SiblingPlaneCarlemanS`, `CubicTorus_Profiles_TransverseTorus`, `CubicTorus_Reflection_ActualAxialFlux`, `CubicTorus_Reflection_AxialAreaDensity`, `CubicTorus_Reflection_AxialAreaMarginal`, `CubicTorus_Reflection_AxialFluxDensity`, `CubicTorus_Reflection_AxialNormalCalibration`, `CubicTorus_Reflection_AxialSectionCoordinates`, `CubicTorus_Reflection_AxialSectionCorner`, `CubicTorus_Reflection_AxialWeightedHeight`, `CubicTorus_Reflection_BVConeSecondaryFlux`, `CubicTorus_Reflection_BVScaledFlux`, `CubicTorus_Reflection_BVTorusGraphFlux`, `CubicTorus_Reflection_ChamberGlobalFold`, `CubicTorus_Reflection_CoordinateChamber`, `CubicTorus_Reflection_CoordinateReflection`, `CubicTorus_Reflection_CoordinateReflection2`, `CubicTorus_Reflection_DelaunayPeriodicMoments`, `CubicTorus_Reflection_MinimizerAxialCenter`, `CubicTorus_Reflection_RevolutionTangents`, `CubicTorus_Reflection_SiblingAxialProjection`, `CubicTorus_Reflection_TorusCylinders`, `CubicTorus_Regularity_BVBlowupNormalMeasure`, `CubicTorus_Regularity_BVBlowupRigidCovariance`, `CubicTorus_Regularity_BVC1Patch`, `CubicTorus_Regularity_BVColumnHeight`, `CubicTorus_Regularity_BVFlatBlowupRegular`, `CubicTorus_Regularity_BVGraphNormalization`, `CubicTorus_Regularity_BVLipschitzGraph`, `CubicTorus_Regularity_BVMovingOrientedReplacement`, `CubicTorus_Regularity_BVNormalTiltMeasure`, `CubicTorus_Regularity_BVOrientedGraphCost`, `CubicTorus_Regularity_BVPlanarAngularChart`, `CubicTorus_Regularity_BVPlanarEssentialBoundary`, `CubicTorus_Regularity_BVPlaneAreaCoordinates`, `CubicTorus_Regularity_BVRadialVariation`, `CubicTorus_Regularity_BVRegularity`, `CubicTorus_Regularity_BVStationaryDensity`, `CubicTorus_Regularity_BVTangentialBlowup`, `CubicTorus_Regularity_CoverEssentialBoundary`, `CubicTorus_Regularity_FiberPoint`, `CubicTorus_Regularity_GradientCalibration`, `CubicTorus_Regularity_GraphNormalExtensionDivergence`, `CubicTorus_Regularity_MinimalGraphDensity`, `CubicTorus_Regularity_NormalCoverMap`, `CubicTorus_Regularity_NormalFirstVariation`, `CubicTorus_Regularity_NormalMeasureCoordinatePermutation`, `CubicTorus_Regularity_SmoothApproxLip`, `CubicTorus_Regularity_SurfaceGraphBundleMeasure`, `CubicTorus_Regularity_SurfaceH1Tangency`, `CubicTorus_Regularity_SurfaceH1Translation`, `CubicTorus_Regularity_SurfaceNormalReverse`, `CubicTorus_Regularity_TorusC1Boundary`, `CubicTorus_Regularity_TranslateNormal`, `CubicTorus_Regularity_WeightedPerimeter`, `CubicTorus_Rigidity_TwoVolumeNodal`, `CubicTorus_Variation_ComponentDivergence`.
--
--   **Imports.** It imports the published bundle `Def_CubicTorus`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ079A003`; the statements `OAI_CubicTorus_MovingCenter_isMinimizerAt_epsilon_improvement`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay`, `OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic`, `OAI.CubicTorus.NestingGain.integrated_uniform_gain`, `OAI.CubicTorus.Periodic.connected_CMC_strict_sign`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian`, `OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability`, `OAI.CubicTorus.Periodic.isMinimizerAt_normal_support_jets`, `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.Periodic.profile_hessian_of_CMC`, `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero`, `OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter`, `OAI.CubicTorus.actual_centered_graph_phase_patch`, `OAI.CubicTorus.actual_primary_fixed_scale_packets`, `OAI.CubicTorus.actual_primary_offvertex_C1`, `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs`, `OAI.CubicTorus.actual_tangent_secondary_representation`, `OAI.CubicTorus.antitoneOn_isoperimetricProfile_half`, `OAI.CubicTorus.axialSurface_density_eq_flux`, `OAI.CubicTorus.axial_integrated_flux`, `OAI.CubicTorus.axial_integrated_flux_actual`, `OAI.CubicTorus.cmc_linearized_holder_gradient`, `OAI.CubicTorus.cmc_weak_continuous_C1`, `OAI.CubicTorus.continuousOn_isoperimetricProfile`, `OAI.CubicTorus.corner_grid_202`, `OAI.CubicTorus.corner_grid_269`, `OAI.CubicTorus.corner_grid_332`, `OAI.CubicTorus.critical_baseline_positive`, `OAI.CubicTorus.critical_nesting_contradiction`, `OAI_CubicTorus_cylinderRatio_first`, `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution`, `OAI.CubicTorus.forced_cmc_linearized_holder_gradient`, `OAI.CubicTorus.isMinimizerAt_CMC_sign`, `OAI_CubicTorus_isMinimizerAt_H1_jacobi_equation`, `OAI.CubicTorus.isMinimizerAt_antitoneOn_axialSectionArea`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_axial_boundary_null`, `OAI.CubicTorus.isMinimizerAt_axial_endFlux`, `OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter`, `OAI.CubicTorus.isMinimizerAt_axial_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign`, `OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae`, `OAI.CubicTorus.isMinimizerAt_center_normal_unique`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus`, `OAI.CubicTorus.isMinimizerAt_centered_holder_CMC`, `OAI.CubicTorus.isMinimizerAt_centered_multiplier`, `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit`, `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry`, `OAI.CubicTorus.isMinimizerAt_continuous_axial_sections`, `OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_bounds`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_cylinder_interval_standard`, `OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube`, `OAI.CubicTorus.isMinimizerAt_density_pos`, `OAI_CubicTorus_isMinimizerAt_exists_coordinate_symmetries_measurable`, `OAI_CubicTorus_isMinimizerAt_first_transition_any_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_first_transition_atMostOne_axis`, `OAI.CubicTorus.isMinimizerAt_first_transition_corner_excluded`, `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices`, `OAI.CubicTorus.isMinimizerAt_four_corner_necessary_data`, `OAI_CubicTorus_isMinimizerAt_general_positive_nodal_not_disjoint`, `OAI.CubicTorus.isMinimizerAt_global_normal`, `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small`, `OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones`, `OAI_CubicTorus_isMinimizerAt_mean_curvature_bound`, `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical`, `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound`, `OAI_CubicTorus_isMinimizerAt_missing_neighbor_area_flux`, `OAI.CubicTorus.isMinimizerAt_moving_limit_comparison`, `OAI_CubicTorus_isMinimizerAt_nesting_area_bound`, `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system`, `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal`, `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy`, `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero`, `OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative`, `OAI_CubicTorus_isMinimizerAt_normal_graph_chart`, `OAI.CubicTorus.isMinimizerAt_normal_linear_chart`, `OAI_CubicTorus_isMinimizerAt_normal_strong_minimum`, `OAI_CubicTorus_isMinimizerAt_normal_unique`, `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball`, `OAI.CubicTorus.isMinimizerAt_openRepresentative_ae`, `OAI.CubicTorus.isMinimizerAt_oriented_CMC_charts`, `OAI.CubicTorus.isMinimizerAt_paired_blowup`, `OAI.CubicTorus.isMinimizerAt_perimeter_lower_density`, `OAI.CubicTorus.isMinimizerAt_perimeter_upper_density`, `OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary`, `OAI_CubicTorus_isMinimizerAt_primary_halfspace`, `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_second_endpoint_linear_bound`, `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density`, `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_small_slab_standard`, `OAI.CubicTorus.isMinimizerAt_smaller_side_double_vertices_vacant`, `OAI.CubicTorus.isMinimizerAt_smooth_CMC`, `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_spherical_standard_ball`, `OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection`, `OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup`, `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible`, `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation`, `OAI.CubicTorus.isMinimizerAt_tubular_sections`, `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux`, `OAI_CubicTorus_isMinimizerAt_two_occupied_vertices_bottom_flux`, `OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube`, `OAI.CubicTorus.isMinimizerAt_umbilic_local_sphere`, `OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary`, `OAI.CubicTorus.isMinimizerAt_zero_component_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_zero_component_multiplier_ne_zero`, `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_local_normal`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_not_preconnected`, `OAI.CubicTorus.isoperimetricProfile_cylinder_interval`, `OAI.CubicTorus.isoperimetricProfile_power_upper_support`, `OAI.CubicTorus.isoperimetricProfile_second_transition`, `OAI.CubicTorus.isoperimetricProfile_slab_local_min`, `OAI.CubicTorus.minimizing_planar_product_halfplane`, `OAI.CubicTorus.monotoneOn_isoperimetricProfile_half`, `OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball`, `OAI.CubicTorus.nesting_scalar_contradiction`, `OAI.CubicTorus.normal_transverse_near_reflection_height`, `OAI.CubicTorus.planar_radial_both_extents`, `OAI.CubicTorus.planar_radial_isoperimetric`, `OAI.CubicTorus.planar_radial_strip_gain_first`, `OAI.CubicTorus.planar_radial_strip_gain_second`, `OAI.CubicTorus.profile_ge_second_chord`, `OAI.CubicTorus.profile_upper_support_power_secant`, `OAI.CubicTorus.profile_upper_support_slope_nonneg`, `OAI.CubicTorus.profile_upper_support_slope_nonpos`, `OAI.CubicTorus.strict_C1_cone_halfspace`, `OAI.CubicTorus.strict_normal_component_ne_zero_ae`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_baseline_positive_left`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_102_106`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_106_110`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_110_114`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_114_118`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_118_122`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_122_126`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_126_130`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_130_134`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_134_138` and `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_138_142`; the proofs of `OAI_CubicTorus_MovingCenter_isMinimizerAt_epsilon_improvement`, `OAI.CubicTorus.NestingGain.integrated_uniform_gain`, `OAI.CubicTorus.Periodic.connected_CMC_strict_sign`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab`, `OAI.CubicTorus.SmallStandardRegion.bv_data`, `OAI.CubicTorus.actual_centered_graph_phase_patch`, `OAI.CubicTorus.axialSurface_density_eq_flux`, `OAI.CubicTorus.axial_integrated_flux`, `OAI.CubicTorus.axial_integrated_flux_actual`, `OAI.CubicTorus.cmc_weak_continuous_C1`, `OAI.CubicTorus.corner_grid_202`, `OAI.CubicTorus.corner_grid_269`, `OAI.CubicTorus.corner_grid_332`, `OAI_CubicTorus_cylinderRatio_first`, `OAI.CubicTorus.delaunay_chamber_monotone_mean`, `OAI.CubicTorus.fourCorner_normalized_contradiction`, `OAI_CubicTorus_isMinimizerAt_H1_jacobi_equation`, `OAI.CubicTorus.isMinimizerAt_axial_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_center_normal_unique`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_continuous_axial_sections`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_bounds`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_density_pos`, `OAI_CubicTorus_isMinimizerAt_exists_coordinate_symmetries_measurable`, `OAI_CubicTorus_isMinimizerAt_first_transition_any_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_first_transition_atMostOne_axis`, `OAI.CubicTorus.isMinimizerAt_first_transition_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_general_positive_nodal_not_disjoint`, `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small`, `OAI_CubicTorus_isMinimizerAt_mean_curvature_bound`, `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound`, `OAI_CubicTorus_isMinimizerAt_missing_neighbor_area_flux`, `OAI_CubicTorus_isMinimizerAt_nesting_area_bound`, `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal`, `OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative`, `OAI_CubicTorus_isMinimizerAt_normal_graph_chart`, `OAI_CubicTorus_isMinimizerAt_normal_strong_minimum`, `OAI_CubicTorus_isMinimizerAt_normal_unique`, `OAI.CubicTorus.isMinimizerAt_oriented_CMC_charts`, `OAI_CubicTorus_isMinimizerAt_primary_halfspace`, `OAI_CubicTorus_isMinimizerAt_second_transition_standard`, `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection`, `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation`, `OAI_CubicTorus_isMinimizerAt_two_occupied_vertices_bottom_flux`, `OAI.CubicTorus.isMinimizerAt_umbilic_local_sphere`, `OAI.CubicTorus.isMinimizerAt_zero_component_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_local_normal`, `OAI.CubicTorus.planar_radial_both_extents`, `OAI.CubicTorus.planar_radial_isoperimetric`, `OAI.CubicTorus.planar_radial_strip_gain_first`, `OAI.CubicTorus.planar_radial_strip_gain_second`, `OAI.CubicTorus.profile_upper_support_slope_nonneg`, `OAI.CubicTorus.profile_upper_support_slope_nonpos`, `OAI.CubicTorus.secondCorner_endpoint_contradiction`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_baseline_positive_left`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_102_106`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_106_110`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_110_114`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_114_118`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_118_122`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_122_126`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_126_130`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_130_134`, `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_134_138` and `OAI_ReusedScalar205_CubicTorus_Scalar_Cert_positive_138_142`.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_CubicTorus

section
-- module Solutions.OAIQ079_CT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma continuous_quotientMap : Continuous quotientMap := by
  unfold quotientMap
  fun_prop

lemma measurable_quotientMap : Measurable quotientMap := continuous_quotientMap.measurable

lemma measurableSet_fundamentalCube : MeasurableSet fundamentalCube := by
  unfold fundamentalCube
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun x : Cover => x i) := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

lemma volume_fundamentalCube : volume fundamentalCube = 1 := by
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage measurableSet_fundamentalCube.nullMeasurableSet
  have heq : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
      Set.pi univ (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
    ext x
    simp [fundamentalCube]
  rw [heq] at hm
  have hv : volume (Set.pi univ (fun _ : Fin 3 => Ico (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_pi_Ico]
    norm_num
  exact hm.symm.trans hv

lemma torusVolume_univ : torusVolume univ = 1 := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap MeasurableSet.univ]
  simp [volume_fundamentalCube]

instance instIsProbabilityMeasureTorusTorusVolume : IsProbabilityMeasure torusVolume := ⟨torusVolume_univ⟩

lemma continuous_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (divergence F) := by
  unfold divergence
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i).continuous.comp
    ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)

def characteristic (E : Set Torus) (x : Torus) : ℝ := E.indicator (fun _ => 1) x

end CubicTorus

namespace CubicTorus

abbrev ProductTorus := Fin 3 → AddCircle (1 : ℝ)

instance circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  simp

end CubicTorus

namespace CubicTorus

lemma quotientMap_add (x y : Cover) : quotientMap (x + y) = quotientMap x + quotientMap y := by
  ext i
  simp [quotientMap]

def representative (x : Torus) : Cover :=
  WithLp.toLp 2 (fun i => ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ))

lemma measurable_representative : Measurable representative := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.measurable.comp
  apply Measurable.of_eval
  intro i
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma quotientMap_representative (x : Torus) : quotientMap (representative x) = x := by
  ext i
  simp [quotientMap, representative]

lemma quotientMap_surjective : Function.Surjective quotientMap :=
  fun x => ⟨representative x, quotientMap_representative x⟩

lemma same_quotient_lattice {x y : Cover} (h : quotientMap x = quotientMap y) :
    ∃ n : Fin 3 → ℤ, x = y + latticeVector n := by
  have hh : ∀ i : Fin 3, ∃ n : ℤ, (n : ℝ) = x i - y i := by
    intro i
    have hi : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      have he := congrArg (fun z : Torus => z i) h
      simpa [quotientMap, AddCircle.coe_sub] using sub_eq_zero.mpr he
    simpa only [zsmul_eq_mul, mul_one] using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi)
  choose n hn using hh
  refine ⟨n, ?_⟩
  ext i
  simp only [PiLp.add_apply, latticeVector]
  linarith [hn i]

lemma periodic_representative {Y : Type*} {f : Cover → Y}
    (hf : ∀ n x, f (x + latticeVector n) = f x) (x : Cover) :
    f (representative (quotientMap x)) = f x := by
  obtain ⟨n, hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  rw [hn, hf]

lemma divergence_translate (F : Cover → Cover) (a x : Cover) :
    divergence (fun y => F (y + a)) x = divergence F (x + a) := by
  simp only [divergence, fderiv_comp_add_right]

lemma divergence_periodic {F : Cover → Cover}
    (hf : ∀ n x, F (x + latticeVector n) = F x) (n : Fin 3 → ℤ) (x : Cover) :
    divergence F (x + latticeVector n) = divergence F x := by
  have he : (fun y : Cover => F (y + latticeVector n)) = F := funext (hf n)
  rw [← divergence_translate, he]

end CubicTorus

namespace CubicTorus

lemma periodic_bounded {Y : Type*} [SeminormedAddGroup Y] {f : Cover → Y}
    (hf : Continuous f) (hp : ∀ n x, f (x + latticeVector n) = f x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  let K : Set Cover := (WithLp.toLp 2) '' (Icc (0 : Fin 3 → ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [← periodic_representative hp x]
  apply (hM _ ?_).trans (le_max_left _ _)
  refine ⟨fun i => ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i) : ℝ), ?_, rfl⟩
  constructor
  · intro i
    exact ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i)).property.1
  · intro i
    exact le_of_lt (by simpa using ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i)).property.2)

lemma fderiv_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Cover → Y} (hp : ∀ n x, f (x + latticeVector n) = f x)
    (n : Fin 3 → ℤ) (x : Cover) :
    fderiv ℝ f (x + latticeVector n) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right (latticeVector n)]
  exact congrArg (fun g : Cover → Y => fderiv ℝ g x) (funext (hp n))

instance finiteMeasure_liftSet (E : Set Torus) :
    IsFiniteMeasure (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono inter_subset_left)
  rw [volume_fundamentalCube]
  exact ENNReal.one_lt_top

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

def mollifier (n : ℕ) : ContDiffBump (0 : Cover) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma locallyIntegrable_of_bounded {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) : LocallyIntegrable g volume := by
  apply (continuous_const : Continuous (fun _ : Cover => (1 : ℝ))).locallyIntegrable.mono
    hg.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_one] using hb x

end CubicTorus

namespace CubicTorus

lemma quotientMap_latticeVector (n : Fin 3 → ℤ) : quotientMap (latticeVector n) = 0 := by
  ext i
  simp [quotientMap, latticeVector]

lemma measurable_characteristic {E : Set Torus} (hE : MeasurableSet E) :
    Measurable (characteristic E) := measurable_const.indicator hE

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicTorus

lemma characteristic_dichotomy (E : Set Torus) (x : Torus) :
    characteristic E x = 0 ∨ characteristic E x = 1 := by
  classical
  by_cases hx : x ∈ E <;> simp [characteristic, hx]

lemma characteristic_bound (E : Set Torus) (x : Torus) : |characteristic E x| ≤ 1 := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

lemma integrable_characteristic {E : Set Torus} (hE : MeasurableSet E) :
    Integrable (characteristic E) torusVolume := (integrable_const 1).indicator hE

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

def closedFundamentalCube : Set Cover :=
  (WithLp.toLp 2) '' (Icc (0 : Fin 3 → ℝ) 1)

lemma isCompact_closedFundamentalCube : IsCompact closedFundamentalCube :=
  isCompact_Icc.image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous

abbrev CompactCell := closedFundamentalCube

instance instCompactSpaceElemCoverCompactCell : CompactSpace CompactCell := isCompact_iff_compactSpace.mp isCompact_closedFundamentalCube

lemma representative_mem_closedCube (x : Torus) : representative x ∈ closedFundamentalCube := by
  refine ⟨fun i => ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ), ?_, rfl⟩
  constructor
  · intro i
    exact ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.1
  · intro i
    exact le_of_lt (by simpa using ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.2)

def cubeRepresentative (x : Torus) : CompactCell := ⟨representative x, representative_mem_closedCube x⟩

lemma measurable_cubeRepresentative : Measurable cubeRepresentative :=
  measurable_representative.subtype_mk

lemma integrable_cubeEval (f : BoundedContinuousFunction CompactCell ℝ) :
    Integrable (fun x => f (cubeRepresentative x)) torusVolume :=
  Integrable.of_bound (f.continuous.measurable.comp measurable_cubeRepresentative).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall fun x => f.norm_coe_le_norm (cubeRepresentative x))

def cubeToL1 (f : BoundedContinuousFunction CompactCell ℝ) : Lp ℝ 1 torusVolume :=
  (integrable_cubeEval f).toL1 (fun x => f (cubeRepresentative x))

def characteristicL1 (E : Set Torus) (hE : MeasurableSet E) : Lp ℝ 1 torusVolume :=
  (integrable_characteristic hE).toL1 (characteristic E)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

def isoperimetricProfile (V : ℝ) : ℝ :=
  (sInf {p : ℝ≥0∞ | ∃ E : Set Torus,
    FinitePerimeter E ∧ torusVolume E = ENNReal.ofReal V ∧ perimeter E = p}).toReal / 2

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_periodic_continuous {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) : IntegrableOn f fundamentalCube := by
  let : IsFiniteMeasure (volume.restrict fundamentalCube) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_fundamentalCube]; norm_num⟩
  obtain ⟨M, _, hM⟩ := periodic_bounded hf hp
  exact Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)

lemma gradient_contDiff {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) := by
  exact (InnerProductSpace.toDual ℝ Cover).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp))

lemma gradient_periodic {f : Cover → ℝ}
    (hp : ∀ n x, f (x + latticeVector n) = f x) (n : Fin 3 → ℤ) (x : Cover) :
    gradient f (x + latticeVector n) = gradient f x := by
  unfold gradient
  rw [fderiv_periodic hp]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def gradientCalibration (f : Cover → ℝ) (ε : ℝ) (x : Cover) : Cover :=
  -(Real.sqrt (⟪gradient f x, gradient f x⟫ + ε ^ 2))⁻¹ • gradient f x

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

abbrev NormalSphere := {v : Cover // ‖v‖ = 1}

instance instCompactSpaceNormalSphere : CompactSpace NormalSphere := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact ((WithLp.toLp 2) '' (Icc (-1 : Fin 3 → ℝ) 1)) :=
    isCompact_Icc.image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hK.of_isClosed_subset (isClosed_eq continuous_norm continuous_const)
  intro v hv
  change ‖v‖ = 1 at hv
  refine ⟨WithLp.ofLp v, ⟨?_, ?_⟩, rfl⟩
  · intro i
    have hh : |v i| ≤ 1 := by simpa only [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i
    exact (abs_le.mp hh).1
  · intro i
    have hh : |v i| ≤ 1 := by simpa only [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i
    exact (abs_le.mp hh).2

abbrev NormalBundle := CompactCell × NormalSphere

def normalizedVector (v : Cover) : Cover :=
  if v = 0 then EuclideanSpace.single 0 1 else ‖v‖⁻¹ • v

lemma normalizedVector_norm (v : Cover) : ‖normalizedVector v‖ = 1 := by
  unfold normalizedVector
  split_ifs with hv
  · simp
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

def normalTest (F : Cover → Cover) (hF : Continuous F) : C(NormalBundle, ℝ) :=
  ⟨fun z ↦ ⟪(z.2 : Cover), F (z.1 : Cover)⟫,
    (continuous_subtype_val.comp continuous_snd).inner
      (hF.comp (continuous_subtype_val.comp continuous_fst))⟩

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

def IsNormalMeasure (E : Set Torus) (μ : FiniteMeasure NormalBundle) : Prop :=
  (μ.mass : ℝ) = (perimeter E).toReal ∧
  ∀ (F : Cover → Cover) (hF : AdmissibleField F),
    (∫ z, normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x

end CubicTorus

open scoped RealInnerProductSpace

namespace CubicTorus
open Filter
open scoped Topology

def coordinateMove (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) : Cover :=
  x + (t * f x) • EuclideanSpace.single i 1

def coordinateMoveDeriv (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) :
    Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight (t • EuclideanSpace.single i 1)

def coordinateJacobian (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x : Cover) : ℝ :=
  1 + t * fderiv ℝ f x (EuclideanSpace.single i 1)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

def coordinatePullback (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (G : Cover → Cover)
    (x : Cover) : Cover :=
  coordinateJacobian i f t x • G (coordinateMove i f t x) -
    (t * fderiv ℝ f x (G (coordinateMove i f t x))) • EuclideanSpace.single i 1

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace

namespace CubicTorus

def fiberPoint (i : Fin 3) (x : Cover) (u : ℝ) : Cover :=
  x + (u - x i) • EuclideanSpace.single i 1

end CubicTorus

namespace CubicTorus

def coordinateRegion (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (E : Set Torus) : Set Torus :=
  representative ⁻¹' (coordinateMove i f t '' (fundamentalCube ∩ quotientMap ⁻¹' E))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def coordinateCofactor (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (x n : Cover) : Cover :=
  coordinateJacobian i f t x • n -
    (t * ⟪n, EuclideanSpace.single i 1⟫) • gradient f x

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x n : Cover) : Cover :=
  fderiv ℝ f x (EuclideanSpace.single i 1) • n -
    ⟪n, EuclideanSpace.single i 1⟫ • gradient f x

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def directionalFlux (E : Set Torus) (i : Fin 3) (f : Cover → ℝ) : ℝ :=
  ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    fderiv ℝ f x (EuclideanSpace.single i 1)

structure WallVariation where
  coordinate : Fin 3
  function : Cover → ℝ
  bound : NNReal
  smooth : ContDiff ℝ (⊤ : ℕ∞) function
  periodic : ∀ n x, function (x + latticeVector n) = function x
  derivative_bound : ∀ x, ‖fderiv ℝ function x‖₊ ≤ bound
  faces : ∀ x, x coordinate = 0 ∨ x coordinate = 1 → function x = 0

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def doubleRegion (a b : WallVariation) (t s : ℝ) (E : Set Torus) : Set Torus :=
  coordinateRegion b.coordinate b.function s (coordinateRegion a.coordinate a.function t E)

def doubleCofactor (a b : WallVariation) (t s : ℝ) (x n : Cover) : Cover :=
  coordinateCofactor b.coordinate b.function s (coordinateMove a.coordinate a.function t x)
    (coordinateCofactor a.coordinate a.function t x n)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def doubleVelocityCoefficient (a b : WallVariation) (k t : ℝ) (x n : Cover) : Cover :=
  coordinateNormalVelocity a.coordinate a.function x n +
    k • coordinateNormalVelocity b.coordinate b.function
      (coordinateMove a.coordinate a.function t x)
      (n + t • coordinateNormalVelocity a.coordinate a.function x n)

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : WallVariation) : ℝ :=
  ∫ z, ⟪(z.2 : Cover), coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫
    ∂(μ : Measure NormalBundle)

end CubicTorus

namespace CubicTorus

def wallCutoff (i : Fin 3) (x : Cover) : ℝ := (1 - Real.cos (2 * Real.pi * x i)) / 2

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

def tangentialDivergence (F : Cover → Cover) (x n : Cover) : ℝ :=
  divergence F x - ⟪n, fderiv ℝ F x n⟫

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma latticeVector_add (m n : Fin 3 → ℤ) : latticeVector (m + n) = latticeVector m + latticeVector n := by
  ext i
  simp [latticeVector]

lemma latticeVector_zero : latticeVector 0 = 0 := by
  ext i
  simp [latticeVector]

lemma finite_lattice_support_near {Y : Type*} [Zero Y] {f : Cover → Y}
    (hf : HasCompactSupport f) (a : Cover) :
    ∃ s : Finset (Fin 3 → ℤ), ∀ x ∈ Metric.ball a 1, ∀ n ∉ s,
      f (x + latticeVector n) = 0 := by
  classical
  obtain ⟨R, _, hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (R + ‖a‖ + 1)
  let S : Set (Fin 3 → ℤ) := {n | ∀ i, n i ∈ Icc (-(N : ℤ)) N}
  have hS : S.Finite := Set.Finite.pi' (fun _ ↦ Set.finite_Icc (-(N : ℤ)) N)
  refine ⟨hS.toFinset, ?_⟩
  intro x hx n hn
  by_contra hnonzero
  have hmem : x + latticeVector n ∈ tsupport f := subset_tsupport f hnonzero
  have hnx : ‖x‖ ≤ ‖a‖ + 1 := by
    have hh := norm_add_le (x - a) a
    rw [sub_add_cancel] at hh
    have hx' : ‖x - a‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    linarith
  have hln : ‖latticeVector n‖ < N := by
    have hh := norm_sub_le (x + latticeVector n) x
    rw [add_sub_cancel_left] at hh
    exact lt_of_le_of_lt (hh.trans (add_le_add (hR _ hmem) hnx)) (by linarith)
  apply hn
  rw [Set.Finite.mem_toFinset]
  intro i
  have hc : |(n i : ℝ)| < N := by
    have hh : |(n i : ℝ)| ≤ ‖latticeVector n‖ := by
      simpa only [latticeVector, Real.norm_eq_abs] using
        (PiLp.norm_apply_le (latticeVector n) i)
    exact hh.trans_lt hln
  constructor
  · exact_mod_cast (abs_le.mp hc.le).1
  · exact_mod_cast (abs_le.mp hc.le).2

def latticePeriodize {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y]
    (f : Cover → Y) (x : Cover) : Y := ∑' n : Fin 3 → ℤ, f (x + latticeVector n)

lemma latticePeriodize_periodic {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y]
    (f : Cover → Y) (m : Fin 3 → ℤ) (x : Cover) :
    latticePeriodize f (x + latticeVector m) = latticePeriodize f x := by
  unfold latticePeriodize
  calc
    _ = ∑' n : Fin 3 → ℤ, f (x + latticeVector (n + m)) := by
      apply tsum_congr
      intro n
      rw [latticeVector_add]
      congr 1
      abel
    _ = _ := (Equiv.addRight m).tsum_eq (fun n ↦ f (x + latticeVector n))

lemma latticePeriodize_contDiff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Cover → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (latticePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨s, hs⟩ := finite_lattice_support_near hs a
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∑ n ∈ s, f (x + latticeVector n)) :=
    ContDiff.sum fun n _ ↦ hf.comp (contDiff_id.add contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1)] with x hx
  exact tsum_eq_sum (hs x hx)

end CubicTorus

namespace CubicTorus

def coordinateBox (r : ℝ) : Set Torus :=
  {x | ∀ i : Fin 3, ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) < r}

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def sublevelCutoff (q : Cover → ℝ) (t ε : ℝ) (x : Cover) : ℝ :=
  Real.smoothTransition ((t - q x) / ε)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def cubeCenter : Cover := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def cubeBall (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball cubeCenter r

def radialBump : ContDiffBump cubeCenter where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def radialCore (x : Cover) : ℝ := radialBump x * (1 - ‖x - cubeCenter‖ ^ 2)

def radialSquared (x : Cover) : ℝ := 1 - latticePeriodize radialCore x

end CubicTorus

namespace CubicTorus

def localRadialSquared (a : Torus) (x : Cover) : ℝ :=
  radialSquared (x + representative (quotientMap cubeCenter - a))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def volumeSupport (E : Set Torus) : Set Torus := (torusVolume.restrict E).support

def openRepresentative (E : Set Torus) : Set Torus := (volumeSupport Eᶜ)ᶜ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalProjection (z : NormalBundle) : Torus := quotientMap z.1

lemma normalProjection_continuous : Continuous normalProjection :=
  continuous_quotientMap.comp (continuous_subtype_val.comp continuous_fst)

def spatialNormalMeasure (μ : FiniteMeasure NormalBundle) : FiniteMeasure Torus :=
  μ.map normalProjection

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

def shortestLift (x : Torus) : Cover := representative (x + quotientMap cubeCenter) - cubeCenter

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torus_compactSpace : CompactSpace Torus :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ))).symm.compactSpace

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def reverseNormal (z : NormalBundle) : NormalBundle :=
  (z.1, ⟨-(z.2 : Cover), by simpa only [norm_neg] using z.2.property⟩)

lemma continuous_reverseNormal : Continuous reverseNormal := by
  exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalExcess (σ : FiniteMeasure Torus) (N : Torus → Cover) (a : Torus)
    (n : Cover) (r : ℝ) : ℝ :=
  (∫ x in Metric.closedBall a r, ‖N x - n‖ ^ 2 ∂(σ : Measure Torus)) / r ^ 2

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_UnitAngle
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

def unitAngle (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)

def radialCurve (r : ℝ → ℝ) (t : ℝ) : ℂ := (r t : ℂ)*unitAngle t

end CubicTorus

end
end

section

noncomputable section
open Set Complex
open scoped Topology Real
namespace CubicTorus

def complexSquareGauge (z : ℂ) : ℝ := max |z.re| |z.im|
def complexFold (z : ℂ) : ℂ := ⟨|z.re|,|z.im|⟩
def unitSquareScale (t : ℝ) : ℝ := 1/(2*complexSquareGauge (unitAngle t))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallProbability
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [μ.IsAddHaarMeasure]

def ballProbability (δ : ℝ) : Measure X :=
  (μ (closedBall 0 δ))⁻¹ • μ.restrict (closedBall 0 δ)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVTangentialBlowup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalOscillation (σ : FiniteMeasure Torus) (N : Torus → Cover) (c : Torus)
    (n : Cover) (r : ℝ) : ℝ :=
  (∫ x in Metric.closedBall c r, ‖N x - n‖ ∂(σ : Measure Torus)) / r ^ 2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

def orderDefect (E : Set Torus) (a : Torus) (x : Torus) : ℝ :=
  characteristic E x * (1 - characteristic E (x - a))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def BoundaryFlatAt (B : Set Torus) (c : Torus) (n : Cover) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ y ∈ B,
    dist y c < r → |⟪n, shortestLift (y - c)⟫| < ε * r

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def normalCap (c : Torus) (n : Cover) (r h : ℝ) : Set Torus :=
  {x | dist x c < r ∧ h < ⟪n, shortestLift (x - c)⟫}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialDensityWeight (a : Cover) (r ε : ℝ) (x : Cover) : ℝ :=
  sublevelCutoff (fun y ↦ ‖y - a‖ ^ 2) (r ^ 2) ε x

def radialDensitySlope (a : Cover) (r ε : ℝ) (x : Cover) : ℝ :=
  deriv Real.smoothTransition ((r ^ 2 - ‖x - a‖ ^ 2) / ε) / ε

def radialDensityField (a : Cover) (r ε : ℝ) (x : Cover) : Cover :=
  radialDensityWeight a r ε x • (x - a)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialDensityMass (μ : FiniteMeasure NormalBundle) (a : Cover) (ε r : ℝ) : ℝ :=
  ∫ z, radialDensityWeight a r ε z.1 ∂(μ : Measure NormalBundle)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def cellBallMass (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ) : ℝ :=
  (μ : Measure NormalBundle).real {z | (z.1 : Cover) ∈ Metric.ball a r}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def halfspaceIndicator (n : Cover) (x : Cover) : ℝ :=
  {y | ⟪n, y⟫ < 0}.indicator (fun _ ↦ 1) x

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_of_notMem_tsupport {F : Cover → Cover} {x : Cover}
    (hx : x ∉ tsupport F) : divergence F x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport ℝ hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalRotation (n : Cover) : Cover ≃ₗᵢ[ℝ] Cover :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.single 0 1 - n))ᗮ

lemma normalRotation_axis {n : Cover} (hn : ‖n‖ = 1) :
    normalRotation n (EuclideanSpace.single 0 1) = n := by
  apply Submodule.reflection_sub
  simpa using hn.symm

def normalProductChart (n : Cover) : (ℝ × (Fin 2 → ℝ)) ≃ᵐ Cover :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))).trans (normalRotation n).toMeasurableEquiv

lemma normalProductChart_apply (n : Cover) (t : ℝ) (y : Fin 2 → ℝ) :
    normalProductChart n (t, y) = normalRotation n (WithLp.toLp 2 (Fin.cons t y)) := by
  simp [normalProductChart, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero']

lemma normalProductChart_decompose {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    normalProductChart n (t, y) = t • n + normalProductChart n (0, y) := by
  rw [normalProductChart_apply, normalProductChart_apply]
  have he : (WithLp.toLp 2 (Fin.cons t y) : Cover) =
      t • EuclideanSpace.single 0 1 + WithLp.toLp 2 (Fin.cons 0 y) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [he, map_add, map_smul, normalRotation_axis hn]

lemma normalProductChart_inner {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    ⟪n, normalProductChart n (t, y)⟫ = t := by
  rw [normalProductChart_apply]
  conv_lhs => lhs; rw [← normalRotation_axis hn]
  rw [(normalRotation n).inner_map_map]
  simp [EuclideanSpace.inner_single_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def tangentPart (ν n : Cover) : Cover := n - ⟪ν, n⟫ • ν

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialHeightCutoff (a : Cover) (r : ℝ) : Cover → ℝ :=
  radialDensityWeight a (2 * r) (3 * r ^ 2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def normalPlaneEmbedding (n : Cover) (y : Plane) : Cover :=
  normalProductChart n (0, WithLp.ofLp y)

lemma normalPlaneEmbedding_norm (n : Cover) (y : Plane) :
    ‖normalPlaneEmbedding n y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalPlaneEmbedding, normalProductChart_apply, (normalRotation n).norm_map]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVLipschitzGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalPlaneProjection (n v : Cover) : Cover := v - ⟪n, v⟫ • n

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTiltMeasure (σ : FiniteMeasure Torus) (N : Torus → Cover) (n : Cover) : Measure Torus :=
  (σ : Measure Torus).withDensity (fun x ↦ ENNReal.ofReal (‖N x - n‖ ^ 2))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalPlaneLinearIsometry (n : Cover) : Plane →ₗᵢ[ℝ] Cover where
  toFun := normalPlaneEmbedding n
  map_add' y z := by
    simp only [normalPlaneEmbedding, normalProductChart_apply]
    rw [← map_add]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' t y := by
    simp only [normalPlaneEmbedding, normalProductChart_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  norm_map' := normalPlaneEmbedding_norm n

lemma normalPlaneEmbedding_inner {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    ⟪n, normalPlaneEmbedding n y⟫ = 0 := normalProductChart_inner hn 0 _

def normalGraph (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover :=
  normalPlaneEmbedding n y + g y • n

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

def planarMollifier (i : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((i : ℝ) + 1)
  rOut := 2 / ((i : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeProductCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans Complex.equivRealProdCLM

def planeSquare (R : ℝ) : Set Plane :=
  planeProductCoordinates ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def planarCoordinateDivergence (X Y : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVTriangleRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def coordinateTriangle (b l u : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Ioc 0 b ∧ z.1 ∈ Ioc (z.2*l) (z.2*u)}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

abbrev PrismCoordinates := ℝ × (ℝ × ℝ)

def prismCoordinateDivergence (T X Y : PrismCoordinates → ℝ) (z : PrismCoordinates) : ℝ :=
  fderiv ℝ T z (1,(0,0)) + fderiv ℝ X z (0,(1,0)) + fderiv ℝ Y z (0,(0,1))

def coordinatePrism (a c b l u : ℝ) : Set PrismCoordinates :=
  Ioc a c ×ˢ coordinateTriangle b l u

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def prismRadialFlux (X Y : PrismCoordinates → ℝ) (a c b l u : ℝ) : ℝ :=
  ∫ t in a..c, ∫ s in (0 : ℝ)..b,
    (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))

def prismClosingFlux (T Y : PrismCoordinates → ℝ) (a c b l u : ℝ) : ℝ :=
  (∫ z in coordinateTriangle b l u, T (c,z)-T (a,z)) +
    (∫ t in a..c, ∫ x in (b*l)..(b*u), Y (t,(x,b)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def gluedRegion (E F B : Set Torus) : Set Torus := (E \ B) ∪ (F ∩ B)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_hasFDerivAt {n : Cover} {g : Plane → ℝ} {y : Plane}
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (normalGraph n g)
      ((normalPlaneLinearIsometry n).toContinuousLinearMap + (fderiv ℝ g y).smulRight n) y := by
  exact (normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt.add
    (hg.hasFDerivAt.smul_const n)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

instance plane_hausdorff_two_haar : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure 2 : Measure Plane) := by
  simpa only [finrank_euclideanSpace_fin, Nat.cast_ofNat] using
    (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Plane))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeAreaFactor : ℝ≥0 := Measure.addHaarScalarFactor
  (volume : Measure Plane) (Measure.hausdorffMeasure 2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalPlaneCoordinates (n : Cover) : Cover →L[ℝ] Plane :=
  (normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint

lemma normalPlaneCoordinates_embedding (n : Cover) (y : Plane) :
    normalPlaneCoordinates n (normalPlaneEmbedding n y) = y := by
  apply ext_inner_left ℝ
  intro z
  rw [normalPlaneCoordinates, ContinuousLinearMap.adjoint_inner_right]
  exact (normalPlaneLinearIsometry n).inner_map_map z y

lemma normalPlaneCoordinates_normal {n : Cover} (hn : ‖n‖ = 1) :
    normalPlaneCoordinates n n = 0 := by
  apply ext_inner_left ℝ
  intro z
  rw [normalPlaneCoordinates, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn z)

lemma normalPlaneCoordinates_reconstruct {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v) + ⟪n, v⟫ • n = v := by
  obtain ⟨⟨t, y⟩, rfl⟩ := (normalProductChart n).surjective v
  rw [normalProductChart_inner hn]
  have he : normalProductChart n (t, y) =
      normalPlaneEmbedding n (WithLp.toLp 2 y) + t • n := by
    rw [normalProductChart_decompose hn]
    simp only [normalPlaneEmbedding, add_comm]
  rw [he]
  simp only [map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalColumnHeight (U : Set Torus) (a : Torus) (n : Cover) (r : ℝ) (y : Plane) : ℝ :=
  (∫ t in Icc (-r / 4) (r / 4),
    characteristic U (a + quotientMap (normalPlaneEmbedding n y + t • n))) - r / 4

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

def normalScalarTest (a n : Cover) (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) : ℝ :=
  χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalColumnChart (a n : Cover) : (ℝ × Plane) ≃ᵐ Cover :=
  (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
    (normalProductChart n)).trans (MeasurableEquiv.addLeft a)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalMove (n : Cover) (f : Cover → ℝ) (x : Cover) : Cover := x + f x • n

def normalJacobian (n : Cover) (f : Cover → ℝ) (x : Cover) : ℝ :=
  1 + fderiv ℝ f x n

def normalPullback (n : Cover) (f : Cover → ℝ) (F : Cover → Cover) (x : Cover) : Cover :=
  normalJacobian n f x • F (normalMove n f x) -
    fderiv ℝ f x (F (normalMove n f x)) • n

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphHeightExtension (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  g (normalPlaneCoordinates n (x-a))

def graphShear (a n : Cover) (g : Plane → ℝ) : Cover → Cover :=
  normalMove n (graphHeightExtension a n g)

lemma graphShear_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    normalPlaneCoordinates n (graphShear a n g x - a) = normalPlaneCoordinates n (x-a) := by
  rw [graphShear, normalMove, add_sub_right_comm, map_add, map_smul,
    normalPlaneCoordinates_normal hn, smul_zero, add_zero]

lemma graphShear_inverse (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Function.LeftInverse (graphShear a n (-g)) (graphShear a n g) := by
  intro x
  change graphShear a n g x + (-g) (normalPlaneCoordinates n (graphShear a n g x-a)) • n = x
  rw [graphShear_projection a hn]
  simp only [Pi.neg_apply, neg_smul, graphShear, normalMove, graphHeightExtension]
  abel

lemma graphShear_continuous (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    Continuous (graphShear a n g) := by
  unfold graphShear normalMove graphHeightExtension
  exact continuous_id.add ((hg.comp ((normalPlaneCoordinates n).continuous.comp
    (continuous_id.sub continuous_const))).smul continuous_const)

def graphShearHomeomorph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) : Cover ≃ₜ Cover where
  toFun := graphShear a n g
  invFun := graphShear a n (-g)
  left_inv := graphShear_inverse a hn g
  right_inv := by
    intro x
    simpa only [neg_neg] using graphShear_inverse a hn (-g) x
  continuous_toFun := graphShear_continuous a n hg
  continuous_invFun := graphShear_continuous a n hg.neg

lemma graphHeightExtension_contDiff (a n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (graphHeightExtension a n g) :=
  hg.comp ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphSublevelIndicator (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  {z : Cover | ⟪n,z-a⟫ < graphHeightExtension a n g z}.indicator (fun _ ↦ 1) x

def graphAreaVector (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover :=
  n - normalPlaneEmbedding n (gradient g y)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_trace_continuous {X : Type*} [TopologicalSpace X]
    (a n : Cover) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hF : Continuous F) : Continuous (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  apply hF.comp
  exact continuous_const.add ((normalPlaneLinearIsometry n).continuous.add (hg.smul continuous_const))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

def graphSmoothingMeasure (b : ContDiffBump (0 : Plane)) : Measure Plane :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (b.normed volume y))

instance graphSmoothingMeasure_probability (b : ContDiffBump (0 : Plane)) :
    IsProbabilityMeasure (graphSmoothingMeasure b) := by
  constructor
  rw [graphSmoothingMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal b.integrable_normed
      (Eventually.of_forall b.nonneg_normed), b.integral_normed]
  norm_num

def graphSmooth (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) : Plane → ℝ :=
  fun x ↦ ∫ y, f (x-y) ∂graphSmoothingMeasure b

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVOrientedGraphCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphSlopeNormal (n : Cover) (p : Plane) : Cover :=
  ‖n-normalPlaneEmbedding n p‖⁻¹ • (n-normalPlaneEmbedding n p)

lemma graphSlopeVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    ‖n-normalPlaneEmbedding n p‖^2 = 1+‖p‖^2 := by
  rw [norm_sub_sq_real, hn, normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn]
  ring

lemma graphSlopeVector_norm_ge {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    1 ≤ ‖n-normalPlaneEmbedding n p‖ := by
  have hh := graphSlopeVector_norm_sq hn p
  nlinarith [norm_nonneg (n-normalPlaneEmbedding n p), sq_nonneg ‖p‖]

lemma graphSlopeNormal_unit {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    ‖graphSlopeNormal n p‖ = 1 := by
  rw [graphSlopeNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn p))

def graphOrientedCost (n ν : Cover) (g : Plane → ℝ) (y : Plane) : ℝ :=
  ‖graphAreaVector n g y‖-⟪graphAreaVector n g y,ν⟫

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphBallOrientedCost (a n ν : Cover) (g : Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ y in {y : Plane | a+normalGraph n g y ∈ Metric.ball a r}, graphOrientedCost n ν g y

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def graphBlend (χ g u : Plane → ℝ) (y : Plane) : ℝ :=
  g y + χ y * (u y-g y)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVAnnulusSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CubicTorus

def planeAnnulus (ρ δ : ℝ) (i : ℕ) : Set Plane :=
  Metric.ball 0 (ρ+(i+1)*δ) \ Metric.ball 0 (ρ+i*δ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

def normalColumnCutoff (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r / 3
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma norm_normalPlaneCoordinates_le (n : Cover) : ‖normalPlaneCoordinates n‖ ≤ 1 := by
  simp [normalPlaneCoordinates]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphRescale (r e m : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  r * (m + e * f (r⁻¹ • y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def columnPhase (q t : ℝ) : ℝ := (Iio q).indicator (fun _ ↦ (1 : ℝ)) t

def columnGraphMismatch (U : Set Torus) (a : Torus) (n : Cover)
    (r : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ :=
  ∫ t in Icc (-r/4) (r/4), |characteristic U
    (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphNormalize (r e m : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ :=
  (r*e)⁻¹ * (g (r • y)-r*m)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def interiorWallWeight (x : Cover) : ℝ := ∏ i : Fin 3, wallCutoff i x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

def InteriorCenter := {a : Cover // ‖a-cubeCenter‖ ≤ 1/8}

instance instCoeInteriorCenterCover : Coe InteriorCenter Cover := ⟨Subtype.val⟩

variable {c : InteriorCenter}

def cubeBall (c : InteriorCenter) (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball (c : Cover) r

def radialBump (c : InteriorCenter) : ContDiffBump (c : Cover) where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def radialCore (c : InteriorCenter) (x : Cover) : ℝ := (radialBump c) x * (1 - ‖x - (c : Cover)‖ ^ 2)

def radialSquared (c : InteriorCenter) (x : Cover) : ℝ := 1 - latticePeriodize (radialCore c) x

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVMovingOrientedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

def bundleOrientedExcess (c : InteriorCenter) (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) : ℝ :=
  ∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, 1-⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVC1Patch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_bounded_one {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) : Integrable g η :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)

def boundedFunctionL1 (η : Measure Cover) [IsFiniteMeasure η]
    (g : Cover → ℝ) (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) : Lp ℝ 1 η :=
  (integrable_bounded_one hg hb).toL1 g

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def blowupCharacteristic (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) : ℝ :=
  characteristic E (quotientMap (c+r • x))

lemma measurable_blowupCharacteristic {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) (r : ℝ) : Measurable (blowupCharacteristic E c r) :=
  (measurable_characteristic hE).comp (measurable_quotientMap.comp
    (measurable_const.add (measurable_id.const_smul r)))

lemma blowupCharacteristic_bound (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) :
    |blowupCharacteristic E c r x| ≤ 1 := characteristic_bound _ _

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

instance finiteMeasure_cover_closedBall (a : Cover) (R : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.closedBall a R)) :=
  isFiniteMeasure_restrict.mpr Metric.isBounded_closedBall.measure_lt_top.ne

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev BlowupNormalBundle := Cover × NormalSphere

def blowupNormalMap (c : Cover) (r : ℝ) (z : NormalBundle) : BlowupNormalBundle :=
  (r⁻¹ • ((z.1 : Cover)-c),z.2)

def blowupNormalMeasure (μ : FiniteMeasure NormalBundle) (c : Cover) (r R : ℝ) :
    FiniteMeasure BlowupNormalBundle :=
  Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (blowupNormalMap c r)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma tangentialDivergence_zero_of_notMem_tsupport {F : Cover → Cover} {x : Cover}
    (hx : x ∉ tsupport F) (n : Cover) : tangentialDivergence F x n = 0 := by
  simp [tangentialDivergence,divergence_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]

lemma hasCompactSupport_normalBundle_test {F : Cover → Cover} (hF : HasCompactSupport F)
    {g : BlowupNormalBundle → ℝ} (hg : ∀ z, z.1 ∉ tsupport F → g z = 0) :
    HasCompactSupport g := by
  apply (hF.prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_univ)
  intro z hz
  refine ⟨?_,mem_univ _⟩
  by_contra hh
  exact hz (hg z hh)

lemma continuous_blowupFluxTest {F : Cover → Cover} (hF : Continuous F) :
    Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) :=
  (continuous_subtype_val.comp continuous_snd).inner (hF.comp continuous_fst)

lemma continuous_blowupTangentTest {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : BlowupNormalBundle ↦ tangentialDivergence F z.1 z.2) :=
  ((continuous_divergence hF).comp continuous_fst).sub
    ((continuous_subtype_val.comp continuous_snd).inner
      (((hF.continuous_fderiv (by simp)).comp continuous_fst).clm_apply
        (continuous_subtype_val.comp continuous_snd)))

def blowupFluxTest {F : Cover → Cover} (hF : Continuous F) (hs : HasCompactSupport F) :
    BlowupNormalBundle →ᵇ ℝ :=
  ofCompactSupport _ (continuous_blowupFluxTest hF)
    (hasCompactSupport_normalBundle_test hs (fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport hz]))

def blowupTangentTest {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : HasCompactSupport F) : BlowupNormalBundle →ᵇ ℝ :=
  ofCompactSupport _ (continuous_blowupTangentTest hF)
    (hasCompactSupport_normalBundle_test hs (fun z hz ↦
      tangentialDivergence_zero_of_notMem_tsupport hz z.2))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_indicator_bound (F : Set Cover) (x : Cover) :
    |F.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
  classical
  by_cases hx : x ∈ F <;> simp [hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverLocalPerimeter (A O : Set Cover) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
    (_ : HasCompactSupport F) (_ : tsupport F ⊆ O) (_ : ∀ x, ‖F x‖ ≤ 1),
      ENNReal.ofReal (∫ x in A, divergence F x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def coverPrismCoordinates : Cover ≃L[ℝ] PrismCoordinates :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).trans
    { toLinearEquiv :=
        { toFun := fun v ↦ (v 0,(v 1,v 2))
          invFun := fun z ↦ ![z.1,z.2.1,z.2.2]
          left_inv := by intro v; ext i; fin_cases i <;> rfl
          right_inv := by intro z; rfl
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

lemma coverPrismCoordinates_apply (x : Cover) :
    coverPrismCoordinates x = (x 0,(x 1,x 2)) := rfl

def euclideanPrism (a c b l u : ℝ) : Set Cover :=
  coverPrismCoordinates ⁻¹' coordinatePrism a c b l u

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVLocalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def affineCoverRegion (A : Set Cover) (c : Cover) (r : ℝ) : Set Cover :=
  {x | r⁻¹ • (x-c) ∈ A}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def intervalSmoothHat (b : ℝ → ℝ) (a c t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t-a, b u) - ∫ u in (0 : ℝ)..t-c, b u

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def partitionSmoothTest (b : ℝ → ℝ) (u σ : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, σ i * intervalSmoothHat b (u i) (u (i+1)) t

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

def angularMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/(16*((n : ℝ)+1))
  rOut := 2/(16*((n : ℝ)+1))
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

def radialBalance (t : ℝ) : ℝ :=
  Real.smoothTransition (1-t)-t*deriv Real.smoothTransition (1-t)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVConeSecondaryFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

def affineScalarTest (p : Cover) (r : ℝ) (ψ : Cover → ℝ) (x : Cover) : ℝ :=
  ψ (r⁻¹ • (x-p))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVStationaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def euclideanRadialMass (ν : FiniteMeasure BlowupNormalBundle) (a : Cover) (ε r : ℝ) : ℝ :=
  ∫ z, radialDensityWeight a r ε z.1 ∂(ν : Measure BlowupNormalBundle)

def euclideanBallMass (ν : FiniteMeasure BlowupNormalBundle) (a : Cover) (r : ℝ) : ℝ :=
  (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball a r}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def euclideanNormalMap (c : Cover) (r : ℝ) (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (r⁻¹ • ((z.1 : Cover)-c),z.2)

def euclideanNormalMeasure (μ : FiniteMeasure BlowupNormalBundle) (c : Cover) (r R : ℝ) :
    FiniteMeasure BlowupNormalBundle :=
  Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (euclideanNormalMap c r)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarAngularChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarWedgeChart (z : ℝ × ℝ) : Plane :=
  planeProductCoordinates.symm (z.1,z.1*z.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarAxialBump : ContDiffBump (0 : ℝ) where
  rIn := 1/64
  rOut := 1/32
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def angularEssentialBoundary (D : Set ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → 0 < volume (D ∩ Metric.ball x δ) ∧
    0 < volume (Dᶜ ∩ Metric.ball x δ)}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def planarWedgeCoordinates (y : Plane) : ℝ × ℝ :=
  ((planeProductCoordinates y).1,(planeProductCoordinates y).1⁻¹*(planeProductCoordinates y).2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_apply (y : Plane) : planeProductCoordinates y = (y 0,y 1) := by
  simp [planeProductCoordinates,Complex.orthonormalBasisOneI]

lemma planeProductCoordinates_symm_apply (z : ℝ × ℝ) :
    planeProductCoordinates.symm z = WithLp.toLp 2 ![z.1,z.2] := by
  apply planeProductCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,planeProductCoordinates_apply]
  rfl

def coverPlaneCoordinates : Cover ≃L[ℝ] ℝ × Plane :=
  coverPrismCoordinates.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr planeProductCoordinates.symm)

lemma coverPlaneCoordinates_apply (x : Cover) :
    coverPlaneCoordinates x = (x 0,WithLp.toLp 2 ![x 1,x 2]) := by
  simp [coverPlaneCoordinates,coverPrismCoordinates_apply,planeProductCoordinates_symm_apply]

lemma coverPlaneCoordinates_norm_sq (x : Cover) :
    ‖x‖^2 = (coverPlaneCoordinates x).1^2 + ‖(coverPlaneCoordinates x).2‖^2 := by
  rw [coverPlaneCoordinates_apply,EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

def coverPlaneRotationCLE (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃L[ℝ] Cover :=
  (coverPlaneCoordinates.trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr R.toContinuousLinearEquiv)).trans coverPlaneCoordinates.symm

lemma coverPlaneRotationCLE_coordinates (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Cover) :
    coverPlaneCoordinates (coverPlaneRotationCLE R x) =
      ((coverPlaneCoordinates x).1,R (coverPlaneCoordinates x).2) := by
  simp [coverPlaneRotationCLE]

def coverPlaneRotation (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃ₗᵢ[ℝ] Cover :=
  { (coverPlaneRotationCLE R).toLinearEquiv with
    norm_map' := by
      intro x
      change ‖coverPlaneRotationCLE R x‖ = ‖x‖
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [coverPlaneCoordinates_norm_sq,coverPlaneCoordinates_norm_sq,
        coverPlaneRotationCLE_coordinates,R.norm_map] }

def swapPrismPlane : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1 : Fin 3) 2)

def prismFrame (n : Cover) (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃ₗᵢ[ℝ] Cover :=
  (swapPrismPlane.trans (coverPlaneRotation R)).trans (normalRotation n)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverHalfspace (n : Cover) : Set Cover := {x | ⟪n,x⟫ < 0}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlaneAreaCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radial_face_coefficients (u : ℝ) :
    (u/Real.sqrt (1+u^2))^2+(1/Real.sqrt (1+u^2))^2 = 1 := by
  have hpos : (0 : ℝ) < 1+u^2 := by positivity
  have hs := Real.sq_sqrt hpos.le
  have hd := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeFaceCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).trans
    { toLinearEquiv :=
        { toFun := fun y ↦ (y 0,y 1)
          invFun := fun z ↦ ![z.1,z.2]
          left_inv := by intro y; ext i; fin_cases i <;> rfl
          right_inv := by intro z; rfl
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupRigidCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def pullbackBlowupNormal (R : Cover ≃ₗᵢ[ℝ] Cover) (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (R.symm z.1,⟨R.symm (z.2 : Cover),by simpa only [R.symm.norm_map] using z.2.property⟩)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarEssentialBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarEssentialBoundary (C : Set Plane) : Set Plane :=
  (volume.restrict C).support ∩ (volume.restrict Cᶜ).support

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarNormalRotation (n : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.single 0 1 - n))ᗮ

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

def blowupTilt (n : Cover) (z : BlowupNormalBundle) : ℝ :=
  radialHeightCutoff 0 (1/8) z.1 * ‖(z.2 : Cover)-n‖^2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def BoundaryNormalChart (E : Set Torus) (c n : Cover) (r e C K ρ : ℝ) : Prop :=
  ∃ ν : Cover → Cover,
    ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128)) ∧
    (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
      ‖ν a‖ = 1 ∧ ‖n-ν a‖ ≤ C*e ∧
      BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
    ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
      ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
        dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

def fieldMove (F : Cover → Cover) (t : ℝ) (x : Cover) : Cover := x + t • F x

def fieldMoveDeriv (F : Cover → Cover) (t : ℝ) (x : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover + t • fderiv ℝ F x

def derivativeEntry (F : Cover → Cover) (x : Cover) (i j : Fin 3) : ℝ :=
  (fderiv ℝ F x (EuclideanSpace.single j 1)) i

def secondJacobian (F : Cover → Cover) (x : Cover) : ℝ :=
  derivativeEntry F x 0 0 * derivativeEntry F x 1 1 +
  derivativeEntry F x 0 0 * derivativeEntry F x 2 2 +
  derivativeEntry F x 1 1 * derivativeEntry F x 2 2 -
  derivativeEntry F x 0 1 * derivativeEntry F x 1 0 -
  derivativeEntry F x 0 2 * derivativeEntry F x 2 0 -
  derivativeEntry F x 1 2 * derivativeEntry F x 2 1

def thirdJacobian (F : Cover → Cover) (x : Cover) : ℝ :=
  Matrix.det (Matrix.of (derivativeEntry F x))

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

def cubeCenter : Cover := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def cubeBall (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball cubeCenter r

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def discProjection : Cover →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ x i.succ)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

@[simp] lemma discProjection_apply (x : Cover) (i : Fin 2) :
    discProjection x i = x i.succ := rfl

def tubeSplit : Cover ≃ᵐ ℝ × Plane :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

@[simp] lemma tubeSplit_apply (x : Cover) : tubeSplit x = (x 0, discProjection x) := by
  rfl

@[simp] lemma tubeSplit_symm_zero (p : ℝ × Plane) : (tubeSplit.symm p) 0 = p.1 := by
  simp [tubeSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr]

@[simp] lemma tubeSplit_symm_succ (p : ℝ × Plane) (i : Fin 2) :
    (tubeSplit.symm p) i.succ = p.2 i := by
  simp [tubeSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr]

def discCenter : Plane := WithLp.toLp 2 (fun _ ↦ (1 / 2 : ℝ))

def coverTube (r : ℝ) : Set Cover :=
  tubeSplit ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)

def axialProjection : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover -
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1)

@[simp] lemma axialProjection_zero (x : Cover) : axialProjection x 0 = 0 := by
  simp [axialProjection]

@[simp] lemma axialProjection_succ (x : Cover) (i : Fin 2) :
    axialProjection x i.succ = x i.succ := by
  simp [axialProjection]

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

def cubeTube (r : ℝ) : Set Torus := representative ⁻¹' coverTube r

def centeredTube (r : ℝ) : Set Torus := {x | ‖x 1‖^2 + ‖x 2‖^2 < r^2}

end CubicTorus.UpperComparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVBallCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def ballCalibration (r s : ℝ) (x : Cover) : Cover :=
  s⁻¹ • radialDensityField cubeCenter s (s^2-r^2) x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

def tubeCalibration (b : ContDiffBump (1/2 : ℝ)) (r s : ℝ) (x : Cover) : Cover :=
  s⁻¹ • (b (x 0) • radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter)))

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

def axialExhaustionBump (a : ℝ) (ha : 0 < a) (ha' : a < 1/2) : ContDiffBump (1/2 : ℝ) where
  rIn := a
  rOut := (a+1/2)/2
  rIn_pos := ha
  rIn_lt_rOut := by linarith

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Pointwise
namespace CubicTorus

instance latticeAddAction : AddAction (Fin 3 → ℤ) Cover where
  vadd n x := x+latticeVector n
  zero_vadd x := by change x+latticeVector 0=x; ext i; simp [latticeVector]
  add_vadd n m x := by
    change x+latticeVector (n+m)=(x+latticeVector m)+latticeVector n
    ext i; simp [latticeVector]; ring

instance latticeMeasurableVAdd : MeasurableConstVAdd (Fin 3 → ℤ) Cover where
  measurable_const_vadd shift :=
    show Measurable (fun point : Cover ↦ point+latticeVector shift) from
      measurable_id.add measurable_const

instance latticeVolumeInvariant : VAddInvariantMeasure (Fin 3 → ℤ) Cover volume where
  measure_preimage_vadd n s hs := by
    change volume ((fun x : Cover ↦ x+latticeVector n) ⁻¹' s)=volume s
    exact (measurePreserving_add_right volume (latticeVector n)).measure_preimage hs.nullMeasurableSet

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def periodicCoordinateRegion (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (E : Set Torus) : Set Torus :=
  representative ⁻¹' (coordinateMove i f t '' (quotientMap ⁻¹' E))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

namespace Periodic

structure Variation where
  coordinate : Fin 3
  function : Cover → ℝ
  bound : NNReal
  smooth : ContDiff ℝ (⊤ : ℕ∞) function
  periodic : ∀ n x,function (x+latticeVector n)=function x
  derivative_bound : ∀ x,‖fderiv ℝ function x‖₊≤bound

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

abbrev VariationChain := List (Variation × ℝ)

def chainMove : VariationChain → Cover → Cover
  | [],x => x
  | (a,t)::l,x => chainMove l (coordinateMove a.coordinate a.function t x)

def chainJacobian : VariationChain → Cover → ℝ
  | [],_ => 1
  | (a,t)::l,x => coordinateJacobian a.coordinate a.function t x *
      chainJacobian l (coordinateMove a.coordinate a.function t x)

def chainCofactor : VariationChain → Cover → Cover → Cover
  | [],_,n => n
  | (a,t)::l,x,n => chainCofactor l (coordinateMove a.coordinate a.function t x)
      (coordinateCofactor a.coordinate a.function t x n)

def chainPullback : VariationChain → (Cover → Cover) → Cover → Cover
  | [],F => F
  | (a,t)::l,F => coordinatePullback a.coordinate a.function t (chainPullback l F)

def chainRegion : VariationChain → Set Torus → Set Torus
  | [],E => E
  | (a,t)::l,E => chainRegion l (periodicCoordinateRegion a.coordinate a.function t E)

def ChainValid (l : VariationChain) : Prop := ∀ p∈l,|p.2| *(p.1.bound:ℝ)<1

def chainBound : VariationChain → ℝ
  | [] => 1
  | (a,t)::l => (1+2*|t| *(a.bound:ℝ))*chainBound l

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainMass (l : VariationChain) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x

def chainTransportedFlux (l : VariationChain) (b : Variation) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
    chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def simultaneousChain (l : List Variation) (t : ℝ) : VariationChain := l.map (fun a ↦ (a,t))

@[simp] lemma simultaneousMove_zero (l : List Variation) (x : Cover) :
    chainMove (simultaneousChain l 0) x=x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainMove,coordinateMove] using ih x

@[simp] lemma simultaneousJacobian_zero (l : List Variation) (x : Cover) :
    chainJacobian (simultaneousChain l 0) x=1 := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainJacobian,coordinateJacobian,coordinateMove] using ih x

@[simp] lemma simultaneousFlux_zero (l : List Variation) (b : Variation) (E : Set Torus) :
    chainTransportedFlux (simultaneousChain l 0) b E=directionalFlux E b.coordinate b.function := by
  simp [chainTransportedFlux,directionalFlux]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainCorrection (l : List Variation) (b : Variation) (E : Set Torus) (t : ℝ) : ℝ :=
  (torusVolume.real E-chainMass (simultaneousChain l t) E)/chainTransportedFlux (simultaneousChain l t) b E

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normSmoothingBump : ContDiffBump (0 : ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩

def normalEmbedding (z : NormalBundle) : Cover×Cover := (z.1,z.2)

lemma normalEmbedding_continuous : Continuous normalEmbedding :=
  (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)

def normalCarrier : Set (Cover×Cover) := closedFundamentalCube×ˢ Metric.sphere 0 1

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CorrectedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def correctedChain (l : List Variation) (b : Variation) (γ : ℝ → ℝ) (t : ℝ) : VariationChain :=
  simultaneousChain l t++[(b,γ t)]

def correctedChainArea (l : List Variation) (b : Variation) (γ : ℝ → ℝ)
    (μ : FiniteMeasure NormalBundle) (t : ℝ) : ℝ :=
  ∫ z,‖chainCofactor (correctedChain l b γ t) z.1 z.2‖ ∂(μ : Measure NormalBundle)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : Variation) : ℝ :=
  ∫ z,⟪(z.2 : Cover),coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫ ∂(μ : Measure NormalBundle)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Periodic

def chainVelocity (l : List Variation) (x : Cover) : Cover :=
  (l.map (fun a ↦ a.function x • EuclideanSpace.single a.coordinate (1 : ℝ))).sum

def chainNormalVelocity (l : List Variation) (x n : Cover) : Cover :=
  (l.map (fun a ↦ coordinateNormalVelocity a.coordinate a.function x n)).sum

def chainFlux (l : List Variation) (E : Set Torus) : ℝ :=
  (l.map (fun a ↦ directionalFlux E a.coordinate a.function)).sum

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Periodic

def normalJet (l : List Variation) (x n : Cover) : Cover×Cover×Cover :=
  l.foldl (fun j a ↦
    (j.1+a.function x • EuclideanSpace.single a.coordinate 1,
      j.2.1+coordinateNormalVelocity a.coordinate a.function x n,
      j.2.2+2 • (fderiv ℝ (fun p : Cover×Cover ↦
        coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n) (j.1,j.2.1)))) (0,0,0)

end Periodic
end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def componentDivergence (a : Variation) (x : Cover) : ℝ :=
  fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1)

def massJet (l : List Variation) (x : Cover) : Cover×ℝ×ℝ :=
  l.foldl (fun j a ↦ (j.1+a.function x • EuclideanSpace.single a.coordinate 1,
    j.2.1+componentDivergence a x,
    j.2.2+2*(fderiv ℝ (componentDivergence a) x j.1+j.2.1*componentDivergence a x))) (0,0,0)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainQuadratic (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (l : List Variation) : ℝ :=
  (∫ z,‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
    ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫ ∂(μ : Measure NormalBundle))-
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,(massJet l x).2.2)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverTrace (L : Cover →L[ℝ] Cover) : ℝ :=
  ∑ i : Fin 3, L (EuclideanSpace.single i 1) i

@[simp] lemma coverTrace_zero : coverTrace 0=0 := by simp [coverTrace]
@[simp] lemma coverTrace_add (L M : Cover →L[ℝ] Cover) :
    coverTrace (L+M)=coverTrace L+coverTrace M := by simp [coverTrace,Finset.sum_add_distrib]
@[simp] lemma coverTrace_smul (a : ℝ) (L : Cover →L[ℝ] Cover) :
    coverTrace (a • L)=a*coverTrace L := by simp [coverTrace,Finset.mul_sum]

def coverTraceCLM : (Cover →L[ℝ] Cover) →L[ℝ] ℝ :=
  ({toFun := coverTrace, map_add' := coverTrace_add,
    map_smul' := by intro a L; exact coverTrace_smul a L} :
      (Cover →L[ℝ] Cover) →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] lemma coverTraceCLM_apply (L : Cover →L[ℝ] Cover) : coverTraceCLM L=coverTrace L := rfl

def cofactorLinear (L : Cover →L[ℝ] Cover) (n : Cover) : Cover :=
  coverTrace L • n-L.adjoint n

def cofactorQuadratic (L : Cover →L[ℝ] Cover) (n : Cover) : Cover :=
  ((coverTrace L)^2-coverTrace (L.comp L)) • n-
    (2*coverTrace L) • L.adjoint n+2 • L.adjoint (L.adjoint n)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def ActualBoundaryGraph (E : Set Torus) (c n : Cover) (q : ℝ) : Prop :=
  ∃ a : Cover, dist a c < q/(544*4096) ∧
    ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
      ContDiffOn ℝ 1 g (Metric.ball 0 ((q/544)/1024)) ∧
      (∀ y ∈ Metric.ball (0 : Plane) ((q/544)/1024),
        quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
        ‖normalGraph n g y‖ < (q/544)/512) ∧
      (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((q/544)/128),
        normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalGraphDerivative (n ν : Cover) : Plane →L[ℝ] ℝ :=
  (⟪ν,n⟫)⁻¹ • (-((innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_CoverEssentialBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverEssentialBoundary (A : Set Cover) : Set Cover :=
  {x | ∀ t : ℝ, 0 < t → 0 < volume.real (A ∩ Metric.ball x t) ∧
    0 < volume.real (Aᶜ ∩ Metric.ball x t)}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def CoverC1BoundaryAt (A : Set Cover) (p : Cover) : Prop :=
  ∃ (n b : Cover) (s : ℝ) (G : Plane → ℝ), ‖n‖ = 1 ∧ 0 < s ∧
    ‖b‖ ≤ 1/(544*4096) ∧ LipschitzWith (1/4) G ∧
    ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) (1/(544*2048))) ∧
    (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
      p+s • (b+normalGraph n G y) ∈ coverEssentialBoundary A) ∧
    (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
      p+s • x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b))=x-b)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphMollifier (i : ℕ) : ContDiffBump (0 : Plane) where
  rIn := ((i:ℝ)+1)⁻¹/2
  rOut := ((i:ℝ)+1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hh : 0 < ((i:ℝ)+1)⁻¹ := by positivity
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSlopeNormal_contDiff {n : Cover} (hn : ‖n‖ = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (graphSlopeNormal n) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane ↦ n-normalPlaneEmbedding n p) :=
    contDiff_const.sub (normalPlaneLinearIsometry n).contDiff
  have hz (p : Plane) : n-normalPlaneEmbedding n p ≠ 0 := by
    intro h
    have hh := graphSlopeVector_norm_ge hn p
    rw [h,norm_zero] at hh
    norm_num at hh
  exact ((hv.norm ℝ hz).inv (fun p ↦ norm_ne_zero_iff.mpr (hz p))).smul hv

def graphUnitNormalExtension (a n : Cover) (g : Plane → ℝ) (x : Cover) : Cover :=
  graphSlopeNormal n (gradient g (normalPlaneCoordinates n (x-a)))

lemma graphUnitNormalExtension_unit (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) : ‖graphUnitNormalExtension a n g x‖ = 1 :=
  graphSlopeNormal_unit hn _

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalCoverMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalCoverMap (z : NormalBundle) : BlowupNormalBundle := ((z.1 : Cover),z.2)

def normalCoverMeasure (μ : FiniteMeasure NormalBundle) : FiniteMeasure BlowupNormalBundle :=
  μ.map normalCoverMap

def HasCutoffSaturation (ν : FiniteMeasure BlowupNormalBundle) (O : Set Cover) : Prop :=
  ∀ (φ : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ O → (∀ x, φ x ∈ Icc 0 1) → ∀ C : ℝ,
    (∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
        ∂(ν : Measure BlowupNormalBundle)) ≤ C) →
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(ν : Measure BlowupNormalBundle)) ≤ C

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphSignedHeight (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  ⟪n,x-a⟫-graphHeightExtension a n g x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def dilatedGraph (s : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ := s*g (s⁻¹ • y)

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ConeSlopeReciprocalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

def coneSlopeReciprocalArea (f q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (Real.sqrt (1+(f s-s*q s)^2+(q s)^2))⁻¹

def coneSlopeFlux (f q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (q s-s*(f s-s*q s))*coneSlopeReciprocalArea f q s

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def minimalGraphDensity (g ψ : Plane → ℝ) (y : Plane) : ℝ :=
  fderiv ℝ ψ y (gradient g y)/Real.sqrt (1+‖gradient g y‖^2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphReparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) : Plane → ℝ :=
  fun y ↦ g (R y-v)+c

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcFlux (p : Plane) : Plane := (Real.sqrt (1+‖p‖^2))⁻¹ • p

def WeakCMCGraph (g : Plane → ℝ) (H : ℝ) (U : Set Plane) : Prop :=
  ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆U →
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g y)))=H*(∫ y, ψ y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcWeight (p : Plane) : ℝ := Real.sqrt (1+‖p‖^2)

def cmcJacobian (p : Plane) : Plane →L[ℝ] Plane :=
  (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane -
    ((cmcWeight p)^3)⁻¹ • (innerSL ℝ p).smulRight p

lemma cmcWeight_pos (p : Plane) : 0 < cmcWeight p := by
  exact Real.sqrt_pos.2 (by positivity)
lemma cmcWeight_sq (p : Plane) : (cmcWeight p)^2=1+‖p‖^2 :=
  Real.sq_sqrt (by positivity)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def LinearCMCEquation (g : Plane → ℝ) (p B : Plane → Plane) (U : Set Plane) : Prop :=
  ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆U →
    (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (gradient g y)-B y))=0

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def differenceStep (δ : ℝ) (i : ℕ) : ℝ := δ*(1/((i:ℝ)+1))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_continuous {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hf.continuous_fderiv (by simp))

lemma plane_gradient_compact {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gradient f) :=
  (hf.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ Plane).symm)

lemma compact_C1_gradient_memLp {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (gradient f) 2 :=
  (C1_gradient_continuous hf).memLp_of_hasCompactSupport (plane_gradient_compact hc)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def PlaneWeakGradient (S : Set Plane) (u : Plane → ℝ) (G : Plane → Plane) : Prop :=
  ∀ (v : Plane) (ψ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ⊆S → (∫ y, ⟪G y,v⟫*ψ y)= -(∫ y,u y*fderiv ℝ ψ y v)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_add {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gradient (f+g)=gradient f+gradient g := by
  funext x
  simp only [gradient,fderiv_add ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt),map_add,Pi.add_apply]

lemma C1_gradient_smul {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) :
    gradient (a • f)=a • gradient f := by
  funext x
  simp only [gradient,fderiv_const_smul ((hf.differentiable (by simp)).differentiableAt),
    map_smul,Pi.smul_apply]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcStretch (p : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.id ℝ Plane+(cmcWeight p+1)⁻¹ • (innerSL ℝ p).smulRight p

def cmcCompress (p : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.id ℝ Plane-(cmcWeight p*(cmcWeight p+1))⁻¹ • (innerSL ℝ p).smulRight p

lemma cmcStretch_apply (p v : Plane) :
    cmcStretch p v=v+((cmcWeight p+1)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcStretch,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcCompress_apply (p v : Plane) :
    cmcCompress p v=v-((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p := by
  simp only [cmcCompress,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcCompress_stretch (p v : Plane) : cmcCompress p (cmcStretch p v)=v := by
  rw [cmcCompress_apply,cmcStretch_apply,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  have he : (cmcWeight p*(cmcWeight p+1))⁻¹*
      (⟪p,v⟫+(cmcWeight p+1)⁻¹*⟪p,v⟫*‖p‖^2)=
      (cmcWeight p+1)⁻¹*⟪p,v⟫ := by
    rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
    field_simp
    ring
  rw [he,add_sub_cancel_right]

lemma cmcStretch_compress (p v : Plane) : cmcStretch p (cmcCompress p v)=v := by
  rw [cmcStretch_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  have he : (cmcWeight p+1)⁻¹*
      (⟪p,v⟫-(cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫*‖p‖^2)=
      (cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫ := by
    rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
    field_simp
    ring
  rw [he,sub_add_cancel]

def cmcMetricEquiv (p : Plane) : Plane ≃L[ℝ] Plane :=
  { cmcCompress p with
    invFun := cmcStretch p
    left_inv := cmcStretch_compress p
    right_inv := cmcCompress_stretch p
    continuous_toFun := (cmcCompress p).continuous
    continuous_invFun := (cmcStretch p).continuous }

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeChangeFactor (L : Plane ≃L[ℝ] Plane) : ℝ≥0 :=
  addHaarScalarFactor (volume.map L) (volume : Measure Plane)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneScaleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeScaleEquiv (r : ℝ) (hr : r≠0) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.smulOfNeZero ℝ Plane r hr).toContinuousLinearEquiv

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_HolderNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

def HolderNear {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) (x : E) : Prop :=
  ∃ r α C : ℝ,0 < r ∧ 0<α ∧ α≤1 ∧ 0≤C ∧
    ∀ y∈Metric.ball x r,∀ z∈Metric.ball x r,dist (f y) (f z)≤C*(dist y z)^α

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

def HolderJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] : ℕ → (E → F) → E → Prop
  | 0,f,x => HolderNear f x
  | n+1,f,x => ContDiffAt ℝ 1 f x ∧ HolderJet n (fderiv ℝ f) x

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def LinearCMCEquationNear (g : Plane → ℝ) (p B : Plane → Plane) : Prop :=
  ∃ R : ℝ,0<R ∧ LinearCMCEquation g p B (Metric.ball 0 R)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def linearCMCSource (g : Plane → ℝ) (p B : Plane → Plane) (v : Plane) : Plane → Plane :=
  fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeDivergence (F : Plane → Plane) (y : Plane) : ℝ :=
  (fderiv ℝ F y (EuclideanSpace.single 0 1)) 0+
  (fderiv ℝ F y (EuclideanSpace.single 1 1)) 1

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def TorusC2CMCAt (E : Set Torus) (a : Torus) : Prop :=
  ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0 < r ∧
    LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 2 g (Metric.ball 0 r) ∧
    (∀ y∈Metric.ball (0 : Plane) r,
      a+quotientMap (normalGraph n g y)∈frontier (openRepresentative E)) ∧
    (∀ x∈Metric.ball (0 : Cover) r,
      a+quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) ∧
    WeakCMCGraph g H (Metric.ball 0 r)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphJacobiForm (A : Plane → Plane →L[ℝ] Plane) (q φ ψ : Plane → ℝ) : ℝ :=
  ∫ y,(q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫-
    q y*planeDivergence (fun z ↦ A z (gradient q z)) y*φ y*ψ y

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphShapeOperator (g : Plane → ℝ) (y : Plane) : Plane →L[ℝ] Plane :=
  (cmcJacobian (gradient g y)).comp (fderiv ℝ (gradient g) y)

def planeTraceSquare (L : Plane →L[ℝ] Plane) : ℝ :=
  (L (EuclideanSpace.single 0 1) 0)^2+
    2*L (EuclideanSpace.single 0 1) 1*L (EuclideanSpace.single 1 1) 0+
    (L (EuclideanSpace.single 1 1) 1)^2

def graphSquaredSecondFundamentalForm (g : Plane → ℝ) (y : Plane) : ℝ :=
  planeTraceSquare (graphShapeOperator g y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeTrace (L : Plane →L[ℝ] Plane) : ℝ :=
  ∑ i : Fin 2,L (EuclideanSpace.single i 1) i

@[simp] lemma planeTrace_neg (L : Plane →L[ℝ] Plane) : planeTrace (-L)= -planeTrace L := by
  simp [planeTrace,Finset.sum_neg_distrib]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_fderiv_apply {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (n : Cover) (y v : Plane) :
    fderiv ℝ (normalGraph n g) y v=normalPlaneEmbedding n v+⟪gradient g y,v⟫ • n := by
  rw [(normalGraph_hasFDerivAt (hg.differentiable (by simp) y)).fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,inner_gradient_left]
  rfl

lemma graphSlopeNormal_weight {n : Cover} (hn : ‖n‖=1) (p : Plane) :
    graphSlopeNormal n p=(cmcWeight p)⁻¹ • (n-normalPlaneEmbedding n p) := by
  have he : ‖n-normalPlaneEmbedding n p‖=cmcWeight p := by
    rw [cmcWeight,← graphSlopeVector_norm_sq hn p,Real.sqrt_sq (norm_nonneg _)]
  simp only [graphSlopeNormal,he]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def translateNormal (a : Cover) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (quotientMap z.1-quotientMap a),z.2)

lemma measurable_translateNormal (a : Cover) : Measurable (translateNormal a) := by
  exact (measurable_cubeRepresentative.comp ((measurable_quotientMap.comp
    (measurable_subtype_coe.comp measurable_fst)).sub measurable_const)).prodMk measurable_snd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcGraphJacobi (g φ ψ : Plane → ℝ) : ℝ :=
  graphJacobiForm (fun y ↦ cmcJacobian (gradient g y))
    (fun y ↦ cmcWeight (gradient g y)) φ ψ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cofactorOperator : (Cover →L[ℝ] Cover) →L[ℝ] (Cover →L[ℝ] Cover) :=
  ({toFun := fun L ↦ coverTrace L • ContinuousLinearMap.id ℝ Cover-L.adjoint,
    map_add' := by intro L M; simp only [coverTrace_add,map_add]; module,
    map_smul' := by intro a L; simp only [coverTrace_smul,map_smul,RingHom.id_apply]; module} :
      (Cover →L[ℝ] Cover) →ₗ[ℝ] (Cover →L[ℝ] Cover)).toContinuousLinearMap

@[simp] lemma cofactorOperator_apply (L : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorOperator L n=cofactorLinear L n := rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def variationField (a : Variation) (x : Cover) : Cover :=
  a.function x • EuclideanSpace.single a.coordinate 1

def motionJet (l : List Variation) (x : Cover) : Cover×Cover :=
  l.foldl (fun j a ↦ (j.1+variationField a x,
    j.2+2 • fderiv ℝ (variationField a) x j.1)) (0,0)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def volumeQuadratic (L : Cover →L[ℝ] Cover) : ℝ :=
  (coverTrace L)^2-coverTrace (L.comp L)

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainAcceleration (l : List Variation) (x : Cover) : Cover := (motionJet l x).2

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def ambientAreaQuadratic (L : Cover →L[ℝ] Cover) (n : Cover) : ℝ :=
  ‖cofactorLinear L n‖^2-⟪n,cofactorLinear L n⟫^2+⟪n,cofactorQuadratic L n⟫

def ambientQuadratic (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (F : Cover → Cover) : ℝ :=
  (∫ z,ambientAreaQuadratic (fderiv ℝ F z.1) z.2 ∂(μ : Measure NormalBundle))-
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,volumeQuadratic (fderiv ℝ F x))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def volumeCorrection (F : Cover → Cover) (x : Cover) : Cover :=
  divergence F x • F x-fderiv ℝ F x (F x)

def ambientBoundaryQuadratic (H : ℝ) (F : Cover → Cover) (x n : Cover) : ℝ :=
  ambientAreaQuadratic (fderiv ℝ F x) n-H*⟪n,volumeCorrection F x⟫

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalExtensionJacobi (μ : FiniteMeasure NormalBundle) (f : Cover → ℝ)
    (N : Cover → Cover) : ℝ :=
  ∫ z,‖gradient f z.1-⟪(z.2 : Cover),gradient f z.1⟫ • (z.2 : Cover)‖^2-
    (f z.1)^2*coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def regularizedNormal (R : Cover → Cover) (x : Cover) : Cover :=
  (Real.sqrt (‖R x‖^2+(1-Real.smoothTransition (4*‖R x‖^2))))⁻¹ • R x

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem continuous_periodic_descent {Y : Type*} [TopologicalSpace Y]
    {F : Cover → Y} (hF : Continuous F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    Continuous (fun a : Torus ↦ F (representative a)) := by
  let q : CompactCell → Torus := fun z ↦ quotientMap z
  have hq : Continuous q := continuous_quotientMap.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro a
    exact ⟨cubeRepresentative a,quotientMap_representative a⟩
  apply (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
  have he : (fun a : Torus ↦ F (representative a)) ∘ q = fun z : CompactCell ↦ F z := by
    funext z
    exact periodic_representative hp z
  rw [he]
  exact hF.comp continuous_subtype_val

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphInverseMetric (p : Plane) : Plane →L[ℝ] Plane :=
  cmcWeight p • cmcJacobian p

def graphTangentialGradient (n : Cover) (g φ : Plane → ℝ) (y : Plane) : Cover :=
  fderiv ℝ (normalGraph n g) y (graphInverseMetric (gradient g y) (gradient φ y))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_curvature_continuous {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    Continuous (fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) :=
  coverTraceCLM.continuous.comp ((hN.continuous_fderiv (by simp)).clm_comp
    (hN.continuous_fderiv (by simp)))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_LatticeHeightHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def latticeHeightHom (n : Cover) : (Fin 3 → ℤ) →+ ℝ where
  toFun m := ⟪n,latticeVector m⟫
  map_zero' := by rw [latticeVector_zero,inner_zero_right]
  map_add' m k := by rw [latticeVector_add,inner_add_right]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def integerCharacter (m : Fin 3 → ℤ) : Torus →+ AddCircle (1 : ℝ) where
  toFun x := ∑ i, m i • x i
  map_zero' := by simp
  map_add' x y := by simp [smul_add,Finset.sum_add_distrib]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def simultaneousArea (l : List Variation) (μ : FiniteMeasure NormalBundle) (t : ℝ) : ℝ :=
  ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖ ∂(μ : Measure NormalBundle)

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CirclePeriodize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def circlePeriodize (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n : ℤ,f (x+n)

lemma circlePeriodize_periodic (f : ℝ → ℝ) : Function.Periodic (circlePeriodize f) 1 := by
  intro x
  unfold circlePeriodize
  calc
    _ = ∑' n : ℤ,f (x+(n+1 : ℤ)) := by
      apply tsum_congr
      intro n
      congr 1
      push_cast
      ring
    _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n ↦ f (x+n))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def circlePhaseGood (K : Set (AddCircle (1 : ℝ))) (x : ℝ) : Prop :=
  Tendsto (fun n ↦ ∫ t : ℝ,K.indicator (fun _ ↦ (1 : ℝ)) (t : AddCircle (1 : ℝ))*
    (angularMollifier n).normed volume (t-x)) atTop
    (𝓝 (K.indicator (fun _ ↦ (1 : ℝ)) (x : AddCircle (1 : ℝ))))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TubeCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace CubicTorus.Reduction

structure UpperSupport (I C : ℝ → ℝ) (x : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 C x
  contact : C x = I x
  above : ∀ᶠ y in 𝓝 x, I y ≤ C y

end CubicTorus.Reduction

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def torusCoordinatePermute (e : Fin 3 ≃ Fin 3) : Torus ≃ᵢ Torus where
  toFun x := WithLp.toLp 2 (fun i ↦ x (e i))
  invFun x := WithLp.toLp 2 (fun i ↦ x (e.symm i))
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  isometry_toFun x y := by
    rw [PiLp.edist_eq_of_L2,PiLp.edist_eq_of_L2]
    exact congrArg (fun s : ℝ≥0∞ ↦ s^(1/2 : ℝ))
      (e.sum_comp (fun i ↦ edist (x i) (y i)^2))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SurfaceJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev SurfaceJet (μ : FiniteMeasure NormalBundle) :=
  Lp ℝ 2 (μ : Measure NormalBundle) × Lp Cover 2 (μ : Measure NormalBundle)

def surfaceMultiplier (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Lp ℝ 2 (μ : Measure NormalBundle) →L[ℝ] Lp ℝ 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ q • f
      map_add' := fun f g ↦ Lp.add_smul q f g
      map_smul' := fun c f ↦ (Lp.smul_comm c q f).symm }
    ‖q‖ (fun f ↦ Lp.norm_smul_le q f)

def surfaceJacobiB (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ) : ℝ :=
  ⟪u.2,v.2⟫-⟪surfaceMultiplier μ q u.1,v.1⟫

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothPeriodicScalars : Submodule ℝ (Cover → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ m x,f (x+latticeVector m)=f x}
  zero_mem' := ⟨contDiff_const,by simp⟩
  add_mem' := by
    rintro f g ⟨hf,hfp⟩ ⟨hg,hgp⟩
    exact ⟨hf.add hg,fun m x ↦ by simp only [Pi.add_apply,hfp,hgp]⟩
  smul_mem' := by
    rintro c f ⟨hf,hfp⟩
    exact ⟨contDiff_const.smul hf,fun m x ↦ by simp only [Pi.smul_apply,hfp]⟩

def smoothScalarValue (f : smoothPeriodicScalars) : C(NormalBundle,ℝ) :=
  ⟨fun z ↦ f.val z.1,f.property.1.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩

def smoothScalarGradient (f : smoothPeriodicScalars) : C(NormalBundle,Cover) :=
  ⟨fun z ↦ gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover),by
    have hg : Continuous (fun z : NormalBundle ↦ gradient f.val z.1) :=
      (gradient_contDiff f.property.1).continuous.comp normalEmbedding_continuous.fst
    exact hg.sub (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) hg).smul
      (continuous_subtype_val.comp continuous_snd))⟩

lemma smoothScalarGradient_add (f g : smoothPeriodicScalars) :
    smoothScalarGradient (f+g)=smoothScalarGradient f+smoothScalarGradient g := by
  apply ContinuousMap.ext
  intro z
  have hg : gradient (f.val+g.val) z.1=gradient f.val z.1+gradient g.val z.1 := by
    simp only [gradient,fderiv_add (f.property.1.differentiable (by simp) _)
      (g.property.1.differentiable (by simp) _),map_add]
  change gradient (f.val+g.val) z.1-⟪(z.2 : Cover),gradient (f.val+g.val) z.1⟫ • (z.2 : Cover)=_
  rw [hg,inner_add_right,add_smul]
  change _=(gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))+
    (gradient g.val z.1-⟪(z.2 : Cover),gradient g.val z.1⟫ • (z.2 : Cover))
  abel

lemma smoothScalarGradient_smul (c : ℝ) (f : smoothPeriodicScalars) :
    smoothScalarGradient (c • f)=c • smoothScalarGradient f := by
  apply ContinuousMap.ext
  intro z
  have hg : gradient (c • f.val) z.1=c • gradient f.val z.1 := by
    simp only [gradient,fderiv_const_smul (f.property.1.differentiable (by simp) _) c,map_smul]
  change gradient (c • f.val) z.1-⟪(z.2 : Cover),gradient (c • f.val) z.1⟫ • (z.2 : Cover)=_
  rw [hg,real_inner_smul_right,mul_smul]
  change _=c • (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub]

def surfaceSmoothJet (μ : FiniteMeasure NormalBundle) :
    smoothPeriodicScalars →ₗ[ℝ] SurfaceJet μ where
  toFun f := (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (smoothScalarValue f),
    ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (smoothScalarGradient f))
  map_add' f g := by
    apply Prod.ext
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f+smoothScalarValue g)=_
      exact map_add (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarValue f) (smoothScalarValue g)
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarGradient (f+g))=_
      rw [smoothScalarGradient_add,map_add]
      rfl
  map_smul' c f := by
    apply Prod.ext
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (c • smoothScalarValue f)=_
      exact map_smul (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) c (smoothScalarValue f)
    · change (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ) (smoothScalarGradient (c • f))=_
      rw [smoothScalarGradient_smul,map_smul]
      rfl

def surfaceCurvatureLp (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) : Lp ℝ ∞ (μ : Measure NormalBundle) :=
  ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ
    ⟨fun z ↦ coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)),
      (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalComponentScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (i : Fin 3) : smoothPeriodicScalars :=
  ⟨fun x ↦ ⟪EuclideanSpace.single i 1,N x⟫,(contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover ↦ EuclideanSpace.single i (1 : ℝ))).inner ℝ hN,fun m x ↦ by dsimp; rw [hp]⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_NormalCurvatureScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_curvature_contDiff {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ N) := hN.fderiv_right (by simp)
  exact coverTraceCLM.contDiff.comp (hd.clm_comp hd)

def normalCurvatureScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) : smoothPeriodicScalars :=
  ⟨fun x ↦ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)),normal_curvature_contDiff hN,
    fun m x ↦ by dsimp; rw [fderiv_periodic hp]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def positiveTrunc (n : ℕ) (t : ℝ) : ℝ := t*Real.smoothTransition (((n:ℝ)+1)*t)
def positiveTruncCoeff (t : ℝ) : ℝ := Real.smoothTransition t+t*deriv Real.smoothTransition t

lemma positiveTrunc_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (positiveTrunc n) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def positiveSurfaceValue (f : smoothPeriodicScalars) (z : NormalBundle) : ℝ := max (f.val z.1) 0

def positiveSurfaceGradient (f : smoothPeriodicScalars) : NormalBundle → Cover :=
  {z | 0<f.val z.1}.indicator (smoothScalarGradient f)

lemma positiveSurfaceValue_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    MemLp (positiveSurfaceValue f) 2 (μ : Measure NormalBundle) := by
  exact ((smoothScalarValue f).continuous.max continuous_const).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma positiveSurfaceGradient_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    MemLp (positiveSurfaceGradient f) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarGradient f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator
    (isOpen_lt continuous_const (smoothScalarValue f).continuous).measurableSet

def positiveSurfaceJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) : SurfaceJet μ :=
  ((positiveSurfaceValue_memLp μ f).toLp (positiveSurfaceValue f),
    (positiveSurfaceGradient_memLp μ f).toLp (positiveSurfaceGradient f))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def directionalNormalScalar (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (v : Cover) : smoothPeriodicScalars :=
  ∑ i : Fin 3,v i • normalComponentScalar N hN hp i

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nodalEpsilon (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SmoothScalarSeparatedTrunc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nodalSurfaceValue (f : smoothPeriodicScalars) (D : Set Torus) : NormalBundle → ℝ :=
  (normalProjection ⁻¹' D).indicator (smoothScalarValue f)
def nodalSurfaceGradient (f : smoothPeriodicScalars) (D : Set Torus) : NormalBundle → Cover :=
  (normalProjection ⁻¹' D).indicator (smoothScalarGradient f)

lemma nodalSurfaceValue_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : MemLp (nodalSurfaceValue f D) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarValue f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator (hD.preimage normalProjection_continuous.measurable)
lemma nodalSurfaceGradient_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : MemLp (nodalSurfaceGradient f D) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarGradient f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator (hD.preimage normalProjection_continuous.measurable)

def nodalSurfaceJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : SurfaceJet μ :=
  ((nodalSurfaceValue_memLp μ f D hD).toLp (nodalSurfaceValue f D),
    (nodalSurfaceGradient_memLp μ f D hD).toLp (nodalSurfaceGradient f D))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def IsPositiveNodalPiece (f : smoothPeriodicScalars) (S D : Set Torus) : Prop :=
  (∃ U : Set Torus,IsOpen U ∧ D={a | a∈S ∧ 0<f.val (representative a)}∩U) ∧
  (∃ C : Set Torus,IsClosed C ∧ D={a | a∈S ∧ 0<f.val (representative a)}∩C)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def positiveBoundaryLocus (f : smoothPeriodicScalars) (S : Set Torus) : Set S :=
  {a | 0<f.val (representative a.val)}

def positiveBoundaryDomain (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : Set Torus :=
  (fun b : positiveBoundaryLocus f S ↦ b.val.val) '' connectedComponent a

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateReflection (i : Fin 3) : Torus → Torus :=
  fun x => WithLp.toLp 2 (fun j => if j=i then -x j else x j)

@[simp] lemma coordinateReflection_apply (i : Fin 3) (x : Torus) (j : Fin 3) :
    coordinateReflection i x j=if j=i then -x j else x j := rfl

@[simp] lemma coordinateReflection_involutive (i : Fin 3) (x : Torus) :
    coordinateReflection i (coordinateReflection i x)=x := by
  ext j
  by_cases h : j=i <;> simp [h]

lemma coordinateReflection_isometry (i : Fin 3) : Isometry (coordinateReflection i) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i <;> simp [h,neg_add_eq_sub,norm_sub_rev]

def coordinateReflectionEquiv (i : Fin 3) : Torus ≃ᵢ Torus where
  toFun := coordinateReflection i
  invFun := coordinateReflection i
  left_inv := coordinateReflection_involutive i
  right_inv := coordinateReflection_involutive i
  isometry_toFun := coordinateReflection_isometry i

def coverCoordinateReflection (i : Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] lemma coverCoordinateReflection_apply (i : Fin 3) (x : Cover) (j : Fin 3) :
    coverCoordinateReflection i x j=if j=i then -x j else x j := by
  simp only [coverCoordinateReflection,LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

@[simp] lemma coverCoordinateReflection_involutive (i : Fin 3) (x : Cover) :
    coverCoordinateReflection i (coverCoordinateReflection i x)=x := by
  ext j
  by_cases h : j=i <;> simp [h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateReflectedField (i : Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => coverCoordinateReflection i (F (coverCoordinateReflection i x))

def coordinateEvenField (i : Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => (1/2 : ℝ) • (F x+coordinateReflectedField i F x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateSine (i : Fin 3) (x : Cover) : ℝ := Real.sin (2*Real.pi*x i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateHalf (i : Fin 3) (a : ℝ) : Set Torus :=
  {z | Real.sin (2*Real.pi*((representative z) i-a))<0}

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceGraphBundleMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Measurable (graphUnitNormalExtension a n g) := by
  have hm : Measurable (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  exact (graphSlopeNormal_contDiff hn).continuous.measurable.comp
    (hm.comp ((normalPlaneCoordinates n).continuous.measurable.comp (measurable_id.sub measurable_const)))

def graphNormalSection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) : BlowupNormalBundle :=
  (x, ⟨graphUnitNormalExtension a n g x, graphUnitNormalExtension_unit a hn g x⟩)

lemma graphNormalSection_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Measurable (graphNormalSection a hn g) :=
  measurable_id.prodMk (graphUnitNormalExtension_measurable a hn g).subtype_mk

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def clampCell (x : Cover) : CompactCell :=
  ⟨WithLp.toLp 2 (fun i => max 0 (min 1 (x i))),
    ⟨fun i => max 0 (min 1 (x i)),
      ⟨fun _ => le_max_left _ _, fun _ => max_le zero_le_one (min_le_left _ _)⟩, rfl⟩⟩

lemma continuous_clampCell : Continuous clampCell := by
  apply Continuous.subtype_mk
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    (continuous_pi (fun i => continuous_const.max (continuous_const.min (by fun_prop))))

def normalCellProjection (z : BlowupNormalBundle) : NormalBundle :=
  (clampCell z.1, z.2)

lemma continuous_normalCellProjection : Continuous normalCellProjection :=
  (continuous_clampCell.comp continuous_fst).prodMk continuous_snd

def actualNormalGraphChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : NormalBundle :=
  normalCellProjection (graphNormalSection a hn g (a + normalGraph n g y))

lemma actualNormalGraphChart_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) : Measurable (actualNormalGraphChart a hn g) := by
  apply continuous_normalCellProjection.measurable.comp
  apply (graphNormalSection_measurable a hn g).comp
  simpa only [id_eq] using (graph_trace_continuous a n hg continuous_id).measurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def lpPullbackLE {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) :
    Lp F 2 μ →L[ℝ] Lp F 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ f ⟨hf,rfl⟩).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using hle))

def graphCovector (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover →L[ℝ] Plane :=
  normalPlaneCoordinates n + (innerSL ℝ n).smulRight (gradient g y)

lemma measurable_graphCovector (n : Cover) (g : Plane → ℝ) :
    Measurable (graphCovector n g) := by
  have hm : Measurable (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  exact measurable_const.add ((ContinuousLinearMap.smulRightL ℝ Cover Plane (innerSL ℝ n)).continuous.measurable.comp hm)

lemma graphCovector_norm_le {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphCovector n g y‖ ≤ 1+K := by
  calc
    _ ≤ ‖normalPlaneCoordinates n‖+‖(innerSL ℝ n).smulRight (gradient g y)‖ := norm_add_le _ _
    _ ≤ 1+‖innerSL ℝ n‖*‖gradient g y‖ := add_le_add (norm_normalPlaneCoordinates_le n) (ContinuousLinearMap.norm_smulRight_apply _ _).le
    _ ≤ 1+K := by
      rw [innerSL_apply_norm,hn,one_mul]
      apply add_le_add le_rfl
      simpa only [gradient, LinearIsometryEquiv.norm_map] using norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)

lemma graphCovector_memLp {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    MemLp (graphCovector n g) ∞ ν :=
  memLp_top_of_bound (measurable_graphCovector n g).aestronglyMeasurable (1+K)
    (ae_of_all _ (graphCovector_norm_le hn hg))

def graphCovectorLp {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Lp Cover 2 ν →L[ℝ] Lp Plane 2 ν :=
  (ContinuousLinearMap.id ℝ (Cover →L[ℝ] Plane)).holderL ν ∞ 2 2
    ((graphCovector_memLp (ν := ν) hn hg).toLp (graphCovector n g))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def PlaneWeakGradientOn (S : Set Plane) (u : Plane → ℝ) (G : Plane → Plane) : Prop :=
  ∀ (v : Plane) (ψ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ⊆S → (∫ y in S, ⟪G y,v⟫*ψ y)= -(∫ y in S,u y*fderiv ℝ ψ y v)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Tangency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def periodicGraphScalar (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : smoothPeriodicScalars :=
  ⟨latticePeriodize (fun x => χ x*graphHeightExtension a n ψ x),
    latticePeriodize_contDiff (hχ.mul (graphHeightExtension_contDiff a n hψ)) hc.mul_right,
    latticePeriodize_periodic _⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceNormalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma reverseNormal_reverseNormal (z : NormalBundle) :
    reverseNormal (reverseNormal z)=z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext; simp [reverseNormal]

lemma reverseNormal_measurePreserving_back (μ : FiniteMeasure NormalBundle) :
    MeasurePreserving reverseNormal (μ.map reverseNormal : Measure NormalBundle)
      (μ : Measure NormalBundle) := by
  refine ⟨continuous_reverseNormal.measurable,?_⟩
  change Measure.map reverseNormal (Measure.map reverseNormal (μ : Measure NormalBundle))=_
  rw [Measure.map_map continuous_reverseNormal.measurable continuous_reverseNormal.measurable]
  simp only [Function.comp_def,reverseNormal_reverseNormal,Measure.map_id']

def normalReverseLp (μ : FiniteMeasure NormalBundle) (p : ℝ≥0∞) [Fact (1≤p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F p (μ : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp F p (μ.map reverseNormal : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ reverseNormal (reverseNormal_measurePreserving_back μ)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma translateNormal_measurePreserving (μ : FiniteMeasure NormalBundle) (a : Cover) :
    MeasurePreserving (translateNormal a) (μ : Measure NormalBundle)
      (μ.map (translateNormal a) : Measure NormalBundle) :=
  ⟨measurable_translateNormal a,rfl⟩

def normalTranslationLp (μ : FiniteMeasure NormalBundle) (a : Cover)
    (p : ℝ≥0∞) [Fact (1≤p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F p (μ.map (translateNormal a) : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp F p (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ (translateNormal a) (translateNormal_measurePreserving μ a)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeFrameOperator (B : Plane → Fin 2 → Plane) (b : Plane → Plane)
    (f : Plane → ℝ) (x : Plane) : ℝ :=
  (∑ i,⟪fderiv ℝ (gradient f) x (B x i),B x i⟫)+⟪gradient f x,b x⟫

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev PlaneSmooth (f : Plane → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

def planeElliptic (A : Plane → Plane →L[ℝ] Plane) (f : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun x => A x (gradient f x))

def planeDrift (b : Plane → Plane) (f : Plane → ℝ) (x : Plane) : ℝ :=
  fderiv ℝ f x (b x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeEnergy (A : Plane → Plane →L[ℝ] Plane) (u : Plane → ℝ) (x : Plane) : ℝ :=
  ⟪gradient u x,A x (gradient u x)⟫

def planeRellichFlux (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (u : Plane → ℝ) (x : Plane) : Plane :=
  (2*planeDrift b u x+planeDivergence b x*u x) • A x (gradient u x)-
    planeEnergy A u x • b x-
    ((1/2:ℝ)*u x^2) • A x (gradient (planeDivergence b) x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCarlemanS (A : Plane → Plane →L[ℝ] Plane) (q : Plane → ℝ)
    (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ := planeElliptic A u x+τ^2*q x*u x

def planeCarlemanT (b : Plane → Plane) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ :=
  -τ*(2*planeDrift b u x+planeDivergence b x*u x)

def planeCarlemanP (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : ℝ :=
  planeCarlemanS A q τ u x+planeCarlemanT b τ u x

def planeCarlemanR (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (x w : Plane) : ℝ := 4*⟪w,fderiv ℝ b x (A x w)⟫-
      2*⟪w,(fderiv ℝ A x (b x)) w⟫

def planeCarlemanFlux (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (τ : ℝ) (u : Plane → ℝ) (x : Plane) : Plane :=
  (2*τ) • planeRellichFlux A b u x+(2*τ^3*q x*u x^2) • b x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure PlaneCarlemanData (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (q : Plane → ℝ) (U : Set Plane) (C D Q c : ℝ) : Prop where
  C_nonneg : 0≤C
  D_nonneg : 0≤D
  pseudoconvex : 2≤2*c-(C+1)*Q
  principal : ∀ x∈U,∀ w,-C*⟪w,A x w⟫≤planeCarlemanR A b x w
  weight_bound : ∀ x∈U,q x≤Q
  transport_bound : ∀ x∈U,c≤planeDrift b q x
  remainder_bound : ∀ x∈U,planeElliptic A (planeDivergence b) x≤D

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneQuadraticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeQuadraticWeight (a n : Plane) (κ ε : ℝ) (x : Plane) : ℝ :=
  ⟪n,x-a⟫+(κ/2)*⟪n,x-a⟫^2-(ε/2)*‖x-a‖^2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma planeElliptic_zero (A : Plane → Plane →L[ℝ] Plane) (x : Plane) :
    planeElliptic A (fun _ => 0) x=0 := by
  simp [planeElliptic,planeDivergence,gradient]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeHopfBarrier (c : Plane) (α R : ℝ) (x : Plane) : ℝ :=
  Real.exp (-α*‖x-c‖^2)-Real.exp (-α*R^2)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CMCFrameOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSymbolDrift (A : Plane → Plane →L[ℝ] Plane) (x : Plane) : Plane :=
  ∑ j : Fin 2,planeDivergence (fun z => A z (EuclideanSpace.single j 1)) x •
    EuclideanSpace.single j 1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTranslationNumerator (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : ℝ := σ*(⟪v,n⟫-⟪normalPlaneCoordinates n v,gradient g y⟫)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CMCSecantSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcSecant (p q : Plane) : Plane →L[ℝ] Plane :=
  ((cmcWeight p+cmcWeight q)/(2*cmcWeight p*cmcWeight q)) •
    ContinuousLinearMap.id ℝ Plane -
  (1/(2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))) •
    (innerSL ℝ (p+q)).smulRight (p+q)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure OrientedCMCCharts (S : Set Torus) (H : ℝ) (N : Cover → Cover) : Prop where
  normal_smooth : ContDiff ℝ (⊤ : ℕ∞) N
  normal_periodic : ∀ m x,N (x+latticeVector m)=N x
  chart : ∀ x : Cover,quotientMap x∈S → ‖N x‖=1 ∧
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (x+normalGraph (N x) f y)=graphSlopeNormal (N x) (gradient f y) ∧
        quotientMap (x+normalGraph (N x) f y)∈S ∧
        planeDivergence (fun z => cmcFlux (gradient f z)) y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S ↔
        normalGraph (N x) f (normalPlaneCoordinates (N x) v)=v

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_MinimizerAxialCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCenter (v : Cover) (H : ℝ) (N : Cover → Cover) (x : Cover) : Cover :=
  x-⟪v,x⟫ • v-H⁻¹ • N x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialProjection (v : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover-(innerSL ℝ v).smulRight v

@[simp] lemma axialProjection_apply (v x : Cover) :
    axialProjection v x=x-⟪v,x⟫ • v := rfl

def euclideanCylinder (v c : Cover) (R : ℝ) : Set Cover :=
  {x | ‖axialProjection v (x-c)‖=R}

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_TorusCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def torusAxialProjection (i : Fin 3) (x : Torus) : Torus :=
  WithLp.toLp 2 (fun j => if j=i then 0 else x j)

@[simp] lemma torusAxialProjection_apply (i : Fin 3) (x : Torus) (j : Fin 3) :
    torusAxialProjection i x j=if j=i then 0 else x j := rfl

@[simp] lemma torusAxialProjection_zero (i : Fin 3) : torusAxialProjection i 0=0 := by ext j; simp

def axialTube (i : Fin 3) (c : Torus) (r : ℝ) : Set Torus :=
  {x | ‖torusAxialProjection i (x-c)‖ < r}

def axialTubeExterior (i : Fin 3) (c : Torus) (r : ℝ) : Set Torus :=
  {x | r<‖torusAxialProjection i (x-c)‖}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma torusCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Torus) (i : Fin 3) :
    torusCoordinatePermute e x i=x (e i) := rfl

@[simp] lemma torusCoordinatePermute_inverse (e : Fin 3 ≃ Fin 3) (x : Torus) :
    torusCoordinatePermute e (torusCoordinatePermute e.symm x)=x := by ext i; simp

def coverCoordinatePermute (e : Fin 3 ≃ Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

@[simp] lemma coverCoordinatePermute_apply (e : Fin 3 ≃ Fin 3) (x : Cover) (i : Fin 3) :
    coverCoordinatePermute e x i=x (e i) := rfl

@[simp] lemma coverCoordinatePermute_inverse (e : Fin 3 ≃ Fin 3) (x : Cover) :
    coverCoordinatePermute e (coverCoordinatePermute e.symm x)=x := by ext i; simp

lemma coverCoordinatePermute_single (e : Fin 3 ≃ Fin 3) (j : Fin 3) :
    coverCoordinatePermute e (EuclideanSpace.single j 1)=EuclideanSpace.single (e.symm j) 1 := by
  exact LinearIsometryEquiv.piLpCongrLeft_single e.symm j (1 : ℝ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePermutedField (e : Fin 3 ≃ Fin 3) (F : Cover → Cover) : Cover → Cover :=
  fun x => coverCoordinatePermute e.symm (F (coverCoordinatePermute e x))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateChamber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateChamber (s : Fin 3 → Bool) : Set Torus :=
  ⋂ i,coordinateHalf i (if s i then 0 else 1/2)

def chamberCorner (s : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i => if s i then (1/2 : ℝ) else 0)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def openHalfBox (c : Cover) : Set Cover := {x | ∀ i,c i<x i ∧ x i < c i+1/2}
def closedHalfBox (c : Cover) : Set Cover := {x | ∀ i,c i≤x i ∧ x i ≤ c i+1/2}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def foldCoordinate (i : Fin 3) (d : ℝ) (upper : Bool) (x : Cover) : Cover :=
  x+((if upper then d-|x i-d| else d+|x i-d|)-x i) • EuclideanSpace.single i 1

def localFoldCoordinate (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) (x : Cover) : Cover :=
  if y i=chamberCorner s i then foldCoordinate i (chamberCorner s i) false x
  else if y i=chamberCorner s i+1/2 then foldCoordinate i (chamberCorner s i+1/2) true x else x

def localChamberFold (s : Fin 3 → Bool) (y x : Cover) : Cover :=
  localFoldCoordinate s y 2 (localFoldCoordinate s y 1 (localFoldCoordinate s y 0 x))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberGlobalFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def chamberFoldLift (s : Fin 3 → Bool) (a : Torus) : Cover :=
  localChamberFold s (chamberCorner s)
    (shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s)

def chamberVertex (s b : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i => chamberCorner s i+if b i then (1/2 : ℝ) else 0)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def chamberSegment (x y : Cover) (t : ℝ) : Cover := x+t • (y-x)

@[simp] lemma chamberSegment_apply (x y : Cover) (t : ℝ) (i : Fin 3) :
    chamberSegment x y t i=x i+t*(y i-x i) := rfl

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePlaneLift : ℂ →L[ℝ] Cover :=
  Complex.reCLM.smulRight (EuclideanSpace.single 1 1)+
    Complex.imCLM.smulRight (EuclideanSpace.single 2 1)

def coordinateSectionPoint (c : Cover) (t : ℝ) (z : ℂ) : Cover :=
  c+(t-c 0) • EuclideanSpace.single 0 1+coordinatePlaneLift z

@[simp] lemma coordinatePlaneLift_apply (z : ℂ) (i : Fin 3) :
    coordinatePlaneLift z i=if i=1 then z.re else if i=2 then z.im else 0 := by
  fin_cases i <;> simp [coordinatePlaneLift]

@[simp] lemma coordinateSectionPoint_apply (c : Cover) (t : ℝ) (z : ℂ) (i : Fin 3) :
    coordinateSectionPoint c t z i=if i=0 then t else if i=1 then c 1+z.re else c 2+z.im := by
  fin_cases i <;> simp [coordinateSectionPoint]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialNormalWeight (i : Fin 3) (z : NormalBundle) : ℝ := 1-((z.2 : Cover) i)^2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialFluxWeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) : ℝ :=
  (∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle))/(μ.mass : ℝ)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialWeightedHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def axialBundleHeight (i : Fin 3) (z : NormalBundle) : AddCircle (1 : ℝ) := z.1.1 i

def axialCoverHeight (i : Fin 3) (x : Cover) : AddCircle (1 : ℝ) := x i

def axialWeightedHeight (μ : FiniteMeasure NormalBundle) (i : Fin 3) : Measure (AddCircle (1 : ℝ)) :=
  Measure.map (axialBundleHeight i)
    ((μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (axialNormalWeight i z)))

def axialVolumeHeight (E : Set Torus) (i : Fin 3) : Measure (AddCircle (1 : ℝ)) :=
  Measure.map (axialCoverHeight i) (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))

instance axialVolumeHeight_finite (E : Set Torus) (i : Fin 3) :
    IsFiniteMeasure (axialVolumeHeight E i) := by
  unfold axialVolumeHeight
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCriticalLift (E : Set Torus) (N : Cover → Cover) (i : Fin 3) : Set Cover :=
  {x | quotientMap x∈frontier (openRepresentative E) ∧ ∀ j : Fin 3,j≠i → N x j=0}

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSplit (i : Fin 3) : Cover ≃ᵐ ℝ × Plane :=
  (coverCoordinatePermute (Equiv.swap 0 i)).toMeasurableEquiv.trans UpperComparison.tubeSplit

@[simp] lemma axialSplit_fst (i : Fin 3) (x : Cover) : (axialSplit i x).1=x i := by
  simp [axialSplit]

@[simp] lemma axialSplit_symm_axis (i : Fin 3) (z : ℝ × Plane) : (axialSplit i).symm z i=z.1 := by
  simpa only [axialSplit_fst] using congrArg Prod.fst ((axialSplit i).apply_symm_apply z)

def transverseSquare : Set Plane := {y | ∀ j,0≤y j ∧ y j<1}

def axialSection (E : Set Torus) (i : Fin 3) (t : ℝ) : Set Plane :=
  transverseSquare∩(fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E

def axialSectionArea (E : Set Torus) (i : Fin 3) (t : ℝ) : ℝ :=
  volume.real (axialSection E i t)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSplit_symm_axis_line (i : Fin 3) (u v : ℝ) (y : Plane) :
    (axialSplit i).symm (u,y)=(axialSplit i).symm (v,y)+(u-v) • EuclideanSpace.single i 1 := by
  let L := coverCoordinatePermute (Equiv.swap 0 i)
  change L.symm (UpperComparison.tubeSplit.symm _) = L.symm (UpperComparison.tubeSplit.symm _)+_
  apply L.injective
  rw [map_add,map_smul,L.apply_symm_apply,L.apply_symm_apply]
  change UpperComparison.tubeSplit.symm _=UpperComparison.tubeSplit.symm _+
    (u-v) • coverCoordinatePermute (Equiv.swap 0 i) (EuclideanSpace.single i 1)
  rw [coverCoordinatePermute_single]
  simp only [Equiv.symm_swap,Equiv.swap_apply_right]
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Classical
namespace CubicTorus

lemma periodic_unit_sine : Function.Periodic (fun t : ℝ => Real.sin (2*Real.pi*t)) 1 := by
  intro t
  dsimp only
  rw [show 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi by ring,Real.sin_add_two_pi]

def circleUnitSine : AddCircle (1 : ℝ) → ℝ := periodic_unit_sine.lift

@[simp] lemma circleUnitSine_coe (t : ℝ) : circleUnitSine t=Real.sin (2*Real.pi*t) :=
  Function.Periodic.lift_coe periodic_unit_sine t

def chamberHeightSign (b : Bool) (t : AddCircle (1 : ℝ)) : ℝ :=
  if (if b then circleUnitSine t<0 else 0 < circleUnitSine t) then 1 else -1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSection_periodic (E : Set Torus) (i : Fin 3) :
    Function.Periodic (axialSection E i) 1 := by
  intro t
  ext y
  have he : EuclideanSpace.single i (1 : ℝ)=latticeVector (Pi.single i (1 : ℤ)) := by
    ext j
    simp [latticeVector,Pi.single_apply]
  have hq : quotientMap ((axialSplit i).symm (t+1,y))=quotientMap ((axialSplit i).symm (t,y)) := by
    rw [axialSplit_symm_axis_line i (t+1) t y,show t+1-t=1 by ring,one_smul,he,
      quotientMap_add,quotientMap_latticeVector,add_zero]
  simp only [axialSection,mem_inter_iff,mem_preimage,hq]

lemma axialSectionArea_periodic (E : Set Torus) (i : Fin 3) :
    Function.Periodic (axialSectionArea E i) 1 := fun t =>
  congrArg (fun S : Set Plane => volume.real S) (axialSection_periodic E i t)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialFluxDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def axialCircleArea (E : Set Torus) (i : Fin 3) : AddCircle (1 : ℝ) → ℝ :=
  (axialSectionArea_periodic E i).lift

@[simp] lemma axialCircleArea_coe (E : Set Torus) (i : Fin 3) (t : ℝ) :
    axialCircleArea E i t=axialSectionArea E i t :=
  Function.Periodic.lift_coe (axialSectionArea_periodic E i) t

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSectionIntegral (E : Set Torus) (i : Fin 3) (g : Cover → ℝ) (t : ℝ) : ℝ :=
  ∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*
    g ((axialSplit i).symm (t,y))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialNormalCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialTangentPart (i : Fin 3) (u : Cover) : Cover := u-u i • EuclideanSpace.single i 1

def axialNormalCalibration (N : Cover → Cover) (i : Fin 3) : Cover → Cover :=
  regularizedNormal (fun x => axialTangentPart i (N x))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSlicePerimeter (E : Set Torus) (i : Fin 3) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F) (_ : ∀ x,F x i=0),
    ENNReal.ofReal (axialSectionIntegral E i (divergence F) t)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_SliceJensenWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace CubicTorus

def axialJensenFlux (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H V : ℝ)
    (i : Fin 3) (t : AddCircle (1 : ℝ)) : ℝ :=
  (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalMeasureCoordinatePermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def permuteNormal (e : Fin 3 ≃ Fin 3) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (torusCoordinatePermute e (quotientMap z.1)),
    ⟨coverCoordinatePermute e z.2,by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlanarRadialArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

def planarRadialRegion (r : ℝ → ℝ) : Set ℂ :=
  {z | ‖z‖ < r (z.arg/(2*Real.pi))}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped Real
namespace CubicTorus

def complexDet (z w : ℂ) : ℝ := z.re*w.im-z.im*w.re

def complexRealDiv (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ F z 1).re+(fderiv ℝ F z Complex.I).im

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePlaneProjection : Cover →L[ℝ] ℂ :=
  (EuclideanSpace.proj (1 : Fin 3)).smulRight (1 : ℂ)+
    (EuclideanSpace.proj (2 : Fin 3)).smulRight Complex.I

@[simp] lemma coordinatePlaneProjection_re (u : Cover) : (coordinatePlaneProjection u).re=u 1 := by
  simp [coordinatePlaneProjection]
@[simp] lemma coordinatePlaneProjection_im (u : Cover) : (coordinatePlaneProjection u).im=u 2 := by
  simp [coordinatePlaneProjection]

def coordinatePlaneField (F : Cover → Cover) (c : Cover) (t : ℝ) : ℂ → ℂ :=
  fun z => coordinatePlaneProjection (F (coordinateSectionPoint c t z))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_RadialSectionArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def centeredPlaneSection (E : Set Torus) (c : Cover) (t : ℝ) : Set ℂ :=
  {z | complexSquareGauge z<1/2 ∧ quotientMap (coordinateSectionPoint c t z)∈E}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma tubeSplit_symm_one (p : ℝ × Plane) : UpperComparison.tubeSplit.symm p 1=p.2 0 :=
  UpperComparison.tubeSplit_symm_succ p 0

@[simp] lemma tubeSplit_symm_two (p : ℝ × Plane) : UpperComparison.tubeSplit.symm p 2=p.2 1 :=
  UpperComparison.tubeSplit_symm_succ p 1

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def TrueRadialTube (E : Set Torus) (c : Cover) (r : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) r ∧
  (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
  (∀ p,0 < r p ∧ r p<unitSquareScale p.2) ∧
  (∀ p,quotientMap (coordinateSectionPoint c p.1
    (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
  (∀ p u,0≤u → u≤unitSquareScale p.2 →
    (quotientMap (coordinateSectionPoint c p.1
      (u • unitAngle p.2))∈openRepresentative E ↔ u < r p)) ∧
  (∀ p u,0≤u → u≤unitSquareScale p.2 →
    (quotientMap (coordinateSectionPoint c p.1
      (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r p)) ∧
  ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
    ε ≤ r (t,a) ∧ r (t,a)+ε≤unitSquareScale a

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_SurfaceJacobiLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def periodicCoordinate (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (j : Fin 3) : smoothPeriodicScalars := by
  refine ⟨fun x => g (x j-c j),hg.comp ((EuclideanSpace.proj j : Cover →L[ℝ] ℝ).contDiff.sub contDiff_const),?_⟩
  intro m x
  change g (x j+(m j : ℝ)-c j)=g (x j-c j)
  convert hp.int_mul (m j) (x j-c j) using 1; congr 1; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def periodicRotation (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (x : Cover) : Cover :=
  (periodicCoordinate g hg hp c 1).val x • EuclideanSpace.single 2 1-
    (periodicCoordinate g hg hp c 2).val x • EuclideanSpace.single 1 1

lemma periodicRotation_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicRotation g hg hp c) :=
  ((periodicCoordinate g hg hp c 1).property.1.smul contDiff_const).sub
    ((periodicCoordinate g hg hp c 2).property.1.smul contDiff_const)

lemma periodicRotation_periodic (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (m : Fin 3 → ℤ) (x : Cover) :
    periodicRotation g hg hp c (x+latticeVector m)=periodicRotation g hg hp c x := by
  simp only [periodicRotation,(periodicCoordinate g hg hp c 1).property.2 m x,
    (periodicCoordinate g hg hp c 2).property.2 m x]

def periodicRotationNormalScalar (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x) :
    smoothPeriodicScalars := by
  refine ⟨fun x => ⟪N x,periodicRotation g hg hp c x⟫,
    hN.inner ℝ (periodicRotation_contDiff g hg hp c),?_⟩
  intro m x
  dsimp only
  rw [hNp,periodicRotation_periodic]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTangentRotation (N : Cover → Cover) (x : Cover) : Cover :=
  N x 2 • EuclideanSpace.single 1 1-N x 1 • EuclideanSpace.single 2 1

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def firstReflection : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 3 ↦
    if i=0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] lemma firstReflection_apply (x : Cover) (i : Fin 3) :
    firstReflection x i=if i=0 then -x i else x i := by
  simp only [firstReflection,LinearIsometryEquiv.piLpCongrRight_apply,WithLp.ofLp_toLp]
  split_ifs <;> rfl

@[simp] lemma firstReflection_involutive (x : Cover) :
    firstReflection (firstReflection x)=x := by
  ext i
  simp only [firstReflection_apply]
  split_ifs <;> simp

def torusFirstReflection : Torus ≃ᵢ Torus where
  toFun x := WithLp.toLp 2 (fun i ↦ if i=0 then -x i else x i)
  invFun x := WithLp.toLp 2 (fun i ↦ if i=0 then -x i else x i)
  left_inv x := by ext i; dsimp; split_ifs <;> simp
  right_inv x := by ext i; dsimp; split_ifs <;> simp
  isometry_toFun x y := by
    rw [PiLp.edist_eq_of_L2,PiLp.edist_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    split_ifs <;> simp

@[simp] lemma torusFirstReflection_apply (x : Torus) (i : Fin 3) :
    torusFirstReflection x i=if i=0 then -x i else x i := rfl

@[simp] lemma torusFirstReflection_involutive (x : Torus) :
    torusFirstReflection (torusFirstReflection x)=x := by
  exact torusFirstReflection.symm_apply_apply x

lemma firstReflection_quotient (x : Cover) :
    quotientMap (firstReflection x)=torusFirstReflection (quotientMap x) := by
  ext i
  simp only [quotientMap,WithLp.ofLp_toLp,firstReflection_apply,torusFirstReflection_apply]
  split_ifs <;> simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure LatticeIsometry where
  cover : Cover ≃ₗᵢ[ℝ] Cover
  torus : Torus ≃ᵢ Torus
  commute : ∀ x,quotientMap (cover x)=torus (quotientMap x)

namespace LatticeIsometry

def symm (e : LatticeIsometry) : LatticeIsometry where
  cover := e.cover.symm
  torus := e.torus.symm
  commute x := by
    apply e.torus.injective
    rw [←e.commute,e.cover.apply_symm_apply,e.torus.apply_symm_apply]

lemma map_zero (e : LatticeIsometry) : e.torus 0=0 := by
  have hz : quotientMap (0 : Cover) = 0 := by ext j; simp [quotientMap]
  simpa only [LinearIsometryEquiv.map_zero,hz] using (e.commute 0).symm

lemma map_add (e : LatticeIsometry) (x y : Torus) : e.torus (x+y)=e.torus x+e.torus y := by
  obtain ⟨a,rfl⟩ := quotientMap_surjective x
  obtain ⟨b,rfl⟩ := quotientMap_surjective y
  rw [←quotientMap_add,←e.commute,LinearIsometryEquiv.map_add,quotientMap_add,e.commute,e.commute]

def addHom (e : LatticeIsometry) : Torus →+ Torus where
  toFun := e.torus
  map_zero' := e.map_zero
  map_add' := e.map_add

def pullback (e : LatticeIsometry) (F : Cover → Cover) : Cover → Cover :=
  fun x ↦ e.cover.symm (F (e.cover x))

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def centeredIsometryLift (φ : Torus ≃ᵢ Torus) (x : Cover) : Cover :=
  shortestLift (φ (quotientMap x) - φ 0)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CenteredJacobiChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure CenteredJacobiChart (E : Set Torus) (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) where
  n : Cover
  g : Plane → ℝ
  sign : ℝ
  K : ℝ≥0
  R : ℝ
  ρ : ℝ
  r : ℝ
  U : Set Cover
  C : ℝ≥0∞
  n_unit : ‖n‖=1
  smooth : ContDiff ℝ (⊤ : ℕ∞) g
  compact : HasCompactSupport g
  lip : LipschitzWith K g
  zero : g 0=0
  sign_eq : sign=1 ∨ sign= -1
  R_pos : 0<R
  rho_pos : 0<ρ
  r_pos : 0 < r
  open_U : IsOpen U
  patch_in_U : Metric.closedBall cubeCenter (2*ρ)⊆U
  U_in_ball : U⊆Metric.ball cubeCenter R
  U_in_cell : U⊆{x | ∀ i,0<x i ∧ x i<1}
  phase : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
    (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))
  normal_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    N (cubeCenter+normalGraph n g y)=sign•graphSlopeNormal n (gradient g y)
  boundary_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)
  image_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (ρ/2)
  slope_disk : ∀ y∈Metric.closedBall (0 : Plane) r,‖gradient g y‖≤(1/4 : ℝ)
  C_finite : C≠⊤
  domination : Measure.map (fun y : Plane ↦ quotientMap (cubeCenter+normalGraph n g y))
    (volume.restrict (Metric.closedBall 0 r))≤C•(spatialNormalMeasure μ : Measure Torus)
  cover_germ : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
    normalGraph n g (normalPlaneCoordinates n v)=v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjection_measurePreserving (μ : FiniteMeasure NormalBundle) :
    MeasurePreserving normalProjection (μ : Measure NormalBundle)
      (spatialNormalMeasure μ : Measure Torus) :=
  ⟨normalProjection_continuous.measurable,rfl⟩

def spatialPullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Lp W 2 (spatialNormalMeasure μ : Measure Torus) →ₗᵢ[ℝ]
      Lp W 2 (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ normalProjection (normalProjection_measurePreserving μ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def dominatedL2Pullback {α β W : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ν : Measure α) (μ : Measure β) (f : α → β) (hf : Measurable f)
    {C : ℝ≥0∞} (hC : C≠⊤) (hdom : Measure.map f ν≤C•μ) :
    Lp W 2 μ →L[ℝ] Lp W 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ f (show MeasurePreserving f ν (Measure.map f ν) from
    ⟨hf,rfl⟩)).toContinuousLinearMap.comp (Lp.LpToLpOfMeasureLeSMul hC hdom)

def spatialPushdown (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] :
    Lp W 2 (μ : Measure NormalBundle) →L[ℝ]
      Lp W 2 (spatialNormalMeasure μ : Measure Torus) :=
  (spatialPullback μ W).toContinuousLinearMap.adjoint

@[simp] lemma spatialPushdown_pullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (u : Lp W 2 (spatialNormalMeasure μ : Measure Torus)) :
    spatialPushdown μ W (spatialPullback μ W u)=u := by
  exact congr($(spatialPullback μ W |>.adjoint_comp_self) u)

def surfaceChartPullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (F : Plane → Torus) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map F (volume.restrict D)≤C•(spatialNormalMeasure μ : Measure Torus)) :
    Lp W 2 (μ : Measure NormalBundle) →L[ℝ] Lp W 2 (volume.restrict D) :=
  (dominatedL2Pullback (volume.restrict D) (spatialNormalMeasure μ : Measure Torus)
    F hF hC hdom).comp (spatialPushdown μ W)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalProjectedGradient (N : Cover → Cover) (F : Cover → ℝ) (x : Cover) : Cover :=
  gradient F x-⟪N x,gradient F x⟫ • N x

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def HasPlanarWeakGradient (D : Set Plane) (v : Plane → ℝ) (G : Plane → Plane) : Prop :=
  MemLp v 2 (volume.restrict D) ∧ MemLp G 2 (volume.restrict D) ∧
  ∀ φ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ⊆D →
    ∀ w : Plane,(∫ y in D,φ y*⟪G y,w⟫)= -(∫ y in D,fderiv ℝ φ y w*v y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace CenteredJacobiChart
variable {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}

def parameter (c : CenteredJacobiChart E μ N) : Plane → Cover :=
  fun y ↦ cubeCenter+normalGraph c.n c.g y

lemma parameter_smooth (c : CenteredJacobiChart E μ N) :
    ContDiff ℝ (⊤ : ℕ∞) c.parameter :=
  contDiff_const.add ((normalPlaneLinearIsometry c.n).contDiff.add (c.smooth.smul contDiff_const))

lemma parameter_measurable (c : CenteredJacobiChart E μ N) :
    Measurable (fun y ↦ quotientMap (c.parameter y)) :=
  (continuous_quotientMap.comp c.parameter_smooth.continuous).measurable

def value (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) :=
  surfaceChartPullback μ ℝ (Metric.closedBall 0 c.r) (fun y ↦ quotientMap (c.parameter y))
    c.parameter_measurable c.C_finite c.domination u.1

def ambientGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) :=
  surfaceChartPullback μ Cover (Metric.closedBall 0 c.r) (fun y ↦ quotientMap (c.parameter y))
    c.parameter_measurable c.C_finite c.domination u.2

def planarGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : Plane :=
  (fderiv ℝ c.parameter y).adjoint (c.ambientGradient u y)

def weight (c : CenteredJacobiChart E μ N) (y : Plane) : ℝ := cmcWeight (gradient c.g y)

def weightedValue (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : ℝ :=
  c.weight y*(Metric.closedBall (0 : Plane) c.r).indicator (c.value u) y

def weightedGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : Plane :=
  c.weight y • (Metric.closedBall (0 : Plane) c.r).indicator (c.planarGradient u) y+
    (Metric.closedBall (0 : Plane) c.r).indicator (c.value u) y • gradient c.weight y

end CenteredJacobiChart
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSlopeClamp (p : Plane) : Plane := (max (1 : ℝ) ‖p‖)⁻¹ • p

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NodalTorusScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nodalTorusScalar (f : smoothPeriodicScalars) (D : Set Torus) : Torus → ℝ :=
  D.indicator (fun a ↦ f.val (representative a))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeRadialExp (a : Plane) (k : ℝ) (y : Plane) : ℝ :=
  Real.exp (-k*‖y-a‖^2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeTransport (b : Plane → Plane) (f : Plane → ℝ) (y : Plane) : ℝ :=
  2*⟪b y,gradient f y⟫+planeDivergence b y*f y

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SiblingPlaneCarlemanS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeBentHessian (n : Plane) (ℓ M : ℝ) : Plane →L[ℝ] Plane :=
  ℓ • (innerSL ℝ n).smulRight n-M • ContinuousLinearMap.id ℝ Plane

def planeBentWeight (x n : Plane) (ℓ M : ℝ) (y : Plane) : ℝ :=
  -⟪n,y-x⟫+(1/2)*⟪y-x,planeBentHessian n ℓ M (y-x)⟫

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCarlemanG (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (f : Plane → ℝ) (y : Plane) : ℝ :=
  4*⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫-
  2*⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SiblingCmcSecant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCMC (g : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun y ↦ cmcFlux (gradient g y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_tangent_normal {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    ⟪graphSlopeNormal n (gradient g y),fderiv ℝ (normalGraph n g) y v⟫=0 := by
  rw [graphSlopeNormal_weight hn,normalGraph_fderiv_apply hg,real_inner_smul_left]
  have he := (normalPlaneLinearIsometry n).inner_map_map (gradient g y) v
  change ⟪normalPlaneEmbedding n (gradient g y),normalPlaneEmbedding n v⟫=⟪gradient g y,v⟫ at he
  have ho : ⟪normalPlaneEmbedding n (gradient g y),n⟫=0 := by
    rw [real_inner_comm]; exact normalPlaneEmbedding_inner hn _
  simp only [inner_sub_left,inner_add_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,he,mul_one,
    ho,mul_zero]
  ring

lemma graph_projection_injective {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Plane}
    (ht : ⟪graphSlopeNormal n (gradient g y),m⟫≠0) :
    Function.Injective ((normalPlaneCoordinates m).comp (fderiv ℝ (normalGraph n g) y)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let w := fderiv ℝ (normalGraph n g) y v
  have hw : w=⟪m,w⟫ • m := by
    have hr := normalPlaneCoordinates_reconstruct hm w
    change normalPlaneCoordinates m w=0 at hv
    rw [hv] at hr
    change (normalPlaneLinearIsometry m) 0+⟪m,w⟫ • m=w at hr
    simpa only [map_zero,zero_add] using hr.symm
  have ho := normalGraph_tangent_normal hn hg y v
  change ⟪graphSlopeNormal n (gradient g y),w⟫=0 at ho
  rw [hw,real_inner_smul_right] at ho
  have hz : w=0 := by rw [hw,(mul_eq_zero.mp ho).resolve_right ht,zero_smul]
  have hh := congrArg (normalPlaneCoordinates n) hz
  dsimp [w] at hh
  rw [normalGraph_fderiv_apply hg,map_add,map_smul,normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn,smul_zero,add_zero,map_zero] at hh
  exact hh

def graphProjectionEquiv {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Plane}
    (ht : ⟪graphSlopeNormal n (gradient g y),m⟫≠0) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.ofBijective (((normalPlaneCoordinates m).comp
    (fderiv ℝ (normalGraph n g) y)).toLinearMap)
      ⟨graph_projection_injective hn hm hg ht,
        (LinearMap.injective_iff_surjective).mp (graph_projection_injective hn hm hg ht)⟩).toContinuousLinearEquiv

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalizedCMCCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def HasNormalizedCMCCharts (B : Set Torus) (N : Cover → Cover) (H : ℝ) : Prop :=
  ∀ a : Cover,quotientMap a∈B → ‖N a‖=1 ∧
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ gradient f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (a+normalGraph (N a) f y)=graphSlopeNormal (N a) (gradient f y) ∧
        quotientMap (a+normalGraph (N a) f y)∈B ∧ planeCMC f y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (a+v)∈B ↔
        normalGraph (N a) f (normalPlaneCoordinates (N a) v)=v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def boundaryZeroGerm (S : Set Torus) (F : Torus → ℝ) : Set Torus :=
  {x | ∀ᶠ y in 𝓝 x,y∈S → F y=0}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_translateNormal_measurePreserving (μ : FiniteMeasure NormalBundle) (a : Cover) :
    MeasurePreserving (translateNormal a) (μ : Measure NormalBundle)
      (μ.map (translateNormal a) : Measure NormalBundle) :=
  ⟨measurable_translateNormal a,rfl⟩

def normalTranslatePullback (μ : FiniteMeasure NormalBundle) (a : Cover) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Lp W 2 (μ.map (translateNormal a) : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp W 2 (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ (translateNormal a) (sibling_translateNormal_measurePreserving μ a)

def normalTranslateJet (μ : FiniteMeasure NormalBundle) (a : Cover) :
    SurfaceJet (μ.map (translateNormal a)) →L[ℝ] SurfaceJet μ :=
  (normalTranslatePullback μ a ℝ).toContinuousLinearMap.prodMap
    (normalTranslatePullback μ a Cover).toContinuousLinearMap

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTranslateField (a : Cover) (N : Cover → Cover) : Cover → Cover := fun x ↦ N (x+a)

lemma normalTranslateField_smooth (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) : ContDiff ℝ (⊤ : ℕ∞) (normalTranslateField a N) :=
  hN.comp (contDiff_id.add contDiff_const)

lemma normalTranslateField_periodic (a : Cover) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    ∀ m x,normalTranslateField a N (x+latticeVector m)=normalTranslateField a N x := by
  intro m x
  dsimp [normalTranslateField]
  rw [add_right_comm,hp]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FirstSeamFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def firstSeamFunction (x : Cover) : ℝ := Real.sin (2*Real.pi*x 0)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingAxialProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_axialProjection (v : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover-(innerSL ℝ v).smulRight v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCylinder (v c : Cover) (r : ℝ) : Set Cover :=
  {x | ‖sibling_axialProjection v x-c‖=r}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_TransverseTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def transverseTorus (i : Fin 3) (x : Torus) : Torus :=
  WithLp.toLp 2 (fun j ↦ if j=i then 0 else x j)

@[simp] lemma transverseTorus_apply (i j : Fin 3) (x : Torus) :
    transverseTorus i x j=if j=i then 0 else x j := rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateTube (i : Fin 3) (a : Torus) (r : ℝ) : Set Torus :=
  {x | ‖transverseTorus i (x-a)‖ < r}

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_coverCoordinatePermute (e : Fin 3 ≃ Fin 3) : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

lemma coverCoordinatePermute_quotient (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (sibling_coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := by
  ext i
  rfl

def coordinatePermutation (e : Fin 3 ≃ Fin 3) : LatticeIsometry where
  cover := sibling_coverCoordinatePermute e
  torus := torusCoordinatePermute e
  commute := coverCoordinatePermute_quotient e

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace LatticeIsometry

def normalMap (e : LatticeIsometry) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (e.torus (quotientMap z.1)),
    ⟨e.cover (z.2 : Cover),by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisReflection (i : Fin 3) : LatticeIsometry where
  cover := ((sibling_coverCoordinatePermute (Equiv.swap 0 i)).trans firstReflection).trans
    (sibling_coverCoordinatePermute (Equiv.swap 0 i))
  torus := ((torusCoordinatePermute (Equiv.swap 0 i)).trans torusFirstReflection).trans
    (torusCoordinatePermute (Equiv.swap 0 i))
  commute x := by
    change quotientMap (sibling_coverCoordinatePermute (Equiv.swap 0 i)
      (firstReflection (sibling_coverCoordinatePermute (Equiv.swap 0 i) x)))=_
    rw [coverCoordinatePermute_quotient,firstReflection_quotient,coverCoordinatePermute_quotient]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def OrientedCoordinateLE (b : Fin 3 → Bool) (x y : Cover) : Prop :=
  ∀ i,if b i then x i≤y i else y i≤x i

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_OctantVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def closedUpperOctant : Set Cover := {x | ∀ i : Fin 3,(1/2 : ℝ)≤x i ∧ x i≤1}

def octantContract (t : ℝ) (x : Cover) : Cover :=
  (1-t) • x+t • WithLp.toLp 2 (fun _ : Fin 3 ↦ (3/4 : ℝ))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def octantFlipSet (s : Finset (Fin 3)) (x : Cover) : Cover :=
  WithLp.toLp 2 (fun i ↦ if i∈s then 1-x i else x i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def upperVertex (c : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i ↦ if c i then (1 : ℝ) else 1/2)

def orientedUpperVertex (b c : Fin 3 → Bool) : Cover :=
  upperVertex (fun i ↦ if b i then c i else !c i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialTransverseMass (μ : FiniteMeasure NormalBundle) (i : Fin 3) : ℝ :=
  ∫ z,1-((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle)

lemma normal_component_continuous (i : Fin 3) :
    Continuous (fun z : NormalBundle ↦ (z.2 : Cover) i) :=
  (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp normalEmbedding_continuous.snd

lemma normal_axial_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun z : NormalBundle ↦ f ((z.1 : Cover) i)*(1-((z.2 : Cover) i)^2))
      (μ : Measure NormalBundle) :=
  ((hf.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    normalEmbedding_continuous.fst)).mul
      (continuous_const.sub ((normal_component_continuous i).pow 2))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma normal_transverse_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (fun z : NormalBundle ↦ 1-((z.2 : Cover) i)^2) (μ : Measure NormalBundle) := by
  simpa only [one_mul] using normal_axial_integrable μ i (f := fun _ ↦ (1 : ℝ)) continuous_const

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

def circleMollifier (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1/((n : ℝ)+1)
  rOut := 2/((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def circleSmoothApprox (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (circleMollifier n).normed volume ⋆ f

lemma circleSmoothApprox_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (circleSmoothApprox f n) 1 := by
  intro x
  simp only [circleSmoothApprox,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [show x+1-y=(x-y)+1 by ring,hp]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev AxisCircle := AddCircle (1 : ℝ)

def axialSurfaceMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2))
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal
    (normal_transverse_integrable μ i).hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def axialVolumeMarginal (E : Set Torus) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)
  haveI : IsFiniteMeasure η := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono inter_subset_left).trans_lt (by rw [volume_fundamentalCube]; exact ENNReal.one_lt_top)⟩
  exact ⟨Measure.map (fun x : Cover ↦ (x i : AxisCircle)) η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AxisCircleLebesgue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisCircleLebesgue : FiniteMeasure AxisCircle :=
  ⟨Measure.map (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc 0 1)),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSeamFunction (i : Fin 3) (x : Cover) : ℝ := Real.sin (2*Real.pi*x i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisFixedHeights : Set AxisCircle := {0,((1/2 : ℝ) : AxisCircle)}

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialAreaMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle :=
  μ.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev TransverseProduct := Fin 2 → AxisCircle

def torusAxialSplit (i : Fin 3) : Torus ≃ᵐ AxisCircle × TransverseProduct :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AxisCircle)).toMeasurableEquiv.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ AxisCircle) i)

@[simp] lemma torusAxialSplit_symm_same (i : Fin 3) (t : AxisCircle) (y : TransverseProduct) :
    ((torusAxialSplit i).symm (t,y)) i=t := by
  change i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y i=t
  exact Fin.insertNth_apply_same (α := fun _ : Fin 3 ↦ AxisCircle) i t y

@[simp] lemma torusAxialSplit_symm_succAbove (i : Fin 3) (t : AxisCircle)
    (y : TransverseProduct) (j : Fin 2) :
    ((torusAxialSplit i).symm (t,y)) (i.succAbove j)=y j := by
  change i.insertNth (α := fun _ : Fin 3 ↦ AxisCircle) t y (i.succAbove j)=y j
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 ↦ AxisCircle) i t y j

def axialSlice (E : Set Torus) (i : Fin 3) (t : AxisCircle) : Set TransverseProduct :=
  {y | (torusAxialSplit i).symm (t,y)∈E}

def axialSliceVolume (E : Set Torus) (i : Fin 3) (t : AxisCircle) : ℝ≥0∞ :=
  volume (axialSlice E i t)

lemma axialSliceVolume_le_one (E : Set Torus) (i : Fin 3) (t : AxisCircle) :
    axialSliceVolume E i t≤1 := by
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : volume (univ : Set TransverseProduct)=1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialPlanePoint (i : Fin 3) (t : ℝ) (y : Plane) : Cover :=
  WithLp.toLp 2 (i.insertNth t y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialPositiveFluxMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let w : NormalBundle → ℝ := fun z ↦ 1+((z.2 : Cover) i)
  have hi : Integrable w (μ : Measure NormalBundle) :=
    (continuous_const.add (normal_component_continuous i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (w z))
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def axialNormalDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialPositiveFluxMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal-
    ((axialAreaMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def octantHeight (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) : ℝ :=
  if b i then (1+t)/2 else 1-t/2

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ActualAxialFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def actualAxialFlux (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (i : Fin 3) (t : AxisCircle) : ℝ :=
  axialTransverseMass μ i+H*((axialSliceVolume E i t).toReal-torusVolume.real E)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NormalTransverseLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTransverseLength (i : Fin 3) (z : NormalBundle) : ℝ :=
  Real.sqrt (1-((z.2 : Cover) i)^2)

lemma normalTransverseLength_continuous (i : Fin 3) : Continuous (normalTransverseLength i) :=
  (continuous_const.sub ((normal_component_continuous i).pow 2)).sqrt

def axialPerimeterMarginal (μ : FiniteMeasure NormalBundle) (i : Fin 3) : FiniteMeasure AxisCircle := by
  let η := (μ : Measure NormalBundle).withDensity (fun z ↦ ENNReal.ofReal (normalTransverseLength i z))
  have hi : Integrable (normalTransverseLength i) (μ : Measure NormalBundle) :=
    (normalTransverseLength_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : IsFiniteMeasure η := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  exact ⟨Measure.map (fun z : NormalBundle ↦ (((z.1 : Cover) i) : AxisCircle)) η,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def axialPerimeterDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSliceIntegral (E : Set Torus) (i : Fin 3) (f : Torus → ℝ) (t : AxisCircle) : ℝ :=
  ∫ y in axialSlice E i t,f ((torusAxialSplit i).symm (t,y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSection_integrable (E : Set Torus) (i : Fin 3) (t : AxisCircle) (f : C(Torus,ℝ)) :
    Integrable (fun y : TransverseProduct ↦ f ((torusAxialSplit i).symm (t,y)))
      (volume.restrict (axialSlice E i t)) := by
  apply Integrable.of_bound
    (f.continuous.measurable.comp ((torusAxialSplit i).symm.measurable.comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable ‖f‖
  exact ae_of_all _ fun y ↦ f.norm_coe_le_norm _

def axialSliceFunctional (E : Set Torus) (i : Fin 3) (t : AxisCircle) : C(Torus,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ axialSliceIntegral E i f t
      map_add' := by
        intro f g
        exact integral_add (axialSection_integrable E i t f) (axialSection_integrable E i t g)
      map_smul' := by
        intro c f
        exact integral_const_mul c (fun y : TransverseProduct ↦ f ((torusAxialSplit i).symm (t,y))) }
    1 (by
      intro f
      have hh := norm_setIntegral_le_of_norm_le_const (measure_lt_top volume (axialSlice E i t))
        (fun y (_ : y∈axialSlice E i t) ↦ f.norm_coe_le_norm ((torusAxialSplit i).symm (t,y)))
      have hm : (volume (axialSlice E i t)).toReal≤1 := by
        simpa only [axialSliceVolume,ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞)≠∞) (axialSliceVolume_le_one E i t)
      change ‖axialSliceIntegral E i f t‖≤1*‖f‖
      simpa only [one_mul,axialSliceIntegral] using hh.trans (mul_le_of_le_one_right (norm_nonneg f) hm))

def axialDivergenceClass (i : Fin 3) : Set C(Torus,ℝ) :=
  {f | ∃ (F : Cover → Cover) (hF : AdmissibleField F),
    (∀ x,F x i=0) ∧ f=⟨fun z ↦ divergence F (representative z),
      continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)⟩}

def axialTestPerimeter (E : Set Torus) (i : Fin 3) (t : AxisCircle) : ℝ≥0∞ :=
  ⨆ (F : Cover → Cover) (_ : AdmissibleField F) (_ : ∀ x,F x i=0),
    ENNReal.ofReal (axialSliceIntegral E i (fun z ↦ divergence F (representative z)) t)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeAxisEmbedding (i : Fin 3) : Plane →L[ℝ] Cover :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ WithLp.toLp 2 (i.insertNth 0 y.ofLp)
      map_add' := by
        intro x y; ext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩ <;> simp
      map_smul' := by
        intro a x; ext j
        rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩ <;> simp }

def planeAxisProjection (i : Fin 3) : Cover →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (fun j ↦ x (i.succAbove j))
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

@[simp] lemma planeAxisEmbedding_same (i : Fin 3) (y : Plane) :
    planeAxisEmbedding i y i=0 := by
  change i.insertNth (α := fun _ : Fin 3 ↦ ℝ) 0 y.ofLp i=0
  exact Fin.insertNth_apply_same (α := fun _ : Fin 3 ↦ ℝ) i 0 y.ofLp
@[simp] lemma planeAxisEmbedding_succAbove (i : Fin 3) (y : Plane) (j : Fin 2) :
    planeAxisEmbedding i y (i.succAbove j)=y j := by
  change i.insertNth (α := fun _ : Fin 3 ↦ ℝ) 0 y.ofLp (i.succAbove j)=y j
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 ↦ ℝ) i 0 y.ofLp j
@[simp] lemma planeAxisProjection_apply (i : Fin 3) (x : Cover) (j : Fin 2) :
    planeAxisProjection i x j=x (i.succAbove j) := rfl

@[simp] lemma planeAxisProjection_embedding (i : Fin 3) (y : Plane) :
    planeAxisProjection i (planeAxisEmbedding i y)=y := by ext j; simp

@[simp] lemma planeAxisProjection_single_same (i : Fin 3) :
    planeAxisProjection i (EuclideanSpace.single i 1)=0 := by
  ext j
  simp [Fin.succAbove_ne]

@[simp] lemma planeAxisProjection_single_succAbove (i : Fin 3) (j : Fin 2) :
    planeAxisProjection i (EuclideanSpace.single (i.succAbove j) 1)=EuclideanSpace.single j 1 := by
  ext k
  simp [Fin.succAbove_right_injective.eq_iff]

def PlanarAdmissibleField (G : Plane → Plane) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) G ∧
  (∀ (n : Fin 2 → ℤ) (y : Plane),G (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=G y) ∧
  ∀ y,‖G y‖≤1

def liftPlanarField (i : Fin 3) (G : Plane → Plane) (x : Cover) : Cover :=
  planeAxisEmbedding i (G (planeAxisProjection i x))

@[simp] lemma liftPlanarField_same (i : Fin 3) (G : Plane → Plane) (x : Cover) :
    liftPlanarField i G x i=0 := planeAxisEmbedding_same _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma planeAxisEmbedding_single (i : Fin 3) (j : Fin 2) :
    planeAxisEmbedding i (EuclideanSpace.single j 1)=EuclideanSpace.single (i.succAbove j) 1 := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨k,rfl⟩
  · simp
  · simp [Fin.succAbove_right_injective.eq_iff]

def planeAxisAt (i : Fin 3) (a : ℝ) (y : Plane) : Cover :=
  a • EuclideanSpace.single i 1+planeAxisEmbedding i y

@[simp] lemma planeAxisAt_same (i : Fin 3) (a : ℝ) (y : Plane) : planeAxisAt i a y i=a := by
  simp [planeAxisAt]
@[simp] lemma planeAxisAt_succAbove (i : Fin 3) (a : ℝ) (y : Plane) (j : Fin 2) :
    planeAxisAt i a y (i.succAbove j)=y j := by
  simp [planeAxisAt,Fin.succAbove_ne]

def planarRepresentative (y : TransverseProduct) : Plane :=
  WithLp.toLp 2 (fun j ↦ ((AddCircle.equivIco (1 : ℝ) 0) (y j) : ℝ))

def planarTorusPerimeter (A : Set TransverseProduct) : ℝ≥0∞ :=
  ⨆ (G : Plane → Plane) (_ : PlanarAdmissibleField G),
    ENNReal.ofReal (∫ y in A,planeDivergence G (planarRepresentative y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarAxialField (j : Fin 2) (ψ : ℝ → ℝ) (y : Plane) : Plane :=
  ψ (y j) • EuclideanSpace.single j 1

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSectionCorner (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) : Cover :=
  WithLp.toLp 2 (i.insertNth t (fun j ↦ octantHeight b (i.succAbove j) (if n j then 1 else 0)))

@[simp] lemma axialSectionCorner_same (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) :
    axialSectionCorner b i t n i=t := by simp [axialSectionCorner]
@[simp] lemma axialSectionCorner_other (b : Fin 3 → Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 → Bool) (j : Fin 2) :
    axialSectionCorner b i t n (i.succAbove j)=octantHeight b (i.succAbove j) (if n j then 1 else 0) := by
  simp [axialSectionCorner]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarProductField (σ a b : ℝ → ℝ) (y : Plane) : Plane :=
  (σ (y 0)*a (y 1)) • EuclideanSpace.single 0 1 +
    b (y 1) • EuclideanSpace.single 1 1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def closedCentralArc (K : ℝ) : Set AxisCircle := (fun t : ℝ ↦ (t : AxisCircle)) '' Icc (-K) K

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarRadialDownset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def PlanarRadialDownset (A : Set TransverseProduct) : Prop :=
  ∀ y z : TransverseProduct,(∀ j,‖y j‖≤‖z j‖) →z∈A →y∈A

def planarAxisPoint (t : ℝ) : TransverseProduct := ![0,(t : AxisCircle)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarFirstAxisPoint (t : ℝ) : TransverseProduct := ![(t : AxisCircle),0]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarQuotient (x : Plane) : TransverseProduct := fun j ↦ (x j : AxisCircle)

@[simp] lemma planarQuotient_representative (y : TransverseProduct) :
    planarQuotient (planarRepresentative y)=y := by
  ext j
  exact AddCircle.coe_equivIco

@[simp] lemma planarQuotient_add (x y : Plane) : planarQuotient (x+y)=planarQuotient x+planarQuotient y := by
  ext j
  change ((x j+y j : ℝ) : AxisCircle)=(x j : AxisCircle)+(y j : AxisCircle)
  simp only [AddCircle.coe_add]
@[simp] lemma planarQuotient_neg (x : Plane) : planarQuotient (-x)=-planarQuotient x := by
  ext j
  change ((-x j : ℝ) : AxisCircle)=-(x j : AxisCircle)
  simp only [AddCircle.coe_neg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSectionCenter (b : Fin 3 →Bool) (i : Fin 3) : TransverseProduct :=
  fun j ↦ if b (i.succAbove j) then ((1/2 : ℝ) : AxisCircle) else 0

def centeredAxialSlice (O : Set Torus) (b : Fin 3 →Bool) (i : Fin 3) (t : AxisCircle) : Set TransverseProduct :=
  (fun y ↦ y+axialSectionCenter b i) ⁻¹' axialSlice O i t

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarSquareCorner (n : Fin 2 →Bool) : TransverseProduct :=
  fun j ↦ if n j then ((1/2 : ℝ) : AxisCircle) else 0

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialAreaDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialAreaMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

def axialSecondDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSwap : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

def planarSwap : TransverseProduct ≃ᵐ TransverseProduct :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ↦ AxisCircle) (Equiv.swap (0 : Fin 2) 1)

@[simp] lemma planeSwap_apply (x : Plane) (j : Fin 2) :
    planeSwap x j=x (Equiv.swap 0 1 j) := rfl
@[simp] lemma planarSwap_apply (y : TransverseProduct) (j : Fin 2) :
    planarSwap y j=y (Equiv.swap 0 1 j) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 2 ↦ AxisCircle) (Equiv.swap (0 : Fin 2) 1) y (Equiv.swap 0 1 j)
  simpa only [planarSwap,Equiv.swap_apply_self] using h
@[simp] lemma planeSwap_involutive (x : Plane) : planeSwap (planeSwap x)=x := by
  ext j; simp
@[simp] lemma planarSwap_involutive (x : TransverseProduct) : planarSwap (planarSwap x)=x := by
  ext j; simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma planarSwap_zero : planarSwap (0 : TransverseProduct)=0 := by ext j; simp

@[simp] lemma planarSwap_firstAxisPoint (t : ℝ) : planarSwap (planarFirstAxisPoint t)=planarAxisPoint t := by
  ext j
  fin_cases j <;> simp [planarFirstAxisPoint,planarAxisPoint]

@[simp] lemma planarSwap_secondAxisPoint (t : ℝ) : planarSwap (planarAxisPoint t)=planarFirstAxisPoint t := by
  rw [←planarSwap_firstAxisPoint,planarSwap_involutive]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

def lambda : ℝ := 49 / 50
def ell : ℝ := 7 / 25
def cutoff : ℝ := Real.sqrt 48 / 7
def rawWeight (X : ℝ) : ℝ := (1 - lambda * X ^ 2) / Real.sqrt (1 - X ^ 2)
def weight (X : ℝ) : ℝ := rawWeight (min X cutoff)

def squaredWeight (r : ℝ) : ℝ := (1 - lambda * r) / Real.sqrt (1 - r)

end CubicTorus.Nesting

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

def t (h : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 + 4 * h ^ 2 / Real.pi))
def c : ℝ := 27 / 10
def dm : ℝ := 21 / 100
def u (h : ℝ) : ℝ := min (1 - 1 / Real.pi) ((24 / 25 : ℝ) / h)
def theta : ℝ := 2 / (1 + Real.sqrt (1 + 4 * c * dm / Real.pi))
def shape (q : ℝ) : ℝ := min (q ^ 2) (Real.pi * (1 - q) / (c * dm))
def moment : ℝ := ∫ q in (0 : ℝ)..1, shape q
def firstMoment : ℝ := ∫ q in (0 : ℝ)..1, q * shape q
def meanQ : ℝ := firstMoment / moment
def p₂ : ℝ := 1 + c * dm ^ 2 * theta ^ 2

end CubicTorus.Shape
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nestingEndpointBound (h s : ℝ) : ℝ :=
  1-2*h*Shape.t h/Real.pi+(2/Real.pi)*Real.sqrt (Real.pi+2*h^2*Shape.t h)*Real.sqrt (s-Shape.t h)

def nestingDelta (h s : ℝ) : ℝ := min Shape.dm (max (Shape.u h-nestingEndpointBound h s) 0)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def unitPlanarProfile (s : ℝ) : ℝ :=
  min (2*Real.sqrt (Real.pi*s)) (min 2 (2*Real.sqrt (Real.pi*(1-s))))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SharpSectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sharpSectionWeight (H s : ℝ) : ℝ :=
  if s∈Ico 0 1 then Nesting.weight (H*s/unitPlanarProfile s) else Nesting.ell

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def improvedSectionWeight (H δ v : ℝ) : ℝ :=
  if 0<δ ∧ v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) then
    Nesting.weight ((H/2)*v/Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))
  else sharpSectionWeight H v

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nestingBaseline (h : ℝ) : ℝ :=
  Nesting.lambda*h/Real.pi+(∫ v in (0 : ℝ)..Shape.t h,sharpSectionWeight (2*h) v)-1

def nestingC0 (h : ℝ) : ℝ := min ((134/1000 : ℝ)*h^3) (36/100)
def nestingP (h : ℝ) : ℝ := Shape.u h-1+2*h*Shape.t h/Real.pi
def nestingQ (h : ℝ) : ℝ := (2/Real.pi)*Real.sqrt (Real.pi+2*h^2*Shape.t h)
def nestingExcess (h y : ℝ) : ℝ := Nesting.ell*y^2+
  nestingC0 h*(min Shape.dm (max (nestingP h-nestingQ h*y) 0))^3

def nestingGainInfimum (h : ℝ) : ℝ := sInf (nestingExcess h '' Ici 0)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Rigidity_TwoVolumeNodal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CubicTorus.TwoVolume
noncomputable section
open Set Filter
open scoped Topology
open Reduction

def sphereArea (v : ℝ) : ℝ := (9 * Real.pi / 2) ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ)
def tubeArea (v : ℝ) : ℝ := Real.sqrt (Real.pi * v)
def V₁ : ℝ := 4 * Real.pi / 81
def V₂ : ℝ := 1 / Real.pi

def envelope (V : ℝ) : ℝ :=
  let v := min V (1 - V)
  min (sphereArea v) (min (tubeArea v) 1)

end
end CubicTorus.TwoVolume

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_RevolutionTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisRadialField (c : Cover) (α β g : ℝ → ℝ) (x : Cover) : Cover :=
  α (x 0) • EuclideanSpace.single 0 1+
    (β (x 0)*g (x 1-c 1)) • EuclideanSpace.single 1 1+
    (β (x 0)*g (x 2-c 2)) • EuclideanSpace.single 2 1

@[simp] lemma axisRadialField_zero (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 0=α (x 0) := by simp [axisRadialField]
@[simp] lemma axisRadialField_one (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 1=β (x 0)*g (x 1-c 1) := by simp [axisRadialField]
@[simp] lemma axisRadialField_two (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 2=β (x 0)*g (x 2-c 2) := by simp [axisRadialField]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_DelaunayPeriodicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set MeasureTheory
namespace CubicTorus

def delaunayRecurrence (r : ℝ → ℝ) (β k : ℝ) (j : ℤ) (t : ℝ) : ℝ :=
  (j : ℝ)/β*r t^j/(r t^2+k)-β*((j+1 : ℝ)*r t^j+(j-1 : ℝ)*k*r t^(j-2))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
namespace CubicTorus

def delaunayAmplitude (a b : ℝ) (r : ℝ) : ℝ :=
  Real.arccos ((2*r^2-(a^2+b^2))/(b^2-a^2))/2

def delaunaySquare (a b θ : ℝ) : ℝ :=
  (a^2+b^2+(b^2-a^2)*Real.cos (2*θ))/2

@[simp] lemma delaunayAmplitude_b {a b : ℝ} (ha : 0<a) (hab : a<b) :
    delaunayAmplitude a b b=0 := by
  have hΔ : b^2-a^2≠0 := (show 0<b^2-a^2 by nlinarith only [ha,hab]).ne'
  unfold delaunayAmplitude
  rw [show (2*b^2-(a^2+b^2))/(b^2-a^2)=1 by field_simp; ring]
  simp

@[simp] lemma delaunayAmplitude_a {a b : ℝ} (ha : 0<a) (hab : a<b) :
    delaunayAmplitude a b a=Real.pi/2 := by
  have hΔ : b^2-a^2≠0 := (show 0<b^2-a^2 by nlinarith only [ha,hab]).ne'
  unfold delaunayAmplitude
  rw [show (2*a^2-(a^2+b^2))/(b^2-a^2)= -1 by field_simp; ring,Real.arccos_neg_one]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FourStarScalarGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace CubicTorus

structure CornerRootData (t d x : ℝ) : Prop where
  t0 : 0≤t
  t1 : t<1
  d0 : 0≤d
  d3 : d^2≤1/3
  x0 : 0≤x
  xcap : x≤7/4
  root : Real.pi*(1-t-d^2)=x*(1-t^2)

end CubicTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cylinderRatio (V : ℝ) : ℝ := isoperimetricProfile V/Real.sqrt V

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

def criticalCorrection (h : ℝ) : ℝ := (49/50 : ℝ)/Real.pi*h+(51*Real.pi/200)*h⁻¹-1

end CubicTorus

end
end

end OAI
end


