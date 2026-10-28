-- Prove2me | Definitions.Def_OAIQ079A003
-- name    : OAIQ079A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:41:49.174062+00:00
-- url     : https://prove2.me/theorems/2a66dd02-25e9-45ce-9e1f-e78b88a668fd
-- title:
--   Definitions bundle OAIQ079A003 of the split of OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 921 declarations of OpenAI's Lean: 912 definitions and 9 theorems. The definitions and types are `OAI.CubicTorus.radialFaceIsometry`, `OAI.CubicTorus.radialVelocity`, `OAI.CubicTorus.rebasedGraph`, `OAI.CubicTorus.reflectNormal`, `OAI.CubicTorus.reflectionCompetitor`, `OAI.CubicTorus.reflectionPullback`, `OAI.CubicTorus.regionDistance`, `OAI.CubicTorus.relativeContainmentNeighborhood`, `OAI.CubicTorus.relativeZeroNeighborhood`, `OAI.CubicTorus.rescaledActualBoundary`, `OAI.CubicTorus.reverseBlowupNormal`, `OAI.CubicTorus.revolutionPoint`, `OAI.CubicTorus.separatedPositiveTrunc`, `OAI.CubicTorus.sibling_planeCarlemanP`, `OAI.CubicTorus.sibling_planeCarlemanS`, `OAI.CubicTorus.sibling_planeElliptic`, `OAI.CubicTorus.sibling_reflectNormal`, `OAI.CubicTorus.sibling_smoothScalarTranslate`, `OAI.CubicTorus.slopeHorizontalVector`, `OAI.CubicTorus.slopeScalarTest`, `OAI.CubicTorus.slopeVerticalVector`, `OAI.CubicTorus.smoothApprox`, `OAI.CubicTorus.smoothApproxLip`, `OAI.CubicTorus.smoothGradientSpace`, `OAI.CubicTorus.smoothNormalLength`, `OAI.CubicTorus.smoothNormalMap`, `OAI.CubicTorus.smoothNormalMeasure`, `OAI.CubicTorus.smoothScalarMul`, `OAI.CubicTorus.smoothScalarOne`, `OAI.CubicTorus.smoothScalarPositiveTrunc`, `OAI.CubicTorus.smoothScalarSeparatedTrunc`, `OAI.CubicTorus.smoothScalarTranslate`, `OAI.CubicTorus.sublevelRegion`, `OAI.CubicTorus.sublevelVolume`, `OAI.CubicTorus.surfaceCenter`, `OAI.CubicTorus.surfaceCutoffError`, `OAI.CubicTorus.surfaceCutoffJet`, `OAI.CubicTorus.surfaceGradientMultiplier`, `OAI.CubicTorus.surfaceH1`, `OAI.CubicTorus.surfaceH1ZeroMean` and 872 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CubicTorus_Curvature_CMCFrameOperator`, `CubicTorus_Curvature_NormalCurvatureScalar`, `CubicTorus_Curvature_SurfaceJacobiLocalization`, `CubicTorus_Estimates_BVLocalScaling`, `CubicTorus_Estimates_ChainMass`, `CubicTorus_Estimates_ConeSlopeReciprocalArea`, `CubicTorus_Estimates_DifferenceStep`, `CubicTorus_Estimates_NodalBalanceValue`, `CubicTorus_Estimates_PlaneWeakGradient`, `CubicTorus_Estimates_SmoothScalarSeparatedTrunc`, `CubicTorus_Estimates_SurfaceJet`, `CubicTorus_Estimates_UnitAngle`, `CubicTorus_Profiles_AxisCircleLebesgue`, `CubicTorus_Profiles_CMCSecantSymbol`, `CubicTorus_Profiles_GainBounds`, `CubicTorus_Profiles_NodalTorusScalar`, `CubicTorus_Profiles_NormalMap`, `CubicTorus_Profiles_NormalTransverseLength`, `CubicTorus_Profiles_NormalizedCMCCharts`, `CubicTorus_Profiles_PlanarProfile`, `CubicTorus_Profiles_SiblingPlaneCarlemanS`, `CubicTorus_Profiles_ValueEnclosures289To507`, `CubicTorus_Profiles_ValueEnclosures2921To3142`, `CubicTorus_Profiles_ValueEnclosures3143To3335`, `CubicTorus_Profiles_ValueEnclosures508To725`, `CubicTorus_Profiles_ValueEnclosures726To944`, `CubicTorus_Profiles_ValueEnclosures72To288`, `CubicTorus_Profiles_ValueEnclosures945To1164`, `CubicTorus_Reflection_BVTorusGraphFlux`, `CubicTorus_Reflection_CoordinateReflection`, `CubicTorus_Reflection_CoordinateReflection2`, `CubicTorus_Reflection_NormalMeasureCoordinateReflection`, `CubicTorus_Reflection_RevolutionTangents`, `CubicTorus_Reflection_SiblingReflectNormal`, `CubicTorus_Regularity_BVBlowupComplement`, `CubicTorus_Regularity_BVPlanarAngularChart`, `CubicTorus_Regularity_BVPlaneAreaCoordinates`, `CubicTorus_Regularity_BVRegularity`, `CubicTorus_Regularity_FiberPoint`, `CubicTorus_Regularity_GradientCalibration`, `CubicTorus_Regularity_MinimalGraphDensity`, `CubicTorus_Regularity_NormalFirstVariation`, `CubicTorus_Regularity_SmoothApproxLip`, `CubicTorus_Regularity_SurfaceH1Translation`, `CubicTorus_Regularity_SurfaceNormalReverse`, `CubicTorus_Regularity_WeightedPerimeter`, `CubicTorus_Variation_ComponentDivergence`.
--
--   **Imports.** It imports the published bundle `Def_CubicTorus`; the bundles `OAIQ079A000`, `OAIQ079A001` and `OAIQ079A002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CubicTorus.CenteredJacobiChart.classical_ground_state`, `OAI.CubicTorus.CenteredJacobiChart.nodal_truncation_impossible`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay`, `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC`, `OAI.CubicTorus.isMinimizerAt_H1_jacobi_unique_continuation`, `OAI.CubicTorus.isMinimizerAt_bottom_both_extents`, `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration`, `OAI.CubicTorus.isMinimizerAt_chamber_upper_downset`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_not_three_vertices`, `OAI.CubicTorus.isMinimizerAt_fixed_downset_not_three_vertices`, `OAI.CubicTorus.isMinimizerAt_improved_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_projection`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux`, `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain`, `OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle`, `OAI.CubicTorus.isMinimizerAt_nodal_splice_closed`, `OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible`, `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant`, `OAI.CubicTorus.isMinimizerAt_planar_profile_circle`, `OAI.CubicTorus.isMinimizerAt_positive_position_spherical`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor`, `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs`, `OAI.CubicTorus.isMinimizerAt_section_extent_perimeter`, `OAI.CubicTorus.isMinimizerAt_section_improved_profile`, `OAI.CubicTorus.isMinimizerAt_section_planar_profile`, `OAI.CubicTorus.isMinimizerAt_section_strip_perimeter`, `OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_three_vertex_bottom`, `OAI.CubicTorus.isMinimizerAt_three_vertex_parameters`, `OAI.CubicTorus.normalComponentScalar_global_jacobi`, `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear`, `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_smoothAt`, `OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_positive_right`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_146`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_150`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_154`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_158`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_162`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_74_84`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102`, `OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower`, `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected`, `OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support`, `OAI.ReusedScalar205.CubicTorus.Scalar.linearBaseline_eq_of_range` and `OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range`; the proofs of `OAI.CubicTorus.CenteredJacobiChart.classical_ground_state`, `OAI.CubicTorus.CenteredJacobiChart.nodal_truncation_impossible`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay`, `OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic`, `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian`, `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability`, `OAI.CubicTorus.Periodic.isMinimizerAt_normal_support_jets`, `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.Periodic.profile_hessian_of_CMC`, `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC`, `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero`, `OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter`, `OAI.CubicTorus.actual_primary_fixed_scale_packets`, `OAI.CubicTorus.actual_primary_offvertex_C1`, `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs`, `OAI.CubicTorus.actual_tangent_secondary_representation`, `OAI.CubicTorus.antitoneOn_isoperimetricProfile_half`, `OAI.CubicTorus.cmc_linearized_holder_gradient`, `OAI.CubicTorus.continuousOn_isoperimetricProfile`, `OAI.CubicTorus.critical_baseline_positive`, `OAI.CubicTorus.critical_nesting_contradiction`, `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution`, `OAI.CubicTorus.forced_cmc_linearized_holder_gradient`, `OAI.CubicTorus.isMinimizerAt_CMC_sign`, `OAI.CubicTorus.isMinimizerAt_H1_jacobi_unique_continuation`, `OAI.CubicTorus.isMinimizerAt_antitoneOn_axialSectionArea`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_axial_boundary_null`, `OAI.CubicTorus.isMinimizerAt_axial_endFlux`, `OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter`, `OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign`, `OAI.CubicTorus.isMinimizerAt_bottom_both_extents`, `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration`, `OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae`, `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus`, `OAI.CubicTorus.isMinimizerAt_centered_holder_CMC`, `OAI.CubicTorus.isMinimizerAt_centered_multiplier`, `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit`, `OAI.CubicTorus.isMinimizerAt_chamber_upper_downset`, `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry`, `OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_not_three_vertices`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_cylinder_interval_standard`, `OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube`, `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices`, `OAI.CubicTorus.isMinimizerAt_first_transition_standard`, `OAI.CubicTorus.isMinimizerAt_fixed_downset_not_three_vertices`, `OAI.CubicTorus.isMinimizerAt_four_corner_necessary_data`, `OAI.CubicTorus.isMinimizerAt_global_normal`, `OAI.CubicTorus.isMinimizerAt_improved_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones`, `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_projection`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux`, `OAI.CubicTorus.isMinimizerAt_moving_limit_comparison`, `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain`, `OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle`, `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution`, `OAI.CubicTorus.isMinimizerAt_nodal_splice_closed`, `OAI.CubicTorus.isMinimizerAt_nodal_truncation_impossible`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system`, `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant`, `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy`, `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero`, `OAI.CubicTorus.isMinimizerAt_normal_linear_chart`, `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball`, `OAI.CubicTorus.isMinimizerAt_openRepresentative_ae`, `OAI.CubicTorus.isMinimizerAt_paired_blowup`, `OAI.CubicTorus.isMinimizerAt_perimeter_lower_density`, `OAI.CubicTorus.isMinimizerAt_perimeter_upper_density`, `OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary`, `OAI.CubicTorus.isMinimizerAt_planar_profile_circle`, `OAI.CubicTorus.isMinimizerAt_positive_position_spherical`, `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs`, `OAI.CubicTorus.isMinimizerAt_second_endpoint_linear_bound`, `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density`, `OAI.CubicTorus.isMinimizerAt_section_extent_perimeter`, `OAI.CubicTorus.isMinimizerAt_section_improved_profile`, `OAI.CubicTorus.isMinimizerAt_section_planar_profile`, `OAI.CubicTorus.isMinimizerAt_section_strip_perimeter`, `OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_small_slab_standard`, `OAI.CubicTorus.isMinimizerAt_smaller_side_double_vertices_vacant`, `OAI.CubicTorus.isMinimizerAt_smooth_CMC`, `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_spherical_standard_ball`, `OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup`, `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible`, `OAI.CubicTorus.isMinimizerAt_three_vertex_bottom`, `OAI.CubicTorus.isMinimizerAt_three_vertex_parameters`, `OAI.CubicTorus.isMinimizerAt_tubular_sections`, `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux`, `OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube`, `OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary`, `OAI.CubicTorus.isMinimizerAt_zero_component_multiplier_ne_zero`, `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_not_preconnected`, `OAI.CubicTorus.isoperimetricProfile_cylinder_interval`, `OAI.CubicTorus.isoperimetricProfile_power_upper_support`, `OAI.CubicTorus.isoperimetricProfile_second_transition`, `OAI.CubicTorus.isoperimetricProfile_slab_local_min`, `OAI.CubicTorus.minimizing_planar_product_halfplane`, `OAI.CubicTorus.monotoneOn_isoperimetricProfile_half`, `OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball`, `OAI.CubicTorus.nesting_scalar_contradiction`, `OAI.CubicTorus.normalComponentScalar_global_jacobi`, `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_equationNear`, `OAI.CubicTorus.normalMeasure_H1_jacobi_signed_graph_smoothAt`, `OAI.CubicTorus.normal_transverse_near_reflection_height`, `OAI.CubicTorus.profile_ge_second_chord`, `OAI.CubicTorus.profile_upper_support_power_secant`, `OAI.CubicTorus.strict_C1_cone_halfspace`, `OAI.CubicTorus.strict_normal_component_ne_zero_ae`, `OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt`, `OAI.CubicTorus.unit_cubic_isoperimetric`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_positive_right`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_146`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_150`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_154`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_158`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_162`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_74_84`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102`, `OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower`, `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected`, `OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support`, `OAI.ReusedScalar205.CubicTorus.Scalar.linearBaseline_eq_of_range` and `OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range`.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001
import Definitions.Def_OAIQ079A002

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

def radialVelocity (r dr : ℝ → ℝ) (t : ℝ) : ℂ :=
  ((dr t : ℂ)+(2*Real.pi*r t : ℝ)*Complex.I)*unitAngle t

end CubicTorus

end
end

section

noncomputable section
open Set Complex
open scoped Topology Real
namespace CubicTorus

def unitSquareEnd (t : ℝ) : ℂ := unitSquareScale t • complexFold (unitAngle t)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open scoped Topology Convolution

def smoothApprox (g : Cover → ℝ) (n : ℕ) : Cover → ℝ :=
  (mollifier n).normed volume ⋆ g

lemma smoothApprox_contDiff {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothApprox g n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (mollifier n).contDiff_normed
      (locallyIntegrable_of_bounded hg hb)

lemma smoothApprox_bound {g : Cover → ℝ} (hb : ∀ x, |g x| ≤ 1) (n : ℕ) (x : Cover) :
    |smoothApprox g n x| ≤ 1 := by
  rw [← Real.norm_eq_abs, smoothApprox, convolution_def]
  calc
    _ ≤ ∫ y : Cover, (mollifier n).normed volume y := by
      apply norm_integral_le_of_norm_le (mollifier n).integrable_normed
      exact Eventually.of_forall fun y => by
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ((mollifier n).nonneg_normed y), Real.norm_eq_abs]
        exact mul_le_of_le_one_right ((mollifier n).nonneg_normed y) (hb (x - y))
    _ = 1 := (mollifier n).integral_normed

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
open scoped Topology Convolution

def smoothApproxLip (n : ℕ) : NNReal :=
  ⟨∫ y : Cover, ‖fderiv ℝ ((mollifier n).normed volume) y‖,
    integral_nonneg fun _ => norm_nonneg _⟩

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

def torusApprox (E : Set Torus) (n : ℕ) (x : Torus) : ℝ :=
  smoothApprox (characteristic E ∘ quotientMap) n (representative x)

lemma torusApprox_measurable {E : Set Torus} (hE : MeasurableSet E) (n : ℕ) :
    Measurable (torusApprox E n) :=
  (smoothApprox_contDiff ((measurable_characteristic hE).comp measurable_quotientMap)
    (fun x => characteristic_bound E (quotientMap x)) n).continuous.measurable.comp
      measurable_representative

lemma torusApprox_bound (E : Set Torus) (n : ℕ) (x : Torus) : |torusApprox E n x| ≤ 1 :=
  smoothApprox_bound (fun y => characteristic_bound E (quotientMap y)) n (representative x)

lemma torusApprox_integrable {E : Set Torus} (hE : MeasurableSet E) (n : ℕ) :
    Integrable (torusApprox E n) torusVolume :=
  Integrable.of_bound (torusApprox_measurable hE n).aestronglyMeasurable 1
    (Eventually.of_forall (torusApprox_bound E n))

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

def torusApproxL1 (E : Set Torus) (hE : MeasurableSet E) (n : ℕ) : Lp ℝ 1 torusVolume :=
  (torusApprox_integrable hE n).toL1 (torusApprox E n)

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

def unitNormal (v : Cover) : NormalSphere := ⟨normalizedVector v, normalizedVector_norm v⟩

def smoothNormalMap (f : Cover → ℝ) (x : Cover) : NormalBundle :=
  (cubeRepresentative (quotientMap x), unitNormal (-gradient f x))

def smoothNormalMeasure (f : Cover → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) : FiniteMeasure NormalBundle := by
  let μ := (volume.restrict fundamentalCube).withDensity (fun x ↦ ENNReal.ofReal ‖gradient f x‖)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal
    (integrableOn_periodic_continuous (gradient_contDiff hf).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])).hasFiniteIntegral
  exact ⟨Measure.map (smoothNormalMap f) μ, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end CubicTorus

open scoped RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
open Filter
open scoped Topology RealInnerProductSpace

def transportedFlux (a b : WallVariation) (E : Set Torus) (t : ℝ) : ℝ :=
  ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
    coordinateJacobian a.coordinate a.function t x *
      fderiv ℝ b.function (coordinateMove a.coordinate a.function t x)
        (EuclideanSpace.single b.coordinate 1)

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
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

def volumeCorrectionCoefficient (a b : WallVariation) (E : Set Torus) (t : ℝ) : ℝ :=
  -directionalFlux E a.coordinate a.function / transportedFlux a b E t

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

def regionDistance (E F : Set Torus) : ℝ :=
  ∫ x, ‖characteristic E x - characteristic F x‖ ∂torusVolume

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

def sublevelRegion (q : Cover → ℝ) (t : ℝ) : Set Torus :=
  {z | q (representative z) < t}

def sublevelVolume (E : Set Torus) (q : Cover → ℝ) (t : ℝ) : ℝ :=
  torusVolume.real (E ∩ sublevelRegion q t)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def torusGraphRegion (a n : Cover) (g : Plane → ℝ) : Set Torus :=
  {z | ⟪n, representative z - a⟫ < graphHeightExtension a n g (representative z)}

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVLocalScaling
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

def torusCoverRegion (A : Set Cover) : Set Torus := {z | representative z ∈ A}

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

def slopeScalarTest (χ ψ : ℝ → ℝ) (x : Plane) : ℝ :=
  χ (planeProductCoordinates x).1 *
    ψ ((planeProductCoordinates x).2 / (planeProductCoordinates x).1)

def slopeVerticalVector : Plane := planeProductCoordinates.symm (0,1)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlaneAreaCoordinates
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

def radialFaceIsometry (u : ℝ) : Plane →ₗᵢ[ℝ] Cover where
  toFun y := WithLp.toLp 2 ![y 0,(u/Real.sqrt (1+u^2))*(y 1),(1/Real.sqrt (1+u^2))*(y 1)]
  map_add' y z := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' t y := by ext i; fin_cases i <;> simp [mul_left_comm]
  norm_map' y := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
    change (y 0)^2+((u/Real.sqrt (1+u^2))*(y 1))^2+((1/Real.sqrt (1+u^2))*(y 1))^2 = (y 0)^2+(y 1)^2
    calc
      _ = (y 0)^2+((u/Real.sqrt (1+u^2))^2+(1/Real.sqrt (1+u^2))^2)*(y 1)^2 := by ring
      _ = _ := by rw [radial_face_coefficients,one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupComplement
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

def reverseBlowupNormal (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (z.1,⟨-(z.2 : Cover),by simpa only [norm_neg] using z.2.property⟩)

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

def smoothNormalLength (v : Cover) : ℝ :=
  Real.sqrt (‖v‖^2+normSmoothingBump (‖v‖^2))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

def rescaledActualBoundary (E : Set Torus) (c : Cover) (q : ℝ) : Set Cover :=
  (fun x ↦ quotientMap (c+q • x)) ⁻¹' frontier (openRepresentative E)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def slopeHorizontalVector : Plane := planeProductCoordinates.symm (1,0)

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

def rebasedGraph (a n : Cover) (g : Plane → ℝ) : Plane → ℝ :=
  graphReparam (LinearIsometryEquiv.refl ℝ Plane) (normalPlaneCoordinates n a) ⟪n,a⟫ g

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

def vectorDifference (f : Plane → Plane) (v : Plane) (t : ℝ) (y : Plane) : Plane :=
  t⁻¹ • (f (y+t • v)-f y)

lemma vectorDifference_memLp {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y, ‖f y‖≤M) (r t : ℝ) (v : Plane) :
    MemLp (vectorDifference f v t) 2 (volume.restrict (Metric.ball 0 r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound (C := |t⁻¹| *(2*M)) (by unfold vectorDifference; fun_prop)
  filter_upwards [] with y
  rw [vectorDifference,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hb (y+t • v),hb y]))
    (abs_nonneg _)

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

def smoothGradientSpace (S : Set Plane) : Submodule ℝ (Lp Plane 2 (volume : Measure Plane)) where
  carrier := {G | ∃ f : Plane → ℝ, ∃ hf : ContDiff ℝ (⊤ : ℕ∞) f,
    ∃ hc : HasCompactSupport f, tsupport f⊆S ∧
      G=(compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f)}
  zero_mem' := by
    refine ⟨0,contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero (E := Plane) (p := 2) (μ := (volume : Measure Plane)),
      (compact_C1_gradient_memLp (f := 0) contDiff_const HasCompactSupport.zero).coeFn_toLp]
      with x hz hx
    rw [hz,hx]
    simp [gradient]
  add_mem' := by
    rintro G K ⟨f,hf,hc,hs,rfl⟩ ⟨g,hg,hgc,hgs,rfl⟩
    refine ⟨f+g,hf.add hg,hc.add hgc,(tsupport_add f g).trans (union_subset hs hgs),?_⟩
    have he := C1_gradient_add (hf.of_le (by simp)) (hg.of_le (by simp))
    apply Lp.ext
    filter_upwards [Lp.coeFn_add
        ((compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f))
        ((compact_C1_gradient_memLp (hg.of_le (by simp)) hgc).toLp (gradient g)),
      (compact_C1_gradient_memLp (hf.of_le (by simp)) hc).coeFn_toLp,
      (compact_C1_gradient_memLp (hg.of_le (by simp)) hgc).coeFn_toLp,
      (compact_C1_gradient_memLp ((hf.add hg).of_le (by simp)) (hc.add hgc)).coeFn_toLp]
      with x hx hfx hgx hfgx
    rw [hx]
    simp only [Pi.add_def] at hfgx ⊢
    rw [hfgx]
    change _ + _ = gradient (f+g) x
    rw [hfx,hgx,he]
    rfl
  smul_mem' := by
    rintro a G ⟨f,hf,hc,hs,rfl⟩
    have hcf : HasCompactSupport (a • f) := hc.smul_left
    refine ⟨a • f,contDiff_const.smul hf,hcf,
      (tsupport_smul_subset_right (fun _ ↦ a) f).trans hs,?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul a
        ((compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f)),
      (compact_C1_gradient_memLp (hf.of_le (by simp)) hc).coeFn_toLp,
      (compact_C1_gradient_memLp ((contDiff_const.smul hf).of_le (by simp)) hcf).coeFn_toLp]
      with x hx hfx hax
    rw [hx]
    simp only [Pi.smul_def,Pi.smul_def'] at hax ⊢
    rw [hax]
    change a • _ = gradient (a • f) x
    rw [hfx,C1_gradient_smul (hf.of_le (by simp)) a]
    rfl

def zeroBoundaryGradientSpace (S : Set Plane) : Submodule ℝ (Lp Plane 2 (volume : Measure Plane)) :=
  (smoothGradientSpace S).topologicalClosure

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

def surfaceH1 (μ : FiniteMeasure NormalBundle) : Submodule ℝ (SurfaceJet μ) :=
  (surfaceSmoothJet μ).range.topologicalClosure

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothScalarOne : smoothPeriodicScalars := ⟨fun _ ↦ 1,contDiff_const,by simp⟩

def surfaceOne (μ : FiniteMeasure NormalBundle) : SurfaceJet μ :=
  surfaceSmoothJet μ smoothScalarOne

def surfaceMean (μ : FiniteMeasure NormalBundle) : SurfaceJet μ →L[ℝ] ℝ :=
  (innerSL ℝ (surfaceOne μ).1).comp (ContinuousLinearMap.fst ℝ _ _)

def surfaceCenter (μ : FiniteMeasure NormalBundle) (u : SurfaceJet μ) : SurfaceJet μ :=
  u-(surfaceMean μ u/(μ : Measure NormalBundle).real univ) • surfaceOne μ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceH1ZeroMean (μ : FiniteMeasure NormalBundle) : Submodule ℝ (SurfaceJet μ) :=
  surfaceH1 μ ⊓ (surfaceMean μ).ker

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothScalarMul (f g : smoothPeriodicScalars) : smoothPeriodicScalars :=
  ⟨f.val*g.val,f.property.1.mul g.property.1,fun m x ↦ by
    simp only [Pi.mul_apply,f.property.2,g.property.2]⟩

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

def smoothScalarPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) : smoothPeriodicScalars :=
  ⟨positiveTrunc n ∘ f.val,(positiveTrunc_contDiff n).comp f.property.1,fun m x ↦ by
    simp only [Function.comp_apply,f.property.2]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def separatedPositiveTrunc (n : ℕ) (t : ℝ) : ℝ := positiveTrunc n (t-nodalEpsilon n)

lemma separatedPositiveTrunc_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (separatedPositiveTrunc n) :=
  (positiveTrunc_contDiff n).comp (contDiff_id.sub contDiff_const)

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

def smoothScalarSeparatedTrunc (f : smoothPeriodicScalars) (n : ℕ) : smoothPeriodicScalars :=
  ⟨separatedPositiveTrunc n ∘ f.val,(separatedPositiveTrunc_contDiff n).comp f.property.1,
    fun m x ↦ by simp only [Function.comp_apply,f.property.2]⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceNodalBalance (μ : FiniteMeasure NormalBundle) (u v : SurfaceJet μ) : SurfaceJet μ :=
  surfaceMean μ v • u+(-surfaceMean μ u) • v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceVectorMultiplier (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Lp Cover 2 (μ : Measure NormalBundle) →L[ℝ] Lp Cover 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ q • f
      map_add' := fun f g ↦ Lp.add_smul q f g
      map_smul' := fun c f ↦ (Lp.smul_comm c q f).symm }
    ‖q‖ (fun f ↦ Lp.norm_smul_le q f)

def surfaceGradientMultiplier (μ : FiniteMeasure NormalBundle)
    (g : Lp Cover ∞ (μ : Measure NormalBundle)) :
    Lp ℝ 2 (μ : Measure NormalBundle) →L[ℝ] Lp Cover 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f • g
      map_add' := fun f h ↦ Lp.smul_add f h g
      map_smul' := fun c f ↦ Lp.smul_assoc c f g }
    ‖g‖ (fun f ↦ (Lp.norm_smul_le f g).trans_eq (mul_comm _ _))

def surfaceCutoffJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) : SurfaceJet μ :=
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let g := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  (surfaceMultiplier μ q u.1,surfaceVectorMultiplier μ q u.2+surfaceGradientMultiplier μ g u.1)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

def reflectionCompetitor (i : Fin 3) (E B : Set Torus) : Set Torus :=
  (E∩B) ∪ coordinateReflection i ⁻¹' (E∩B)

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

def surfaceJetReverse (μ : FiniteMeasure NormalBundle) :
    SurfaceJet μ →L[ℝ] SurfaceJet (μ.map reverseNormal) :=
  (normalReverseLp μ 2).toContinuousLinearMap.prodMap
    (normalReverseLp μ 2).toContinuousLinearMap

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

def smoothScalarTranslate (f : smoothPeriodicScalars) (a : Cover) : smoothPeriodicScalars :=
  ⟨fun x => f.val (x+a),f.property.1.comp (contDiff_id.add contDiff_const),by
    intro m x
    simpa only [add_right_comm x (latticeVector m) a] using f.property.2 m (x+a)⟩

def surfaceJetPullTranslation (μ : FiniteMeasure NormalBundle) (a : Cover) :
    SurfaceJet (μ.map (translateNormal a)) →ₗᵢ[ℝ] SurfaceJet μ where
  toLinearMap := (normalTranslationLp μ a 2).toLinearMap.prodMap
    (normalTranslationLp μ a 2).toLinearMap
  norm_map' u := by
    change max ‖normalTranslationLp μ a 2 u.1‖ ‖normalTranslationLp μ a 2 u.2‖=
      max ‖u.1‖ ‖u.2‖
    rw [(normalTranslationLp μ a 2).norm_map,(normalTranslationLp μ a 2).norm_map]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CMCFrameOperator
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

def relativeZeroNeighborhood (S : Set Torus) (F : Torus → ℝ) : Set Torus :=
  interior (Sᶜ∪{a | F a=0})

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CMCSecantSymbol
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

def relativeContainmentNeighborhood (S T : Set Torus) : Set Torus := interior (Sᶜ∪T)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_NormalMeasureCoordinateReflection
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

def reflectNormal (i : Fin 3) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (coordinateReflection i (quotientMap z.1)),
    ⟨coverCoordinateReflection i z.2,by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_NodalBalanceValue
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

def surfaceNodalBalanceValue (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (x : Torus) : ℝ :=
  surfaceMean μ (nodalSurfaceJet μ g A hA) * D.indicator (fun a => f.val (representative a)) x +
    (-surfaceMean μ (nodalSurfaceJet μ f D hD)) * A.indicator (fun a => g.val (representative a)) x

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

def surfaceCutoffError (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) : Lp Cover 2 (μ : Measure NormalBundle) :=
  surfaceGradientMultiplier μ
    (ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)) u.1

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

def reflectionPullback (F : Cover → Cover) : Cover → Cover :=
  fun x ↦ firstReflection (F (firstReflection x))

end CubicTorus

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

def sibling_planeElliptic (A : Plane → Plane →L[ℝ] Plane) (f : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun y ↦ A y (gradient f y))

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

def sibling_planeCarlemanS (A : Plane → Plane →L[ℝ] Plane) (a : Plane → ℝ)
    (τ : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  sibling_planeElliptic A f y+τ^2*a y*f y

def sibling_planeCarlemanP (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (a : Plane → ℝ) (τ : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  sibling_planeCarlemanS A a τ f y-τ*planeTransport b f y

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

def sibling_smoothScalarTranslate (a : Cover) (f : smoothPeriodicScalars) : smoothPeriodicScalars :=
  ⟨fun x ↦ f.val (x+a),f.property.1.comp (contDiff_id.add contDiff_const),by
    intro m x
    dsimp
    rw [add_right_comm,f.property.2]⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_SiblingReflectNormal
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

def sibling_reflectNormal (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (torusFirstReflection (quotientMap z.1)),
    ⟨firstReflection (z.2 : Cover),by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

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

def upperOctant : Set Cover := {x | ∀ i : Fin 3,(1/2 : ℝ)<x i ∧ x i<1}

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

def upperFold (z : Torus) : Cover := WithLp.toLp 2 (fun i ↦ 1-‖z i‖)

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

def tracePlanarField (i : Fin 3) (a : ℝ) (F : Cover → Cover) (y : Plane) : Plane :=
  planeAxisProjection i (F (planeAxisAt i a y))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory
open _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def baseline (h : ℝ) : ℝ :=
  lambda * h / Real.pi + (∫ v in (0 : ℝ)..t h, weight (h * v / planarProfile v)) - 1

def gain (h : ℝ) : ℝ := cappedInf ell (C₀ h) dm (P h) (Q h)

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def J₀ (x : ℝ) : ℝ := 1 - rawWeight x

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def chordMoment (h a b : ℝ) : ℝ :=
  ((b * rho (a / h) - a * rho (b / h)) * (J₀ b - J₀ a) +
    (rho (b / h) - rho (a / h)) * (J₁ b - J₁ a)) / (b - a)

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def twoChordBaseline (h : ℝ) : ℝ :=
  let x := h / Real.pi
  let y := h * (1 - 1 / Real.pi)
  let z := (y + cutoff) / 2
  lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ x +
    (J₁ y - J₁ x) / h + chordMoment h y z + chordMoment h z cutoff

def linearBaseline (h : ℝ) : ℝ :=
  lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ (h / Real.pi) +
    (J₁ cutoff - J₁ (h / Real.pi)) / h

end CubicTorus.Scalar

namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e51 : ℝ := e5 + e50

def e52 : ℝ := e13 / e51

def e53 : ℝ := e52 ^ 2

def e54 : ℝ := e5 + e53

def e55 : ℝ := Real.sqrt e54

def e56 : ℝ := e5 + e55

def e57 : ℝ := e52 / e56

def e68 : ℝ := e5 + e32

def e69 : ℝ := e12 / e68

def e70 : ℝ := e69 ^ 2

def e71 : ℝ := e5 + e70

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures72To288
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e72 : ℝ := Real.sqrt e71

def e73 : ℝ := e5 + e72

def e74 : ℝ := e69 / e73

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures289To507
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e314 : ℝ := e312 / e313

def e315 : ℝ := e257 + e314

def e316 : ℝ := e4 * e278

def e317 : ℝ := e4 / e190

def e318 : ℝ := e89 * e317

def e319 : ℝ := e317 ^ 2

def e320 : ℝ := e91 * e319

def e321 : ℝ := e5 + e320

def e322 : ℝ := Real.sqrt e321

def e323 : ℝ := e318 * e322

def e324 : ℝ := e97 * e319

def e325 : ℝ := e323 - e324

def e326 : ℝ := e259 * e325

def e327 : ℝ := e316 - e326

def e328 : ℝ := e165 - e287

def e329 : ℝ := e327 * e328

def e330 : ℝ := e325 - e278

def e331 : ℝ := e183 - e309

def e332 : ℝ := e330 * e331

def e333 : ℝ := e329 + e332

def e334 : ℝ := e4 - e259

def e335 : ℝ := e333 / e334

def e336 : ℝ := e315 + e335

def e338 : ℝ := e337 / e0

def e339 : ℝ := e337 * e7

def e340 : ℝ := e8 * e337

def e341 : ℝ := e340 / e0

def e343 : ℝ := e17 * e342

def e344 : ℝ := e343 / e0

def e345 : ℝ := e5 + e344

def e346 : ℝ := Real.sqrt e345

def e347 : ℝ := e5 + e346

def e348 : ℝ := e23 / e347

def e349 : ℝ := e9 * e348

def e350 : ℝ := e341 + e349

def e351 : ℝ := e350 - e5

def e352 : ℝ := e0 / e342

def e353 : ℝ := e338 ^ 2

def e354 : ℝ := e5 - e353

def e355 : ℝ := Real.sqrt e354

def e356 : ℝ := e29 - e355

def e357 : ℝ := e355 ^ 3

def e358 : ℝ := e357 / e35

def e359 : ℝ := e356 + e358

def e360 : ℝ := e8 * e359

def e361 : ℝ := e353 / e355

def e362 : ℝ := e361 - e23

def e363 : ℝ := e23 * e355

def e364 : ℝ := e362 + e363

def e365 : ℝ := e364 / e43

def e366 : ℝ := e360 - e365

def e367 : ℝ := e352 * e366

def e368 : ℝ := e351 + e367

def e369 : ℝ := e339 ^ 2

def e370 : ℝ := e5 - e369

def e371 : ℝ := Real.sqrt e370

def e372 : ℝ := e5 + e371

def e373 : ℝ := e339 / e372

def e374 : ℝ := e373 ^ 2

def e375 : ℝ := e5 + e374

def e376 : ℝ := Real.sqrt e375

def e377 : ℝ := e5 + e376

def e378 : ℝ := e373 / e377

def e379 : ℝ := Real.arcsin e339

def e380 : ℝ := e59 * e379

def e381 : ℝ := e61 * e339

def e382 : ℝ := e381 * e371

def e383 : ℝ := e380 - e382

def e384 : ℝ := e43 * e371

def e385 : ℝ := e339 / e384

def e386 : ℝ := e383 - e385

def e387 : ℝ := e5 + e355

def e388 : ℝ := e338 / e387

def e389 : ℝ := e388 ^ 2

def e390 : ℝ := e5 + e389

def e391 : ℝ := Real.sqrt e390

def e392 : ℝ := e5 + e391

def e393 : ℝ := e388 / e392

def e394 : ℝ := Real.arcsin e338

def e395 : ℝ := e59 * e394

def e396 : ℝ := e61 * e338

def e397 : ℝ := e396 * e355

def e398 : ℝ := e395 - e397

def e399 : ℝ := e43 * e355

def e400 : ℝ := e338 / e399

def e401 : ℝ := e398 - e400

def e402 : ℝ := e386 - e401

def e403 : ℝ := e402 / e337

def e404 : ℝ := e368 + e403

def e405 : ℝ := e339 + e4

def e406 : ℝ := e405 / e23

def e407 : ℝ := e339 / e337

def e408 : ℝ := e89 * e407

def e409 : ℝ := e407 ^ 2

def e410 : ℝ := e91 * e409

def e411 : ℝ := e5 + e410

def e412 : ℝ := Real.sqrt e411

def e413 : ℝ := e408 * e412

def e414 : ℝ := e97 * e409

def e415 : ℝ := e413 - e414

def e416 : ℝ := e406 * e415

def e417 : ℝ := e406 / e337

def e418 : ℝ := e89 * e417

def e419 : ℝ := e417 ^ 2

def e420 : ℝ := e91 * e419

def e421 : ℝ := e5 + e420

def e422 : ℝ := Real.sqrt e421

def e423 : ℝ := e418 * e422

def e424 : ℝ := e97 * e419

def e425 : ℝ := e423 - e424

def e426 : ℝ := e339 * e425

def e427 : ℝ := e416 - e426

def e428 : ℝ := e406 ^ 2

def e429 : ℝ := e8 * e428

def e430 : ℝ := e5 - e429

def e431 : ℝ := e5 - e428

def e432 : ℝ := Real.sqrt e431

def e433 : ℝ := e430 / e432

def e434 : ℝ := e5 - e433

def e435 : ℝ := e8 * e369

def e436 : ℝ := e5 - e435

def e437 : ℝ := e436 / e371

def e438 : ℝ := e5 - e437

def e439 : ℝ := e434 - e438

def e440 : ℝ := e427 * e439

def e441 : ℝ := e425 - e415

def e442 : ℝ := e5 + e432

def e443 : ℝ := e406 / e442

def e444 : ℝ := e443 ^ 2

def e445 : ℝ := e5 + e444

def e446 : ℝ := Real.sqrt e445

def e447 : ℝ := e5 + e446

def e448 : ℝ := e443 / e447

def e449 : ℝ := Real.arcsin e406

def e450 : ℝ := e59 * e449

def e451 : ℝ := e61 * e406

def e452 : ℝ := e451 * e432

def e453 : ℝ := e450 - e452

def e454 : ℝ := e43 * e432

def e455 : ℝ := e406 / e454

def e456 : ℝ := e453 - e455

def e457 : ℝ := e456 - e386

def e458 : ℝ := e441 * e457

def e459 : ℝ := e440 + e458

def e460 : ℝ := e406 - e339

def e461 : ℝ := e459 / e460

def e462 : ℝ := e404 + e461

def e463 : ℝ := e4 * e425

def e464 : ℝ := e4 / e337

def e465 : ℝ := e89 * e464

def e466 : ℝ := e464 ^ 2

def e467 : ℝ := e91 * e466

def e468 : ℝ := e5 + e467

def e469 : ℝ := Real.sqrt e468

def e470 : ℝ := e465 * e469

def e471 : ℝ := e97 * e466

def e472 : ℝ := e470 - e471

def e473 : ℝ := e406 * e472

def e474 : ℝ := e463 - e473

def e475 : ℝ := e165 - e434

def e476 : ℝ := e474 * e475

def e477 : ℝ := e472 - e425

def e478 : ℝ := e183 - e456

def e479 : ℝ := e477 * e478

def e480 : ℝ := e476 + e479

def e481 : ℝ := e4 - e406

def e482 : ℝ := e480 / e481

def e483 : ℝ := e462 + e482

def e485 : ℝ := e484 / e0

def e486 : ℝ := e484 * e7

def e487 : ℝ := e8 * e484

def e488 : ℝ := e487 / e0

def e490 : ℝ := e17 * e489

def e491 : ℝ := e490 / e0

def e492 : ℝ := e5 + e491

def e493 : ℝ := Real.sqrt e492

def e494 : ℝ := e5 + e493

def e495 : ℝ := e23 / e494

def e496 : ℝ := e9 * e495

def e497 : ℝ := e488 + e496

def e498 : ℝ := e497 - e5

def e499 : ℝ := e0 / e489

def e500 : ℝ := e485 ^ 2

def e501 : ℝ := e5 - e500

def e502 : ℝ := Real.sqrt e501

def e503 : ℝ := e29 - e502

def e504 : ℝ := e502 ^ 3

def e505 : ℝ := e504 / e35

def e506 : ℝ := e503 + e505

def e507 : ℝ := e8 * e506

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures508To725
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e508 : ℝ := e500 / e502

def e509 : ℝ := e508 - e23

def e510 : ℝ := e23 * e502

def e511 : ℝ := e509 + e510

def e512 : ℝ := e511 / e43

def e513 : ℝ := e507 - e512

def e514 : ℝ := e499 * e513

def e515 : ℝ := e498 + e514

def e516 : ℝ := e486 ^ 2

def e517 : ℝ := e5 - e516

def e518 : ℝ := Real.sqrt e517

def e519 : ℝ := e5 + e518

def e520 : ℝ := e486 / e519

def e521 : ℝ := e520 ^ 2

def e522 : ℝ := e5 + e521

def e523 : ℝ := Real.sqrt e522

def e524 : ℝ := e5 + e523

def e525 : ℝ := e520 / e524

def e526 : ℝ := Real.arcsin e486

def e527 : ℝ := e59 * e526

def e528 : ℝ := e61 * e486

def e529 : ℝ := e528 * e518

def e530 : ℝ := e527 - e529

def e531 : ℝ := e43 * e518

def e532 : ℝ := e486 / e531

def e533 : ℝ := e530 - e532

def e534 : ℝ := e5 + e502

def e535 : ℝ := e485 / e534

def e536 : ℝ := e535 ^ 2

def e537 : ℝ := e5 + e536

def e538 : ℝ := Real.sqrt e537

def e539 : ℝ := e5 + e538

def e540 : ℝ := e535 / e539

def e541 : ℝ := Real.arcsin e485

def e542 : ℝ := e59 * e541

def e543 : ℝ := e61 * e485

def e544 : ℝ := e543 * e502

def e545 : ℝ := e542 - e544

def e546 : ℝ := e43 * e502

def e547 : ℝ := e485 / e546

def e548 : ℝ := e545 - e547

def e549 : ℝ := e533 - e548

def e550 : ℝ := e549 / e484

def e551 : ℝ := e515 + e550

def e552 : ℝ := e486 + e4

def e553 : ℝ := e552 / e23

def e554 : ℝ := e486 / e484

def e555 : ℝ := e89 * e554

def e556 : ℝ := e554 ^ 2

def e557 : ℝ := e91 * e556

def e558 : ℝ := e5 + e557

def e559 : ℝ := Real.sqrt e558

def e560 : ℝ := e555 * e559

def e561 : ℝ := e97 * e556

def e562 : ℝ := e560 - e561

def e563 : ℝ := e553 * e562

def e564 : ℝ := e553 / e484

def e565 : ℝ := e89 * e564

def e566 : ℝ := e564 ^ 2

def e567 : ℝ := e91 * e566

def e568 : ℝ := e5 + e567

def e569 : ℝ := Real.sqrt e568

def e570 : ℝ := e565 * e569

def e571 : ℝ := e97 * e566

def e572 : ℝ := e570 - e571

def e573 : ℝ := e486 * e572

def e574 : ℝ := e563 - e573

def e575 : ℝ := e553 ^ 2

def e576 : ℝ := e8 * e575

def e577 : ℝ := e5 - e576

def e578 : ℝ := e5 - e575

def e579 : ℝ := Real.sqrt e578

def e580 : ℝ := e577 / e579

def e581 : ℝ := e5 - e580

def e582 : ℝ := e8 * e516

def e583 : ℝ := e5 - e582

def e584 : ℝ := e583 / e518

def e585 : ℝ := e5 - e584

def e586 : ℝ := e581 - e585

def e587 : ℝ := e574 * e586

def e588 : ℝ := e572 - e562

def e589 : ℝ := e5 + e579

def e590 : ℝ := e553 / e589

def e591 : ℝ := e590 ^ 2

def e592 : ℝ := e5 + e591

def e593 : ℝ := Real.sqrt e592

def e594 : ℝ := e5 + e593

def e595 : ℝ := e590 / e594

def e596 : ℝ := Real.arcsin e553

def e597 : ℝ := e59 * e596

def e598 : ℝ := e61 * e553

def e599 : ℝ := e598 * e579

def e600 : ℝ := e597 - e599

def e601 : ℝ := e43 * e579

def e602 : ℝ := e553 / e601

def e603 : ℝ := e600 - e602

def e604 : ℝ := e603 - e533

def e605 : ℝ := e588 * e604

def e606 : ℝ := e587 + e605

def e607 : ℝ := e553 - e486

def e608 : ℝ := e606 / e607

def e609 : ℝ := e551 + e608

def e610 : ℝ := e4 * e572

def e611 : ℝ := e4 / e484

def e612 : ℝ := e89 * e611

def e613 : ℝ := e611 ^ 2

def e614 : ℝ := e91 * e613

def e615 : ℝ := e5 + e614

def e616 : ℝ := Real.sqrt e615

def e617 : ℝ := e612 * e616

def e618 : ℝ := e97 * e613

def e619 : ℝ := e617 - e618

def e620 : ℝ := e553 * e619

def e621 : ℝ := e610 - e620

def e622 : ℝ := e165 - e581

def e623 : ℝ := e621 * e622

def e624 : ℝ := e619 - e572

def e625 : ℝ := e183 - e603

def e626 : ℝ := e624 * e625

def e627 : ℝ := e623 + e626

def e628 : ℝ := e4 - e553

def e629 : ℝ := e627 / e628

def e630 : ℝ := e609 + e629

def e631 : ℝ := e8 / e0

def e632 : ℝ := e8 * e7

def e633 : ℝ := e8 * e8

def e634 : ℝ := e633 / e0

def e635 : ℝ := e8 ^ 2

def e636 : ℝ := e17 * e635

def e637 : ℝ := e636 / e0

def e638 : ℝ := e5 + e637

def e639 : ℝ := Real.sqrt e638

def e640 : ℝ := e5 + e639

def e641 : ℝ := e23 / e640

def e642 : ℝ := e9 * e641

def e643 : ℝ := e634 + e642

def e644 : ℝ := e643 - e5

def e645 : ℝ := e0 / e635

def e646 : ℝ := e631 ^ 2

def e647 : ℝ := e5 - e646

def e648 : ℝ := Real.sqrt e647

def e649 : ℝ := e29 - e648

def e650 : ℝ := e648 ^ 3

def e651 : ℝ := e650 / e35

def e652 : ℝ := e649 + e651

def e653 : ℝ := e8 * e652

def e654 : ℝ := e646 / e648

def e655 : ℝ := e654 - e23

def e656 : ℝ := e23 * e648

def e657 : ℝ := e655 + e656

def e658 : ℝ := e657 / e43

def e659 : ℝ := e653 - e658

def e660 : ℝ := e645 * e659

def e661 : ℝ := e644 + e660

def e662 : ℝ := e632 ^ 2

def e663 : ℝ := e5 - e662

def e664 : ℝ := Real.sqrt e663

def e665 : ℝ := e5 + e664

def e666 : ℝ := e632 / e665

def e667 : ℝ := e666 ^ 2

def e668 : ℝ := e5 + e667

def e669 : ℝ := Real.sqrt e668

def e670 : ℝ := e5 + e669

def e671 : ℝ := e666 / e670

def e672 : ℝ := Real.arcsin e632

def e673 : ℝ := e59 * e672

def e674 : ℝ := e61 * e632

def e675 : ℝ := e674 * e664

def e676 : ℝ := e673 - e675

def e677 : ℝ := e43 * e664

def e678 : ℝ := e632 / e677

def e679 : ℝ := e676 - e678

def e680 : ℝ := e5 + e648

def e681 : ℝ := e631 / e680

def e682 : ℝ := e681 ^ 2

def e683 : ℝ := e5 + e682

def e684 : ℝ := Real.sqrt e683

def e685 : ℝ := e5 + e684

def e686 : ℝ := e681 / e685

def e687 : ℝ := Real.arcsin e631

def e688 : ℝ := e59 * e687

def e689 : ℝ := e61 * e631

def e690 : ℝ := e689 * e648

def e691 : ℝ := e688 - e690

def e692 : ℝ := e43 * e648

def e693 : ℝ := e631 / e692

def e694 : ℝ := e691 - e693

def e695 : ℝ := e679 - e694

def e696 : ℝ := e695 / e8

def e697 : ℝ := e661 + e696

def e698 : ℝ := e632 + e4

def e699 : ℝ := e698 / e23

def e700 : ℝ := e632 / e8

def e701 : ℝ := e89 * e700

def e702 : ℝ := e700 ^ 2

def e703 : ℝ := e91 * e702

def e704 : ℝ := e5 + e703

def e705 : ℝ := Real.sqrt e704

def e706 : ℝ := e701 * e705

def e707 : ℝ := e97 * e702

def e708 : ℝ := e706 - e707

def e709 : ℝ := e699 * e708

def e710 : ℝ := e699 / e8

def e711 : ℝ := e89 * e710

def e712 : ℝ := e710 ^ 2

def e713 : ℝ := e91 * e712

def e714 : ℝ := e5 + e713

def e715 : ℝ := Real.sqrt e714

def e716 : ℝ := e711 * e715

def e717 : ℝ := e97 * e712

def e718 : ℝ := e716 - e717

def e719 : ℝ := e632 * e718

def e720 : ℝ := e709 - e719

def e721 : ℝ := e699 ^ 2

def e722 : ℝ := e8 * e721

def e723 : ℝ := e5 - e722

def e724 : ℝ := e5 - e721

def e725 : ℝ := Real.sqrt e724

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures726To944
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e726 : ℝ := e723 / e725

def e727 : ℝ := e5 - e726

def e728 : ℝ := e8 * e662

def e729 : ℝ := e5 - e728

def e730 : ℝ := e729 / e664

def e731 : ℝ := e5 - e730

def e732 : ℝ := e727 - e731

def e733 : ℝ := e720 * e732

def e734 : ℝ := e718 - e708

def e735 : ℝ := e5 + e725

def e736 : ℝ := e699 / e735

def e737 : ℝ := e736 ^ 2

def e738 : ℝ := e5 + e737

def e739 : ℝ := Real.sqrt e738

def e740 : ℝ := e5 + e739

def e741 : ℝ := e736 / e740

def e742 : ℝ := Real.arcsin e699

def e743 : ℝ := e59 * e742

def e744 : ℝ := e61 * e699

def e745 : ℝ := e744 * e725

def e746 : ℝ := e743 - e745

def e747 : ℝ := e43 * e725

def e748 : ℝ := e699 / e747

def e749 : ℝ := e746 - e748

def e750 : ℝ := e749 - e679

def e751 : ℝ := e734 * e750

def e752 : ℝ := e733 + e751

def e753 : ℝ := e699 - e632

def e754 : ℝ := e752 / e753

def e755 : ℝ := e697 + e754

def e756 : ℝ := e4 * e718

def e758 : ℝ := e89 * e757

def e759 : ℝ := e757 ^ 2

def e760 : ℝ := e91 * e759

def e761 : ℝ := e5 + e760

def e762 : ℝ := Real.sqrt e761

def e763 : ℝ := e758 * e762

def e764 : ℝ := e97 * e759

def e765 : ℝ := e763 - e764

def e766 : ℝ := e699 * e765

def e767 : ℝ := e756 - e766

def e768 : ℝ := e165 - e727

def e769 : ℝ := e767 * e768

def e770 : ℝ := e765 - e718

def e771 : ℝ := e183 - e749

def e772 : ℝ := e770 * e771

def e773 : ℝ := e769 + e772

def e774 : ℝ := e4 - e699

def e775 : ℝ := e773 / e774

def e776 : ℝ := e755 + e775

def e778 : ℝ := e777 / e0

def e779 : ℝ := e777 * e7

def e780 : ℝ := e8 * e777

def e781 : ℝ := e780 / e0

def e783 : ℝ := e17 * e782

def e784 : ℝ := e783 / e0

def e785 : ℝ := e5 + e784

def e786 : ℝ := Real.sqrt e785

def e787 : ℝ := e5 + e786

def e788 : ℝ := e23 / e787

def e789 : ℝ := e9 * e788

def e790 : ℝ := e781 + e789

def e791 : ℝ := e790 - e5

def e792 : ℝ := e0 / e782

def e793 : ℝ := e778 ^ 2

def e794 : ℝ := e5 - e793

def e795 : ℝ := Real.sqrt e794

def e796 : ℝ := e29 - e795

def e797 : ℝ := e795 ^ 3

def e798 : ℝ := e797 / e35

def e799 : ℝ := e796 + e798

def e800 : ℝ := e8 * e799

def e801 : ℝ := e793 / e795

def e802 : ℝ := e801 - e23

def e803 : ℝ := e23 * e795

def e804 : ℝ := e802 + e803

def e805 : ℝ := e804 / e43

def e806 : ℝ := e800 - e805

def e807 : ℝ := e792 * e806

def e808 : ℝ := e791 + e807

def e809 : ℝ := e779 ^ 2

def e810 : ℝ := e5 - e809

def e811 : ℝ := Real.sqrt e810

def e812 : ℝ := e5 + e811

def e813 : ℝ := e779 / e812

def e814 : ℝ := e813 ^ 2

def e815 : ℝ := e5 + e814

def e816 : ℝ := Real.sqrt e815

def e817 : ℝ := e5 + e816

def e818 : ℝ := e813 / e817

def e819 : ℝ := Real.arcsin e779

def e820 : ℝ := e59 * e819

def e821 : ℝ := e61 * e779

def e822 : ℝ := e821 * e811

def e823 : ℝ := e820 - e822

def e824 : ℝ := e43 * e811

def e825 : ℝ := e779 / e824

def e826 : ℝ := e823 - e825

def e827 : ℝ := e5 + e795

def e828 : ℝ := e778 / e827

def e829 : ℝ := e828 ^ 2

def e830 : ℝ := e5 + e829

def e831 : ℝ := Real.sqrt e830

def e832 : ℝ := e5 + e831

def e833 : ℝ := e828 / e832

def e834 : ℝ := Real.arcsin e778

def e835 : ℝ := e59 * e834

def e836 : ℝ := e61 * e778

def e837 : ℝ := e836 * e795

def e838 : ℝ := e835 - e837

def e839 : ℝ := e43 * e795

def e840 : ℝ := e778 / e839

def e841 : ℝ := e838 - e840

def e842 : ℝ := e826 - e841

def e843 : ℝ := e842 / e777

def e844 : ℝ := e808 + e843

def e845 : ℝ := e779 + e4

def e846 : ℝ := e845 / e23

def e847 : ℝ := e779 / e777

def e848 : ℝ := e89 * e847

def e849 : ℝ := e847 ^ 2

def e850 : ℝ := e91 * e849

def e851 : ℝ := e5 + e850

def e852 : ℝ := Real.sqrt e851

def e853 : ℝ := e848 * e852

def e854 : ℝ := e97 * e849

def e855 : ℝ := e853 - e854

def e856 : ℝ := e846 * e855

def e857 : ℝ := e846 / e777

def e858 : ℝ := e89 * e857

def e859 : ℝ := e857 ^ 2

def e860 : ℝ := e91 * e859

def e861 : ℝ := e5 + e860

def e862 : ℝ := Real.sqrt e861

def e863 : ℝ := e858 * e862

def e864 : ℝ := e97 * e859

def e865 : ℝ := e863 - e864

def e866 : ℝ := e779 * e865

def e867 : ℝ := e856 - e866

def e868 : ℝ := e846 ^ 2

def e869 : ℝ := e8 * e868

def e870 : ℝ := e5 - e869

def e871 : ℝ := e5 - e868

def e872 : ℝ := Real.sqrt e871

def e873 : ℝ := e870 / e872

def e874 : ℝ := e5 - e873

def e875 : ℝ := e8 * e809

def e876 : ℝ := e5 - e875

def e877 : ℝ := e876 / e811

def e878 : ℝ := e5 - e877

def e879 : ℝ := e874 - e878

def e880 : ℝ := e867 * e879

def e881 : ℝ := e865 - e855

def e882 : ℝ := e5 + e872

def e883 : ℝ := e846 / e882

def e884 : ℝ := e883 ^ 2

def e885 : ℝ := e5 + e884

def e886 : ℝ := Real.sqrt e885

def e887 : ℝ := e5 + e886

def e888 : ℝ := e883 / e887

def e889 : ℝ := Real.arcsin e846

def e890 : ℝ := e59 * e889

def e891 : ℝ := e61 * e846

def e892 : ℝ := e891 * e872

def e893 : ℝ := e890 - e892

def e894 : ℝ := e43 * e872

def e895 : ℝ := e846 / e894

def e896 : ℝ := e893 - e895

def e897 : ℝ := e896 - e826

def e898 : ℝ := e881 * e897

def e899 : ℝ := e880 + e898

def e900 : ℝ := e846 - e779

def e901 : ℝ := e899 / e900

def e902 : ℝ := e844 + e901

def e903 : ℝ := e4 * e865

def e904 : ℝ := e4 / e777

def e905 : ℝ := e89 * e904

def e906 : ℝ := e904 ^ 2

def e907 : ℝ := e91 * e906

def e908 : ℝ := e5 + e907

def e909 : ℝ := Real.sqrt e908

def e910 : ℝ := e905 * e909

def e911 : ℝ := e97 * e906

def e912 : ℝ := e910 - e911

def e913 : ℝ := e846 * e912

def e914 : ℝ := e903 - e913

def e915 : ℝ := e165 - e874

def e916 : ℝ := e914 * e915

def e917 : ℝ := e912 - e865

def e918 : ℝ := e183 - e896

def e919 : ℝ := e917 * e918

def e920 : ℝ := e916 + e919

def e921 : ℝ := e4 - e846

def e922 : ℝ := e920 / e921

def e923 : ℝ := e902 + e922

def e925 : ℝ := e924 / e777

def e926 : ℝ := min e7 e925

def e927 : ℝ := e926 - e5

def e928 : ℝ := e23 * e777

def e929 : ℝ := e928 * e788

def e930 : ℝ := e929 / e0

def e931 : ℝ := e927 + e930

def e933 : ℝ := e23 * e782

def e934 : ℝ := e933 * e788

def e935 : ℝ := e0 + e934

def e936 : ℝ := Real.sqrt e935

def e937 : ℝ := e932 * e936

def e940 : ℝ := e939 * e938

def e942 : ℝ := min e940 e941

def e943 : ℝ := e23 * e931

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures945To1164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e945 : ℝ := e944 * e942

def e946 : ℝ := e937 ^ 2

def e947 : ℝ := e945 * e946

def e948 : ℝ := e947 * e931

def e949 : ℝ := e948 / e9

def e950 : ℝ := e5 + e949

def e951 : ℝ := Real.sqrt e950

def e952 : ℝ := e5 + e951

def e953 : ℝ := e943 / e952

def e955 : ℝ := e942 * e954

def e956 : ℝ := e931 - e953

def e957 : ℝ := e956 / e937

def e958 : ℝ := e957 ^ 2

def e959 : ℝ := e9 * e958

def e960 : ℝ := e953 ^ 3

def e961 : ℝ := e942 * e960

def e962 : ℝ := e959 + e961

def e963 : ℝ := min e955 e962

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures2921To3142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e3134 : ℝ := e3128 - e3133

def e3135 : ℝ := e3120 * e3134

def e3136 : ℝ := e3119 + e3135

def e3137 : ℝ := e5 + e3123

def e3138 : ℝ := e3107 / e3137

def e3139 : ℝ := e3138 ^ 2

def e3140 : ℝ := e5 + e3139

def e3141 : ℝ := Real.sqrt e3140

def e3142 : ℝ := e5 + e3141

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures3143To3335
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e3143 : ℝ := e3138 / e3142

def e3144 : ℝ := Real.arcsin e3107

def e3145 : ℝ := e59 * e3144

def e3146 : ℝ := e61 * e3107

def e3147 : ℝ := e3146 * e3123

def e3148 : ℝ := e3145 - e3147

def e3149 : ℝ := e43 * e3123

def e3150 : ℝ := e3107 / e3149

def e3151 : ℝ := e3148 - e3150

def e3152 : ℝ := e183 - e3151

def e3153 : ℝ := e3152 / e3106

def e3154 : ℝ := e3136 + e3153

def e3155 : ℝ := e924 / e3106

def e3156 : ℝ := min e7 e3155

def e3157 : ℝ := e3156 - e5

def e3158 : ℝ := e23 * e3106

def e3159 : ℝ := e3158 * e3116

def e3160 : ℝ := e3159 / e0

def e3161 : ℝ := e3157 + e3160

def e3162 : ℝ := e23 * e3110

def e3163 : ℝ := e3162 * e3116

def e3164 : ℝ := e0 + e3163

def e3165 : ℝ := Real.sqrt e3164

def e3166 : ℝ := e932 * e3165

def e3167 : ℝ := e3106 ^ 3

def e3168 : ℝ := e939 * e3167

def e3169 : ℝ := min e3168 e941

def e3170 : ℝ := e23 * e3161

def e3171 : ℝ := e944 * e3169

def e3172 : ℝ := e3166 ^ 2

def e3173 : ℝ := e3171 * e3172

def e3174 : ℝ := e3173 * e3161

def e3175 : ℝ := e3174 / e9

def e3176 : ℝ := e5 + e3175

def e3177 : ℝ := Real.sqrt e3176

def e3178 : ℝ := e5 + e3177

def e3179 : ℝ := e3170 / e3178

def e3180 : ℝ := e3169 * e954

def e3181 : ℝ := e3161 - e3179

def e3182 : ℝ := e3181 / e3166

def e3183 : ℝ := e3182 ^ 2

def e3184 : ℝ := e9 * e3183

def e3185 : ℝ := e3179 ^ 3

def e3186 : ℝ := e3169 * e3185

def e3187 : ℝ := e3184 + e3186

def e3188 : ℝ := min e3180 e3187

def e3190 : ℝ := e3189 / e0

def e3191 : ℝ := e8 * e3189

def e3192 : ℝ := e3191 / e0

def e3194 : ℝ := e17 * e3193

def e3195 : ℝ := e3194 / e0

def e3196 : ℝ := e5 + e3195

def e3197 : ℝ := Real.sqrt e3196

def e3198 : ℝ := e5 + e3197

def e3199 : ℝ := e23 / e3198

def e3200 : ℝ := e9 * e3199

def e3201 : ℝ := e3192 + e3200

def e3202 : ℝ := e3201 - e5

def e3203 : ℝ := e0 / e3193

def e3204 : ℝ := e3190 ^ 2

def e3205 : ℝ := e5 - e3204

def e3206 : ℝ := Real.sqrt e3205

def e3207 : ℝ := e29 - e3206

def e3208 : ℝ := e3206 ^ 3

def e3209 : ℝ := e3208 / e35

def e3210 : ℝ := e3207 + e3209

def e3211 : ℝ := e8 * e3210

def e3212 : ℝ := e3204 / e3206

def e3213 : ℝ := e3212 - e23

def e3214 : ℝ := e23 * e3206

def e3215 : ℝ := e3213 + e3214

def e3216 : ℝ := e3215 / e43

def e3217 : ℝ := e3211 - e3216

def e3218 : ℝ := e3203 * e3217

def e3219 : ℝ := e3202 + e3218

def e3220 : ℝ := e5 + e3206

def e3221 : ℝ := e3190 / e3220

def e3222 : ℝ := e3221 ^ 2

def e3223 : ℝ := e5 + e3222

def e3224 : ℝ := Real.sqrt e3223

def e3225 : ℝ := e5 + e3224

def e3226 : ℝ := e3221 / e3225

def e3227 : ℝ := Real.arcsin e3190

def e3228 : ℝ := e59 * e3227

def e3229 : ℝ := e61 * e3190

def e3230 : ℝ := e3229 * e3206

def e3231 : ℝ := e3228 - e3230

def e3232 : ℝ := e43 * e3206

def e3233 : ℝ := e3190 / e3232

def e3234 : ℝ := e3231 - e3233

def e3235 : ℝ := e183 - e3234

def e3236 : ℝ := e3235 / e3189

def e3237 : ℝ := e3219 + e3236

def e3239 : ℝ := e3238 / e0

def e3240 : ℝ := e8 * e3238

def e3241 : ℝ := e3240 / e0

def e3243 : ℝ := e17 * e3242

def e3244 : ℝ := e3243 / e0

def e3245 : ℝ := e5 + e3244

def e3246 : ℝ := Real.sqrt e3245

def e3247 : ℝ := e5 + e3246

def e3248 : ℝ := e23 / e3247

def e3249 : ℝ := e9 * e3248

def e3250 : ℝ := e3241 + e3249

def e3251 : ℝ := e3250 - e5

def e3252 : ℝ := e0 / e3242

def e3253 : ℝ := e3239 ^ 2

def e3254 : ℝ := e5 - e3253

def e3255 : ℝ := Real.sqrt e3254

def e3256 : ℝ := e29 - e3255

def e3257 : ℝ := e3255 ^ 3

def e3258 : ℝ := e3257 / e35

def e3259 : ℝ := e3256 + e3258

def e3260 : ℝ := e8 * e3259

def e3261 : ℝ := e3253 / e3255

def e3262 : ℝ := e3261 - e23

def e3263 : ℝ := e23 * e3255

def e3264 : ℝ := e3262 + e3263

def e3265 : ℝ := e3264 / e43

def e3266 : ℝ := e3260 - e3265

def e3267 : ℝ := e3252 * e3266

def e3268 : ℝ := e3251 + e3267

def e3269 : ℝ := e5 + e3255

def e3270 : ℝ := e3239 / e3269

def e3271 : ℝ := e3270 ^ 2

def e3272 : ℝ := e5 + e3271

def e3273 : ℝ := Real.sqrt e3272

def e3274 : ℝ := e5 + e3273

def e3275 : ℝ := e3270 / e3274

def e3276 : ℝ := Real.arcsin e3239

def e3277 : ℝ := e59 * e3276

def e3278 : ℝ := e61 * e3239

def e3279 : ℝ := e3278 * e3255

def e3280 : ℝ := e3277 - e3279

def e3281 : ℝ := e43 * e3255

def e3282 : ℝ := e3239 / e3281

def e3283 : ℝ := e3280 - e3282

def e3284 : ℝ := e183 - e3283

def e3285 : ℝ := e3284 / e3238

def e3286 : ℝ := e3268 + e3285

def e3288 : ℝ := e3287 / e0

def e3289 : ℝ := e8 * e3287

def e3290 : ℝ := e3289 / e0

def e3292 : ℝ := e17 * e3291

def e3293 : ℝ := e3292 / e0

def e3294 : ℝ := e5 + e3293

def e3295 : ℝ := Real.sqrt e3294

def e3296 : ℝ := e5 + e3295

def e3297 : ℝ := e23 / e3296

def e3298 : ℝ := e9 * e3297

def e3299 : ℝ := e3290 + e3298

def e3300 : ℝ := e3299 - e5

def e3301 : ℝ := e0 / e3291

def e3302 : ℝ := e3288 ^ 2

def e3303 : ℝ := e5 - e3302

def e3304 : ℝ := Real.sqrt e3303

def e3305 : ℝ := e29 - e3304

def e3306 : ℝ := e3304 ^ 3

def e3307 : ℝ := e3306 / e35

def e3308 : ℝ := e3305 + e3307

def e3309 : ℝ := e8 * e3308

def e3310 : ℝ := e3302 / e3304

def e3311 : ℝ := e3310 - e23

def e3312 : ℝ := e23 * e3304

def e3313 : ℝ := e3311 + e3312

def e3314 : ℝ := e3313 / e43

def e3315 : ℝ := e3309 - e3314

def e3316 : ℝ := e3301 * e3315

def e3317 : ℝ := e3300 + e3316

def e3318 : ℝ := e5 + e3304

def e3319 : ℝ := e3288 / e3318

def e3320 : ℝ := e3319 ^ 2

def e3321 : ℝ := e5 + e3320

def e3322 : ℝ := Real.sqrt e3321

def e3323 : ℝ := e5 + e3322

def e3324 : ℝ := e3319 / e3323

def e3325 : ℝ := Real.arcsin e3288

def e3326 : ℝ := e59 * e3325

def e3327 : ℝ := e61 * e3288

def e3328 : ℝ := e3327 * e3304

def e3329 : ℝ := e3326 - e3328

def e3330 : ℝ := e43 * e3304

def e3331 : ℝ := e3288 / e3330

def e3332 : ℝ := e3329 - e3331

def e3333 : ℝ := e183 - e3332

def e3334 : ℝ := e3333 / e3287

def e3335 : ℝ := e3317 + e3334

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
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

def revolutionPoint (c : Cover) (r : ℝ → ℝ) (t a : ℝ) : Cover :=
  coordinateSectionPoint c t (r t • unitAngle a)

@[simp] lemma unitAngle_zero : unitAngle 0=1 := by simp [unitAngle]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma unitSquareScale_zero : unitSquareScale 0=1/2 := by
  norm_num [unitSquareScale,unitAngle_zero,complexSquareGauge]

end CubicTorus

end
end

end OAI
end


