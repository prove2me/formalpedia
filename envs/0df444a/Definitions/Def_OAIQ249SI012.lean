-- Prove2me | Definitions.Def_OAIQ249SI012
-- name    : OAIQ249SI012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:10:21.354195+00:00
-- url     : https://prove2.me/theorems/3a4fcb75-78d6-44f9-a517-810c1c85f204
-- title:
--   Definitions bundle OAIQ249SI012 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 208 declarations of OpenAI's Lean: 171 definitions and 37 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasFreeOscillation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordDerivDataSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeOscillation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasNonzero`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteGlobalAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.freeGlobalAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseLabel`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridRestoredPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqGridPhaseIndex`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasLocalIncrement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasRemainder`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncodeLM`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorProjectLM`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorReadBallConstant`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1DataSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1TensorDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualParamFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualParamFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredActualFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredFixedFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredIncrementFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredIncrementFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredInputFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothSectionNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace` and 131 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_MeanError`, `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_PhaseMean`, `Immersion_ClosedSurface_RealBounds`, `SurfaceImmersion_Atlas_AnchoredAtlasIncrement`, `SurfaceImmersion_Atlas_BundleCutoffCoordinates`, `SurfaceImmersion_Atlas_FiniteAtlasIncrement`, `SurfaceImmersion_Atlas_GridAdjustedIncrement`, `SurfaceImmersion_Atlas_GridGeometricIncrement`, `SurfaceImmersion_Atlas_GridRestoredGeometry`, `SurfaceImmersion_Atlas_NonlinearAtlasAnsatz`, `SurfaceImmersion_Atlas_NonlinearAtlasMetric`, `SurfaceImmersion_Atlas_ReferenceCoordinateData`, `SurfaceImmersion_Atlas_TangentMetricBounds`, `SurfaceImmersion_Atlas_TensorChartRead`, `SurfaceImmersion_Atlas_TensorPlaneCoordinates`, `SurfaceImmersion_Correction_AnchoredSmoothedIncrement`, `SurfaceImmersion_Correction_AtlasFreeOscillation`, `SurfaceImmersion_Correction_AtlasGlobalFreeModes`, `SurfaceImmersion_Correction_BoundedSurfaceCorrection`, `SurfaceImmersion_Correction_ChartedCombinedMean`, `SurfaceImmersion_Correction_ChartedFreeDisplacement`, `SurfaceImmersion_Correction_ChartedFreeFamily`, `SurfaceImmersion_Correction_ChartedFreeResidual`, `SurfaceImmersion_Correction_ChartedFreeSeed`, `SurfaceImmersion_Correction_ChartedMeanData`, `SurfaceImmersion_Correction_ChartedMeanFamily`, `SurfaceImmersion_Correction_ChartedMeanFamilyData`, `SurfaceImmersion_Correction_ChartedMetricMean`, `SurfaceImmersion_Correction_ChartedUniformFree`, `SurfaceImmersion_Correction_ChartedZeroMean`, `SurfaceImmersion_Correction_FiniteAtlasFreeMetric`, `SurfaceImmersion_Correction_GridFreeCorrection`, `SurfaceImmersion_Correction_GridGlobalQuadraticCorrection`, `SurfaceImmersion_Correction_JetPolynomialScalar`, `SurfaceImmersion_Correction_JetPolynomialVector`, `SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion`, `SurfaceImmersion_Correction_NormalizedPerturbedMean`, `SurfaceImmersion_Correction_PerturbedFreeMode`, `SurfaceImmersion_Correction_PolynomialGeometry`, `SurfaceImmersion_Correction_PolynomialJetRecursion`, `SurfaceImmersion_Correction_SupportedFreeLinearity`, `SurfaceImmersion_Correction_SurfaceMeanPolynomial`, `SurfaceImmersion_Correction_SurfaceMeanTensor`, `SurfaceImmersion_Correction_TensorAtlasMean`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorMeanIteration`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Geometry_AnchoredActualStep`, `SurfaceImmersion_Geometry_AnchoredFixedOrderStep`, `SurfaceImmersion_Geometry_AnchoredInputStep`, `SurfaceImmersion_Geometry_CoefficientJetBounds`, `SurfaceImmersion_Geometry_CorrectedNormalSeed`, `SurfaceImmersion_Geometry_ExactFastFamily`, `SurfaceImmersion_Geometry_GeometricPerturbedParametrix`, `SurfaceImmersion_Geometry_IndependentGeometricNormal`, `SurfaceImmersion_Geometry_IndependentGlobalNormal`, `SurfaceImmersion_Geometry_IndependentPreservingNormal`, `SurfaceImmersion_Geometry_QuantitativeMetricExpansion`, `SurfaceImmersion_Geometry_ReferenceAmplitudeMargin`, `SurfaceImmersion_Geometry_ReferenceAmplitudeParameterBounds`, `SurfaceImmersion_Geometry_ReferenceCoefficientLower`, `SurfaceImmersion_Geometry_ReferenceCorrectedFamily`, `SurfaceImmersion_Geometry_ReferenceMetricStability`, `SurfaceImmersion_Geometry_ReferenceOperatorStability`, `SurfaceImmersion_Geometry_ReferencePerturbationStability`, `SurfaceImmersion_Geometry_SurfaceMetricExpansion`, `SurfaceImmersion_Geometry_TensorDecodedBounds`, `SurfaceImmersion_Geometry_TensorFrameReadBounds`, `SurfaceImmersion_Geometry_TransverseCoefficientBounds`, `SurfaceImmersion_Geometry_UniformActualAmplitudeC1`, `SurfaceImmersion_Primitive_GridIncrementProfile`, `SurfaceImmersion_Primitive_IndependentCircularBoundary`, `SurfaceImmersion_Primitive_IndependentCircularBoundaryStep`, `SurfaceImmersion_Primitive_IndependentConstructedCircular`, `SurfaceImmersion_Primitive_IndependentExactCircular`, `SurfaceImmersion_Primitive_IndependentExactOriginalProfiles`, `SurfaceImmersion_Primitive_IndependentExactPhaseProfiles`, `SurfaceImmersion_Primitive_IndependentExactProfiledPhase`, `SurfaceImmersion_Primitive_IndependentPhaseBoundaryProfiles`, `SurfaceImmersion_Primitive_IndependentPreservingCircular`, `SurfaceImmersion_Primitive_IndependentProfiledFastFamily`, `SurfaceImmersion_Primitive_LeadingProfileStability`, `SurfaceImmersion_Primitive_LocalAnsatzProfiles`, `SurfaceImmersion_Primitive_LocalPeriodicCalculus`, `SurfaceImmersion_Primitive_LocalPeriodicExpansionInit`, `SurfaceImmersion_Primitive_LocalPeriodicFamilies`, `SurfaceImmersion_Primitive_LocalPeriodicFamilyAlgebra`, `SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation`, `SurfaceImmersion_Primitive_LocalPeriodicFiniteAnsatz`, `SurfaceImmersion_Primitive_LocalPeriodicMetricCoefficients`, `SurfaceImmersion_Primitive_LocalPeriodicMetricRemainder`, `SurfaceImmersion_Primitive_PrimitiveCoordinateDerivative`, `SurfaceImmersion_Primitive_PrimitiveCoordinateGerms`, `SurfaceImmersion_Primitive_PrimitivePatchBoundaryStep`, `SurfaceImmersion_Primitive_ReferenceCircularMargins`, `SurfaceImmersion_Primitive_SurfacePrimitiveError`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI010` and `OAIQ249SI011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI014` and `OAIQ249SI016`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CrosscapCoordinateStrip_nondegenerate_normal_defect_framed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_constructed_circular_primitive_boundary`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_phase_primitive_five_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_preserving_circular_primitive_boundary`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_preserving_circular_primitive_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_global_polynomial_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedAmplitude_coordinate_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_metric_split`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_linearized_residual_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_adjusted_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_jetProfile`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_seed_profile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_profiled_atlas_adjusted_mean`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_real_restored_polynomial_quadratic`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_polynomial_representation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_zeroPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_amplitude_reads`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_small_increment`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_vectorPlaneRestore_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_vectorPlaneRestore_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_error_finiteSmooth`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finiteSmooth_approximation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_iterated_residual_bounded`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_iterated_residual_norm_le`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_double_curve_boundary_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_double_curve_boundary_paths`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_add_orders`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_compact`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_smooth`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_transverse_double_curve_boundary_chart`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_crossings`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_curve_cover`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.freeDisplacement_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.freeDisplacement_residual_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_difference_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.originalFreeSeed_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_charted_forced_mode`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_coordinateFullLinearized_sum`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_coordinateFullLinearized_unperturbed`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_chartedFamilyData_majorants`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets`, `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients`, `OAI.ClosedSurfaceR4.JetPolynomial.exists_polynomial_coefficients`, `OAI_ClosedSurfaceR4_PhaseGeometry_explicit_finite_split_cancellation`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_bounded_surface_correction`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_supported_primitive_expansion`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_five_profiles`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles` and `OAI_ClosedSurfaceR4_atlas_phase_weight_constants_with_catalog`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_constructed_circular_primitive_boundary`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_phase_primitive_five_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_preserving_circular_primitive_boundary`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_preserving_circular_primitive_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_finite_slow_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.circular_operator_metric_stability`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_global_polynomial_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_catalog_global_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_geometry_polynomial_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedAmplitude_coordinate_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_crossing_safe_phase_normal_gluing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_reference_circular_atlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_metric_split`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_exterior_crossing_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_adjusted_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.metric_firstJet_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_jetProfile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_free_profile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_point_crossings`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_profiled_atlas_adjusted_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_real_restored_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_convex_phases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_induced_metric_upper_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_amplitude_reads`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_vectorPlaneRestore_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_current_second`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_old_boundary_crossing`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_error_finiteSmooth`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finiteSmooth_approximation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_iterated_residual_bounded`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_iterated_residual_norm_le`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_join_time_charts`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_normalized_pair_frame_filling`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_add_orders`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_compact`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_residual_smooth`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_signed_diagonal_filling`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_crossings`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_curve_cover`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.freeDisplacement_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.freeDisplacement_residual_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_difference_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.originalFreeSeed_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_coordinateFullLinearized_sum`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_coordinateFullLinearized_unperturbed`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_normalizedPolynomialMean_bounds`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_phaseCoordinatePolynomialOperator_bounds`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_free_family`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_seed_bounds`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_mean_family_from_budgets`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_coordinate_taylor_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_quadraticFamilyTensor_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_chartedFamilyData_majorants`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_combined_mean`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_free_family`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_polynomial_mean`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets`, `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients`, `OAI.ClosedSurfaceR4.JetPolynomial.exists_polynomial_coefficients`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_profiled_split_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_relative_phase_polynomial_cancellation`, `OAI_ClosedSurfaceR4_RealModes_polynomial_frame_envelope`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_bounded_surface_correction`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_supported_primitive_expansion`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_five_profiles`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles` and `OAI_ClosedSurfaceR4_atlas_phase_weight_constants_with_catalog`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

section Elimination
variable {n : ℕ}


def reducedLx (G : Field n) (ux uy : Scalar) (p : Base) : ℂ :=
  coordDeriv dx ux p - connectionTerm G ux uy dx dx p -
    secondRatio G dx dx p * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p)

def reducedLy (G : Field n) (ux uy : Scalar) (p : Base) : ℂ :=
  coordDeriv dx uy p + coordDeriv dy ux p - 2 * connectionTerm G ux uy dx dy p -
    2 * secondRatio G dx dy p * (coordDeriv dy uy p - connectionTerm G ux uy dy dy p)


end Elimination

section LinearStructure
variable {n : ℕ}



def errorGenerator (G V : Field n) (h : Tensor) : Tensor :=
  let kx := reducedKx G V (component h 0) (component h 2)
  let ky := reducedKy G V (component h 1) (component h 2)
  tensorOf (fun p => 2 * reducedLx G kx ky p) (reducedLy G kx ky) (fun _ => 0)


def errorHierarchy (G V : Field n) (h : Tensor) : ℕ → Tensor
  | 0 => errorGenerator G V h
  | j + 1 => errorGenerator G (fun _ => 0) (errorHierarchy G V h j)

end LinearStructure

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanError
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates



def modeMeanError {n : ℕ} (τ : ℝ) (G V W : Field n) (q : ℕ) (v w : Base) : Base → ℝ :=
  fun p => ClosedSurfaceR4.QuadraticMean.zeroPair
      (gradientAmplitude τ (modeApprox τ G V (fun _ => 0) q) v p)
      (gradientAmplitude τ (modeApprox τ G W (fun _ => 0) q) w p) -
    ClosedSurfaceR4.QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ W w p)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates


def normalizedMeanError (δ τ : ℝ) (F : RField 4) (b : Base → ℝ) (q : ℕ) (v w : Base) : Base → ℝ :=
  fun p => (δ ^ 2)⁻¹ * modeMeanError τ (fun p => complexify (F p))
    (freeSeed δ τ b F) (freeSeed δ τ b F) q v w p



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.RootMean ClosedSurfaceR4.WeightedEstimates
open Set



def meanTensor (δ τ : ℝ) (F : RField 4) (b : Base → ℝ) (q : ℕ) : Base → Tensor :=
  fun p i => normalizedMeanError δ τ F b q (firstDirection i) (secondDirection i) p



def meanTerm (δ s : ℝ) (F : RField 4) (ψ : Base → ℝ)
    (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) (q : ℕ)
    (η : ℝ) (A : Base → Tensor) : Base → Tensor :=
  fun p => pullbackField χ p
    (meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e A)) q (χ p))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_BundleCutoffCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading a section with an arbitrary compact chart cutoff is bounded by
its atlas norm. This allows phase patches to use unweighted tensor values. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)

include hdomain

variable [CompactSpace M]

/-- Cutoff coordinates lose no derivatives and have constants independent of
both the section and its weighted scale. -/
theorem bundleCutoff_bound (i : A.centers) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart (i : M)).source) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x, E x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e s m C u →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D * C) (A.bundleCutoff e i ψ u) := by
  classical
  have hb (j : A.centers) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D * C) (A.bundleCutoff e i ψ (A.bundleRestore e j f)) := by
    let K : Set Base := (chart (i : M)) '' (tsupport ψ ∩ tsupport (A.outer j))
    have hK : IsCompact K :=
      ((isClosed_tsupport ψ).inter (isClosed_tsupport (A.outer j))).isCompact.image_of_continuousOn
        ((chart (i : M)).continuousOn.mono (fun _ hx => hsupp hx.1))
    have hKO : K ⊆ (transition (i : M) (j : M)).source := by
      rintro x ⟨p,⟨hp,hq⟩,rfl⟩
      refine ⟨(chart (i : M)).map_source (hsupp hp),?_⟩
      change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
      rw [(chart (i : M)).left_inv (hsupp hp)]
      exact A.outer_support j hq
    obtain ⟨D,hD,hd⟩ := compact_localized_clm_composition_bound
      (transition (i : M) (j : M)).open_source hK hKO
      (localize_smooth (i : M) hψ hsupp (A.outer_smooth j))
      (localize_tsupport_inter (i : M) hsupp (A.outer j))
      (A.bundleTransition_smooth e hdomain i j) (transition_smooth (i : M) (j : M)) m
    refine ⟨D,hD,?_⟩
    intro f s C hs hs1 hC hf hbf
    rw [A.bundleCutoff_restore e hdomain]
    exact hd f s C hs hs1 hC hf hbf
  choose D hD hd using hb
  refine ⟨∑ j : A.centers, D j, Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro u s C hs hs1 hC hu hbu
  have heq : A.bundleCutoff e i ψ u = fun x => ∑ j : A.centers,
      A.bundleCutoff e i ψ (A.bundleRestore e j (A.bundleLocalize e j u)) x := by
    have hu' : u = (fun p => ∑ j : A.centers,
        A.bundleRestore e j (A.bundleLocalize e j u) p) :=
      (funext (A.bundle_sum_restore_localize e hdomain u)).symm
    funext x
    conv_lhs => rw [hu']
    by_cases hx : x ∈ (chart (i : M)).target <;>
      simp [bundleCutoff, bundleComponent, localize, hx, Finset.smul_sum]
  rw [heq, Finset.sum_mul]
  apply WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (A.bundleCutoff_smooth e hdomain i hψ hsupp
      (A.bundleRestore_smooth e hdomain j (A.bundleLocalize_smooth e hdomain j hu))).contDiffOn
  · intro j _
    exact hd j (A.bundleLocalize e j u) s C hs hs1 hC
      (A.bundleLocalize_smooth e hdomain j hu) (hbu j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing on the actual covariant two-tensor bundle of the surface. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_rd68e99_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_rd68e99_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul
variable (A : SmoothingAtlas M)

def tensorSmooth (r : ℕ) (s : ℝ) (u : ∀ p : M, CovariantTwoTensor p) :
    ∀ p : M, CovariantTwoTensor p := A.bundleSmooth (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv r s u

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.sectionTensorNormed
local instance sectionTensorSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorEncode_add (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (u + v) = A.tensorEncode u + A.tensorEncode v := by
  funext x i
  exact congrFun (A.bundleLocalize_add A.tensorTriv i u v) x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x))) :
    ContDiff ℝ ∞ (A.tensorChartRead i u) :=
  fiberToThree.contDiff.comp (A.bundleCutoff_smooth A.tensorTriv A.tensorTriv_domain i
    (A.outer_smooth i) (A.outer_support i) hu)

lemma tensorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x : M, CovariantTwoTensor x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) → A.TensorWeightedBound s m C u →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D * C) (A.tensorChartRead i u) := by
  obtain ⟨D,hD,hd⟩ := A.bundleCutoff_bound A.tensorTriv A.tensorTriv_domain i
    (A.outer_smooth i) (A.outer_support i) m
  refine ⟨‖fiberToThree‖ * D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro u s C hs hs1 hC hu hbu
  have hh := (hd u s C hs hs1 hC hu hbu).linear uniqueDiffOn_univ hs.le
    (A.bundleCutoff_smooth A.tensorTriv A.tensorTriv_domain i
      (A.outer_smooth i) (A.outer_support i) hu).contDiffOn fiberToThree
  simpa only [tensorChartRead, mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x : M, CovariantTwoTensor x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) → A.TensorWeightedBound s m C u →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D * C) (A.tensorPlaneRead i u) := by
  obtain ⟨D,hD,hd⟩ := A.tensorChartRead_bound i m
  refine ⟨D,hD,?_⟩
  intro u s C hs hs1 hC hu hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm (A.tensorChartRead_smooth i hu)
    (hd u s C hs hs1 hC hu hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GeometricPerturbedParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite improvement of the actual geometric parametrix in the presence
of a supported differential perturbation. The perturbation estimate is
stated with explicit derivative loss so that polynomial operators can be
inserted without a Banach-space inverse assumption. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

def perturbedMode (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q : ℕ) : SupportedField (F := Ambient n) K :=
  FiniteParametrix.improve ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f
    (forcedModeLM τ hG h K hKU 0 f) q

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => primitiveOn F S hS hF hm z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedFreeMode
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite correction of an actual supported free normal seed in the
presence of the polynomial differential perturbation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

def perturbedFreeMode (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) : SupportedField (F := Ambient n) K :=
  FiniteParametrix.improve ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) 0 (initialMode τ h K hKU V 0) q

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedFreeLinearity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free seed and its finite perturbed correction are actual linear maps. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial
variable {n : ℕ} {G : Field n} {U : Set Base}

def initialFreeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) :
    SupportedField (F := Ambient n) K →ₗ[ℂ] SupportedField (F := Ambient n) K where
  toFun V := initialMode τ h K hKU V 0
  map_add' V W := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_sub τ hG h (V.contDiff.add W.contDiff).contDiffOn W.contDiff.contDiffOn
        (f := fun _ => 0) (g := fun _ => 0) contDiffOn_const contDiffOn_const 0 hp
      change initialAmplitude τ G (fun x => V x + W x) (fun _ => 0) p =
        initialAmplitude τ G V (fun _ => 0) p + initialAmplitude τ G W (fun _ => 0) p
      simp only [modeApprox, add_sub_cancel_right, sub_self] at hh
      exact sub_eq_iff_eq_add.mp hh.symm
    · have hk : p ∉ (K : Set Base) := fun hk => hp (hKU hk)
      change initialMode τ h K hKU (V + W) 0 p =
        initialMode τ h K hKU V 0 p + initialMode τ h K hKU W 0 p
      rw [(initialMode τ h K hKU (V + W) 0).zero_on_compl hk,
        (initialMode τ h K hKU V 0).zero_on_compl hk,
        (initialMode τ h K hKU W 0).zero_on_compl hk]
      simp only [Pi.zero_apply, zero_add]
  map_smul' c V := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_smul τ c hG h V.contDiff.contDiffOn
        (f := fun _ => 0) contDiffOn_const 0 hp
      change initialAmplitude τ G (fun x => c • V x) (fun _ => 0) p =
        c • initialAmplitude τ G V (fun _ => 0) p
      simpa only [modeApprox, smul_zero] using hh
    · have hk : p ∉ (K : Set Base) := fun hk => hp (hKU hk)
      change initialMode τ h K hKU (c • V) 0 p = c • initialMode τ h K hKU V 0 p
      rw [(initialMode τ h K hKU (c • V) 0).zero_on_compl hk,
        (initialMode τ h K hKU V 0).zero_on_compl hk]
      simp only [Pi.zero_apply, smul_zero]

def perturbedFreeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K :=
  (FiniteParametrix.homogeneousLM ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) q).comp
    ((initialFreeLM τ hG h K hKU).restrictScalars ℝ)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPerturbedMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the actual corrected metric mean by the seed amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

def normalizedPerturbedMean (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) : ℝ :=
  let V := supportedFreeSeed δ τ hF h K hKU b
  let T := perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
  δ⁻¹ ^ 2 * seedMeanError τ T V V v w p

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CorrectedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

def correctedNormalSeed (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) : SupportedField (F := Ambient 4) K :=
  perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
    (supportedFreeSeed δ τ hF h K hKU b)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free geometric amplitude in the original coordinates. The same
actual polynomial operator is conjugated into the phase chart, and the
resulting amplitude is transported back with controlled derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def freeSeed (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := SmallModes.Ambient 4) c.chartCompact :=
  correctedNormalSeed δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b

def originalFreeSeed (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Fin 4 → ℂ) K :=
  (supportedCoordinateEquiv planeCoordinateIsometry K).symm
    ((chartEquiv c.e c.smoothForward c.smoothInverse (modeSupport K) c.supportChart).symm
      (c.freeSeed δ q b))

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedZeroMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero phase of a transported free amplitude. The metric
part transforms as a covariant tensor through the phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
open SmallModes (gradientAmplitude)
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def metricMeanInChart (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SmallModes.Base → Tensor := fun y k =>
  normalizedPerturbedMean δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b
    (firstDirection k) (secondDirection k) y

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMetricMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global supported metric mean fields for the actual charted free seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes JetPolynomial
lemma normalizedPerturbedMean_smooth_general {F : RField 4} {U : Set SmallModes.Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts SmallModes.Base)
    (hKU : (K : Set SmallModes.Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (δ τ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) K) (v w : SmallModes.Base) :
    ContDiff ℝ ∞ (normalizedPerturbedMean δ τ hF h K hKU R q b v w) :=
  (seedMeanError_smooth τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q)
    (supportedFreeSeed δ τ hF h K hKU b) (supportedFreeSeed δ τ hF h K hKU b) v w).const_smul (δ⁻¹ ^ 2)
end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def metricMeanFieldInChart (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) c.chartCompact :=
  ⟨c.metricMeanInChart δ q b,
    contDiff_pi.mpr (fun k => normalizedPerturbedMean_smooth_general c.smoothMap c.realDomain
      c.chartCompact (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator δ τ q b
      (firstDirection k) (secondDirection k)),
    fun y hy => by
      ext k
      change δ⁻¹ ^ 2 * SmallModes.seedMeanError τ _ _ _ (firstDirection k) (secondDirection k) y = 0
      rw [SmallModes.seedMeanError_zero_outside τ c.chartCompact _ _ _ _ _ _ hy, mul_zero]⟩

def metricMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.metricMeanFieldInChart δ q b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedCombinedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The combined mean of the actual transported free amplitude, with the
polynomial evaluated in the original coordinates and the metric transformed
as a two-tensor. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def polynomialMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) K :=
  ⟨(fun x k => normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 x),
    contDiff_pi.mpr (fun k => normalizedPolynomialMean_smooth c.openU c.openO (c.smoothP k)
      hG c.smoothPhase c.mapsG K c.supportU (c.originalFreeSeed δ q b) δ ε τ 0),
    fun x hx => by
      ext k
      exact image_eq_zero_of_notMem_tsupport (fun hz => hx
        ((c.originalFreeSeed δ q b).tsupport_subset
          (normalizedPolynomialMean_tsupport (P k) δ ε G c.smoothPhase
            (c.originalFreeSeed δ q b).contDiff τ 0 hz)))⟩

def combinedMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  c.metricMeanField δ q b + pushSupported planeCoordinateIsometry K (c.polynomialMeanField δ q b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and jet bounds for the actual mean map of one phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

def mean (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  c.combinedMeanField δ q (d.amplitude hρ A)

def freeAmplitude (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    SupportedField (F := Fin 4 → ℂ) K := c.originalFreeSeed δ q (d.amplitude hρ A)

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual charted free amplitudes and their zero-phase tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

def chartedFamilyMean (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => ∑ i, (d i).mean hρ δ q A x

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeDisplacement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real displacement of the actual charted free amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

def freeDisplacement (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) : RField 4 :=
  QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b))

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual free displacement solves the full metric/polynomial
linearization to arbitrary finite order, in the original coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

def freeResidual (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := ComplexTensor) c.chartCompact :=
  ((SmallModes.conjugatedDLM τ (contDiff_complexify c.smoothMap) c.chartCompact).restrictScalars ℝ +
    c.operator) (c.freeSeed δ q b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedUniformFree
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform size and full-linearization residuals for the actual free
oscillation used by the charted mean construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def displacement (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : RField 4 :=
  c.freeDisplacement δ q (d.amplitude hρ A)

end ChartedMeanData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite free oscillation and its original-coordinate linear
residual. The constants precede the immersion and scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def chartedFreeSum (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : RField 4 :=
  QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude ((d i).freeAmplitude hρ δ q A))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamilyData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite charted phase family with its actual solvers and amplitudes,
packaged for assembling different coordinate patches on one surface. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def mean (d : ChartedMeanFamilyData P ε τ s r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) : (SmallModes.Base → Tensor) → SmallModes.Base → Tensor :=
  chartedFamilyMean d.data hρ δ q

/-- The actual zero-phase tensor of the finite free family in original coordinates. -/
def quadraticMean (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  combinedQuadraticMean P ε d.G d.phase
    (fun j => (d.data j).freeAmplitude hρ δ q f) τ 0

end ChartedMeanFamilyData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasFreeOscillation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global free oscillation and its weighted displacement bound. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeFiberSpace
local instance atlasFreeDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasFreeFiberNormed
local instance atlasFreeSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasFreeSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def atlasFreeOscillation
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) : M → RealModes.RVec 4 :=
  A.vectorPlaneRestore (fun i => chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

/-- The global complex amplitude retains the original compact support. -/
def freeGlobalAmplitude
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : Fin 3) : M → Fin 4 → ℂ :=
  restore (i : M) (A.outer i) ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_rd68e99_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable
def finiteGlobalAmplitude
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : ι i) : M → Fin 4 → ℂ :=
  restore (i : M) (A.outer i) ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))

def finiteAtlasFreeOscillation
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    M → RealModes.RVec 4 :=
  ∑ a : Σ i, ι i, surfaceMode τ (A.finiteGlobalPhase (φ := φ) a.1 a.2)
    (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FiniteAtlasIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free/forced metric step for an arbitrary finite family of local phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualSmul
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementSectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberNormed
local instance finiteIncrementSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteIncrementIndexDecidable
def finiteAtlasFreeMean
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x :=
  δ^2 • A.tensorPlaneRestore (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
    chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u))

noncomputable def finiteAtlasNonzero
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x := by
  classical
  exact A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
    (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
    (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x)

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanIteration
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationModelNormed
local instance iterationModelSpace_rd68e99_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance iterationDualSmul_rd68e99_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance iterationSectionTensorNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorEncodeLM : (∀ x : M, CovariantTwoTensor x) →ₗ[ℝ] (Base → A.centers → TensorFiber) where
  toFun := A.tensorEncode
  map_add' := A.tensorEncode_add
  map_smul' := A.tensorEncode_smul

def tensorProjectLM : (Base → A.centers → TensorFiber) →ₗ[ℝ] (Base → A.centers → TensorFiber) :=
  A.tensorEncodeLM.comp A.tensorDecodeLM

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorDecodedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform chart-reading estimates for the redundant coordinates used by
finite mean substitution, including the radius of every local trial ball. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedFiberSpace
local instance decodedDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedFiberNormed
local instance decodedSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance decodedSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem tensorPlaneRead_decode_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D*C) (A.tensorPlaneRead i (A.tensorDecode f)) := by
  classical
  obtain ⟨E,hE,he⟩ := A.tensorDecode_bound m
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i m
  let B : ℝ := (∑ i : A.centers, D i) * E
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro i f s C hs hs1 hC hf hb
  have hh := hd i (A.tensorDecode f) s (E*C) hs hs1 (mul_nonneg hE hC)
    (A.tensorDecode_smooth hf) (he f s C hs hs1 hC hf hb)
  apply hh.mono_const
  have hi : D i ≤ ∑ j : A.centers, D j :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
  calc
    D i * (E*C) = (D i * E)*C := by ring
    _ ≤ B*C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hE) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hC

theorem tensorPlaneRead_decode_ball : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (reference : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
    ∀ (f : Base → A.centers → TensorFiber) (r : ℝ), 0 ≤ r → ContDiff ℝ ∞ f →
      InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
      InTrialBall univ (A.tensorPlaneRead i reference) (D*r) (A.tensorPlaneRead i (A.tensorDecode f)) := by
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRead_decode_bound 0
  refine ⟨D+1,by linarith,?_⟩
  intro reference href f r hr hf hb i x _
  have hdiff : ContDiff ℝ ∞ (f-A.tensorEncode reference) := hf.sub (A.tensorEncode_smooth href)
  have hbound : _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ 1 0 r (f-A.tensorEncode reference) := by
    intro j hj y hy
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero, Pi.sub_apply] using (hb y hy).le
  have hh := (hd i (f-A.tensorEncode reference) 1 r zero_lt_one le_rfl hr hdiff hbound).norm_le
    (mem_univ x)
  rw [A.tensorPlaneRead_decode_sub, A.tensorDecode_encode] at hh
  have hrpos : 0 < r := (norm_nonneg (f 0 - A.tensorEncode reference 0)).trans_lt (hb 0 (mem_univ 0))
  exact hh.trans_lt (by nlinarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The atlas-only enlargement needed when a global encoded tensor ball is
read in any one chart. It is independent of reference tensors and all orders. -/
def tensorReadBallConstant : ℝ := Classical.choose A.tensorPlaneRead_decode_ball

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridRestoredGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normal margins for the restored phases selected on a
variable grid in one fixed atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry PhaseGrid JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def gridPhaseLabel {s : A.centers → Finset Index} (a : A.GridPhaseIndex s) :
    AtlasCellPhase (ι := A.centers) := (a.1,a.2.1.val,a.2.2)

def gridPhaseSupport (h : ℝ) {s : A.centers → Finset Index} (a : A.GridPhaseIndex s) : Set M :=
  tsupport (refinedCutoff (a.1 : M) (A.weight a.1) (s a.1) h a.2.1.val)

def gridRestoredPhase {s : A.centers → Finset Index}
    (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
    (w : AtlasCellPhase (ι := A.centers) → ℝ) (a : A.GridPhaseIndex s) : M → ℝ :=
  restore (a.1 : M) (A.outer a.1)
    (phaseLinear (w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a)) ∘ planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def primitive (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) : Family O E :=
  ofLocal (primitiveOn F.val O O.isOpen F.smooth hm) (primitiveOn_smooth _ _ _ _ _)

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilyAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra and support preservation for periodic families on an open domain. -/
noncomputable section

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {O : TopologicalSpace.Opens A} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma centered_mean_zero (F : Family O E) (p : A) :
    average ((F - F.vectorMean).val p) = 0 := by
  change average (fun t => F.val p t - F.vectorMean.val p t) = 0
  simp only [vectorMean_apply]
  rw [average_sub (F.val p).continuous continuous_const, average_const, sub_self]

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

namespace VectorExpression

def Represents {S : TopologicalSpace.Opens Base} (G : Base → Space)
    (R : VectorExpression) (U : Family S R4) : Prop :=
  ∀ i p, p ∈ S → ∀ t : ℝ, (R i).eval G (p, t) = U.val p (t : CovarianceCorrector.Period) i

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

def fastValue (U : Family O E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p : A) : E :=
  U.val p ((ℓ p / z : ℝ) : Period)

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridGlobalQuadraticCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual correction for the variable grid with a fixed polynomial budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGlobalQuadraticDualAdd
local instance gridGlobalQuadraticFiberNormed_rd68e99_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGlobalQuadraticFiberSpace_rd68e99_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridGlobalQuadraticDualSmul_rd68e99_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance gridGlobalQuadraticSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGlobalQuadraticSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridFreeCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridFreeCorrectionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeCorrectionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridFreeCorrectionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeCorrectionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GridIncrementProfile
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridIncrementProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridIncrementProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridIncrementProfileDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridIncrementProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridAdjustedIncrement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridAdjustedIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridAdjustedIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridAdjustedIncrementDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridAdjustedIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridGeometricIncrement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridGeometricIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGeometricIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridGeometricIncrementDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridGeometricIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AnchoredAtlasIncrement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial increments selected uniformly near a fast atlas map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry PhaseGrid
local instance anchoredIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredIncrementDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

def Represents {S : TopologicalSpace.Opens Base} (G : Base → Space)
    (e : Expression) (f : Family S ℝ) : Prop :=
  ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = f.val p (t : Period)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFiniteAnsatz
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

def finiteAnsatz (F : A → E) (U : ℕ → Family O E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p : A) : E :=
  F p + ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z p

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the pullback metric of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}



def xxQuadratic (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (xCoefficient dx U i).inner (xCoefficient dx U (r - i))

def xyQuadratic (dx dy : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (xCoefficient dx U i).inner (yCoefficient dy U (r - i))

def yyQuadratic (dy : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (yCoefficient dy U i).inner (yCoefficient dy U (r - i))

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xxCoefficient (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  (2 : ℝ) • g.longitudinal.inner (xCoefficient dx U r) + xxQuadratic dx U r

def xyCoefficient (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  g.longitudinal.inner (yCoefficient dy U r) +
  g.transverse.inner (xCoefficient dx U r) + xyQuadratic dx dy U r

def yyCoefficient (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  (2 : ℝ) • g.transverse.inner (yCoefficient dy U r) + yyQuadratic dy U r

end Geometry

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionInit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

def initial : Family O E :=
  (g.V - g.V.vectorMean).primitive (fun p _ => g.V.centered_mean_zero p)

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported finite ansatz in a nonlinear phase chart, restored to the
original surface and retaining its exact coordinate expression. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseAtlasLocalIncrement (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (χ : JetPolynomial.Base → ℝ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) : JetPolynomial.Base → Space :=
  supportedChartPullback e χ
    (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm))

def phaseAtlasAnsatz (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (χ : JetPolynomial.Base → ℝ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) : M → Space :=
  F + restore (i : M) (A.outer i) (A.phaseAtlasLocalIncrement i F e χ U ℓ L z)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialJetRecursion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite jet-order induction for the explicit periodic correction recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open Expression

/-- Low-jet longitudinal vector, including the velocity loop. -/
def longitudinal (X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4)) :
    VectorExpression := fun a => .coeff (fun z => (X₀ z.1 + V z.1 (z.2 : CovarianceCorrector.Period)) a)

def initial (V : LowJet → C(CovarianceCorrector.Period, R4)) : VectorExpression := fun a =>
  (Expression.coeff (fun z => V z.1 (z.2 : CovarianceCorrector.Period) a)).fluct.primitive

/-- All forcing expressions are formed before the full correction is applied. -/
def step (Y C X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4))
    (q : LowJet → ℝ) (dx dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : VectorExpression :=
  fun a => fullComponent Y C X₀ V q (EuclideanSpace.proj a) dy
    ((mixedForcing (longitudinal X₀ V) (transverse Y) dx dy U r).fluct.scale (-1))
    ((transverseForcing dy U r).fluct.scale (-1 / 2))
    ((longitudinalForcing (longitudinal X₀ V) dx U r).fluct.scale (-1))

def coefficients (Y C X₀ : LowJet → R4) (V : LowJet → C(CovarianceCorrector.Period, R4))
    (q : LowJet → ℝ) (dx dy : Fin 2) : ℕ → ℕ → VectorExpression
  | 0 => fun _ => initial V
  | n + 1 => Function.update (coefficients Y C X₀ V q dx dy n) (n + 1)
      (step Y C X₀ V q dx dy (coefficients Y C X₀ V q dx dy n) (n + 1))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-jet geometry and the initial primitive in the actual periodic family
are represented by the corresponding coordinate polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector

namespace MetricPolynomial

def velocity (V : LowJet → C(Period, R4)) : VectorExpression :=
  fun a => .coeff (fun z => V z.1 (z.2 : Period) a)

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BoundedSurfaceCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite periodic correction to the actual geometric second-jet
family, including global smooth extension and its uniform scale bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def coefficientExpressions (n : ℕ) : ℕ → VectorExpression :=
  MetricPolynomial.coefficients yData cData xData l.euclideanVelocity l.q 0 1 n

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric polynomial coefficients of the finite periodic derivative ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial vectorPolynomialValue
  )


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xxPolynomial (dx : A) (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.xTangent dx U L i).val p t)
    (fun i => (g.xTangent dx U L i).val p t)

def xyPolynomial (dx : A) (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.xTangent dx U L i).val p t)
    (fun i => (g.yTangent U i).val p t)

def yyPolynomial (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.yTangent U i).val p t)
    (fun i => (g.yTangent U i).val p t)

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coefficient families and exact remainder of the finite metric expansion. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial vectorPolynomialValue
  )


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

def metricCoefficientFamily (n r : ℕ) (a b : ℕ → Family O E) : Family O ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    if i + j = r then (a i).inner (b j) else 0

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xxRemainder (dx : A) (U : ℕ → Family O E) (L r : ℕ) : Family O ℝ :=
  metricCoefficientFamily L r (g.xTangent dx U L) (g.xTangent dx U L)

def xyRemainder (dx : A) (U : ℕ → Family O E) (L r : ℕ) : Family O ℝ :=
  metricCoefficientFamily L r (g.xTangent dx U L) (g.yTangent U)

def yyRemainder (U : ℕ → Family O E) (L r : ℕ) : Family O ℝ :=
  metricCoefficientFamily L r (g.yTangent U) (g.yTangent U)

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TangentMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite-tail estimate to the actual two tangent expansions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

def tangentFamily {S : TopologicalSpace.Opens Base} {dy : Base}
    (g : Geometry (E := R4) S dy) (U : ℕ → Family S R4) (dx : Base) (L : ℕ)
    (b : Bool) : ℕ → Family S R4 :=
  if b then g.xTangent dx U L else g.yTangent U

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuantitativeMetricExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pullback metric, after subtracting its finite mean expansion,
has the fast-scale remainder bound used by the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

namespace MetricPolynomial

def meanMetric {S : TopologicalSpace.Opens Base} {dy : Base}
    (g : Geometry (E := R4) S dy) (dx : Base) (U : ℕ → Family S R4)
    (n : ℕ) (b c : Bool) (z : ℝ) (p : Base) : ℝ :=
  if b && c then
    inner ℝ (g.X₀ p) (g.X₀ p) + g.q p +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient dx U r).val p) * z ^ r
  else if b || c then
    inner ℝ (g.X₀ p) (g.Y p) +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient dx U r).val p) * z ^ r
  else
    inner ℝ (g.Y p) (g.Y p) +
      ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceMetricExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite metric expansion of the actual surface map, with its leading
primitive tensor identified and its fast remainder uniformly bounded. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def meanCorrection {S : TopologicalSpace.Opens JetPolynomial.Base}
    (g : Geometry (E := Euclidean) S (coordinateVector 1))
    (U : ℕ → Family S Euclidean) (n : ℕ) (b c : Bool) (z : ℝ)
    (p : JetPolynomial.Base) : ℝ :=
  if b && c then
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient (coordinateVector 0) U r).val p) * z ^ r
  else if b || c then
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient (coordinateVector 0) U r).val p) * z ^ r
  else
    ∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SurfaceMeanPolynomial
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite mean correction is an actual higher-jet polynomial, so the
perturbed small-increment solver applies to the same metric expansion. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def meanTangentExpression (n : ℕ) (b : Bool) : ℕ → VectorExpression :=
  MetricPolynomial.tangentExpression (MetricPolynomial.longitudinal xData l.euclideanVelocity)
    (MetricPolynomial.transverse yData) (l.coefficientExpressions n) 0 1 (n+1) b

def meanPolynomial (n : ℕ) (b c : Bool) : Fin n → Expression := fun r =>
  (MetricPolynomial.finiteMetric (n+1) (r.val+1)
    (l.meanTangentExpression n (b || c)) (l.meanTangentExpression n (b && c))).mean

def meanCoefficientValue {S : TopologicalSpace.Opens JetPolynomial.Base}
    (g : Geometry (E := Euclidean) S (coordinateVector 1))
    (U : ℕ → Family S Euclidean) (b c : Bool) (r : ℕ) (p : JetPolynomial.Base) : ℝ :=
  if b && c then average ((g.xxCoefficient (coordinateVector 0) U r).val p)
  else if b || c then average ((g.xyCoefficient (coordinateVector 0) U r).val p)
  else average ((g.yyCoefficient U r).val p)

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfacePrimitiveError
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite primitive's actual metric error is the sum of its solved mean
error and the fast finite tail. The prescribed amplitude is fixed in position. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def meanOperator (n : ℕ) (b c : Bool) (z : ℝ) (G : JetPolynomial.Base → JetPolynomial.Space) (p : Base) : ℝ :=
  inner ℝ
    (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) b))
    (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (MetricPolynomial.metricDirection (coordinateVector 0) (coordinateVector 1) c)) +
  Perturbation.eval (l.meanPolynomial n b c) z G (p,0)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SurfaceMeanTensor
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primitive's three mean metric coefficients are exactly the tensor
operator used by the finite parametrix, in its product coordinates. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def meanTensorPolynomial (n : ℕ) : Fin 3 → Fin n → Expression :=
  ![l.meanPolynomial n true true,l.meanPolynomial n true false,l.meanPolynomial n false false]

def meanTensorOperator (n : ℕ) (z : ℝ) (G : JetPolynomial.Base → JetPolynomial.Space) :
    SmallModes.Base → PhaseMean.Tensor := fun p =>
  ![l.meanOperator n true true z G (planeCoordinateIsometry.symm p),
    l.meanOperator n true false z G (planeCoordinateIsometry.symm p),
    l.meanOperator n false false z G (planeCoordinateIsometry.symm p)]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasMetric
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberSpace
local instance nonlinearMetricDualSmul_rd68e99_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberNormed
local instance nonlinearMetricSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearMetricSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def phaseAtlasRemainder (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (B : JetPolynomial.Base → PhaseMean.Tensor) :
    JetPolynomial.Base → PhaseMean.Tensor := fun y =>
  RealModes.realMetricTensor
    (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z ∘ planeCoordinateIsometry.symm)
    (planeCoordinateIsometry y) -
  coordinateMetricMap P z (A.jetChartMap i F ∘ e.symm) (planeCoordinateIsometry y) - B y

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalAnsatzProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading jets of the supported local ansatz are the geometric profiles
of the initial periodic primitive. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

/-- Retain the actual coefficient values when a supported local family has
already been proved smooth after extension by zero. -/
def globalCoefficients (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period))) :
    ℕ → PeriodicExpansion.Family A E := fun i => ⟨(U i).val,hU i⟩

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CoefficientJetBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite first and second slow/angular coefficient jets needed by the
primitive's five leading derivative estimates share one fixed scale loss. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def coefficientFamilyDerivative {S : TopologicalSpace.Opens Base}
    (U : Family S R4) (k : Fin 3) : Family S R4 :=
  ![U.slow (coordinateVector 0),U.slow (coordinateVector 1),U.angle] k

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseCoefficientBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the first two transverse derivatives of represented
periodic coefficients. Their common loss is fixed before the slow map. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def transverseFamily {S : TopologicalSpace.Opens Base} (U : Family S R4) (second : Bool) : Family S R4 :=
  if second then (U.slow (coordinateVector 1)).slow (coordinateVector 1) else U.slow (coordinateVector 1)

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform C3 stability of the leading profiles on a compact spatial set,
including every phase on the period circle. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def geometricLeadingProfile {S : TopologicalSpace.Opens JetPolynomial.Base}
    (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) (p : JetPolynomial.Base) (t : Period) :
    EuclideanBoundaryProfile :=
  ![(l.geometry G hG hGO).longitudinal.val p t,(l.geometry G hG hGO).Y p,
    (l.geometry G hG hGO).C p,
    ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p t,
    (l.geometry G hG hGO).V.angle.val p t]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AnchoredSmoothedIncrement
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual anchored increment at the smoothed input, with polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
local instance anchoredSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredSmoothDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredSmoothDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredSmoothSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredActualStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized correction steps with an explicit fast-map neighborhood. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
local instance anchoredActualFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredFixedOrderStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial fixed-order thresholds for the actual anchored correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
local instance anchoredFixedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredInputStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full next-input recurrence with polynomial fast-family constants. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
local instance anchoredInputFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactFastFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily accurate primitive maps give an actual smooth exact metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
local instance exactFastFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentProfiledFastFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast approximants with prescribed accuracy in the leading five
primitive derivatives and the slow baseline, retained for the exact step. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PrimitiveRealization CovarianceCorrector
local instance independentProfiledFamilyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentProfiledFamilyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentProfiledFamilyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactProfiledPhase
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes
local instance independentExactProfiledPhasePrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentExactProfiledPhasePrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentExactProfiledPhasePrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactPhaseProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector
local instance independentActualPhasePrimitiveProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentActualPhasePrimitiveProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentActualPhasePrimitiveProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactOriginalProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector
local instance independentExactPhaseOriginalProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentExactPhaseOriginalProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentExactPhaseOriginalProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentPhaseBoundaryProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_exactPhaseBoundaryProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_exactPhaseBoundaryProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_exactPhaseBoundaryProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactCircular
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_exactCircularPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_exactCircularPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_exactCircularPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentCircularBoundary
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_exactCircularBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_exactCircularBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_exactCircularBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentConstructedCircular
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_constructedCircularBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_constructedCircularBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_constructedCircularBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentPreservingCircular
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_preservingCircularBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_preservingCircularBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_preservingCircularBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentPreservingNormal
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_preservingCircularNormalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_preservingCircularNormalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_preservingCircularNormalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentGeometricNormal
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_geometricCircularNormalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_geometricCircularNormalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_geometricCircularNormalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentGlobalNormal
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_globalCircularNormalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_globalCircularNormalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_globalCircularNormalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentCircularBoundaryStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_boundaryCircularPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_boundaryCircularPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_boundaryCircularPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchBoundaryStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed local primitive data feed the exact analytic theorem,
with the global rank-one metric written in the original surface variables. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
local instance patchStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance patchStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance patchStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularMargins
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive inverse margins in the actual reference chart frames. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance referenceMarginFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceMarginFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
open PhaseMean PhaseGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceCoefficientLower
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive coefficient lower bound fixed on the full reference atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance lowerFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance lowerFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceOperatorStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact chart margins imply invertibility of the actual global tensor
operator and positivity of every active primitive coefficient. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refOperatorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refOperatorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance refOperatorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceMetricStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual remainder metric inherits the fixed positive inverse margins
from C1 approximation of the reference immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance refMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refMetricDualSmul_rd68e99_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ReferenceCoordinateData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, identity and positivity of the fixed reference data in any active
chart. The constants precede every independent radius and phase choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance refDataDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceAmplitudeMargin
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed parameter derivative bound for all active reference charts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance amplitudeMarginFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance amplitudeMarginFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferencePerturbationStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine independent circular phase and cutoff choices preserve the
fixed reference inverse margins for all sufficiently close starting maps. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
local instance perturbationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance perturbationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceAmplitudeParameterBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independent circular data remain inside the fixed positive
amplitude neighborhood for every sufficiently close starting map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualParamFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualParamFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceCorrectedFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual positive smooth primitive decompositions of every nearby
remainder, using independently perturbed supported weights and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance referenceFamilyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceFamilyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary first-jet bounds for symmetric tensor components on the fixed
primitive chart supports, including their boundaries. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance tensorReadBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorReadBoundsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance tensorReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance tensorReadBoundsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

local instance tensorReadBoundsSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorReadBoundsSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorFrameRead (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (y : JetPolynomial.Base) : TensorFiber :=
  (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm y)
    (u ((chart (i : M)).symm y))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateGerms
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate model agrees with the actual corrected amplitude
on a neighborhood, including at zero cutoff values. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordinateGermFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateGermFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coordinateGermDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordinateGermDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordinateGermDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordinateGermDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative control of the actual amplitude from its finite active
chart data. The data bounds involve only first jets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordDerivFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordDerivFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coordDerivDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivFiberT2_rd68e99_1 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_rd68e99_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_rd68e99_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordDerivDualAdd_rd68e99_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordDerivDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
local instance coordDerivFiberT2_rd68e99_2 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_rd68e99_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_rd68e99_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualAdd_rd68e99_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)
local instance coordDerivSectionNormed_rd68e99_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordDerivSectionSpace_rd68e99_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance coordDerivDataNormed_rd68e99_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformActualAmplitudeC1
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-derivative bounds for the genuine corrected amplitudes.
The tolerances and bounds precede all later finite cycles and boundary choices. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualC1FiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualC1FiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance actualC1FiberAdd : AddCommGroup TensorFiber := actualC1FiberNormed.toAddCommGroup
local instance actualC1TensorDualNormed_rd68e99_1 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1TensorDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1FiberT2_rd68e99_1 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2_rd68e99_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2_rd68e99_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed_rd68e99_1 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataSpace (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


