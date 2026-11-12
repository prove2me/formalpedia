-- Prove2me | Definitions.Def_OAIQ258005
-- name    : OAIQ258005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:18:59.008193+00:00
-- url     : https://prove2.me/theorems/ac1e7f12-117b-47c3-aadb-6f594617659f
-- title:
--   Definitions bundle OAIQ258005 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 310 declarations of OpenAI's Lean: 227 definitions, 29 instances and 54 theorems. The definitions and types are `OAI.InvariantIsing.fieldAdjacentFamily`, `OAI.InvariantIsing.fieldAdjacentInner`, `OAI.InvariantIsing.fieldAdjacentTail`, `OAI.InvariantIsing.fieldAffineFamily`, `OAI.InvariantIsing.fieldBiasCurvature`, `OAI.InvariantIsing.fieldBiasMean`, `OAI.InvariantIsing.fieldCanonicalEndpointLaw`, `OAI.InvariantIsing.fieldCanonicalSpinLaw`, `OAI.InvariantIsing.fieldCanonicalVectorLaw`, `OAI.InvariantIsing.fieldConstantPrefix`, `OAI.InvariantIsing.fieldDepthPairIntegrand`, `OAI.InvariantIsing.fieldFinalChart`, `OAI.InvariantIsing.fieldHeightCoordinateValue`, `OAI.InvariantIsing.fieldInteriorChart`, `OAI.InvariantIsing.fieldLevelPath`, `OAI.InvariantIsing.fieldMagnetizationLevel`, `OAI.InvariantIsing.fieldMagnetizationPath`, `OAI.InvariantIsing.fieldRegularized`, `OAI.InvariantIsing.fieldScalarOverlaps`, `OAI.InvariantIsing.fieldScalarSquareAt`, `OAI.InvariantIsing.fieldSpinPairIntegrand`, `OAI.InvariantIsing.fieldTailEndpointKernel`, `OAI.InvariantIsing.fieldTerminalFamily`, `OAI.InvariantIsing.fieldVectorDepthPairMean`, `OAI.InvariantIsing.fieldVectorLogNormalizer`, `OAI.InvariantIsing.fieldVectorPairSpinKernel`, `OAI.InvariantIsing.fieldVectorSitePairKernel`, `OAI.InvariantIsing.fieldVectorSpinKernel`, `OAI.InvariantIsing.fieldVectorSpinPairMean`, `OAI.InvariantIsing.fieldVectorTailSpinKernel`, `OAI.InvariantIsing.finiteInteractionEnergy`, `OAI.InvariantIsing.finiteSpectralBlock`, `OAI.InvariantIsing.finiteTemperatureFunctional`, `OAI.InvariantIsing.haarHeatEntropy`, `OAI.InvariantIsing.haarPolynomialMean`, `OAI.InvariantIsing.haarPolynomialMoment`, `OAI.InvariantIsing.haarPolynomialMomentDerivative`, `OAI.InvariantIsing.jointSpectralMonomialCoefficients`, `OAI.InvariantIsing.lowerGridPath`, `OAI.InvariantIsing.magneticBias` and 187 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_FullPerturbationMinima`, `InvariantIsing_Arrays_NSpinTensorCascade`, `InvariantIsing_Arrays_NSpinTensorFlatLaw`, `InvariantIsing_Arrays_NSpinTensorFlatMean`, `InvariantIsing_Arrays_NSpinTensorFrozen`, `InvariantIsing_Arrays_NSpinTensorFrozenCGF`, `InvariantIsing_Arrays_NSpinTensorFrozenFluctuation`, `InvariantIsing_Arrays_NSpinTensorGaussianLaw`, `InvariantIsing_Arrays_NSpinTensorHaarFluctuation`, `InvariantIsing_Arrays_NSpinTensorLabeled`, `InvariantIsing_Arrays_NSpinTensorPairConditioning`, `InvariantIsing_Arrays_NSpinTensorRootVariance`, `InvariantIsing_Arrays_PerturbationFeatures`, `InvariantIsing_Arrays_PerturbationMeasurability`, `InvariantIsing_Arrays_TensorArrayLaw`, `InvariantIsing_Arrays_TensorCoefficientDerivative`, `InvariantIsing_Arrays_TensorContactContinuity`, `InvariantIsing_Arrays_TensorContactField`, `InvariantIsing_Arrays_TensorContactMinimum`, `InvariantIsing_Arrays_TensorCoordinateMinimum`, `InvariantIsing_Arrays_TensorDiagonalCGF`, `InvariantIsing_Arrays_TensorDiagonalPrincipalObservables`, `InvariantIsing_Arrays_TensorDiagonalWardCorrectionBound`, `InvariantIsing_Arrays_TensorDiagonalWardMeasurability`, `InvariantIsing_Arrays_TensorFieldDerivative`, `InvariantIsing_Arrays_TensorFieldDerivativeLaw`, `InvariantIsing_Arrays_TensorFiniteGG`, `InvariantIsing_Arrays_TensorLimitingGG`, `InvariantIsing_Arrays_TensorObservableAverageLaw`, `InvariantIsing_Arrays_TensorPerturbationObjective`, `InvariantIsing_Arrays_TensorPrincipalBlock`, `InvariantIsing_Arrays_TensorPrincipalWard`, `InvariantIsing_Arrays_TensorReplicaAverageLaw`, `InvariantIsing_Arrays_TensorTruncatedDiagonalWard`, `InvariantIsing_Arrays_TensorTruncatedWard`, `InvariantIsing_Arrays_TensorWardCorrectionBound`, `InvariantIsing_Arrays_TensorWardError`, `InvariantIsing_Arrays_TensorWardMeasurability`, `InvariantIsing_Cavity_ConsecutiveBlockTransport`, `InvariantIsing_Cavity_OffsetBlockPrior`, `InvariantIsing_Cavity_OffsetBlockSpin`, `InvariantIsing_Cavity_OffsetEnvelopeLower`, `InvariantIsing_Cavity_OffsetMinimumSequence`, `InvariantIsing_Cavity_OffsetPhysicalIncrement`, `InvariantIsing_Core_TrialGridApproximation`, `InvariantIsing_Fields_CanonicalOrthogonalLaw`, `InvariantIsing_Fields_FieldAdjacentOrder`, `InvariantIsing_Fields_FieldAffineRecursion`, `InvariantIsing_Fields_FieldCanonicalEndpoint`, `InvariantIsing_Fields_FieldCanonicalVectorMoments`, `InvariantIsing_Fields_FieldConstantPrefix`, `InvariantIsing_Fields_FieldDepthPair`, `InvariantIsing_Fields_FieldEndpointSampling`, `InvariantIsing_Fields_FieldHeightChart`, `InvariantIsing_Fields_FieldHeightRegularization`, `InvariantIsing_Fields_FieldHeightUpdate`, `InvariantIsing_Fields_FieldLevelPath`, `InvariantIsing_Fields_FieldLogNormalizer`, `InvariantIsing_Fields_FieldMagnetization`, `InvariantIsing_Fields_FieldPairProductLaw`, `InvariantIsing_Fields_FieldScalarChain`, `InvariantIsing_Fields_FieldScalarOverlap`, `InvariantIsing_Fields_FieldSpinEvaluation`, `InvariantIsing_Fields_FieldSpinMeasurability`, `InvariantIsing_Fields_FieldTerminalOrder`, `InvariantIsing_Fields_FieldVectorPairSampling`, `InvariantIsing_Fields_FieldVectorSampling`, `InvariantIsing_Fields_FieldZeroIncrement`, `InvariantIsing_Fields_PriorArrayLaw`, `InvariantIsing_Fields_PriorContactContinuity`, `InvariantIsing_Fields_PriorDiagonalStatistics`, `InvariantIsing_Fields_PriorFieldDerivative`, `InvariantIsing_Fields_PriorFiniteGG`, `InvariantIsing_Fields_PriorFrozenCGF`, `InvariantIsing_Fields_PriorFrozenReference`, `InvariantIsing_Fields_PriorLabeledDepthMean`, `InvariantIsing_Fields_PriorLabeledModelSpin`, `InvariantIsing_Fields_PriorLimitingGG`, `InvariantIsing_Fields_PriorReplicaAverage`, `InvariantIsing_Fields_PriorTensorNamespace`, `InvariantIsing_Fields_PriorTensorReference`, `InvariantIsing_Fields_SpinPriorArrayLaw`, `InvariantIsing_Fields_SpinPriorCascadePressure`, `InvariantIsing_Fields_SpinPriorContact`, `InvariantIsing_Fields_SpinPriorContactField`, `InvariantIsing_Fields_SpinPriorContactMinimum`, `InvariantIsing_Fields_SpinPriorDiagonalStatistics`, `InvariantIsing_Fields_SpinPriorFieldDerivative`, `InvariantIsing_Fields_SpinPriorFieldInsertionLaw`, `InvariantIsing_Fields_SpinPriorFiniteGG`, `InvariantIsing_Fields_SpinPriorFlatLaw`, `InvariantIsing_Fields_SpinPriorFlatVariance`, `InvariantIsing_Fields_SpinPriorFrozenCGF`, `InvariantIsing_Fields_SpinPriorFrozenReference`, `InvariantIsing_Fields_SpinPriorLabeledMoments`, `InvariantIsing_Fields_SpinPriorLeafTail`, `InvariantIsing_Fields_SpinPriorLimitingGG`, `InvariantIsing_Fields_SpinPriorReplicaAverage`, `InvariantIsing_Fields_SpinPriorTemperatureDerivative`, `InvariantIsing_Haar_HaarHeatEntropy`, `InvariantIsing_Haar_HaarHeatMean`, `InvariantIsing_Haar_HaarPolynomialMoment`, `InvariantIsing_Haar_HaarPolynomialValue`, `InvariantIsing_Haar_ReflectionPairCurve`, `InvariantIsing_Haar_ReflectionPairPath`, `InvariantIsing_Haar_ReflectionSegment`, `InvariantIsing_Haar_ReflectionSegmentDerivative`, `InvariantIsing_Magnetic_MagneticBlockPath`, `InvariantIsing_Magnetic_MagneticCanonicalSpin`, `InvariantIsing_Magnetic_MagneticFieldBias`, `InvariantIsing_Magnetic_MagneticFieldCurvature`, `InvariantIsing_Magnetic_MagneticFieldFamily`, `InvariantIsing_Magnetic_MagneticFieldInverse`, `InvariantIsing_Magnetic_MagneticFieldLevels`, `InvariantIsing_Magnetic_MagneticGroupPath`, `InvariantIsing_Magnetic_MagneticHeatSecond`, `InvariantIsing_Magnetic_MagneticHeatSpatial`, `InvariantIsing_Magnetic_MagneticHeatWeighted`, `InvariantIsing_Magnetic_MagneticLevelDerivative`, `InvariantIsing_Magnetic_MagneticPairComparison`, `InvariantIsing_Magnetic_MagneticScalarFourJet`, `InvariantIsing_Magnetic_MagneticScaledContinuation`, `InvariantIsing_Magnetic_MagneticScaledSlab`, `InvariantIsing_Magnetic_MagneticSquareJet`, `InvariantIsing_Magnetic_RestrictedBlockOverlap`, `InvariantIsing_Magnetic_RestrictedCanonicalGroupCutoff`, `InvariantIsing_Magnetic_RestrictedCanonicalHaarLog`, `InvariantIsing_Magnetic_RestrictedCoordinateOverlap`, `InvariantIsing_Magnetic_RestrictedDepthPair`, `InvariantIsing_Magnetic_RestrictedDisorderTest`, `InvariantIsing_Magnetic_RestrictedEndpointKernel`, `InvariantIsing_Magnetic_RestrictedEndpointTest`, `InvariantIsing_Magnetic_RestrictedFullTest`, `InvariantIsing_Magnetic_RestrictedGeometricMean`, `InvariantIsing_Magnetic_RestrictedHaarLogObservable`, `InvariantIsing_Magnetic_RestrictedLinearCoordinate`, `InvariantIsing_Magnetic_RestrictedLinearDepthEvaluation`, `InvariantIsing_Magnetic_RestrictedPairMoments`, `InvariantIsing_Magnetic_RestrictedPairOrder`, `InvariantIsing_Magnetic_RestrictedPairRecursion`, `InvariantIsing_Magnetic_RestrictedPairRootEntropy`, `InvariantIsing_Magnetic_RestrictedPairSpinKernel`, `InvariantIsing_Magnetic_RestrictedPhysicalCutoff`, `InvariantIsing_Magnetic_RestrictedProjectorCavity`, `InvariantIsing_Magnetic_RestrictedProjectorLog`, `InvariantIsing_Magnetic_RestrictedProjectorPartition`, `InvariantIsing_Magnetic_RestrictedRandomHaarLog`, `InvariantIsing_Magnetic_RestrictedRotationArray`, `InvariantIsing_Magnetic_RestrictedRotationProbability`, `InvariantIsing_Magnetic_RestrictedSpinEvaluation`, `InvariantIsing_Magnetic_RestrictedSpinKernel`, `InvariantIsing_Magnetic_RestrictedTailSpinKernel`, `InvariantIsing_Magnetic_RestrictedZeroTreeArrayLaw`, `InvariantIsing_Spectral_SpectralEnergy`, `InvariantIsing_Spectral_SpectralGG`, `InvariantIsing_Spectral_SpectralQuantileSynchronization`, `InvariantIsing_Spectral_SpectralReplicaLaw`, `InvariantIsing_Spectral_SpectralReplicaProduct`, `InvariantIsing_Spectral_SpectralTemperatureFunctional`.
--
--   **Imports.** It imports the published bundle `Def_InvariantIsing`; the bundles `OAIQ258003` and `OAIQ258004` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.InvariantIsing.cavity_base_perturbed_array_law`, `OAI.InvariantIsing.cavity_canonical_capped_log_limit`, `OAI.InvariantIsing.cavity_canonical_group_block_tendsto`, `OAI.InvariantIsing.cavity_compression_capped_log_limit`, `OAI.InvariantIsing.cavity_finite_spin_test`, `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit`, `OAI.InvariantIsing.cavity_full_spin_test_evaluation`, `OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison`, `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match`, `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match`, `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match`, `OAI.InvariantIsing.cavity_linear_rooted_spin_evaluation`, `OAI.InvariantIsing.cavity_orientation_tensor_probability_law`, `OAI.InvariantIsing.cavity_original_overlap_limit`, `OAI.InvariantIsing.cavity_original_scalar_self_consistency`, `OAI.InvariantIsing.cavity_original_spin_limit`, `OAI.InvariantIsing.cavity_physical_spin_cutoff`, `OAI.InvariantIsing.cavity_physical_trial_lower`, `OAI.InvariantIsing.cavity_tensor_pressure_mean`, `OAI.InvariantIsing.cavity_window_minimum_variational_lower`, `OAI.InvariantIsing.closedMagneticSquareContinuationSecond_nonneg`, `OAI.InvariantIsing.constrainedFieldValue_magneticBias`, `OAI.InvariantIsing.fieldBiasMean_magneticBias`, `OAI.InvariantIsing.field_entropy_sequence_of_support`, `OAI.InvariantIsing.field_support_equal_cutList`, `OAI.InvariantIsing.field_vector_depth_pair_evaluation`, `OAI.InvariantIsing.field_vector_log_mean`, `OAI.InvariantIsing.field_vector_log_root_integral`, `OAI.InvariantIsing.field_vector_spin_pair_evaluation`, `OAI.InvariantIsing.fullPerturbationPressure_cost`, `OAI.InvariantIsing.fullPerturbationPressure_variance`, `OAI.InvariantIsing.haarPolynomialMoment_log_bound`, `OAI.InvariantIsing.haar_tensorEnrichedPressure_variance`, `OAI.InvariantIsing.integral_priorCavityLabeledDepthMean`, `OAI.InvariantIsing.magneticBias_uniform_bound`, `OAI.InvariantIsing.magneticBlockPath_l1_tendsto`, `OAI.InvariantIsing.magneticCanonical_projection_distance`, `OAI.InvariantIsing.magneticFieldLevel_radial`, `OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order`, `OAI.InvariantIsing.magneticScaledClosedCurvature_mono`, `OAI.InvariantIsing.magnetic_entropy_sequence_of_support`, `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower`, `OAI.InvariantIsing.offset_envelope_pressure_lower`, `OAI.InvariantIsing.offset_product_tree_spin_error`, `OAI.InvariantIsing.offset_product_weak_self_consistency`, `OAI.InvariantIsing.offset_window_minimum_trial_witness`, `OAI.InvariantIsing.priorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound`, `OAI.InvariantIsing.priorNamespacedPerturbation_variance`, `OAI.InvariantIsing.priorPerturbation_arrayResidual_bound`, `OAI.InvariantIsing.priorPerturbation_minimizers_constantDiagonal`, `OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.restricted_cavity_finite_model_spin_test`, `OAI.InvariantIsing.restricted_cavity_full_spin_test_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_coordinate_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_noise_depth_test`, `OAI.InvariantIsing.restricted_cavity_linear_rooted_spin_evaluation`, `OAI.InvariantIsing.restricted_compression_capped_log_limit`, `OAI.InvariantIsing.restricted_compression_log_limit`, `OAI.InvariantIsing.restricted_field_depth_pair_evaluation`, `OAI.InvariantIsing.restricted_field_spin_pair_evaluation`, `OAI.InvariantIsing.restricted_haar_cutoff_limit`, `OAI.InvariantIsing.restricted_original_full_haar_comparison`, `OAI.InvariantIsing.restricted_original_haar_limit`, `OAI.InvariantIsing.restricted_original_spin_limit`, `OAI.InvariantIsing.restricted_original_split_overlap_limit`, `OAI.InvariantIsing.restricted_physical_cutoff_comparison`, `OAI.InvariantIsing.restricted_physical_log_average`, `OAI.InvariantIsing.restricted_physical_projector_increment`, `OAI.InvariantIsing.restricted_physical_trial_lower`, `OAI.InvariantIsing.restricted_projector_coefficient_error`, `OAI.InvariantIsing.restricted_tree_pressure_capped_increment`, `OAI.InvariantIsing.restricted_zero_tree_perturbed_array_law`, `OAI.InvariantIsing.spectralCanonicalWard_pair`, `OAI.InvariantIsing.spectralCanonical_identification`, `OAI.InvariantIsing.spectralCanonical_symbols`, `OAI.InvariantIsing.spectralPartition_offWardPath`, `OAI.InvariantIsing.spinPriorContactObjective_exists_minimum`, `OAI.InvariantIsing.spinPriorContact_limit_tail_order`, `OAI.InvariantIsing.spinPriorContact_minimum_field_cone`, `OAI.InvariantIsing.spinPriorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.spinPriorMeanPressure_field`, `OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound`, `OAI.InvariantIsing.spinPriorPerturbation_minimizers_constantDiagonal`, `OAI.InvariantIsing.spinPriorPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.spinPriorProfileLog_variance`, `OAI.InvariantIsing.spinPriorRestrictedContactPressure_field_le`, `OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit`, `OAI.InvariantIsing.spinPriorRestrictedContact_zero_cost`, `OAI.InvariantIsing.tensorContactObjective_exists_minimum`, `OAI.InvariantIsing.tensorContact_limit_tail_order`, `OAI.InvariantIsing.tensorContact_minimum_field_cone`, `OAI.InvariantIsing.tensorContact_no_positive_minimizing_sequence`, `OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum`, `OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound`, `OAI.InvariantIsing.tensorFrozenCGF_mean`, `OAI.InvariantIsing.tensorGaussianCoordinatePressure_cost`, `OAI.InvariantIsing.tensorGrowingArrayLaw_off_ward_limit`, `OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit`, `OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus`, `OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost`, `OAI.InvariantIsing.tensorPerturbationPressureMean_modulus`, `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit`, `OAI.InvariantIsing.tensorPerturbedArrayLaw_interactionEnergy_limit`, `OAI.InvariantIsing.tensor_envelope_pressure_lower` and `OAI.InvariantIsing.tensor_zero_field_minimizing_sequence`; the proofs of `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto`, `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto`, `OAI.InvariantIsing.cavity_base_perturbed_array_law`, `OAI.InvariantIsing.cavity_canonical_capped_log_limit`, `OAI.InvariantIsing.cavity_canonical_group_block_tendsto`, `OAI.InvariantIsing.cavity_compression_capped_log_limit`, `OAI.InvariantIsing.cavity_finite_log_evaluation`, `OAI.InvariantIsing.cavity_finite_spin_test`, `OAI.InvariantIsing.cavity_fixed_minimum_geometric_limit`, `OAI.InvariantIsing.cavity_full_spin_test_evaluation`, `OAI.InvariantIsing.cavity_full_tree_cutoff_sequence`, `OAI.InvariantIsing.cavity_haar_cutoff_limit_family`, `OAI.InvariantIsing.cavity_haar_finite_cutoff_comparison`, `OAI.InvariantIsing.cavity_haar_gibbs_numerator_match`, `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match`, `OAI.InvariantIsing.cavity_haar_strict_restricted_spin_match`, `OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation`, `OAI.InvariantIsing.cavity_linear_rooted_log_integral`, `OAI.InvariantIsing.cavity_linear_rooted_spin_evaluation`, `OAI.InvariantIsing.cavity_orientation_tensor_probability_law`, `OAI.InvariantIsing.cavity_original_overlap_limit`, `OAI.InvariantIsing.cavity_original_scalar_self_consistency`, `OAI.InvariantIsing.cavity_original_spin_limit`, `OAI.InvariantIsing.cavity_physical_spin_cutoff`, `OAI.InvariantIsing.cavity_physical_trial_lower`, `OAI.InvariantIsing.cavity_tensor_pressure_mean`, `OAI.InvariantIsing.cavity_window_minimum_variational_lower`, `OAI.InvariantIsing.closedMagneticSlabWeighted_hasDerivAt_time`, `OAI.InvariantIsing.closedMagneticSquareContinuationSecond_nonneg`, `OAI.InvariantIsing.constrainedFieldValue_magneticBias`, `OAI.InvariantIsing.fieldBiasMean_magneticBias`, `OAI.InvariantIsing.field_entropy_sequence_of_support`, `OAI.InvariantIsing.field_support_equal_cutList`, `OAI.InvariantIsing.field_vector_depth_pair_evaluation`, `OAI.InvariantIsing.field_vector_log_mean`, `OAI.InvariantIsing.field_vector_log_root_integral`, `OAI.InvariantIsing.field_vector_spin_pair_evaluation`, `OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot`, `OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper`, `OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper`, `OAI.InvariantIsing.finite_physical_field_pressure_upper`, `OAI.InvariantIsing.fullPerturbationPressure_cost`, `OAI.InvariantIsing.fullPerturbationPressure_variance`, `OAI.InvariantIsing.gaussianPattern_ground_limit`, `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.haarPolynomialMoment_log_bound`, `OAI.InvariantIsing.haar_tensorEnrichedPressure_variance`, `OAI.InvariantIsing.integral_priorCavityLabeledDepthMean`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.magneticBias_uniform_bound`, `OAI.InvariantIsing.magneticBlockPath_l1_tendsto`, `OAI.InvariantIsing.magneticCanonical_projection_distance`, `OAI.InvariantIsing.magneticFieldLevel_radial`, `OAI.InvariantIsing.magneticGroupValue_parameters_uniform`, `OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order`, `OAI.InvariantIsing.magneticScaledClosedCurvature_mono`, `OAI.InvariantIsing.magneticVariational_inward_mono`, `OAI.InvariantIsing.magnetic_affine_field_subsequence_lower`, `OAI.InvariantIsing.magnetic_affine_increment_eventually_lower`, `OAI.InvariantIsing.magnetic_entropy_sequence_of_support`, `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower`, `OAI.InvariantIsing.offset_envelope_pressure_lower`, `OAI.InvariantIsing.offset_product_tree_spin_error`, `OAI.InvariantIsing.offset_product_weak_self_consistency`, `OAI.InvariantIsing.offset_window_minimum_trial_witness`, `OAI.InvariantIsing.panchenkoTalagrandFieldPair_proved`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.priorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.priorNamespacedArrayLaw_diagonalWard_bound`, `OAI.InvariantIsing.priorNamespacedPerturbation_variance`, `OAI.InvariantIsing.priorPerturbation_arrayResidual_bound`, `OAI.InvariantIsing.priorPerturbation_minimizers_constantDiagonal`, `OAI.InvariantIsing.priorPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.prior_linear_rooted_log_integral`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, `OAI.InvariantIsing.restricted_cavity_finite_model_spin_test`, `OAI.InvariantIsing.restricted_cavity_full_spin_test_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_coordinate_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_noise_depth_test`, `OAI.InvariantIsing.restricted_cavity_linear_rooted_depth_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_rooted_spin_evaluation`, `OAI.InvariantIsing.restricted_compression_capped_log_limit`, `OAI.InvariantIsing.restricted_compression_log_limit`, `OAI.InvariantIsing.restricted_field_depth_pair_evaluation`, `OAI.InvariantIsing.restricted_field_spin_pair_evaluation`, `OAI.InvariantIsing.restricted_haar_cutoff_limit`, `OAI.InvariantIsing.restricted_original_full_haar_comparison`, `OAI.InvariantIsing.restricted_original_haar_limit`, `OAI.InvariantIsing.restricted_original_spin_limit`, `OAI.InvariantIsing.restricted_original_split_overlap_limit`, `OAI.InvariantIsing.restricted_physical_cutoff_comparison`, `OAI.InvariantIsing.restricted_physical_log_average`, `OAI.InvariantIsing.restricted_physical_projector_increment`, `OAI.InvariantIsing.restricted_physical_trial_lower`, `OAI.InvariantIsing.restricted_projector_coefficient_error`, `OAI.InvariantIsing.restricted_tree_pressure_capped_increment`, `OAI.InvariantIsing.restricted_zero_tree_perturbed_array_law`, `OAI.InvariantIsing.spectralCanonicalWard_pair`, `OAI.InvariantIsing.spectralCanonical_identification`, `OAI.InvariantIsing.spectralCanonical_symbols`, `OAI.InvariantIsing.spectralPartition_offWardPath`, `OAI.InvariantIsing.spinPriorContactObjective_exists_minimum`, `OAI.InvariantIsing.spinPriorContact_limit_tail_order`, `OAI.InvariantIsing.spinPriorContact_minimum_field_cone`, `OAI.InvariantIsing.spinPriorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean`, `OAI.InvariantIsing.spinPriorMeanPressure_field`, `OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound`, `OAI.InvariantIsing.spinPriorPerturbation_minimizers_constantDiagonal`, `OAI.InvariantIsing.spinPriorPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.spinPriorProfileLog_variance`, `OAI.InvariantIsing.spinPriorRestrictedContactPressure_field_le`, `OAI.InvariantIsing.spinPriorRestrictedContact_entropy_limit`, `OAI.InvariantIsing.spinPriorRestrictedContact_zero_cost`, `OAI.InvariantIsing.tensorContactObjective_exists_minimum`, `OAI.InvariantIsing.tensorContact_limit_tail_order`, `OAI.InvariantIsing.tensorContact_minimum_field_cone`, `OAI.InvariantIsing.tensorContact_no_positive_minimizing_sequence`, `OAI.InvariantIsing.tensorDiagonal_fluctuation_at_minimum`, `OAI.InvariantIsing.tensorFiniteGG_individualDiagonal_bound`, `OAI.InvariantIsing.tensorFlat_leafPrefix_mean`, `OAI.InvariantIsing.tensorFrozenCGF_centered_L1_bound`, `OAI.InvariantIsing.tensorFrozenCGF_mean`, `OAI.InvariantIsing.tensorGaussianCoordinatePressure_cost`, `OAI.InvariantIsing.tensorGrowingArrayLaw_off_ward_limit`, `OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits`, `OAI.InvariantIsing.tensorNamespacedArrayLaw_off_ward_limit`, `OAI.InvariantIsing.tensorNamespacedMeanPressure_field_modulus`, `OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost`, `OAI.InvariantIsing.tensorPerturbationPressureMean_modulus`, `OAI.InvariantIsing.tensorPerturbation_minimizers_have_GG_limit`, `OAI.InvariantIsing.tensorPerturbedArrayLaw_interactionEnergy_limit`, `OAI.InvariantIsing.tensor_envelope_pressure_lower` and `OAI.InvariantIsing.tensor_zero_field_minimizing_sequence`.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor features for spectral-overlap GG perturbations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_spectralMonomialFeature {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N) (v : SpectralTensorIndex I d) :
    Measurable (fun U : SpecialOrthogonal N => spectralMonomialFeature (specialRotation U) I d σ v) := by
  unfold spectralMonomialFeature IsingPerceptron.tensorFeature spectralSpinFeature
  apply Finset.measurable_prod
  intro a _
  apply Finset.measurable_prod
  intro k _
  exact (measurable_specialRotation_eval (spinVector σ) (v a k)).div_const _

/-- Independent tensor marks at the cascade levels realize the additional
tree-overlap power in the paper's joint perturbation kernels. -/
def jointSpectralMonomialCoefficients {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × IsingPerceptron.LabeledLeaf n) : ℕ →₀ ℝ :=
  IsingPerceptron.treeFieldCoefficients n x.2
    (fun i => IsingPerceptron.pathAmplitude (IsingPerceptron.monomialPath n r) i)
    (spectralMonomialFeature U I d x.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_spinTensorFeature {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (σ : Spin N)
    (i : SpinTensorIndex I degree) :
    Measurable (fun U : SpecialOrthogonal N =>
      spinTensorFeature (specialRotation U) I degree amplitude σ i) := by
  cases i with
  | inl i => exact measurable_const
  | inr v => exact (measurable_spectralMonomialFeature I (degree v.1) σ v.2).const_mul _

def spinTensorEnergy {N m k : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) : ℝ :=
  ∑ i, z i * spinTensorFeature U I degree amplitude σ i

def spinTensorTerminal {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ +
    spinTensorEnergy U I degree amplitude z σ)

def tensorCascadeLog {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (T : IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) : ℝ :=
  Real.log (∫ leaf, Real.exp (IsingPerceptron.noiseLeafTerminal n
    (fun _ => spinTensorTerminal eig U c I degree amplitude) (fun _ p => p.1 + p.2) z leaf)
    ∂IsingPerceptron.noiseLeafKernel (SpinTensorIndex I degree → ℝ) n T)

def tensorCascadeValue {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  IsingPerceptron.cascadeRecursion n b (fun i => tensorGaussianLaw I degree (v i))
    (fun _ p => p.1 + p.2) (spinTensorTerminal eig U c I degree amplitude) z

def tensorEnrichedPressure {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (root : SpinTensorIndex I degree → ℝ≥0) : ℝ :=
  (N : ℝ)⁻¹ * ∫ z, tensorCascadeValue eig U c I degree amplitude n b v z
    ∂(tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorRootVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root Gaussian contribution for the finite spectral-tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace InvariantIsing

/-- Reindex independent standard Euclidean coordinates, then apply the
coordinate square roots of the prescribed root variances. -/
def tensorRootMark {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (root : SpinTensorIndex I degree → ℝ≥0)
    (g : TensorGaussianSpace I degree) : SpinTensorIndex I degree → ℝ :=
  fun i => (NNReal.sqrt (root i) : ℝ) * g (Fintype.equivFin (SpinTensorIndex I degree) i)

def tensorRootCoefficient {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (root : SpinTensorIndex I degree → ℝ≥0) (σ : Spin N) : TensorGaussianSpace I degree :=
  WithLp.toLp 2 (fun j =>
    (NNReal.sqrt (root ((Fintype.equivFin (SpinTensorIndex I degree)).symm j)) : ℝ) *
      spinTensorFeature U I degree amplitude σ ((Fintype.equivFin (SpinTensorIndex I degree)).symm j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_spinTensorEnergyMark {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    Measurable (fun z : SpinTensorIndex I degree → ℝ =>
      spinTensorEnergy U I degree amplitude z) := by
  unfold spinTensorEnergy
  fun_prop

def tensorEnergyMarkLaw {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : SpinTensorIndex I degree → ℝ≥0) : ProbabilityMeasure (Spin N → ℝ) :=
  (tensorGaussianLaw I degree v).map (measurable_spinTensorEnergyMark U I degree amplitude).aemeasurable

def tensorSpinBaseEnergy {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) : Spin N → ℝ :=
  fun σ => rotatedEnergy eig U σ + fieldEnergy c σ + spinTensorEnergy U I degree amplitude z σ

def tensorLabeledLaw {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) : Measure (TensorLabeledData N n) :=
  IsingPerceptron.cascadeCoordinateLaw n b (fun i => tensorEnergyMarkLaw U I degree amplitude (v i))

def tensorCoordinateLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) : Measure (TensorCoordinateData I degree n) :=
  (IsingPerceptron.labeledCascadeLaw n b : Measure (IsingPerceptron.LabeledTree n)).prod
    (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
      (tensorGaussianLaw I degree (v (IsingPerceptron.forestVertexDepth n w)) :
        Measure (SpinTensorIndex I degree → ℝ))))

instance tensorCoordinateLaw_probability {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorCoordinateLaw I degree n b v) := by
  unfold tensorCoordinateLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def tensorEnergyCoordinates {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (p : TensorCoordinateData I degree n) : TensorLabeledData N n :=
  (p.1, fun w => spinTensorEnergy U I degree amplitude (p.2 w))

instance tensorLabeledLaw_probability {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorLabeledLaw U I degree amplitude n b v) := by
  unfold tensorLabeledLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def tensorLabeledReference (N n : ℕ) (p : TensorLabeledData N n) : Measure (TensorLabeledState N n) :=
  IsingPerceptron.labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1

instance tensorLabeledReference_probability (N n : ℕ) (p : TensorLabeledData N n) :
    IsProbabilityMeasure (tensorLabeledReference N n p) := by
  unfold tensorLabeledReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def tensorLabeledEnergy {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorLabeledData N n) : TensorLabeledState N n → ℝ :=
  IsingPerceptron.cascadeCoordinateEnergy n (tensorSpinBaseEnergy eig U c I degree amplitude z) p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly measurable Haar-dependent Gaussian tensor fields. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_projectedOverlap {N : ℕ} (I : Finset (Fin N)) (σ τ : Spin N) :
    Measurable (fun U : SpecialOrthogonal N => projectedOverlap (specialRotation U) I σ τ) := by
  unfold projectedOverlap
  exact (Finset.measurable_sum I (fun i _ =>
    (measurable_specialRotation_eval (spinVector σ) i).mul
      (measurable_specialRotation_eval (spinVector τ) i))).const_mul _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorGaussianLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat countable Gaussian field has the actual root/forest mark law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorFlatToCoordinates {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × TensorCoordinateData I degree n :=
  (tensorGaussianNodes I degree n v p.2 none,
    (p.1, fun w => tensorGaussianNodes I degree n v p.2 (some w)))

def tensorFlatToLabeled {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n :=
  let q := tensorFlatToCoordinates I degree n v p
  (q.1, tensorEnergyCoordinates U I degree amplitude n q.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFlatMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat Gaussian spin/leaf pressure has the actual cascade mean. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorFlatLog {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp (rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
    cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorHaarFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Haar, Gaussian-root, and cascade fluctuations for the actual finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The normalized spin/leaf log partition retaining all three disorders. -/
def tensorDisorderPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
    (p : SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) ×
      NoiseTree (SpinTensorIndex I degree → ℝ) n)) : ℝ :=
  (N : ℝ)⁻¹ * tensorCascadeLog eig (specialRotation p.1) c I degree amplitude n p.2.1 p.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorNamespacedCoefficients {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
    tensorNamespaceTag I degree (i.1, (labeledAddress n x.2).take i.1, i.2))
    (fun i => (NNReal.sqrt (v i.1 i.2) : ℝ) * spinTensorFeature U I degree amplitude x.1 i.2)

lemma measurable_tensorNamespacedFields_joint {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) := by
  simp only [tensorNamespacedCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (tensorNamespaceTag I degree (i.1.1, (labeledAddress n x.2).take i.1, i.2))).comp measurable_snd)

def tensorFrozenBaseEnergy {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
      (Function.update amplitude j 0) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, ω.2))

def tensorFrozenReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.1.2)
    (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j ω)

instance tensorFrozenReference_probability {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (ω : TensorFrozenData N n j) :
    IsProbabilityMeasure (tensorFrozenReference eig c I degree amplitude n treeDegree h j ω) :=
  gibbsProbability_probability _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen exponential integrability and selected-field log partition identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing


def tensorNamespacedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)

def tensorFrozenPartitionLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  tensorNamespacedLog eig c I degree (Function.update amplitude j t) n treeDegree h
    (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2))

def tensorFrozenCGF {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
      (specialRotation p.1.1.1) I (degree j) n (treeDegree j) x) p.2)
    (tensorFrozenReference eig c I degree amplitude n treeDegree h j p.1) t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFlatLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual flat spin/leaf pressure and marked-cascade pressure have the same law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def tensorFlatToNoise {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n :=
  let q := tensorFlatToCoordinates I degree n v p
  (q.1, labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
    (q.2.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2.2))

def tensorFlatToDisorder {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) :
    SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  (p.1.1, tensorFlatToNoise I degree n v (p.1.2, p.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the actual three-disorder pressure moments to one frozen Gaussian CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def tensorNamespacedPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) : ℝ :=
  (N : ℝ)⁻¹ * tensorNamespacedLog eig c I degree amplitude n treeDegree h p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian GG bound specialized to the manuscript's spectral/tree kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- The concrete Haar-dependent tensor coefficient map. -/
def spectralPerturbationCoefficients {Ω : Type*} {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (n r : ℕ) : Ω → (Spin N × LabeledLeaf n) → ℕ →₀ ℝ :=
  fun ω => jointSpectralMonomialCoefficients (specialRotation (U ω)) I d n r

def spectralPerturbationKernel {Ω : Type*} {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (n r : ℕ) (ω : Ω) (x y : Spin N × LabeledLeaf n) : ℝ :=
  (∏ a, projectedOverlap (specialRotation (U ω)) (I a) x.1 y.1 ^ d a) *
    treeOverlap n x.2 y.2 ^ r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoordinateMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor coordinates at a penalized pressure minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- The coordinate pressure is the actual root/cascade pressure averaged
over the rotation, with precisely one Gaussian amplitude replaced. -/
def tensorGaussianCoordinatePressure {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ) (j : Fin N) (w : ℝ) : ℝ :=
  ∫ p, tensorDisorderPressure eig c I degree
    (Function.update amplitude j (perturbationAmplitude N j * w)) n p
    ∂(μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-diagonal coordinate as a bounded frozen tilt. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorNamespacedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
      (fun i => tensorPathProfile I degree n r h i) x) p.2

lemma measurable_tensorNamespacedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (Function.uncurry (tensorNamespacedHamiltonian eig c I degree amplitude n r h)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n r h i
  have hf := (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp
    (measurable_fst.fst.prodMk measurable_snd :
      Measurable (fun p : TensorFlatDisorder N n => (p.1.1, p.2)))
  exact ((hr.comp measurable_fst.fst).add_const (fieldEnergy c x.1)).add hf

def tensorNamespacedReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) :
    Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    (tensorNamespacedHamiltonian eig c I degree amplitude n r h p)

instance tensorNamespacedReference_probability {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) :
    IsProbabilityMeasure (tensorNamespacedReference eig c I degree amplitude n r h p) :=
  gibbsProbability_probability _ _

lemma measurable_tensorNamespacedReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (tensorNamespacedReference eig c I degree amplitude n r h) := by
  have : ∀ p : TensorFlatDisorder N n, IsProbabilityMeasure
      ((labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ∘
        fun p : TensorFlatDisorder N n => p.1.2) p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact measurable_gibbsProbability
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.snd) (measurable_tensorNamespacedHamiltonian eig c I degree amplitude n r h)

def tensorDiagonalCGF {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ) (a : Fin m)
    (s : ℝ) (p : TensorFlatDisorder N n) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
    (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude n r h p) s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorReplicaAverageLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite replica averages under the tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def tensorNamespacedReplicaAverage {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n,
    referenceReplicaMean (tensorNamespacedReference eig c I degree amplitude n r h p)
      (fun _ => 0) (D p.1.1)
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorObservableAverageLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both frozen coordinates control observables in the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorNamespacedObservableAverage {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n, ∫ x, D p.1.1 x
    ∂tensorNamespacedReference eig c I degree amplitude n r h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFiniteGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite GG residual expressed in the actual full tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorSpectralGGResidual {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  let avg := fun (q' : ℕ) (F : SpecialOrthogonal N → (Fin q' → Spin N × LabeledLeaf n) → ℝ) =>
    tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h F
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  (q + 1 : ℕ) * avg (q + 1 + 1)
      (fun U τ => D U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) -
    avg (q + 1) D * avg 2 (fun U τ => κ U (τ 1) (τ 0)) -
    avg (q + 1)
      (fun U σ => D U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_FullPerturbationMinima
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For the complete perturbation, both coordinate minima force the
Ghirlanda–Guerra errors to vanish. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorPerturbationPressureMean {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) : ℝ :=
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let treeDegree := fun j : Fin N => enumeratedTreeDegree m j
  ∫ p, tensorDisorderPressure (diagonalPerturbedEigenvalues eig I v t) c I degree
    (tensorPerturbationAmplitude N u) n p
    ∂(μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorPairConditioning
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional independent spin residuals at two sampled cascade leaves. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

def spinLeafTerminal {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) : ℝ :=
  finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α))

def spinLeafPairResidualKernel {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) :
    Kernel (Fin 2 → LabeledLeaf n) (Fin 2 → Spin N) :=
  ⟨fun α => Measure.pi (fun i : Fin 2 =>
      gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun σ => H (σ, α i))),
    measurable_of_countable _⟩

instance spinLeafPairResidualKernel_markov {N n : ℕ} (H : Spin N × LabeledLeaf n → ℝ) :
    IsMarkovKernel (spinLeafPairResidualKernel H) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

lemma measurable_spectralJointEntry {N m : ℕ} (I : Fin m → Finset (Fin N)) (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) =>
      spectralJointEntry (specialRotation p.1) I n p.2.1 p.2.2) := by
  apply measurable_from_prod_countable_left
  intro xy
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [spectralJointEntry, Fin.lastCases_last]
    exact (measurable_const : Measurable
      (fun _ : SpecialOrthogonal N => treeOverlap n xy.1.2 xy.2.2)).subtype_mk
  · simp only [spectralJointEntry, Fin.lastCases_castSucc]
    exact (measurable_projectedOverlap (I a) xy.1.1 xy.2.1).subtype_mk

def spectralReplicaArray {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralArray (m + 1) :=
  fun ij => spectralJointEntry (specialRotation (U p.1)) I n (p.2 ij.1) (p.2 ij.2)

lemma measurable_spectralReplicaArray {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ) : Measurable (spectralReplicaArray U I n) := by
  unfold spectralReplicaArray
  apply Measurable.of_eval
  intro ij
  change Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) =>
    spectralJointEntry (specialRotation (U p.1)) I n (p.2 ij.1) (p.2 ij.2))
  let f : (Ω × (ℕ → Spin N × LabeledLeaf n)) →
      SpecialOrthogonal N × ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) :=
    fun p => (U p.1, (p.2 ij.1, p.2 ij.2))
  have hrot : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => U p.1) :=
    hU.comp measurable_fst
  have hi : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => p.2 ij.1) :=
    (measurable_pi_apply ij.1).comp measurable_snd
  have hj : Measurable (fun p : Ω × (ℕ → Spin N × LabeledLeaf n) => p.2 ij.2) :=
    (measurable_pi_apply ij.2).comp measurable_snd
  have hp : Measurable f := hrot.prodMk (hi.prodMk hj)
  have he := (measurable_spectralJointEntry I n).comp hp
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rfl

def spectralArrayLaw {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : ProbabilityMeasure (SpectralArray (m + 1)) :=
  ⟨(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_spectralReplicaArray U hU I n).aemeasurable).mpr inferInstance⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

def tensorNamespacedArrayLaw {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m + 1)) :=
  spectralArrayLaw ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    (fun p : TensorFlatDisorder N n => p.1.1) measurable_fst.fst I n
    (tensorNamespacedReference eig c I degree amplitude n r h)
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h)

def finiteSpectralBlock {N m z : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (σ : Fin z → Spin N × LabeledLeaf n) :
    SpectralBlock (m + 1) z :=
  fun i j => spectralJointEntry U I n (σ i) (σ j)

def permutedSpectralBlockTest {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin z → Spin N × LabeledLeaf n) : ℝ :=
  D (finiteSpectralBlock (specialRotation U) I n (σ ∘ e.symm))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardError
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite covariance derivative contractions in the tensor perturbation
error of the spectral Ward identity (manuscript, §3, lines 421--439). -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spectralMonomialEndpointCoefficient {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) (a : Fin m) : ℝ :=
  (∏ b ∈ Finset.univ.erase a, projectedOverlap (matrixRotation U) (I b) σ τ ^ d b) *
    ((d a : ℝ) * projectedOverlap (matrixRotation U) (I a) σ τ ^ (d a - 1))

def spectralMonomialEndpointDerivative {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (i j : Fin N) (σ τ : Spin N) : ℝ :=
  ∑ a, spectralMonomialEndpointCoefficient U I d σ τ a * projectedOverlapEndpointDerivative U (I a) i j σ τ

def spectralMonomialEndpointContraction {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) : ℝ :=
  ∑ a, spectralMonomialEndpointCoefficient U groups d σ τ a *
    projectedEndpointContraction U I J (groups a) η θ σ τ

def tensorWardPerturbationError {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) : ℝ :=
  ∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
    spectralMonomialEndpointContraction U groups (degree r) I J η θ x.1 y.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoefficientDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate-plane derivatives of the actual finite spectral tensor
coefficients, with uniform finite-dimensional bounds for Haar differentiation. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The ordinary product-rule derivative of one spectral tensor feature. -/
def spectralTensorPlaneDerivative {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) : ℝ :=
  ∑ a, (∏ b ∈ Finset.univ.erase a,
      tensorFeature (d b) (spectralSpinFeature (matrixRotation U) (I b) σ) (v b)) *
    ∑ k : Fin (d a), (∏ l ∈ Finset.univ.erase k,
      spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
        spectralSpinPlaneDerivative U σ i j (v a k)

/-- The independent linear enrichment has zero rotation derivative. -/
def spinTensorPlaneDerivative {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) : SpinTensorIndex I degree → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => amplitude v.1 * spectralTensorPlaneDerivative U I (degree v.1) σ i j v.2

def spinTensorDerivativeCap {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) : SpinTensorIndex I degree → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => |amplitude v.1| * (2 * ∑ a, (degree v.1 a : ℝ))

/-- The actual derivative coefficient map uses precisely the same Gaussian
namespaces and ancestor tags as the Hamiltonian. -/
def tensorNamespacedPlaneCoefficients {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (fun a : Fin (n + 1) × SpinTensorIndex I degree =>
    tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2))
    (fun a => (NNReal.sqrt (v a.1 a.2) : ℝ) *
      spinTensorPlaneDerivative U I degree amplitude x.1 i j a.2)

def tensorNamespacedDerivativeCap {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) : ℝ :=
  ∑ a : Fin (n + 1) × SpinTensorIndex I degree,
    (NNReal.sqrt (v a.1 a.2) : ℝ) * spinTensorDerivativeCap I degree amplitude a.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPerturbationObjective
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global minima of the actual finite perturbation objective imply both
coordinate minimum conditions used by the GG estimates. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorPerturbationObjective {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -tensorPerturbationPressureMean μ eig c I u v t n b h +
    ∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2 + ∑ a, (v a - 3 / 2) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spin/leaf pair application of the spectral Haar Ward identity.
The spin test is fixed under rotations and may be any function of total
overlap. Arbitrary finite leaf restrictions and zero prior weights are allowed. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionPairPrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) (a : Fin d) : ℝ :=
  tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.1) a +
    tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.2) a

def tensorRestrictionPairPlanePrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (p : S × S) (a : Fin d) : ℝ :=
  tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.1) a +
    tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.2) a

def tensorRestrictionPairHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (g : ℕ → ℝ) (p : S × S) : ℝ :=
  tensorRestrictionPairBase eig c x U p +
    (cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.1)) g +
      cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.2)) g)

def tensorRestrictionPairCovarianceDerivative {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (p q : S × S) : ℝ :=
  cylinderCross
    (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.1) +
      tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.2))
    (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x q.1) +
      tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x q.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-replica diagonal Haar Ward identity for the actual finite
spin/leaf tensor model. The main quadratic coefficient has no extra factor two. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionPrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (s : S) (a : Fin d) : ℝ :=
  tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s) a

def tensorRestrictionPlanePrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (s : S) (a : Fin d) : ℝ :=
  tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x s) a

def tensorRestrictionHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (g : ℕ → ℝ) (s : S) : ℝ :=
  tensorRestrictionBase eig c x U s +
    cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s)) g

def tensorRestrictionCovarianceDerivative {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (s t : S) : ℝ :=
  cylinderCross (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x s))
    (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardCorrectionBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the complete finite Gaussian Ward correction after
spectral coordinate contraction. Constants do not depend on the leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

omit [Fintype S] in
def tensorRestrictionWardContraction {N m n : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ)
    (x : S → Spin N × LabeledLeaf n) (s p q : S × S) : ℝ :=
  F (x s.1).1 (x s.2).1 *
    (tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.1) (x q.1) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.1) (x q.2) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.2) (x q.1) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.2) (x q.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalWardCorrectionBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized one-replica Gaussian Ward correction is quadratic in
the perturbation scale, uniformly in the finite leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionDiagonalWardContraction {N m n : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) (s p q : S) : ℝ :=
  tensorWardPerturbationError U I degree treeDegree n u J K (x s).1 (x s).1 (x p) (x q)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability and bounded integrability of the actual finite
principal Ward term and its Gaussian correction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
def tensorRestrictionOffCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  gaussianWardCorrection (fun p : S × S => w p.1 * w p.2)
    (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionOffObservable i j F x z.1)
    (tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j z.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorNamespacedMeanPressure {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (∫ p, tensorNamespacedPressure eig c I degree amp n treeDegree h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) - h n / 2

def tensorFieldCGFMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : TensorFlatDisorder N n × (ℕ → ℝ),
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) z.2)
      (tensorNamespacedReference eig c I degree amp n treeDegree h z.1) (Real.sqrt a)
    ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod
      gaussianCoordinates

def tensorFieldInsertionMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree h +
    tensorFieldCGFMean μ eig c I degree amp n b treeDegree h g a / N - a * g n / 2


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing the linear field in a nonnegative monotone direction is
exactly an independent Gaussian insertion in the actual tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorFieldInsertedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ)
    (p : TensorFlatDisorder N n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1 x +
      Real.sqrt a * cylinderField (tensorLinearCoefficients n g x) p.2)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2)

def tensorFieldInsertedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ)
    (p : TensorFlatDisorder N n × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) : ℝ :=
  tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1 x +
    Real.sqrt a * cylinderField (tensorLinearCoefficients n g x) p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the actual centered pressure in temperature, field
covariance increments and both complete perturbation amplitudes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite joint contact minima. Restricting a joint minimum to the
two perturbation boxes gives exactly the minima used in the GG limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def tensorContactObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  -tensorContactPressure μ eig c I b p - (∑ i, w i * finiteFieldPath p.2.1 i) / 2 +
    S + V p.1 + ∑ j : Fin N, perturbationWeight j * (p.2.2.1 j - 3 / 2) ^ 2 +
    ∑ a, (p.2.2.2 a - 3 / 2) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactField
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field-coordinate inequality at the actual joint minimum. Tied and
zero covariance levels are allowed; only the upper cap must be inactive. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorContactFieldObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ)
    (t : ℝ) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ) (h : ℕ → ℝ) : ℝ :=
  -tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    n b (fun j => enumeratedTreeDegree m j) h - (∑ i, w i * h i) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPrincipalBlock
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite principal Ward observables contract exactly to projected
overlap products when the two row groups have constant eigenvalues. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorOffBlockDirect {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  let A := fun L s t => projectedOverlap (specialRotation U) L (sp s) (sp t)
  F (sp (σ 0)) (sp (σ 1)) *
    (((J.card : ℝ) / N) * A K (σ 0) (σ 1) - ((K.card : ℝ) / N) * A J (σ 0) (σ 1) +
      δ * (A J (σ 0) (σ 0) * A K (σ 0) (σ 1) + A J (σ 0) (σ 1) * A K (σ 1) (σ 1)))

def tensorOffBlockFresh {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ) (U : SpecialOrthogonal N) (σ : Fin 3 → X) : ℝ :=
  δ * F (sp (σ 0)) (sp (σ 1)) *
    projectedOverlap (specialRotation U) J (sp (σ 0)) (sp (σ 2)) *
    projectedOverlap (specialRotation U) K (sp (σ 1)) (sp (σ 2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalPrincipalObservables
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one- and two-replica principal observables for the diagonal Ward
identity, with a generic spin projection for countable leaf passage. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorDiagonalBlockDirect {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) : ℝ :=
  let A := fun L => projectedOverlap (specialRotation U) L (sp (σ 0)) (sp (σ 0))
  ((J.card : ℝ) / N) * A K - ((K.card : ℝ) / N) * A J + δ * A J * A K

def tensorDiagonalBlockFresh {N : ℕ} (J K : Finset (Fin N)) (δ : ℝ)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  δ * projectedOverlap (specialRotation U) J (sp (σ 0)) (sp (σ 1)) *
    projectedOverlap (specialRotation U) K (sp (σ 0)) (sp (σ 1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalWardMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint integrability for the actual finite diagonal Ward identity. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*} [Fintype S]

def tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  finiteGibbsVariation w (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionDiagonalObservable i j x z.1)
    (fun s => (eig i - eig j) * tensorRestrictionDiagonalObservable i j x z.1 s)
    (tensorRestrictionDiagonalVariation i j x z.1)

def tensorRestrictionDiagonalCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  gaussianWardCorrection w (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionDiagonalObservable i j x z.1)
    (tensorRestrictionCovarianceDerivative I degree amplitude v x i j z.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every weak spectral-array limit of actual finite perturbation minimizers
satisfies the full vector Ghirlanda–Guerra identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def tensorPerturbedArrayLaw {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) : ProbabilityMeasure (SpectralArray (m + 1)) :=
  tensorNamespacedArrayLaw μ (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    n b (fun j : Fin N => enumeratedTreeDegree m j) h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPrincipalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite normalized principal Ward residual bound. The exact Gaussian
correction is eliminated before countable leaf exhaustion. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S ι : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
def tensorRestrictionOffPrincipalVariation {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  finiteGibbsVariation (fun p : S × S => w p.1 * w p.2)
    (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
    (tensorRestrictionOffVariation i j F x z.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-dimensional backward values, physical conditional spin
means, and conditional second moments for a finite list of field increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) :
    ∀ i, Measurable (fieldScalarSquares L F a i) ∧
      ∀ z, fieldScalarSquares L F a i z ∈ Icc (0 : ℝ) 1 := by
  induction L with
  | nil =>
    intro i
    refine ⟨ha.pow_const 2, fun z => ⟨sq_nonneg _, ?_⟩⟩
    have hab := abs_le.mp (haB z)
    change (a z) ^ 2 ≤ 1
    nlinarith
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular (av :: L) hL hF hG ha haB
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨hmean.1.pow_const 2, fun z => ⟨sq_nonneg _, ?_⟩⟩
      have hab := abs_le.mp (hmean.2 z)
      change (fieldScalarMean (av :: L) F a z) ^ 2 ≤ 1
      nlinarith
    · have hj := ih htail j
      refine ⟨measurable_fieldSpinTransition av.1 av.2 hval.1 hj.1, fun z => ⟨?_, ?_⟩⟩
      · exact integral_nonneg (fun u => (hj.2 u).1)
      · have hb : ∀ u, |fieldScalarSquares L F a j u| ≤ 1 := by
          intro u
          rw [abs_of_nonneg (hj.2 u).1]
          exact (hj.2 u).2
        exact (le_abs_self _).trans (fieldSpinTransition_bound av.1 av.2 hval.1 hval.2 hb z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field's actual level overlaps. Their ordering is the
conditional Jensen inequality, and zero increments give exact ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_monotone (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) (z : ℝ) :
    Monotone (fun i => fieldScalarSquares L F a i z) := by
  induction L generalizing z with
  | nil =>
    intro i j _
    exact le_rfl
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hreg := fieldScalarSquares_regular L htail hF hG ha haB
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarMean L F a) z) ^ 2 ≤
        fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a 0) z
      have he : fieldScalarSquares L F a 0 = fun u => (fieldScalarMean L F a u) ^ 2 := by
        funext u
        exact fieldScalarSquares_zero L F a u
      rw [he]
      exact fieldSpinTransition_square_le av.1 av.2 hval.1 hval.2 hmean.1 hmean.2 z
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.castSucc) z ≤
        fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.succ) z
      apply fieldSpinTransition_mono_test av.1 av.2 (fieldScalarValue L F)
        (hreg j.castSucc).1 (hreg j.succ).1
        (fun u => by rw [abs_of_nonneg ((hreg j.castSucc).2 u).1]; exact ((hreg j.castSucc).2 u).2)
        (fun u => by rw [abs_of_nonneg ((hreg j.succ).2 u).1]; exact ((hreg j.succ).2 u).2)
      intro u
      exact ih htail u (by change j.val ≤ j.val + 1; omega)

/-- Root Gaussian averaging produces the level second moments `B_i`. -/
def fieldScalarOverlaps (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (F a : ℝ → ℝ) (i : Fin (L.length + 1)) : ℝ :=
  ∫ z, fieldScalarSquares L F a i z ∂gaussianReal 0 root

lemma fieldScalarOverlaps_mem_unit (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root F a i ∈ Icc (0 : ℝ) 1 := by
  have hr := fieldScalarSquares_regular L hL hF hG ha haB i
  have hi : Integrable (fieldScalarSquares L F a i) (gaussianReal 0 root) :=
    Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]; exact (hr.2 z).2))
  refine ⟨integral_nonneg (fun z => (hr.2 z).1), ?_⟩
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun z => (hr.2 z).2)
  simpa only [fieldScalarOverlaps, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul] using h

lemma fieldScalarOverlaps_monotone (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) :
    Monotone (fieldScalarOverlaps L root F a) := by
  have hi (i : Fin (L.length + 1)) : Integrable (fieldScalarSquares L F a i) (gaussianReal 0 root) := by
    have hr := fieldScalarSquares_regular L hL hF hG ha haB i
    exact Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]; exact (hr.2 z).2))
  intro i j hij
  exact integral_mono (hi i) (hi j) (fun z => fieldScalarSquares_monotone L hL hF hG ha haB z hij)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite scalar log-cosh recursion with affine covariance
increments is a smooth field family on its strict covariance interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldAffineFamily (I : Set ℝ) (hI : IsOpen I) :
    (L : List FieldAffineStep) →
      (∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) → FieldSmoothFamily I
  | [], _ => fieldLogCoshFamily I
  | av :: L, hL =>
      (fieldAffineFamily I hI L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))).transform
        hI av.base av.slope av.exponent (hL av List.mem_cons_self)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldConstantPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation of a covariance derivative through the unchanged earlier
levels. The propagated tangent is the actual conditional expectation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldConstantPrefix {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I) :
    (L : List (ℝ × ℝ≥0)) → (∀ av ∈ L, 0 < (av.2 : ℝ)) → FieldSmoothFamily I
  | [], _ => F
  | av :: L, hL =>
      (fieldConstantPrefix hI F L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))).transform
        hI av.2 0 av.1 (fun _ _ => by simpa only [zero_mul, add_zero] using hL av List.mem_cons_self)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAdjacentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual internal-height comparison in `fld:mixed`. The fixed
tail is the finite log-cosh recursion. Increasing one height adds its
parameter to one variance and subtracts it from the next variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAdjacentTail (a b : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  fieldAffineFamily (Ioo (-a) b) isOpen_Ioo L (fun av hav _ _ => by
    rw [hs av hav, zero_mul, add_zero]
    exact hb av hav)

def fieldAdjacentInner (a b η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  (fieldAdjacentTail a b L hb hs).transform isOpen_Ioo b (-1) η (fun t ht => by
    have h := ht.2
    linarith)

def fieldAdjacentFamily (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  (fieldAdjacentInner a b η L hb hs).transform isOpen_Ioo a 1 ζ (fun t ht => by
    have h := ht.1
    linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTerminalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final covariance coordinate has the same mixed monotonicity;
its backward derivative has the additional constant one half. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldTerminalFamily (a ζ : ℝ) : FieldSmoothFamily (Ioi (-a)) :=
  (fieldLogCoshFamily (Ioi (-a))).transform isOpen_Ioi a 1 ζ (fun t ht => by
    have h : -a < t := ht
    linarith)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

/-- Monotone unit level values become an admissible overlap path on the
same partition as the actual field. -/
def fieldLevelPath (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1) : OverlapPath where
  val := fun s => q (fieldLevelIndex h s)
  monotone := hq.comp (fieldLevelIndex_monotone h)
  nonneg := fun _ => (hunit _).1
  le_one := fun _ => (hunit _).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual magnetization-overlap path for a finite scalar Ising field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- The physical squared conditional spin means, averaged over the root
Gaussian. These are the `B_i(h)` of the field derivative formula. -/
def fieldMagnetizationLevel (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ :=
  fieldScalarOverlaps (scalarFieldIncrements h) (NNReal.mk (h.height 0) (h.nonneg 0))
    (fun z => Real.log (Real.cosh z)) Real.tanh
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)

lemma fieldMagnetizationLevel_mem_unit (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel h i ∈ Icc (0 : ℝ) 1 := by
  exact fieldScalarOverlaps_mem_unit (scalarFieldIncrements h) _ (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth measurable_field_tanh field_abs_tanh_le_one _

lemma fieldMagnetizationLevel_monotone (h : FieldStep) :
    Monotone (fieldMagnetizationLevel h) := by
  have hm := fieldScalarOverlaps_monotone (scalarFieldIncrements h)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth measurable_field_tanh field_abs_tanh_le_one
  intro i j hij
  apply hm
  exact hij

/-- A globally defined admissible representative on the field partition. -/
def fieldMagnetizationPath (h : FieldStep) : InvariantIsing.OverlapPath :=
  fieldLevelPath h (fieldMagnetizationLevel h) (fieldMagnetizationLevel_monotone h)
    (fieldMagnetizationLevel_mem_unit h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- This changes the height at an interior cell, keeping the final
height and every other increment fixed. -/
def fieldInteriorChart (h : FieldStep) (i : Fin h.depth) (t z : ℝ) : ℝ :=
  let L := fieldAllIncrements h
  fieldScalarValue
    (fieldAdjacentIncrements (L.take i.val) (L.drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 t)
    (fun y => Real.log (Real.cosh y)) z - h.height (Fin.last h.depth) / 2

/-- The analogous final-height chart changes the last increment and the
normalizing diagonal covariance together. -/
def fieldFinalChart (h : FieldStep) (t z : ℝ) : ℝ :=
  let L := fieldAllIncrements h
  fieldScalarValue
    (fieldTerminalIncrements (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 t)
    (fun y => Real.log (Real.cosh y)) z - (h.height (Fin.last h.depth) + t) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldBias
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical mean spin is the bias derivative of the actual finite
field functional, including its zero-exponent root Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- The mean spin before the root increment, at an arbitrary bias. -/
def fieldBiasMean (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarMean (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict bias convexity follows from the positive terminal curvature
and the nonnegative conditional variance terms in the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- Actual second bias derivative, with the root exponent fixed at zero. -/
def fieldBiasCurvature (h : FieldStep) : ℝ → ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSecond (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (fun z => 1 / (Real.cosh z) ^ 2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldInverse
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unique interior minimizing bias is the inverse physical mean-spin
map. Its derivative and the magnetization envelope formula are actual
consequences of the scalar Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def magneticBias (h : FieldStep) : ℝ → ℝ := Function.invFun (fieldBiasMean h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCanonicalSpin
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical spin law, including the ordinary Gaussian root.
Its mean is the physical bias derivative, so optimizing the bias gives
the requested group magnetizations exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldCanonicalSpinLaw (h : FieldStep) (b : ℝ) : Measure Bool :=
  (fieldTailSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₖ
    fieldTransitionKernel 0 (NNReal.mk (h.height 0) (h.nonneg 0))
      (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
      (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
        measurable_logCosh logCosh_linearGrowth).1) b

instance fieldCanonicalSpinLaw_probability (h : FieldStep) (b : ℝ) :
    IsProbabilityMeasure (fieldCanonicalSpinLaw h b) := by
  unfold fieldCanonicalSpinLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalEndpoint
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-site canonical endpoint law and its final spin draw. The
ordinary root Gaussian is retained explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTailEndpointKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel ℝ ℝ
  | [], _ => Kernel.id
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldTailEndpointKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldTailEndpointKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldTailEndpointKernel L hL) := by
  induction L with
  | nil => change IsMarkovKernel Kernel.id; infer_instance
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def fieldCanonicalEndpointLaw (h : FieldStep) (b : ℝ) : Measure ℝ :=
  fieldTailEndpointKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₘ
    gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))

instance fieldCanonicalEndpointLaw_probability (h : FieldStep) (b : ℝ) :
    IsProbabilityMeasure (fieldCanonicalEndpointLaw h b) := by
  unfold fieldCanonicalEndpointLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVectorSampling
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual vector spin sampling for independent scalar cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldVectorSpinKernel (N : ℕ) : Kernel (Fin N → ℝ) (Spin N) :=
  ⟨fun z => gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z),
    measurable_gibbsProbability (ν := fun _ : Fin N → ℝ =>
      (uniformSpinPrior N : Measure (Spin N)))
      (H := fun p : (Fin N → ℝ) × Spin N => fieldEnergy p.1 p.2)
      measurable_const (by unfold fieldEnergy; fun_prop)⟩

instance fieldVectorSpinKernel_markov (N : ℕ) : IsMarkovKernel (fieldVectorSpinKernel N) := by
  constructor
  intro z
  change IsProbabilityMeasure (gibbsProbability (uniformSpinPrior N : Measure (Spin N))
    (fieldEnergy z))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def fieldVectorTailSpinKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel (Fin N → ℝ) (Spin N)
  | [], _ => fieldVectorSpinKernel N
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldVectorTailSpinKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldVectorTailSpinKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldVectorTailSpinKernel N L hL) := by
  induction L with
  | nil => exact fieldVectorSpinKernel_markov N
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVectorPairSampling
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the common-prefix vector Ising spin pair law, with the
actual cascade depth distribution and its independent root Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVectorPairSpinKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) → Kernel (Fin N → ℝ) (Spin N × Spin N)
  | [], _, _ => fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL)
      (fun j => fieldVectorPairSpinKernel N L ht j ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2
          (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1) i

instance fieldVectorPairSpinKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorPairSpinKernel N L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      let _ := ih ht j
      change IsMarkovKernel (_ ∘ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEndpointSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional Gaussian endpoint kernels before sampling the cavity spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

instance fieldVectorTailEndpointKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    IsMarkovKernel (fieldVectorTailEndpointKernel N L hL) := by
  induction L with
  | nil => change IsMarkovKernel Kernel.id; infer_instance
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance fieldVectorPairEndpointKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorPairEndpointKernel N L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (Kernel.id ×ₖ Kernel.id); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldVectorTailEndpointKernel N (av :: L) hL ×ₖ
        fieldVectorTailEndpointKernel N (av :: L) hL)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      let _ := ih ht j
      change IsMarkovKernel (_ ∘ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLevels
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conditional squared spin means at prescribed magnetization.
The root Gaussian is averaged at the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def magneticLevelAtBias (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh
      (Fin.cast (by rw [scalarFieldIncrements_length]) i)) b

lemma magneticLevelAtBias_mem_unit (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) : magneticLevelAtBias h b i ∈ Icc (0 : ℝ) 1 := by
  have hL := scalarFieldIncrements_positive h
  have hR := fieldScalarSquares_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hb := fieldSpinTransition_bound 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    hv.1 hv.2 (fun z => by rw [abs_of_nonneg (hR.2 z).1]; exact (hR.2 z).2) b
  refine ⟨?_, (le_abs_self _).trans hb⟩
  unfold magneticLevelAtBias fieldSpinTransition
  exact integral_nonneg (fun z => (hR.2 z).1)

lemma magneticLevelAtBias_monotone (h : FieldStep) (b : ℝ) :
    Monotone (magneticLevelAtBias h b) := by
  have hL := scalarFieldIncrements_positive h
  have hR := fieldScalarSquares_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one
  intro i j hij
  apply fieldSpinTransition_mono_test
    0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (hR _).1 (hR _).1
    (fun z => by rw [abs_of_nonneg ((hR _).2 z).1]; exact ((hR _).2 z).2)
    (fun z => by rw [abs_of_nonneg ((hR _).2 z).1]; exact ((hR _).2 z).2)
  intro z
  exact fieldScalarSquares_monotone (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one z hij

def magneticFieldLevel (h : FieldStep) (s : ℝ) : Fin (h.depth + 1) → ℝ :=
  magneticLevelAtBias h (magneticBias h s)

lemma magneticFieldLevel_mem_unit (h : FieldStep) (s : ℝ)
    (i : Fin (h.depth + 1)) : magneticFieldLevel h s i ∈ Icc (0 : ℝ) 1 :=
  magneticLevelAtBias_mem_unit h _ i

lemma magneticFieldLevel_monotone (h : FieldStep) (s : ℝ) :
    Monotone (magneticFieldLevel h s) := magneticLevelAtBias_monotone h _

def magneticFieldPath (h : FieldStep) (s : ℝ) : OverlapPath :=
  fieldLevelPath h (magneticFieldLevel h s) (magneticFieldLevel_monotone h s)
    (magneticFieldLevel_mem_unit h s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarFourJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual finite scalar Ising mean, and every continued square
observable, has the fourth spatial derivative required in the parabolic
comparison. No additional smoothness hypothesis is imposed on the model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_has_bounded_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    ∃ J : MagneticContinuationFourJet,
      J.value = fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i := by
  induction L with
  | nil =>
    refine ⟨logCoshMeanFourJet.square, ?_⟩
    rfl
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨(magneticLogCoshMeanFourJet (av :: L) hL).square, ?_⟩
      change (fun z => ((magneticLogCoshMeanFourJet (av :: L) hL).value z) ^ 2) = _
      have he := congrArg MagneticContinuationJet.value (magneticLogCoshMeanFourJet_eq (av :: L) hL)
      rw [he]
      rfl
    · obtain ⟨J, hJ⟩ := ih ht j
      have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      let P := magneticLogCoshMeanJet L ht
      have hd : ∀ z, HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
          (P.value z) z := hasDerivAt_fieldScalarLogCosh L ht
      refine ⟨J.transition P av.1 av.2 _ hv.1 hv.2 hd, ?_⟩
      change fieldSpinTransition av.1 av.2 _ J.value = _
      rw [hJ]
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSquareJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-level square continuations satisfy every endpoint
hypothesis of the inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSquareFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) : MagneticContinuationFourJet :=
  (fieldScalarSquares_has_bounded_fourJet L hL i).choose

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed derivative of the first spatial derivative of a bounded
finite Gaussian continuation. The proof differentiates actual normalized
averages and identifies coefficients by ordinary derivative uniqueness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatSpatial (P A : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F A.first q.2 + ζ *
    (magneticHeatMean (A.mul P) F ζ q - magneticHeatMean A F ζ q * magneticHeatMean P F ζ q)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint variance/spatial differentiation of the second spatial
derivative. Fourth terminal derivatives suffice; no unproved interchange
of differentiation and Gaussian integration is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatSecond (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  magneticHeatSpatial P A.slope F ζ q + ζ *
    (magneticHeatSpatial P (A.toMagneticContinuationJet.mul P) F ζ q -
      (magneticHeatSpatial P A.toMagneticContinuationJet F ζ q * magneticHeatMean P F ζ q +
        magneticHeatMean A.toMagneticContinuationJet F ζ q * magneticHeatSpatial P P F ζ q))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual drift-free equation for q²Hᵤᵤ along the inverse mean.
All time derivatives come from normalized Gaussian averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal Topology

namespace InvariantIsing

def magneticHeatWeighted (P A : MagneticContinuationFourJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  magneticHeatSecond P.toMagneticContinuationJet A F ζ q -
    magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet F ζ q *
      magneticHeatSecond P.toMagneticContinuationJet P F ζ q / magneticHeatCurvature P.toMagneticContinuationJet F ζ q

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCanonicalVectorMoments
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent canonical endpoint fields have a total second moment
linear in the block size, uniformly over the cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

def fieldCanonicalVectorLaw (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    Measure (Fin N → ℝ) :=
  Measure.pi (fun i => fieldCanonicalEndpointLaw h (b i))

instance fieldCanonicalVectorLaw_probability (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    IsProbabilityMeasure (fieldCanonicalVectorLaw N h b) := by
  unfold fieldCanonicalVectorLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained terminal spin kernel, including measurability
and its exact conditional entropy cost. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set

namespace InvariantIsing

def restrictedSpinKernel {N : ℕ} (S : Finset (Spin N)) : Kernel (Fin N → ℝ) (Spin N) := by
  refine ⟨fun z => restrictedSpinLaw S (fieldEnergy z), ?_⟩
  apply Measure.measurable_of_measurable_coe
  intro T hT
  change Measurable (fun z => cond (fieldVectorSpinKernel N z) S T)
  simp only [cond_apply S.measurableSet]
  exact ((fieldVectorSpinKernel N).measurable_coe S.measurableSet).inv.mul
    ((fieldVectorSpinKernel N).measurable_coe (S.measurableSet.inter hT))

lemma restrictedSpinKernel_markov {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    IsMarkovKernel (restrictedSpinKernel S) :=
  ⟨fun z => restrictedSpinLaw_probability S hS (fieldEnergy z)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension transport for consecutive constrained blocks. The successor
constraint is exactly the base/cavity product, including its cube mass. -/

noncomputable section
open IsingPerceptron

namespace InvariantIsing

def spinDimensionCast {N M : ℕ} (h : N = M) : Spin N ≃ Spin M where
  toFun σ i := σ (Fin.cast h.symm i)
  invFun σ i := σ (Fin.cast h i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed initial remainder followed by repeated constrained blocks.
Adding a new last block preserves this exact finite spin family. -/
noncomputable section
open IsingPerceptron
namespace InvariantIsing

def offsetBlockJoin (r n K : ℕ) : Spin ((r+K*n)+n) ≃ Spin (r+(K+1)*n) :=
  spinDimensionCast (by simp only [Nat.add_mul,Nat.one_mul]; omega)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedDisorderTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def restrictedCavityFullDisorderTest {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, referenceReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    (F U) ∂gaussianCoordinates ∂μ


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-block spin averaging with an arbitrary fixed remainder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def offsetRegularBlockOverlap {n K r depth : ℕ}
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) : ℝ :=
  cavityTotalSpinOverlap ((cavitySpinSplit r (K*n) (σ 0).1).2,
    (cavitySpinSplit r (K*n) (σ 1).1).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaProduct
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica products for the actual simultaneous spectral GG limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def spectralSpinQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    OverlapPath :=
  spectralQuantilePath Q (spectralSpinWeight m)
    (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantileSynchronization
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every continuous synchronized coordinate agrees with its canonical
group quantile under the same total quantile, including atoms. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def spectralGroupQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) : OverlapPath :=
  spectralQuantilePath Q (Pi.single a.castSucc 1) (spectralCoordinate_unit hn a.castSucc)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (t : ℝ) (p : OverlapPath) : ℝ :=
  spectralFunctional (fun x => finiteSpectralSlope ρ eig hρ hρsum (t * x)) p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorNamespace
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian namespaces for the actual fixed-prior model.
Changing Gaussian coordinates preserves its entire pressure law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorNamespacedHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation p.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation p.1) I degree amplitude n v x) p.2

lemma measurable_priorNamespacedHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (Function.uncurry (priorNamespacedHamiltonian eig c I degree amplitude v)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hb : Measurable (fun U : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1) := by
    exact ((Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul
        (1/2 : ℝ)).add_const _
  exact (hb.comp measurable_fst).add (measurable_tensorNamespacedFields_joint I degree amplitude n v x)

def priorNamespacedLog {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x, Real.exp (priorNamespacedHamiltonian eig c I degree amplitude v p x) ∂ν)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorReference
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed-prior Gibbs law and its spectral diagonal tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorNamespacedReference {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability ν (priorNamespacedHamiltonian eig c I degree amplitude v p)

instance priorNamespacedReference_probability {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) :
    IsProbabilityMeasure (priorNamespacedReference ν eig c I degree amplitude v p) :=
  gibbsProbability_probability _ _

lemma measurable_priorNamespacedReference {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorNamespacedReference ν eig c I degree amplitude v) :=
  measurable_gibbsProbability (ν := fun _ => ν) measurable_const
    (measurable_priorNamespacedHamiltonian eig c I degree amplitude v)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFrozenReference
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freezing one actual Gaussian perturbation coordinate with a fixed prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorFrozenBaseEnergy {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) (x : Spin N × LabeledLeaf n) : ℝ :=
  priorNamespacedHamiltonian eig c I degree (Function.update amplitude j 0)
    (fun i => tensorPathProfile I degree n r h i)
    (ω.1,gaussianNamespaceJoin (j+1) (0,ω.2)) x

def priorFrozenReference {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability ν (priorFrozenBaseEnergy eig c I degree amplitude r h j ω)

instance priorFrozenReference_probability {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) :
    IsProbabilityMeasure (priorFrozenReference ν eig c I degree amplitude r h j ω) :=
  gibbsProbability_probability _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorReplicaAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Observable and replica averages for the actual fixed-prior Gibbs measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def priorNamespacedObservableAverage {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) : ℝ :=
  ∫ p : SpecialOrthogonal N × (ℕ → ℝ), ∫ x, D p.1 x
    ∂priorNamespacedReference ν eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p
    ∂μ.prod gaussianCoordinates

def priorNamespacedReplicaAverage {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : SpecialOrthogonal N × (ℕ → ℝ),
    referenceReplicaMean (priorNamespacedReference ν eig c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i) p) (fun _ => 0) (D p.1)
    ∂μ.prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral array generated by a constrained spin/leaf prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

def priorNamespacedArrayLaw {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m + 1)) :=
  spectralArrayLaw (μ.prod gaussianCoordinates)
    (fun p : SpecialOrthogonal N × (ℕ → ℝ) => p.1) measurable_fst I n
    (priorNamespacedReference ν₀ eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i))
    (measurable_priorNamespacedReference ν₀ eig c I degree amplitude (fun i => tensorPathProfile I degree n r h i))


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFiniteGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite constrained-prior spectral Ghirlanda–Guerra residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def priorSpectralGGResidual {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν₀ : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  let avg := fun (q' : ℕ) (F : SpecialOrthogonal N → (Fin q' → Spin N × LabeledLeaf n) → ℝ) =>
    priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h F
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  (q + 1 : ℕ) * avg (q + 1 + 1)
      (fun U τ => D U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) -
    avg (q + 1) D * avg 2 (fun U τ => κ U (τ 1) (τ 0)) -
    avg (q + 1)
      (fun U σ => D U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Log-partition differences and concentration of a selected prior perturbation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorFrozenCGF {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : PriorFrozenData N j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1) I (degree j) n (r j) x) p.2)
    (priorFrozenReference ν eig c I degree amplitude r h j p.1) t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorDiagonalStatistics
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The diagonal observable's actual CGF inherits concentration from
both neighboring finite-prior log partition functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorDiagonalCGF {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (s : ℝ)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1) (I a) x.1 x.1)
    (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p) s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector GG identities in weak limits of actual constrained-prior minimizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

def priorPerturbedArrayLaw {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  priorNamespacedArrayLaw μ ν (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    (fun j : Fin N => enumeratedTreeDegree m j) h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRotationProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained spin/leaf Gibbs probability, with all Haar,
Gaussian and finite-tree disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRotationProbability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    Measure (Spin N × LabeledLeaf depth) :=
  gibbsProbability (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2)
    (cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.2)

instance restrictedRotationProbability_probability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    IsProbabilityMeasure (restrictedRotationProbability S hS eig I u p) :=
  gibbsProbability_probability _ _

lemma measurable_restrictedRotationProbability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (restrictedRotationProbability (depth := depth) S hS eig I u) := by
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2
  let H : Ω × X → ℝ := fun p =>
    cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure (labeledSpinReference depth
      (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (restrictedSpinPrior S hS : Measure (Spin N))).comp measurable_fst.snd
  have hH : Measurable H := measurable_cavityRotationProbabilityHamiltonian eig I u
  exact measurable_gibbsProbability (ν := ν) (H := H) hν hH


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRotationArray
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral array sampled from the actual constrained base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRotationArrayLaw {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  ⟨(disorderReplicaLaw ((μ.prod ρ).prod gaussianCoordinates)
    (restrictedRotationProbability S hS eig I u) (measurable_restrictedRotationProbability S hS eig I u)).map
      (cavitySampledEntryArray (cavityRotationEntry I)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavitySampledEntryArray (cavityRotationEntry I)
        (measurable_cavityRotationEntry I)).aemeasurable).mpr inferInstance⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedZeroTreeArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical constrained array law with the trivial auxiliary tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

instance restrictedZeroTreePrior_probability {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    IsProbabilityMeasure (restrictedZeroTreePrior S hS) := by
  unfold restrictedZeroTreePrior
  exact labeledSpinReference_probability 0 (restrictedSpinPrior S hS : Measure (Spin N)) PUnit.unit

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetEnvelopeLower
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping the actual minimum envelope for a repeated constrained
block gives its unperturbed pressure lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology
namespace InvariantIsing

def offsetPriorObjective {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (r : ℕ)
    (u : Fin (r₀+(q+r)*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ (r₀+(q+r)*n))
    (restrictedZeroTreePrior (offsetBlockConstraint (q+r) R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig (r₀+(q+r)*n)) (c (r₀+(q+r)*n)) (I (r₀+(q+r)*n)) 1 (fun _ => 0) u v

def offsetPriorIncrement {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  let N := r₀+(q+r)*n
  ((N+n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (N+n))
    (restrictedZeroTreePrior (cavityProductSlice (offsetBlockConstraint (q+r) R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC))
    (eig (N+n)) (c (N+n)) (I (N+n)) 1 (fun _ => 0)
    (fun i => cavityBaseAmplitude (u r) i) (v r) -
  (N : ℝ)*priorPerturbationPressureMean (μ N)
    (restrictedZeroTreePrior (offsetBlockConstraint (q+r) R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig N) (c N) (I N) 1 (fun _ => 0) (u r) (v r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetMinimumSequence
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous actual minima at every repetition count. The small
unused dimensions carry bounded placeholders. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetRepeatedPriorObjective {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (r₀+K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ (r₀+K*n))
    (restrictedZeroTreePrior (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig (r₀+K*n)) (c (r₀+K*n)) (I (r₀+K*n)) 1 (fun _ => 0) u v

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProjectorLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained capped logarithmic cavity factor in physical projector
coordinates, including the vanishing quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedProjectorCappedLog {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t cap δ : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (min (t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ * (1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2))
    ∂((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
      (restrictedSpinPrior C hC)).tilted (fun x => cavityProjectorHamiltonian p.1 c u z x.1))
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetPhysicalIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The consecutive prior increment is the original physical constrained
rotation increment, with the same base perturbation in both dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetRotationIncrement {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (Orthogonal N))
    (eig : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (r₀+K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  let N := r₀+K*n
  let S := offsetBlockConstraint K R C
  let hS := offsetBlockConstraint_nonempty R hR C hC
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  (∫ z, restrictedRotationLogMean (cavityProductSlice S C)
    (cavityProductSlice_nonempty S hS C hC) z.2
    (diagonalPerturbedEigenvalues (eig (N+n)) (I (N+n)) v 1)
    (I (N+n)) (cavityBaseAmplitude u) z.1 ∂(μ (N+n)).prod θ) -
  ∫ z, restrictedRotationLogMean S hS z.2
    (diagonalPerturbedEigenvalues (eig N) (I N) v 1)
    (I N) (cavityBaseAmplitude u) z.1 ∂(μ N).prod θ


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperatureFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- An everywhere-defined primitive; at nonnegative temperatures it is exactly
the manuscript's finite-spectrum interaction functional. -/
def finiteTemperatureFunctional (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (t : ℝ) : ℝ :=
  ∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p

@[simp] theorem finiteTemperatureFunctional_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    finiteTemperatureFunctional ρ eig hρ hρsum p 0 = 0 := by
  simp only [finiteTemperatureFunctional, intervalIntegral.integral_same]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TrialGridApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower finite-grid trials approximate each monotone overlap path in L1,
remain below one, and do not increase the entropy functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def lowerGridPath (p : OverlapPath) (n : ℕ) : OverlapPath where
  val := lowerGrid p.val n
  monotone := lowerGrid_monotone p.monotone n
  nonneg s := (lowerGrid_mem (fun u => ⟨p.nonneg u, p.le_one u⟩) n s).1
  le_one s := (lowerGrid_mem (fun u => ⟨p.nonneg u, p.le_one u⟩) n s).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalOrthogonalLaw
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete orthogonal Haar probability from the square Gaussian frame.
This determines the orthogonal orbit law in the Wishart corollary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def orthogonalGaussianLeftHaar (N : ℕ) : Measure (Orthogonal N) :=
  (cavityConditionedFrameLaw N N).map squareFrameOrthogonal

def orthogonalGaussianHaar (N : ℕ) : Measure (Orthogonal N) := (orthogonalGaussianLeftHaar N).inv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite vector-spin common-depth test under the published
marking input. Both the spin conditioning and exponential integrability
are derived for this model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def fieldVectorSpinPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  ∫ p, referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))
    ∂fieldVectorCoordinateLaw N h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual scalar-field spin test before averaging
the Gaussian root and the labeled forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

instance fieldVectorCoordinateLaw_isProbabilityMeasure (N : ℕ) (h : FieldStep) :
    IsProbabilityMeasure (fieldVectorCoordinateLaw N h) := by
  unfold fieldVectorCoordinateLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def fieldSpinPairIntegrand (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldDepthPair
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of the common-level law by the published finite-field
terminal tilt, including the independent scalar-field spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldDepthPairIntegrand (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) (ψ : ℕ → ℝ) : ℝ :=
  referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))

def fieldVectorDepthPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ) (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, fieldDepthPairIntegrand N h z p ψ ∂fieldVectorCoordinateLaw N h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite covariance charts with literal updates
of a field height. The formula is defined without choosing proofs of the
order constraints; whenever the updated heights are admissible it is the
original `fieldValue` of that field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- The literal single-coordinate value, using exactly the Gaussian
recursion of `fieldValue` with the updated height vector. -/
def fieldHeightCoordinateValue (h : FieldStep) (i : Fin (h.depth + 1))
    (t z : ℝ) : ℝ :=
  let r := Function.update h.height i (h.height i + t)
  fieldScalarValue (List.ofFn fun j : Fin (h.depth + 1) =>
    (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j)))
    (fun y => Real.log (Real.cosh y)) z - r (Fin.last h.depth) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded strict-height approximation of an arbitrary finite field.
Every variance increment is increased by the same small scalar. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldRegularized (h : FieldStep) (t : ℝ) : FieldStep :=
  fieldWithHeights h (fieldRegularizedHeight h t)
    (fun i => add_nonneg (h.nonneg i) (mul_nonneg (fieldHeightEpsilon_nonneg t) (Nat.cast_nonneg _)))
    (fun i j hij => add_le_add (h.ordered_height hij)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hij 1)
        (fieldHeightEpsilon_nonneg t)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLogNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field's actual logarithmic normalizer and its Gaussian
recursion, including joint integrability in the root and forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldVectorLogNormalizer (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) : ℝ :=
  Real.log (∫ s : Spin N × LabeledLeaf h.depth,
    Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPairProductLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence across sites of the full common-prefix two-spin law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVectorSitePairKernel (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    Kernel (Fin N → ℝ) (Fin N → Bool × Bool) :=
  (fieldVectorPairSpinKernel N L hL i).map
    (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm

instance fieldVectorSitePairKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorSitePairKernel N L hL i) := by
  unfold fieldVectorSitePairKernel
  exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldZeroIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inserting a zero covariance increment preserves the scalar Ising
value and spin mean. Its adjacent overlap levels are the same. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

/-- The natural-index form of a scalar square. All indices used by the
finite field are at most the length; the terminal extension avoids casts
in zero-increment insertion. -/
def fieldScalarSquareAt : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → ℕ → ℝ → ℝ
  | [], _, b, _ => fun z => (b z) ^ 2
  | av :: L, F, b, 0 => fun z => (fieldScalarMean (av :: L) F b z) ^ 2
  | av :: L, F, b, i + 1 =>
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquareAt L F b i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorContactContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the constrained-prior contact pressure, including
zero covariance increments and both complete perturbation amplitudes. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def priorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (p : TensorContactParameter N m n) : ℝ :=
  priorPerturbationPressureMean μ ν eig c I p.1 (finiteFieldPath p.2.1) p.2.2.1 p.2.2.2 -
    finiteFieldPath p.2.1 n/2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFieldDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right field derivative of the actual centered constrained-prior
pressure, allowing zero and repeated field-variance levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def priorNamespacedMeanPressure {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (N : ℝ)⁻¹*(∫ p, priorNamespacedLog ν eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) p ∂μ.prod gaussianCoordinates)-h n/2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorLabeledDepthMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite labeled common-depth mean and its full rooted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal BigOperators

namespace InvariantIsing

def priorCavityLabeledDepthMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ)
    (ω : CavityLabeledDisorder d n) : ℝ :=
  referenceReplicaMean (cavityLabeledPriorKernel n R π ω)
    (fun x => cavityLabeledPotential n K L C (ω,x))
    (fun σ : Fin 2 → CavityLabeledState d k n => a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorLabeledModelSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original two-replica spin test, averaged in the fixed-state
finite model used for capped numerator comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal BigOperators

namespace InvariantIsing

def priorCavityLabeledSpinDepthMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) (j : Fin k)
    (ω : CavityLabeledDisorder d n) : ℝ :=
  referenceReplicaMean (cavityLabeledPriorKernel n R π ω)
    (fun x => cavityLabeledPotential n K L C (ω,x))
    (fun σ : Fin 2 → CavityLabeledState d k n => a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1) *
      (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorCascadePressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cascade-enriched pressure for a deterministic spin prior.
Normalized magnetization slices are allowed, while the cascade remains
quenched and is averaged only after taking the logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorNamespacedLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) : ℝ :=
  priorNamespacedLog (labeledSpinReference n π p.1.2) eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) (p.1.1,p.2)

def spinPriorNamespacedReference {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) : Measure (Spin N × LabeledLeaf n) :=
  priorNamespacedReference (labeledSpinReference n π p.1.2) eig c I degree amp
    (fun i => tensorPathProfile I degree n r h i) (p.1.1,p.2)

def spinPriorMeanPressure {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) : ℝ :=
  (N : ℝ)⁻¹*(∫ p, spinPriorNamespacedLog π eig c I degree amp r h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)-h n/2

lemma measurable_spinPriorNamespacedReference {N m k n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (spinPriorNamespacedReference (n := n) π eig c I degree amp r h) := by
  have hν : Measurable (fun p : TensorFlatDisorder N n => labeledSpinReference n π p.1.2) :=
    (measurable_labeledSpinReference_general n π).comp measurable_fst.snd
  exact measurable_gibbsProbability hν (measurable_tensorNamespacedHamiltonian eig c I degree amp n r h)

instance spinPriorNamespacedReference_probability {N m k n : ℕ}
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) :
    IsProbabilityMeasure (spinPriorNamespacedReference π eig c I degree amp r h p) := by
  unfold spinPriorNamespacedReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFrozenReference
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One independent Gaussian coordinate frozen inside the actual constrained
cascade model. The cascade tree remains part of the external disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFrozenReference {N m k : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n π ω.1.2)
    (tensorFrozenBaseEnergy eig c I degree amp n r h j ω)

instance spinPriorFrozenReference_probability {N m k : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ)
    (h : ℕ → ℝ) (j : Fin k) (ω : TensorFrozenData N n j) :
    IsProbabilityMeasure (spinPriorFrozenReference π eig c I degree amp n r h j ω) :=
  gibbsProbability_probability _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorReplicaAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite replica averages under the actual namespaced tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def spinPriorReplicaAverage {N m k q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n,
    referenceReplicaMean (spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h p)
      (fun _ => 0) (D p.1.1)
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorArrayLaw {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m + 1)) :=
  spectralArrayLaw ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    (fun p : TensorFlatDisorder N n => p.1.1) measurable_fst.fst I n
    (spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h)
    (measurable_spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContact
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity for the actual cascade-enriched spin-prior contact
pressure, with the quenched cascade retained in the pressure integral. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorContactPressure {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (p : TensorContactParameter N m n) : ℝ :=
  spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
    b (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint contact minima for the actual cascade-enriched spin prior.
The pressure averages the logarithm over the quenched cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def spinPriorPerturbationPressureMean {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    b (fun j : Fin N => enumeratedTreeDegree m j) h+h n/2

def spinPriorPerturbationObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ)
    (t : ℝ) (h : ℕ → ℝ) (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v+
    ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2+∑ a, (v a-3/2)^2

def spinPriorContactObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (p : TensorContactParameter N m n) : ℝ :=
  -spinPriorContactPressure μ π eig c I b p - (∑ i, w i*finiteFieldPath p.2.1 i)/2 +
    S+V p.1 + ∑ j : Fin N, perturbationWeight j*(p.2.2.1 j-3/2)^2 +
    ∑ a, (p.2.2.2 a-3/2)^2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFieldDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
actual namespaced tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorFieldCGFMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : TensorFlatDisorder N n × (ℕ → ℝ),
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) z.2)
      (spinPriorNamespacedReference (n := n) π eig c I degree amp treeDegree h z.1) (Real.sqrt a)
    ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod
      gaussianCoordinates

def spinPriorFieldInsertionMean {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) : ℝ :=
  spinPriorMeanPressure (n := n) μ π eig c I degree amp b treeDegree h +
    spinPriorFieldCGFMean μ π eig c I degree amp n b treeDegree h g a / N - a * g n / 2


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFieldInsertionLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian insertion for the actual constrained cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorFieldInsertedLog {N m k : ℕ} (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ)
    (p : TensorFlatDisorder N n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1 x +
      Real.sqrt a * cylinderField (tensorLinearCoefficients n g x) p.2)
    ∂labeledSpinReference n π p.1.1.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorContactField
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field-coordinate inequality at the actual joint minimum. Tied and
zero covariance levels are allowed; only the upper cap must be inactive. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorContactFieldObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ)
    (t : ℝ) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ) (h : ℕ → ℝ) : ℝ :=
  -spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    b (fun j => enumeratedTreeDegree m j) h - (∑ i, w i * h i) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorDiagonalStatistics
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal CGF and pressure concentration for the actual constrained
cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorDiagonalCGF {N m k : ℕ} (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ) (a : Fin m)
    (s : ℝ) (p : TensorFlatDisorder N n) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
    (spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude r h p) s


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorTemperatureDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature derivative for the actual constrained cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def spinPriorObservableAverage {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → Spin N × LabeledLeaf n → ℝ) : ℝ :=
  ∫ p : TensorFlatDisorder N n, ∫ x, D p.1.1 x
    ∂spinPriorNamespacedReference π eig c I degree amp r h p
    ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFiniteGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite constrained-prior spectral Ghirlanda–Guerra residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spinPriorSpectralGGResidual {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  let avg := fun (q' : ℕ) (F : SpecialOrthogonal N → (Fin q' → Spin N × LabeledLeaf n) → ℝ) =>
    spinPriorReplicaAverage μ π eig c I degree amplitude n b r h F
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  (q + 1 : ℕ) * avg (q + 1 + 1)
      (fun U τ => D U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) -
    avg (q + 1) D * avg 2 (fun U τ => κ U (τ 1) (τ 0)) -
    avg (q + 1)
      (fun U σ => D U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorLabeledMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional cascade moments for the actual tensor field with an arbitrary
probability spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorCascadeValue {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  energyRecursion n b (fun i => tensorEnergyMarkLaw U I degree amp (v i)) π
    (tensorSpinBaseEnergy eig U c I degree amp z)

def spinPriorLabeledLog {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (p : TensorLabeledData N n) : ℝ :=
  Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amp n z p x)
    ∂labeledSpinReference n π p.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFlatVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual root/cascade fluctuations and their flat Gaussian realization,
uniformly over probability spin priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFlatLog {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n,
    Real.exp (rotatedEnergy eig U x.1+fieldEnergy c x.1+
      cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
    ∂labeledSpinReference n π p.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFlatLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian namespace changes preserve the constrained, quenched cascade
logarithm, including its full probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorJointFlatLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) (p : TensorFlatDisorder N n) : ℝ :=
  priorTensorLog (labeledSpinReference n π p.1.2) eig c I degree amp v (p.1.1,p.2)

def spinPriorProfileLog {N m k n : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) (p : TensorFlatDisorder N n) : ℝ :=
  priorNamespacedLog (labeledSpinReference n π p.1.2) eig c I degree amp v (p.1.1,p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen Gaussian cumulants in the actual constrained cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFrozenCGF {N m k : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ)
    (p : TensorFrozenData N n j × (ℕ → ℝ)) : ℝ :=
  cgf (fun x => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2)
    (spinPriorFrozenReference π eig c I degree amp n r h j p.1) t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorLeafTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cascade prefix law retains an arbitrary deterministic spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal
namespace InvariantIsing

def spinPriorLabeledReference {N : ℕ} (π : Measure (Spin N)) (n : ℕ)
    (p : TensorLabeledData N n) : Measure (Spin N × LabeledLeaf n) :=
  labeledSpinReference n π p.1

instance spinPriorLabeledReference_probability {N : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (n : ℕ) (p : TensorLabeledData N n) :
    IsProbabilityMeasure (spinPriorLabeledReference π n p) := by
  unfold spinPriorLabeledReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorLimitingGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector GG identities in weak limits of actual constrained-prior minimizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

def spinPriorPerturbedArrayLaw {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (h : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  spinPriorArrayLaw μ π (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u) n b
    (fun j : Fin N => enumeratedTreeDegree m j) h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialValue
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded continuous polynomial observables on the physical rotation group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma continuous_haarPolynomialValue {N : ℕ} (p : MatrixPolynomial N) :
    Continuous (haarPolynomialValue p) := by
  have hm : Continuous (fun U : SpecialOrthogonal N =>
      fun ij : Fin N × Fin N => (U : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2) := by
    exact continuous_pi fun ij => (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val)
  exact p.continuous_eval.comp hm

lemma haarPolynomialValue_bound {N : ℕ} (p : MatrixPolynomial N) :
    ∃ B : ℝ, ∀ U : SpecialOrthogonal N, ‖haarPolynomialValue p U‖ ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_haarPolynomialValue p).continuousOn
  exact ⟨B,fun U => hB U (Set.mem_univ U)⟩

lemma haarPolynomialValue_integrable {N : ℕ} (p : MatrixPolynomial N)
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] :
    Integrable (haarPolynomialValue p) μ := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  exact Integrable.of_bound (continuous_haarPolynomialValue p).measurable.aestronglyMeasurable
    B (ae_of_all μ hB)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact preservation of Haar means by the polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialMean {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] :
    MatrixPolynomial N →ₗ[ℝ] ℝ where
  toFun p := ∫ U, haarPolynomialValue p U ∂μ
  map_add' p q := by
    change (∫ U, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (p+q) ∂μ) = _
    simp only [map_add]
    exact integral_add (haarPolynomialValue_integrable p μ) (haarPolynomialValue_integrable q μ)
  map_smul' c p := by
    change (∫ U, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (c • p) ∂μ) = _
    simp only [map_smul]
    exact integral_smul c _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma reflectionNormalSquare_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (reflectionNormalSquare v w) (reflectionNormalSquareDeriv v w t) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (reflectionNormalSegment_hasDerivAt v w t i).pow 2
  refine hd.congr_deriv (Eq.symm ?_)
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_ofNat]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionSegmentDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entry derivatives along a nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma reflectionSegmentMatrix_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ)
    (ht : reflectionNormalSegment v w t ≠ 0) (i j : Fin N) :
    HasDerivAt (fun s => reflectionSegmentMatrix v w s i j)
      (reflectionSegmentDerivative v w t i j) t := by
  have hq : reflectionNormalSquare v w t ≠ 0 := by
    rw [reflectionNormalSquare_eq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ht)
  have hd := (hasDerivAt_const t ((1 : Matrix (Fin N) (Fin N) ℝ) i j)).sub
    ((((reflectionNormalSegment_hasDerivAt v w t i).const_mul 2).mul
      (reflectionNormalSegment_hasDerivAt v w t j)).div
      (reflectionNormalSquare_hasDerivAt v w t) hq)
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    change rotationMatrix (hyperplaneReflection (reflectionNormalSegment v w s)) i j =
      (1 : Matrix (Fin N) (Fin N) ℝ) i j-
        2*reflectionNormalSegment v w s i*reflectionNormalSegment v w s j /
          reflectionNormalSquare v w s
    rw [reflectionNormalSquare_eq,rotationMatrix_reflection_apply]
  · dsimp only [reflectionSegmentDerivative,Matrix.of_apply]
    simp only [Pi.mul_apply]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionPairCurve
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine special-orthogonal curve for a pair of hyperplane reflections. -/
noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma reflectionPairCurve_hasDerivAt {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) (t : ℝ) (ht : reflectionNormalSegment v w t ≠ 0) (i j : Fin N) :
    HasDerivAt (fun s => (reflectionPairCurve v w hw s : Matrix (Fin N) (Fin N) ℝ) i j)
      ((reflectionSegmentDerivative v w t*rotationMatrix (hyperplaneReflection w)) i j) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (reflectionSegmentMatrix_hasDerivAt v w t ht i k).mul_const
      (rotationMatrix (hyperplaneReflection w) k j)
  have hn : ∀ᶠ s in 𝓝 t, reflectionNormalSegment v w s ≠ 0 := by
    have hc : Continuous (reflectionNormalSegment v w) := by
      unfold reflectionNormalSegment
      fun_prop
    exact hc.continuousAt.eventually_ne ht
  have he : (fun s => (reflectionPairCurve v w hw s : Matrix (Fin N) (Fin N) ℝ) i j) =ᶠ[𝓝 t]
      fun s => ∑ k, reflectionSegmentMatrix v w s i k*rotationMatrix (hyperplaneReflection w) k j := by
    filter_upwards [hn] with s hs
    simp only [reflectionPairCurve,dite_eq_left hs,reflectionPair,Matrix.mul_apply,reflectionSegmentMatrix]
  exact hd.congr_of_eventuallyEq he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionPairPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero reflection pair admits a differentiable curve to the identity. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

def reflectionPairPath {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : 0 ≤ inner ℝ v w) : HaarDifferentiableCurve N where
  value := reflectionPairCurve v w hw
  velocity := fun t => reflectionSegmentDerivative v w t*rotationMatrix (hyperplaneReflection w)
  hasDeriv := fun t ht i j => reflectionPairCurve_hasDerivAt v w hw t
    (reflectionNormalSegment_nonzero v w hv hw hvw ht) i j
  continuous_velocity := by
    intro i j
    simp only [Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun k _ =>
      (continuousOn_reflectionSegmentDerivative v w hv hw hvw i k).mul continuousOn_const

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatEntropy
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy dissipation along the actual positive polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

def haarHeatEntropy {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : haarPolynomialSpace N d) (t : ℝ) : ℝ :=
  ∫ U, haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U*
    Real.log (haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments and their derivatives for polynomial observables on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

def haarPolynomialMoment {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (p : MatrixPolynomial N) (t : ℝ) : ℝ :=
  ∫ U, Real.exp (t*haarPolynomialValue p U) ∂μ

def haarPolynomialMomentDerivative {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) (t : ℝ) : ℝ :=
  ∫ U, haarPolynomialValue p U*Real.exp (t*haarPolynomialValue p U) ∂μ

@[simp] lemma haarPolynomialMoment_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) : haarPolynomialMoment μ p 0 = 1 := by
  simp [haarPolynomialMoment]

@[simp] lemma haarPolynomialMomentDerivative_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) :
    haarPolynomialMomentDerivative μ p 0 = ∫ U, haarPolynomialValue p U ∂μ := by
  simp only [haarPolynomialMomentDerivative,zero_mul,Real.exp_zero,mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedTailSpinKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spin law obtained by successively sampling the constrained
Gaussian recursion and then its terminal Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedTailSpinKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) →
      Kernel (Fin N → ℝ) (Spin N)
  | 0, _, _, _ => restrictedSpinKernel S
  | n + 1, b, v, hb =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    restrictedTailSpinKernel hN S hS n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1

instance restrictedTailSpinKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) : IsMarkovKernel (restrictedTailSpinKernel hN S hS n b v hb) := by
  induction n generalizing b v with
  | zero => exact restrictedSpinKernel_markov S hS
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let _ := ih bs vs hbs
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairSpinKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two constrained spins sampled independently after a prescribed common
Gaussian prefix. The common prefix is retained in the actual kernel law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedPairSpinKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) → Fin (n + 1) →
      Kernel (Fin N → ℝ) (Spin N × Spin N)
  | 0, _, _, _, _ => restrictedSpinKernel S ×ₖ restrictedSpinKernel S
  | n + 1, b, v, hb, i =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let hbs := fun j hj => hb (j + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    Fin.cases (restrictedTailSpinKernel hN S hS (n + 1) b v hb ×ₖ
        restrictedTailSpinKernel hN S hS (n + 1) b v hb)
      (fun j => restrictedPairSpinKernel hN S hS n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1) i

instance restrictedPairSpinKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) :
    IsMarkovKernel (restrictedPairSpinKernel hN S hS n b v hb i) := by
  induction n generalizing b v with
  | zero =>
    let _ := restrictedSpinKernel_markov S hS
    change IsMarkovKernel (restrictedSpinKernel S ×ₖ restrictedSpinKernel S)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (_ ×ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let _ := ih bs vs hbs j
      change IsMarkovKernel (_ ∘ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional coordinate means in the constrained block and their
actual two-spin interpretation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedCoordinateMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (j : Fin N) (z : Fin N → ℝ) : ℝ :=
  ∫ σ, spinValue (σ j) ∂restrictedTailSpinKernel hN S hS n b v hb z

def restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j)
    (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) : ℝ :=
  ∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j) ∂restrictedPairSpinKernel hN S hS n b v hb i z

lemma measurable_restrictedCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (j : Fin N) :
    Measurable (restrictedCoordinateMean hN S hS n b v hb j) := by
  have hm : Measurable (fun p : (Fin N → ℝ) × Spin N => spinValue (p.2 j)) :=
    (measurable_of_finite (fun σ : Spin N => spinValue (σ j))).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := restrictedTailSpinKernel hN S hS n b v hb)).measurable

lemma measurable_restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) :
    Measurable (restrictedPairCoordinateMean hN S hS n b v hb i j) := by
  have hm : Measurable (fun p : (Fin N → ℝ) × (Spin N × Spin N) =>
      spinValue (p.2.1 j) * spinValue (p.2.2 j)) :=
    (measurable_of_finite (fun σ : Spin N × Spin N => spinValue (σ.1 j) * spinValue (σ.2 j))).comp measurable_snd
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := restrictedPairSpinKernel hN S hS n b v hb i)).measurable

lemma restrictedCoordinateMean_bound {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (j : Fin N) (z : Fin N → ℝ) :
    |restrictedCoordinateMean hN S hS n b v hb j z| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := restrictedTailSpinKernel hN S hS n b v hb z)
    (f := fun σ => spinValue (σ j)) (Filter.Eventually.of_forall (fun σ => by
      simp only [Real.norm_eq_abs, abs_spinValue, le_refl]))
  simpa only [restrictedCoordinateMean, Real.norm_eq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, mul_one] using he

lemma restrictedPairCoordinateMean_bound {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    |restrictedPairCoordinateMean hN S hS n b v hb i j z| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := restrictedPairSpinKernel hN S hS n b v hb i z)
    (f := fun σ => spinValue (σ.1 j) * spinValue (σ.2 j))
    (Filter.Eventually.of_forall (fun σ => by simp only [Real.norm_eq_abs, abs_mul, abs_spinValue, mul_one, le_refl]))
  simpa only [restrictedPairCoordinateMean, Real.norm_eq_abs, measureReal_def,
    measure_univ, ENNReal.toReal_one, mul_one] using he

lemma restrictedPairSpinKernel_zero {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) :
    restrictedPairSpinKernel hN S hS n b v hb 0 =
      restrictedTailSpinKernel hN S hS n b v hb ×ₖ restrictedTailSpinKernel hN S hS n b v hb := by
  cases n <;> rfl

lemma restrictedPairCoordinateMean_zero {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (j : Fin N) (z : Fin N → ℝ) :
    restrictedPairCoordinateMean hN S hS n b v hb 0 j z =
      (restrictedCoordinateMean hN S hS n b v hb j z) ^ 2 := by
  rw [restrictedPairCoordinateMean, restrictedPairSpinKernel_zero, Kernel.prod_apply,
    integral_prod_mul (fun σ : Spin N => spinValue (σ j)) (fun σ : Spin N => spinValue (σ j))]
  rw [pow_two]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairRecursion
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-step recursion for the actual constrained one- and two-spin means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma integrable_restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (restrictedPairCoordinateMean hN S hS n b v hb i j) μ := by
  apply Integrable.of_bound (measurable_restrictedPairCoordinateMean hN S hS n b v hb i j).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using restrictedPairCoordinateMean_bound hN S hS n b v hb i j z)

lemma restrictedCoordinateMean_succ {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n + 1, 0 < b i) (j : Fin N) (z : Fin N → ℝ) :
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    restrictedCoordinateMean hN S hS (n + 1) b v hb j z =
      ∫ y, restrictedCoordinateMean hN S hS n bs vs hbs j y
        ∂vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
          (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1 z := by
  dsimp only
  change (∫ σ : Spin N, spinValue (σ j) ∂(_ ∘ₖ _) z) = _
  rw [Kernel.integral_comp (Integrable.of_finite)]
  rfl

lemma restrictedPairCoordinateMean_succ {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n + 1, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    let bs := fun k => b (k + 1)
    let vs := fun k => v (k + 1)
    let hbs := fun k hk => hb (k + 1) (by omega)
    restrictedPairCoordinateMean hN S hS (n + 1) b v hb i.succ j z =
      ∫ y, restrictedPairCoordinateMean hN S hS n bs vs hbs i j y
        ∂vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
          (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1 z := by
  dsimp only
  change (∫ σ : Spin N × Spin N, spinValue (σ.1 j) * spinValue (σ.2 j) ∂(_ ∘ₖ _) z) = _
  rw [Kernel.integral_comp (Integrable.of_finite)]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and conditional Jensen monotonicity of the actual
constrained block's coordinate overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedPairCoordinateMean_nonneg {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    0 ≤ restrictedPairCoordinateMean hN S hS n b v hb i j z := by
  induction n generalizing b v z with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi, restrictedPairCoordinateMean_zero]
    positivity
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [restrictedPairCoordinateMean_zero]
      positivity
    · rw [restrictedPairCoordinateMean_succ]
      exact integral_nonneg (fun y => ih _ _ _ k y)

lemma restrictedPairCoordinateMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (j : Fin N) (z : Fin N → ℝ) :
    Monotone (fun i => restrictedPairCoordinateMean hN S hS n b v hb i j z) := by
  induction n generalizing b v z with
  | zero =>
    intro i k _
    have hik : i = k := Fin.ext (by omega)
    subst k
    exact le_rfl
  | succ n ih =>
    let bs := fun k => b (k + 1)
    let vs := fun k => v (k + 1)
    have hbs : ∀ k < n, 0 < bs k := fun k hk => hb (k + 1) (by omega)
    let K := vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
      (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1
    let M := restrictedCoordinateMean hN S hS n bs vs hbs j
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.castSucc_zero, restrictedPairCoordinateMean_zero,
        restrictedCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      simp_rw [restrictedPairCoordinateMean_zero]
      have hm : MemLp M 2 (K z) := MemLp.of_bound
        (measurable_restrictedCoordinateMean hN S hS n bs vs hbs j).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs] using restrictedCoordinateMean_bound hN S hS n bs vs hbs j y))
      have hv := variance_nonneg M (K z)
      rw [variance_eq_sub hm] at hv
      exact sub_nonneg.mp hv
    · change restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.castSucc.succ j z ≤
        restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.succ.succ j z
      rw [restrictedPairCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      apply integral_mono
        (integrable_restrictedPairCoordinateMean hN S hS n bs vs hbs k.castSucc j (K z))
        (integrable_restrictedPairCoordinateMean hN S hS n bs vs hbs k.succ j (K z))
      intro y
      exact ih bs vs hbs y (by change k.val ≤ k.val + 1; omega)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPairRootEntropy
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared Gaussian root preserves the pair entropy estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal

namespace InvariantIsing

def restrictedLevelSpinPair {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (b : Fin N → ℝ) (i : Fin (h.depth + 1)) : Measure (Spin N × Spin N) :=
  restrictedPairSpinKernel hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
    (fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1) i ∘ₘ
      Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))

instance restrictedLevelSpinPair_probability {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : IsProbabilityMeasure (restrictedLevelSpinPair hN S hS h b i) := by
  unfold restrictedLevelSpinPair
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPairComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-free comparison of the actual constrained two-spin mean
with the site-average magnetic field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

def restrictedBlockPairMean {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (b : Fin N → ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  (N : ℝ)⁻¹ * ∫ p, ∑ j, spinValue (p.1 j) * spinValue (p.2 j)
    ∂restrictedLevelSpinPair hN S hS h b i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedBlockOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained block overlap levels form an admissible path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal BigOperators

namespace InvariantIsing

lemma restrictedBlockPairMean_eq_average {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) :
    restrictedBlockPairMean hN S hS h b i = (N : ℝ)⁻¹ * ∑ j,
      ∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
        (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
        ∂Measure.pi (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0))) := by
  rw [restrictedBlockPairMean, integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold restrictedLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  rfl

lemma restrictedBlockPairMean_mem_unit {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : restrictedBlockPairMean hN S hS h b i ∈ Icc (0 : ℝ) 1 := by
  rw [restrictedBlockPairMean_eq_average]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi (j : Fin N) : (∫ z,
      restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
        (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
        ∂Measure.pi (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0)))) ∈
      Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg (fun z => restrictedPairCoordinateMean_nonneg hN S hS _ _ _ _ i j z)
    · calc
        _ ≤ ∫ _z, (1 : ℝ) ∂Measure.pi
            (fun l => gaussianReal (b l) (NNReal.mk (h.height 0) (h.nonneg 0))) :=
          integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
            (integrable_const _) (fun z => (le_abs_self _).trans
              (restrictedPairCoordinateMean_bound hN S hS _ _ _ _ i j z))
        _ = 1 := by simp
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le) (Finset.sum_nonneg (fun j _ => (hi j).1))
  · calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hi j).2)) (inv_nonneg.mpr hn.le)
      _ = 1 := by simp [hn.ne']

lemma restrictedBlockPairMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    Monotone (restrictedBlockPairMean hN S hS h b) := by
  intro i k hik
  rw [restrictedBlockPairMean_eq_average, restrictedBlockPairMean_eq_average]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
    (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ k j _)
    (fun z => restrictedPairCoordinateMean_monotone hN S hS _ _ _ _ j z hik)

def restrictedBlockOverlapPath {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) : OverlapPath :=
  fieldLevelPath h (restrictedBlockPairMean hN S hS h (fun _ => 0))
    (restrictedBlockPairMean_monotone hN S hS h _)
    (restrictedBlockPairMean_mem_unit hN S hS h _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical site-average overlap path and its uniform comparison
with the original constrained-block overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def magneticBlockLevel {N : ℕ} (h : FieldStep) (m : Fin N → ℝ)
    (i : Fin (h.depth + 1)) : ℝ := (N : ℝ)⁻¹ * ∑ j, magneticFieldLevel h (m j) i

lemma magneticBlockLevel_mem_unit {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (m : Fin N → ℝ) (i : Fin (h.depth + 1)) : magneticBlockLevel h m i ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun j _ => (magneticFieldLevel_mem_unit h (m j) i).1))
  · calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun j _ => (magneticFieldLevel_mem_unit h (m j) i).2))
          (inv_nonneg.mpr hn.le)
      _ = 1 := by simp [hn.ne']

lemma magneticBlockLevel_monotone {N : ℕ} (h : FieldStep) (m : Fin N → ℝ) :
    Monotone (magneticBlockLevel h m) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ => magneticFieldLevel_monotone h (m k) hij)) (by positivity)

def magneticBlockPath {N : ℕ} (hN : 0 < N) (h : FieldStep) (m : Fin N → ℝ) : OverlapPath :=
  fieldLevelPath h (magneticBlockLevel h m) (magneticBlockLevel_monotone h m)
    (magneticBlockLevel_mem_unit hN h m)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldFamily
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the joint finite-height derivatives with the actual
physical mean and curvature at every bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Classical
open scoped Topology

namespace InvariantIsing

/-- The unique interior minimizing bias for the actual literal height vector. -/
def magneticHeightBias (h : FieldStep) (s : ℝ) (r : Fin (h.depth + 1) → ℝ) : ℝ :=
  if hr : r ∈ fieldStrictHeightCone h.depth then
    magneticBias (fieldStepOfStrictHeights h r hr) s else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted overlap path for the same field groups as the magnetic
variational functional. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal
namespace InvariantIsing

def magneticGroupLevel {A : Type*} [Fintype A] (γ mag : A → ℝ) (h : FieldStep)
    (i : Fin (h.depth+1)) : ℝ := ∑ a, γ a * magneticFieldLevel h (mag a) i

lemma magneticGroupLevel_mem_unit {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (h : FieldStep) (i : Fin (h.depth+1)) : magneticGroupLevel γ mag h i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hγ a) (magneticFieldLevel_mem_unit h (mag a) i).1
  · calc
      _ ≤ ∑ a, γ a * 1 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (magneticFieldLevel_mem_unit h (mag a) i).2 (hγ a)
      _ = 1 := by simpa only [mul_one] using hγsum

lemma magneticGroupLevel_monotone {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (h : FieldStep) :
    Monotone (magneticGroupLevel γ mag h) := by
  intro i j hij
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (magneticFieldLevel_monotone h (mag a) hij) (hγ a)

def magneticGroupPath {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (h : FieldStep) : OverlapPath :=
  fieldLevelPath h (magneticGroupLevel γ mag h) (magneticGroupLevel_monotone γ mag hγ h)
    (magneticGroupLevel_mem_unit γ mag hγ hγsum h)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticLevelDerivative
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiability of the physical conditional square levels at fixed
magnetization, including the change in the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

def magneticHeightLevel (h : FieldStep) (s : ℝ)
    (r : Fin (h.depth + 1) → ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  if hr : r ∈ fieldStrictHeightCone h.depth then
    magneticFieldLevel (fieldStepOfStrictHeights h r hr) s i else 0

def magneticHeightSchur (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (s : ℝ) (r : Fin (h.depth + 1) → ℝ) (i j : Fin (h.depth + 1)) : ℝ :=
  F.PP i j (r, magneticHeightBias h s r) -
    F.PX i (r, magneticHeightBias h s r) * F.PX j (r, magneticHeightBias h s r) /
      F.XX (r, magneticHeightBias h s r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal scaled inverse curvature used in the radial comparison.
Time is physical variance; its scaling yields the coefficient αζ. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScaledClosedCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarCurvature (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarSlope (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarSecond (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (magneticScaledClosedCurvature L hL α ζ p) ^ 2 / 2 * magneticScaledClosedSecond L hL α ζ p +
    ((α : ℝ) * ζ) * (magneticScaledClosedCurvature L hL α ζ p) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual square continuation in the rescaled physical variance.
Its diffusion coefficient is the rescaled inverse curvature. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScaledSquareJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1)) :
    MagneticContinuationJet :=
  (magneticScalarSquareFourJet (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL)
    (Fin.cast (by rw [fieldScaleIncrements_length]) i)).toMagneticContinuationJet

def magneticScaledSquareContinuation (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuation (fieldScaleIncrements α L)
    (magneticScaledSquareJet L hL α i) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuationSlope (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuationSecond (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (magneticScaledClosedCurvature L hL α ζ p) ^ 2 / 2 *
    magneticScaledSquareSecond L hL α i ζ p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProjectorCavity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cavity observable as a measurable function of the
physical labeled projectors, selected frame and small coefficient blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def restrictedProjectorCavityMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
      (restrictedSpinPrior Cset hCset))
    (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
      t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
    {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCanonicalGroupCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original full-system cutoff and its actual fresh-group Gibbs
representation have the same limit after deterministic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Matrix Topology

namespace InvariantIsing

def restrictedCanonicalGroupCutoffMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) (hk : ∀ a, d ≤ k a)
    (μ : Measure (Orthogonal N))
    (η : Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k g a)))
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t D : ℝ) (B : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) : ℝ :=
  let E := cavityBaseGroupEquiv k e g
  let A := cavityCanonicalGroupFrame k e g hk
  ∫ V, ∫ W, ∫ z, cavityWeightedReplicaMean
    (((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
          (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (restrictedSpinPrior Cset hCset))
    ({x | 1+‖cavitySelectedSiteProjection (fun j => (g j,j))
      (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
      (cavityGroupHaarFrames A W) x.1.1‖^2 ≤ D}.indicator (fun x =>
        Real.exp (t*cavityLogFactor B.1 B.2.1 B.2.2
          (cavitySelectedSiteProjection (fun j => (g j,j))
            (cavityGroupSpinCoordinates (cavityBaseGroupDimension k g) E V)
            (cavityGroupHaarFrames A W) x.1.1) x.2))) F ∂gaussianCoordinates ∂η ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedHaarLogObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame capped logarithm with its actual constrained cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] (C : Finset (Spin n)) (hC : C.Nonempty) (ν : Ω → Measure X)
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) : ℝ :=
  Real.log (∫ x, Real.exp
    (min (t*cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2
      (cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1) x.2) cap -
      δ*(1+‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^2))
    ∂(ν p.1).prod (restrictedSpinPrior C hC : Measure (Spin n)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCanonicalHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained base Gibbs law and independent fresh group frames
in the actual canonical capped logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def restrictedCanonicalHaarLog {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) : ℝ :=
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  restrictedHaarLogObservable C hC
    (restrictedRotationProbability S hS eig (cavitySpectralGroup (fun i => (E.symm i).1)) u)
    (fun j => (a₀ j,j)) (cavityRotationVectors dims E)
    (cavityCanonicalGroupFrame k e a₀ hk) (fun _ => B) t cap δ p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedCoordinateOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate overlap paths for the actual constrained scalar-field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def restrictedCoordinatePairMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep)
    (j : Fin N) (i : Fin (h.depth+1)) : ℝ :=
  ∫ z, restrictedPairCoordinateMean hN S hS h.depth (chainExponent h.cut) (fieldStepVariance h)
    (fun l hl => ((chainExponent_admissible h.ordered_cut h.first h.last).1 l hl).1) i j z
    ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))

lemma restrictedCoordinatePairMean_mem_unit {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N)
    (i : Fin (h.depth+1)) : restrictedCoordinatePairMean hN S hS h j i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun z => restrictedPairCoordinateMean_nonneg hN S hS _ _ _ _ i j z)
  · calc
      _ ≤ ∫ _z, (1 : ℝ) ∂(vectorGaussianLaw N
          (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ)) :=
        integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
          (integrable_const _) (fun z => (le_abs_self _).trans
            (restrictedPairCoordinateMean_bound hN S hS _ _ _ _ i j z))
      _ = 1 := by simp

lemma restrictedCoordinatePairMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N) :
    Monotone (restrictedCoordinatePairMean hN S hS h j) := by
  intro i k hik
  exact integral_mono (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ i j _)
    (integrable_restrictedPairCoordinateMean hN S hS _ _ _ _ k j _)
    (fun z => restrictedPairCoordinateMean_monotone hN S hS _ _ _ _ j z hik)

def restrictedCoordinateOverlapPath {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (j : Fin N) : OverlapPath :=
  fieldLevelPath h (restrictedCoordinatePairMean hN S hS h j)
    (restrictedCoordinatePairMean_monotone hN S hS h j)
    (restrictedCoordinatePairMean_mem_unit hN S hS h j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedEndpointKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual constrained Gaussian endpoint kernels. Sampling terminal
constrained spins commutes with the shared-prefix construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

instance restrictedTailEndpointKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) : IsMarkovKernel (restrictedTailEndpointKernel hN S hS n b v hb) := by
  induction n generalizing b v with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let _ := ih bs vs hbs
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance restrictedPairEndpointKernel_markov {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (i : Fin (n + 1)) :
    IsMarkovKernel (restrictedPairEndpointKernel hN S hS n b v hb i) := by
  induction n generalizing b v with
  | zero => change IsMarkovKernel (Kernel.id ×ₖ Kernel.id); infer_instance
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (_ ×ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let _ := ih bs vs hbs j
      change IsMarkovKernel (_ ∘ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedEndpointTest
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate spin tests of the constrained endpoint law. These are
consequences of the published marking input and the actual spin kernels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedTerminalPairMean {N : ℕ} (S : Finset (Spin N)) (j : Fin N)
    (y : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  ∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
    ∂(restrictedSpinKernel S ∥ₖ restrictedSpinKernel S) y

def restrictedEndpointCoordinateTest {N : ℕ} (S : Finset (Spin N)) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ :=
  Φ (q (fieldDepthLevel h p.1)) * restrictedTerminalPairMean S j p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained spin-pair test under the finite published
endpoint marking input. Integrability is proved from the full model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedFieldSpinPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  referenceReplicaMean
    ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth =>
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))

def restrictedFieldSpinPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ) (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) : ℝ :=
  ∫ p, restrictedFieldSpinPairIntegrand S hS h z p q Φ j ∂fieldVectorCoordinateLaw N h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedDepthPair
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of the common-level law by the published finite-field
terminal tilt, including the independent scalar-field spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def restrictedFieldDepthPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) (ψ : ℕ → ℝ) : ℝ :=
  referenceReplicaMean
    ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))

def restrictedFieldDepthPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ) (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, restrictedFieldDepthPairIntegrand S hS h z p ψ ∂fieldVectorCoordinateLaw N h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPhysicalCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded cutoff tests for the actual perturbed Ising law, with the
same Haar and Gaussian disorder in the full and restricted models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

def restrictedCavityFullCutoffDisorderTest {N m depth : ℕ} (C : Finset (Spin N)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, cavityCutoffReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior C hC : Measure (Spin N)) T)
    (cavityFullHamiltonian eig I u (U, g)) (s U) (F U) ∂gaussianCoordinates ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFullTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full constrained two-replica test with a rotation-independent observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def restrictedFullTest {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  restrictedCavityFullDisorderTest S hS μ T eig I u (fun _ => F)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedGeometricMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-spin geometric cutoff as a measurable bounded
function of its orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def restrictedOriginalGeometricMean {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (U : SpecialOrthogonal (N+n)) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedLinearCoordinate
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained block spin test under its original Euclidean
Gaussian forest, including the independent residual and shared root. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal BigOperators

namespace InvariantIsing

def restrictedCavityLinearCoordinateMean {d k : ℕ} (T : Finset (Spin k)) (hT : T.Nonempty)
    (h : FieldStep) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin k) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (restrictedSpinPrior T hT))
    (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1)
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 : EuclideanSpace ℝ (Fin d)) x.2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))) *
        (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))
    ∂cavityLinearFieldCoordinateLaw h S

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedLinearDepthEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-depth law of the full linear cavity model, after
projection and ordinary-residual marginalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

def restrictedCavityLinearDepthPairMean {d k : ℕ} (T : Finset (Spin k)) (hT : T.Nonempty) (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (restrictedSpinPrior T hT))
    (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1)
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 :
            EuclideanSpace ℝ (Fin d)) x.2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      ψ (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))
    ∂cavityLinearFieldCoordinateLaw h S

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProjectorPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base logarithmic partition function in the same physical
projector variables as the capped cavity factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedProjectorLogPartition {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp (cavityProjectorHamiltonian Q c u z x)
    ∂labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRandomHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical logarithm with independent random compression
coefficients. The original base disorder stays in its own coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRandomHaarLog {Z : Type*} {N n m d depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Z → CavityFactorBlocks d n)
    (p : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a))) : ℝ :=
  restrictedCanonicalHaarLog S hS C hC k e a₀ hk lam v u t cap δ (A p.1.1) (p.1.2,p.2)

end InvariantIsing

end

end OAI
end


