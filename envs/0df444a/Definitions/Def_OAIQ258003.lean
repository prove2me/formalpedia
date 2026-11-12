-- Prove2me | Definitions.Def_OAIQ258003
-- name    : OAIQ258003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:12.237796+00:00
-- url     : https://prove2.me/theorems/589e6b2b-c8cd-4fbd-907a-68477cdc4742
-- title:
--   Definitions bundle OAIQ258003 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 382 declarations of OpenAI's Lean: 249 definitions, 1 inductive type or structure, 12 instances and 120 theorems. The definitions and types are `OAI.InvariantIsing.FieldSmoothFamily.transform`, `OAI.InvariantIsing.FieldVectorAncestorPairLaw`, `OAI.InvariantIsing.HaarConcentrationInput`, `OAI.InvariantIsing.MagneticContinuationFourJet.transition`, `OAI.InvariantIsing.MagneticContinuationFourJet.transitionFourth`, `OAI.InvariantIsing.MagneticContinuationJet.transition`, `OAI.InvariantIsing.MarchenkoPasturInput`, `OAI.InvariantIsing.PanchenkoTalagrandFieldPairInput`, `OAI.InvariantIsing.PanchenkoTalagrandRestrictedFieldPairInput`, `OAI.InvariantIsing.RestrictedFieldAncestorPairLaw`, `OAI.InvariantIsing.TensorCoordinateData`, `OAI.InvariantIsing.TensorGaussianSpace`, `OAI.InvariantIsing.TensorLabeledData`, `OAI.InvariantIsing.TensorLabeledState`, `OAI.InvariantIsing.affineConstrainedObjective`, `OAI.InvariantIsing.affineRestrictedIncrement`, `OAI.InvariantIsing.biasedConstrainedBlockValue`, `OAI.InvariantIsing.biasedFieldLevelSpinPair`, `OAI.InvariantIsing.bilinearMatrixCoefficient`, `OAI.InvariantIsing.bilinearVectorCoefficient`, `OAI.InvariantIsing.cascadeSeedTree`, `OAI.InvariantIsing.cavityAttachSpinRoot`, `OAI.InvariantIsing.cavityBaseCutoffReplicaMean`, `OAI.InvariantIsing.cavityBlockMarkedLaw`, `OAI.InvariantIsing.cavityCanonicalDiagonal`, `OAI.InvariantIsing.cavityCanonicalGroupCutoffMean`, `OAI.InvariantIsing.cavityCanonicalHaarLog`, `OAI.InvariantIsing.cavityCanonicalProjectorFrame`, `OAI.InvariantIsing.cavityCappedFlatSpinValue`, `OAI.InvariantIsing.cavityCappedSpinReplicaTest`, `OAI.InvariantIsing.cavityCappedSpinReplicaValue`, `OAI.InvariantIsing.cavityCompressionFactorBlocks`, `OAI.InvariantIsing.cavityConditionedFrameLaw`, `OAI.InvariantIsing.cavityFactorBlocksFromMatrix`, `OAI.InvariantIsing.cavityFactorDeviation`, `OAI.InvariantIsing.cavityFactorDeviationTest`, `OAI.InvariantIsing.cavityFieldDensity`, `OAI.InvariantIsing.cavityFieldDiagonal`, `OAI.InvariantIsing.cavityFieldPrimitive`, `OAI.InvariantIsing.cavityFieldStep` and 210 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_NSpinCascade`, `InvariantIsing_Arrays_NSpinTensorCascade`, `InvariantIsing_Arrays_NSpinTensorLabeled`, `InvariantIsing_Arrays_NSpinTensorRootVariance`, `InvariantIsing_Arrays_NSpinTensorTerminalDerivative`, `InvariantIsing_Arrays_OverlapBounds`, `InvariantIsing_Arrays_OverlapTestDiagonal`, `InvariantIsing_Arrays_Overlaps`, `InvariantIsing_Arrays_PerturbationFeatures`, `InvariantIsing_Arrays_TensorLeafCoefficients`, `InvariantIsing_Arrays_TensorProfiles`, `InvariantIsing_Cavity_CavityActualCovariance`, `InvariantIsing_Cavity_CavityBaseRestrictedLaw`, `InvariantIsing_Cavity_CavityBlockFactor`, `InvariantIsing_Cavity_CavityBlockMarkedLaw`, `InvariantIsing_Cavity_CavityCanonicalBlockLimit`, `InvariantIsing_Cavity_CavityCanonicalHaarLog`, `InvariantIsing_Cavity_CavityCappedSpinTest`, `InvariantIsing_Cavity_CavityCoefficientProbability`, `InvariantIsing_Cavity_CavityCompressionFactors`, `InvariantIsing_Cavity_CavityConditionedFrame`, `InvariantIsing_Cavity_CavityContinuousCutoff`, `InvariantIsing_Cavity_CavityCutoffTightness`, `InvariantIsing_Cavity_CavityDisorderMean`, `InvariantIsing_Cavity_CavityDisorderTestComparison`, `InvariantIsing_Cavity_CavityExtraReplicaPrefix`, `InvariantIsing_Cavity_CavityFactorBlockProjection`, `InvariantIsing_Cavity_CavityFieldPath`, `InvariantIsing_Cavity_CavityFiniteCovariancePath`, `InvariantIsing_Cavity_CavityFiniteDeficitPath`, `InvariantIsing_Cavity_CavityFiniteGroupSelection`, `InvariantIsing_Cavity_CavityFiniteIncrement`, `InvariantIsing_Cavity_CavityFiniteReplicaLaw`, `InvariantIsing_Cavity_CavityFullCutoff`, `InvariantIsing_Cavity_CavityFullGibbs`, `InvariantIsing_Cavity_CavityFullProjectionMoment`, `InvariantIsing_Cavity_CavityFullSiteIdentity`, `InvariantIsing_Cavity_CavityFullTail`, `InvariantIsing_Cavity_CavityFullTilt`, `InvariantIsing_Cavity_CavityGaussianKernel`, `InvariantIsing_Cavity_CavityGaussianMarkedLaw`, `InvariantIsing_Cavity_CavityGaussianNodePrior`, `InvariantIsing_Cavity_CavityGeometricMean`, `InvariantIsing_Cavity_CavityGeometricTest`, `InvariantIsing_Cavity_CavityGroupHaarProjection`, `InvariantIsing_Cavity_CavityGroupedCoordinates`, `InvariantIsing_Cavity_CavityHaarLogObservable`, `InvariantIsing_Cavity_CavityHaarMarkedLaw`, `InvariantIsing_Cavity_CavityHaarRestrictedWeight`, `InvariantIsing_Cavity_CavityHaarSpinModel`, `InvariantIsing_Cavity_CavityLabeledDepthMean`, `InvariantIsing_Cavity_CavityLabeledDisorderLaw`, `InvariantIsing_Cavity_CavityLabeledModel`, `InvariantIsing_Cavity_CavityLabeledModelNumerator`, `InvariantIsing_Cavity_CavityLabeledModelSpinMean`, `InvariantIsing_Cavity_CavityLabeledPriorTransport`, `InvariantIsing_Cavity_CavityLabeledProjectors`, `InvariantIsing_Cavity_CavityLabeledRestrictedModel`, `InvariantIsing_Cavity_CavityLabeledSpin`, `InvariantIsing_Cavity_CavityLinearDepthEvaluation`, `InvariantIsing_Cavity_CavityLinearSpinEvaluation`, `InvariantIsing_Cavity_CavityLogNormalizerTransport`, `InvariantIsing_Cavity_CavityNormalizerIntegral`, `InvariantIsing_Cavity_CavityOrientation`, `InvariantIsing_Cavity_CavityOrientationArrayLaw`, `InvariantIsing_Cavity_CavityOrientedFamily`, `InvariantIsing_Cavity_CavityOriginalFactor`, `InvariantIsing_Cavity_CavityOriginalGroupCutoffLimit`, `InvariantIsing_Cavity_CavityOverlapObservable`, `InvariantIsing_Cavity_CavityPhysicalGram`, `InvariantIsing_Cavity_CavityProjectedSpin`, `InvariantIsing_Cavity_CavityProjectedSpinNumerator`, `InvariantIsing_Cavity_CavityProjectionGeometry`, `InvariantIsing_Cavity_CavityProjectorCavity`, `InvariantIsing_Cavity_CavityProjectorCoordinates`, `InvariantIsing_Cavity_CavityProjectorHamiltonian`, `InvariantIsing_Cavity_CavityProjectorLog`, `InvariantIsing_Cavity_CavityProjectorPartition`, `InvariantIsing_Cavity_CavityProjectorTensor`, `InvariantIsing_Cavity_CavityQuadraticOneReplica`, `InvariantIsing_Cavity_CavityRandomHaarLog`, `InvariantIsing_Cavity_CavityReplicaNodeProjection`, `InvariantIsing_Cavity_CavityResidualInnovation`, `InvariantIsing_Cavity_CavityResidualSpinMarginal`, `InvariantIsing_Cavity_CavityRestrictedFactor`, `InvariantIsing_Cavity_CavityRestrictedSpinTest`, `InvariantIsing_Cavity_CavityRetainedNorm`, `InvariantIsing_Cavity_CavityRootedDepthMean`, `InvariantIsing_Cavity_CavityRootedDepthTransport`, `InvariantIsing_Cavity_CavityRootedSpinTestTransport`, `InvariantIsing_Cavity_CavityRootedSpinTransport`, `InvariantIsing_Cavity_CavityRootedTestMean`, `InvariantIsing_Cavity_CavityRotationArray`, `InvariantIsing_Cavity_CavityRotationLogMean`, `InvariantIsing_Cavity_CavityRotationMeasurability`, `InvariantIsing_Cavity_CavityRotationProbability`, `InvariantIsing_Cavity_CavityRotationVectors`, `InvariantIsing_Cavity_CavityScalarRoot`, `InvariantIsing_Cavity_CavityScalarSpin`, `InvariantIsing_Cavity_CavitySelectedCappedSpin`, `InvariantIsing_Cavity_CavitySelectedRestrictedSpin`, `InvariantIsing_Cavity_CavitySiteSymmetry`, `InvariantIsing_Cavity_CavitySpinFullLaw`, `InvariantIsing_Cavity_CavitySpinIsometry`, `InvariantIsing_Cavity_CavitySpinObservable`, `InvariantIsing_Cavity_CavitySpinSplit`, `InvariantIsing_Cavity_CavitySpinTiltTransport`, `InvariantIsing_Cavity_CavitySplitOverlapTest`, `InvariantIsing_Cavity_CavitySplitSpinTest`, `InvariantIsing_Cavity_CavityStrictFiniteSpin`, `InvariantIsing_Cavity_CavityStrictLevels`, `InvariantIsing_Cavity_CavityStrictMarkedLaw`, `InvariantIsing_Cavity_CavityStrictUniformPath`, `InvariantIsing_Cavity_CavityValueFubini`, `InvariantIsing_Cavity_ConsecutiveBlockPrior`, `InvariantIsing_Cavity_ConsecutiveBlockSplit`, `InvariantIsing_Cavity_OffsetAffineIncrement`, `InvariantIsing_Cavity_OffsetBlockPrior`, `InvariantIsing_Core_ContactModulus`, `InvariantIsing_Core_Model`, `InvariantIsing_Core_Variational`, `InvariantIsing_Fields_CanonicalPairRootLaw`, `InvariantIsing_Fields_CanonicalSpinWeights`, `InvariantIsing_Fields_CascadeSeedTree`, `InvariantIsing_Fields_Field`, `InvariantIsing_Fields_FieldAdjacentScalarLaw`, `InvariantIsing_Fields_FieldAffineScalarBridge`, `InvariantIsing_Fields_FieldBounds`, `InvariantIsing_Fields_FieldEndpointSampling`, `InvariantIsing_Fields_FieldGaussianFamilyLocal`, `InvariantIsing_Fields_FieldHeightCone`, `InvariantIsing_Fields_FieldHeightUpdate`, `InvariantIsing_Fields_FieldMagnetization`, `InvariantIsing_Fields_FieldMajorantFold`, `InvariantIsing_Fields_FieldPublishedPairInput`, `InvariantIsing_Fields_FieldScalarChain`, `InvariantIsing_Fields_FieldScalarDerivative`, `InvariantIsing_Fields_FieldScalarLogCoshSecond`, `InvariantIsing_Fields_FieldScalarSampling`, `InvariantIsing_Fields_FieldScalarSecondDerivative`, `InvariantIsing_Fields_FieldSmoothFamily`, `InvariantIsing_Fields_FieldSpinSampling`, `InvariantIsing_Fields_FieldSpinSecondDerivative`, `InvariantIsing_Fields_FieldSpinTransition`, `InvariantIsing_Fields_PriorTensorMinimum`, `InvariantIsing_Fields_PriorTensorPressure`, `InvariantIsing_Gaussian_BilinearGaussianComparison`, `InvariantIsing_Gaussian_GaussianGramEmpiricalTransform`, `InvariantIsing_Gaussian_GaussianPatternPublishedInputs`, `InvariantIsing_Haar_HaarPolynomialValue`, `InvariantIsing_Haar_PublishedInputs`, `InvariantIsing_Haar_ReflectionSegment`, `InvariantIsing_Haar_ReflectionSegmentDerivative`, `InvariantIsing_Haar_Rotation`, `InvariantIsing_Magnetic_ConstrainedBlockBias`, `InvariantIsing_Magnetic_MagneticAffineIncrementLower`, `InvariantIsing_Magnetic_MagneticContinuationClosed`, `InvariantIsing_Magnetic_MagneticContinuationClosedPDE`, `InvariantIsing_Magnetic_MagneticContinuationJet`, `InvariantIsing_Magnetic_MagneticContinuationRegular`, `InvariantIsing_Magnetic_MagneticContinuationSpatial`, `InvariantIsing_Magnetic_MagneticFieldHeightDerivative`, `InvariantIsing_Magnetic_MagneticFourJet`, `InvariantIsing_Magnetic_MagneticHeatCurvature`, `InvariantIsing_Magnetic_MagneticHeatMean`, `InvariantIsing_Magnetic_MagneticScalarContinuation`, `InvariantIsing_Magnetic_MagneticScalarFourJet`, `InvariantIsing_Magnetic_MagneticScalarFourth`, `InvariantIsing_Magnetic_MagneticScalarInverse`, `InvariantIsing_Magnetic_MagneticScalarSlab`, `InvariantIsing_Magnetic_MagneticScalarSlabEndpoint`, `InvariantIsing_Magnetic_MagneticScalarThird`, `InvariantIsing_Magnetic_MagneticScalarWeightedPDE`, `InvariantIsing_Magnetic_MagneticSlabBoundary`, `InvariantIsing_Magnetic_MagneticSlabClosedDerivatives`, `InvariantIsing_Magnetic_MagneticSlabContinuation`, `InvariantIsing_Magnetic_MagneticSlabPDE`, `InvariantIsing_Magnetic_MagneticSpatialFourth`, `InvariantIsing_Magnetic_MagneticSpatialThird`, `InvariantIsing_Magnetic_MagneticWeightedBoundary`, `InvariantIsing_Magnetic_MagneticWeightedClosed`, `InvariantIsing_Magnetic_MagneticWeightedJet`, `InvariantIsing_Magnetic_MagneticWeightedSpatial`, `InvariantIsing_Magnetic_RestrictedEndpointKernel`, `InvariantIsing_Magnetic_RestrictedFieldPublishedInput`, `InvariantIsing_Magnetic_RestrictedFieldRecursion`, `InvariantIsing_Magnetic_RestrictedFieldTerminal`, `InvariantIsing_Magnetic_RestrictedProductPrior`, `InvariantIsing_Magnetic_RestrictedRotationLogMean`, `InvariantIsing_Magnetic_RestrictedSpinLaw`, `InvariantIsing_Magnetic_RestrictedSpinPrior`, `InvariantIsing_Magnetic_RestrictedZeroTreeArrayLaw`, `InvariantIsing_Spectral_CompactResolventTests`, `InvariantIsing_Spectral_SpectralReplicaLaw`, `IsingPerceptron_EnrichedFieldCap`, `IsingPerceptron_MonomialGgAtMinimum`, `IsingPerceptron_VariationalDefs`.
--
--   **Imports.** It imports the published bundles `Def_InvariantIsing` and `Def_IsingFiniteness`; the bundles `OAIQ258000`, `OAIQ258001` and `OAIQ258002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ258005`; the statements `OAI.InvariantIsing.CompactSpectralPartition.pressure_tendsto`, `OAI.InvariantIsing.CompactSpectralPartition.selected_pressure_tendsto`, `OAI.InvariantIsing.cavity_finite_capped_energy_increment`, `OAI.InvariantIsing.cavity_finite_cascade_block_average`, `OAI.InvariantIsing.cavity_finite_compact_block`, `OAI.InvariantIsing.cavity_finite_labeled_moment`, `OAI.InvariantIsing.cavity_finite_log_evaluation`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_finite_original_integrability`, `OAI.InvariantIsing.cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.cavity_full_depth_test_evaluation`, `OAI.InvariantIsing.cavity_full_log_evaluation`, `OAI.InvariantIsing.cavity_full_tree_cutoff_sequence`, `OAI.InvariantIsing.cavity_haar_cutoff_limit_family`, `OAI.InvariantIsing.cavity_labeled_linear_depth_pair_evaluation`, `OAI.InvariantIsing.cavity_labeled_projector_joint_integral`, `OAI.InvariantIsing.cavity_labeled_projector_joint_law`, `OAI.InvariantIsing.cavity_linear_rooted_depth_evaluation`, `OAI.InvariantIsing.cavity_linear_rooted_log_integral`, `OAI.InvariantIsing.cavity_original_cutoff_comparison`, `OAI.InvariantIsing.cavity_original_restricted_haar_limit_family`, `OAI.InvariantIsing.cavity_physical_cutoff_comparison`, `OAI.InvariantIsing.cavity_physical_projector_increment`, `OAI.InvariantIsing.cavity_projector_haar_coefficient_error`, `OAI.InvariantIsing.cavity_quadratic_one_transport`, `OAI.InvariantIsing.cavity_rooted_depth_test_transport`, `OAI.InvariantIsing.cavity_rooted_spectral_linear_moment`, `OAI.InvariantIsing.cavity_rooted_spin_depth_test_transport`, `OAI.InvariantIsing.cavity_strict_finite_overlap_test`, `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error`, `OAI.InvariantIsing.cavity_tree_pressure_capped_increment`, `OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time`, `OAI.InvariantIsing.closedMagneticSlabWeighted_hasDerivAt_time`, `OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem`, `OAI.InvariantIsing.compact_spectral_pressure_tendsto_of_mem`, `OAI.InvariantIsing.entropyFunctional_zero`, `OAI.InvariantIsing.finiteSpectrum_meanPressure_variational_upper`, `OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper`, `OAI.InvariantIsing.finite_physical_field_pressure_upper`, `OAI.InvariantIsing.finite_type_field_pressure_tendsto`, `OAI.InvariantIsing.gaussianPattern_ground_limit`, `OAI.InvariantIsing.gaussianPattern_pressure_limit`, `OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto`, `OAI.InvariantIsing.ground_state_limit`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits`, `OAI.InvariantIsing.magneticClosedCurvature_compare_initial`, `OAI.InvariantIsing.magnetic_affine_field_subsequence_lower`, `OAI.InvariantIsing.magnetic_affine_increment_eventually_lower`, `OAI.InvariantIsing.marchenkoPastur_proved`, `OAI.InvariantIsing.panchenkoTalagrandFieldPair_proved`, `OAI.InvariantIsing.physical_mean_pressure_tendsto`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto`, `OAI.InvariantIsing.positive_temperature_pressure`, `OAI.InvariantIsing.prior_cavity_full_log_evaluation`, `OAI.InvariantIsing.prior_linear_rooted_log_integral`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae`, `OAI.InvariantIsing.random_pressure_tendsto_ae`, `OAI.InvariantIsing.restricted_cavity_finite_log_evaluation`, `OAI.InvariantIsing.restricted_cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation`, `OAI.InvariantIsing.restricted_cavity_linear_rooted_depth_evaluation`, `OAI.InvariantIsing.restricted_original_cutoff_comparison`, `OAI.InvariantIsing.selected_spectral_pressure_tendsto`, `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean` and `OAI.InvariantIsing.tensorFlat_leafPrefix_mean`; the proofs of `OAI.InvariantIsing.cavity_finite_capped_energy_increment`, `OAI.InvariantIsing.cavity_finite_cascade_block_average`, `OAI.InvariantIsing.cavity_finite_compact_block`, `OAI.InvariantIsing.cavity_finite_labeled_moment`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_finite_original_integrability`, `OAI.InvariantIsing.cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.cavity_full_depth_test_evaluation`, `OAI.InvariantIsing.cavity_full_log_evaluation`, `OAI.InvariantIsing.cavity_labeled_projector_joint_integral`, `OAI.InvariantIsing.cavity_labeled_projector_joint_law`, `OAI.InvariantIsing.cavity_linear_rooted_depth_evaluation`, `OAI.InvariantIsing.cavity_original_cutoff_comparison`, `OAI.InvariantIsing.cavity_original_restricted_haar_limit_family`, `OAI.InvariantIsing.cavity_physical_cutoff_comparison`, `OAI.InvariantIsing.cavity_physical_projector_increment`, `OAI.InvariantIsing.cavity_projector_haar_coefficient_error`, `OAI.InvariantIsing.cavity_quadratic_one_transport`, `OAI.InvariantIsing.cavity_rooted_depth_test_transport`, `OAI.InvariantIsing.cavity_rooted_quadratic_gaussian`, `OAI.InvariantIsing.cavity_rooted_spectral_linear_moment`, `OAI.InvariantIsing.cavity_rooted_spin_depth_test_transport`, `OAI.InvariantIsing.cavity_spectral_haar_test_tendsto`, `OAI.InvariantIsing.cavity_strict_finite_overlap_test`, `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error`, `OAI.InvariantIsing.cavity_tree_pressure_capped_increment`, `OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time`, `OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem`, `OAI.InvariantIsing.compact_spectral_pressure_tendsto_of_mem`, `OAI.InvariantIsing.davidsonSzarek_proved`, `OAI.InvariantIsing.entropyFunctional_zero`, `OAI.InvariantIsing.finiteMagneticFunctional_transport_le`, `OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot`, `OAI.InvariantIsing.finiteVariational_ne_top_bot`, `OAI.InvariantIsing.finite_type_field_pressure_tendsto`, `OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge`, `OAI.InvariantIsing.gaussianPatternTranspose_lower_edge`, `OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto`, `OAI.InvariantIsing.ground_state_limit`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits`, `OAI.InvariantIsing.magneticClosedCurvature_compare_initial`, `OAI.InvariantIsing.magneticEntropyFunctional_lower`, `OAI.InvariantIsing.marchenkoPastur_proved`, `OAI.InvariantIsing.physical_mean_pressure_tendsto`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto`, `OAI.InvariantIsing.positive_temperature_pressure`, `OAI.InvariantIsing.prior_cavity_full_log_evaluation`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae`, `OAI.InvariantIsing.random_pressure_tendsto_ae`, `OAI.InvariantIsing.restricted_cavity_finite_log_evaluation`, `OAI.InvariantIsing.restricted_cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.restricted_cavity_full_depth_test_evaluation`, `OAI.InvariantIsing.restricted_original_cutoff_comparison`, `OAI.InvariantIsing.selected_spectral_pressure_tendsto`, `OAI.InvariantIsing.spectral_clip_mean_field_pressure_close`, `OAI.InvariantIsing.spectral_clip_mean_pressure_close`, `OAI.InvariantIsing.variationalFunctional_constant`, `OAI.InvariantIsing.vectorTerminal_pair_formula`, `OAI.IsingPerceptron.cascadeEnergyLog_total_mean`, `OAI.IsingPerceptron.enriched_poisson_root_variance` and `OAI.IsingPerceptron.enriched_poisson_unshifted`.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
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
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001
import Definitions.Def_OAIQ258002

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
open MeasureTheory ProbabilityTheory Matrix in
open scoped MatrixOrder in
set_option maxHeartbeats 1000000 in
/-- Mathlib d13f23b's `measurable_multivariateGaussian` (InvariantIsing, q258). -/
theorem _root_.ProbabilityTheory.measurable_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (multivariateGaussian (ι := ι)).uncurry := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [Function.uncurry, multivariateGaussian]
  conv =>
    rhs
    intro b
    rw [Measure.map_apply (by fun_prop) hs]
  have hf : Measurable (fun q : (EuclideanSpace ℝ ι × Matrix ι ι ℝ) × EuclideanSpace ℝ ι =>
      q.1.1 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt q.1.2) q.2) := by
    fun_prop
  let A := {((μ, S), x) | μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x ∈ s}
  exact measurable_measure_prodMk_left (s := A) (hs.preimage hf)

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

/-- A constant quantile has deficit `1 - max q r`. -/
def constantPath (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : OverlapPath where
  val := fun _ => q
  monotone := monotone_const
  nonneg := fun _ => hq.1
  le_one := fun _ => hq.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

@[simp] lemma fieldValue_zero (b : ℝ) : fieldValue zeroField b = Real.log (Real.cosh b) := by
  simp [fieldValue, zeroField, fieldIncrement, List.ofFn_succ]

@[simp] lemma fieldPairing_zero (p : OverlapPath) : fieldPairing p zeroField = 0 := by
  simp [fieldPairing]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {A : Type*} [MeasurableSpace A]

lemma logMean_mono (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) (hFG : ∀ a, F a ≤ G a) :
    logMean b μ F ≤ logMean b μ G := by
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.log_le_log (integral_exp_pos μ F hF)
  apply integral_mono hF hG
  intro a
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG a) hb.le)

lemma logMean_const_add (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : b ≠ 0)
    {F : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    logMean b μ (fun a => c+F a) = c+logMean b μ F := by
  have he a : Real.exp (b*(c+F a)) = Real.exp (b*c)*Real.exp (b*F a) := by
    rw [mul_add, Real.exp_add]
  simp_rw [logMean, he, integral_const_mul]
  rw [Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos μ F hF).ne', Real.log_exp]
  field_simp

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

lemma logMean_hasLinearGrowth (μ : Measure S) [IsProbabilityMeasure μ]
    (hμ : ExponentialNormMoments μ) {F : S → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {b : ℝ} (hb : 0 < b) :
    HasLinearGrowth (fun x => logMean b μ (fun a => F (x+a))) := by
  obtain ⟨C,L,hC,hL,hbound⟩ := hG
  have hG : HasLinearGrowth F := ⟨C,L,hC,hL,hbound⟩
  let U := logMean b μ (fun a : S => L*‖a‖)
  let D := logMean b μ (fun a : S => -L*‖a‖)
  have hiU : Integrable (fun a : S => Real.exp (b*(L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*L)
  have hiD : Integrable (fun a : S => Real.exp (b*(-L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*(-L))
  have hi (x : S) : Integrable (fun a => Real.exp (b*F (x+a))) μ :=
    integrable_exp_of_linearGrowth μ hμ (hF.comp (measurable_const.add measurable_id))
      (hG.add_left x) b
  refine ⟨C+|U|+|D|, L, by positivity, hL, fun x => ?_⟩
  have hup : logMean b μ (fun a => F (x+a)) ≤ (C+L*‖x‖)+U := by
    rw [← logMean_const_add μ hb.ne' hiU]
    apply logMean_mono μ hb (hi x)
    · convert hiU.const_mul (Real.exp (b*(C+L*‖x‖))) using 1
      all_goals try with_reducible_and_instances rfl
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      calc
        F (x+a) ≤ |F (x+a)| := le_abs_self _
        _ ≤ C+L*‖x+a‖ := hbound _
        _ ≤ C+L*(‖x‖+‖a‖) := by gcongr; exact norm_add_le _ _
        _ = (C+L*‖x‖)+L*‖a‖ := by ring
  have hlo : (-C-L*‖x‖)+D ≤ logMean b μ (fun a => F (x+a)) := by
    rw [← logMean_const_add μ hb.ne' hiD]
    refine logMean_mono μ hb ?_ (hi x) ?_
    · convert hiD.const_mul (Real.exp (b*(-C-L*‖x‖))) using 1
      all_goals try with_reducible_and_instances rfl
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      have hh := (abs_le.mp (hbound (x+a))).1
      have hn := mul_le_mul_of_nonneg_left (norm_add_le x a) hL
      linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le D
    linarith [abs_nonneg U]
  · have := le_abs_self U
    linarith [abs_nonneg D]

lemma cascadeRecursion_linearGrowth (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    HasLinearGrowth (cascadeRecursion n b μ (fun _ p => p.1+p.2) F) := by
  induction n generalizing b μ with
  | zero => exact hG
  | succ n ih =>
    exact logMean_hasLinearGrowth _ (hμ 0 (by omega))
      (measurable_cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1))
        (fun _ => measurable_fst.add measurable_snd) hF)
      (ih _ _ (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)))
      (hb 0 (by omega))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in

lemma finite_gaussian_exponentialNormMoments [Nonempty I] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → I → ℝ}
    (hX : Measurable X) (m : I → ℝ) (v : I → ℝ≥0)
    (hlaw : ∀ i, P.map (fun ω => X ω i) = gaussianReal (m i) (v i)) :
    ExponentialNormMoments (P.map X) := by
  intro a
  have hi (i : I) : Integrable (fun ω => Real.exp (|a| * |X ω i|)) P := by
    have hh := gaussianReal_exponentialNormMoments (m i) (v i) (|a|)
    rw [← hlaw i] at hh
    have hm : Measurable (fun ω => X ω i) := (measurable_pi_apply i).comp hX
    simpa only [Function.comp_def,Real.norm_eq_abs] using
      (integrable_map_measure (by fun_prop) hm.aemeasurable).mp hh
  apply (integrable_map_measure (by fun_prop) hX.aemeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).mono'
  · fun_prop
  · apply ae_of_all
    intro ω
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : I => |X ω i|) Finset.univ_nonempty
    have hn : ‖X ω‖ ≤ |X ω i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ _))
    change |Real.exp (a * ‖X ω‖)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (|a| * |X ω i|) := Real.exp_le_exp.mpr
        (le_trans (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hn (abs_nonneg a)))
      _ ≤ ∑ j : I, Real.exp (|a| * |X ω j|) :=
        Finset.single_le_sum (f := fun j : I => Real.exp (|a| * |X ω j|)) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma gaussianTransform_positive_linearGrowth {U : ℝ → ℝ} (hU : Measurable U)
    (hG : HasLinearGrowth U) (s : ℝ) {d : ℝ} (hd : 0 < d) :
    HasLinearGrowth (gaussianTransform s d U) := by
  let μ : Measure ℝ := gaussianReal 0 (NNReal.mk ((Real.sqrt s)^2) (sq_nonneg _))
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt s*z) = μ := by
    simpa only [zero_mul,NNReal.coe_mk,mul_zero,mul_one] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt s)
  have he (x : ℝ) : gaussianTransform s d U x=logMean d μ (fun z => U (x+z)) := by
    simp only [gaussianTransform,hd.ne',ite_false, if_false,logMean]
    rw [← hm]
    have hg : Measurable (fun a : ℝ => Real.exp (d*U (x+a))) :=
      ((hU.comp (measurable_const.add measurable_id)).const_mul d).exp
    rw [integral_map (show AEMeasurable (fun z : ℝ => Real.sqrt s*z) (gaussianReal 0 1) from
      (measurable_id.const_mul _).aemeasurable) hg.aestronglyMeasurable]
  change HasLinearGrowth (fun x => gaussianTransform s d U x)
  simp_rw [he]
  exact logMean_hasLinearGrowth μ (gaussianReal_exponentialNormMoments _ _) hU hG hd

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_eq_transform (a v : ℝ) (f : ℝ → ℝ) :
    gaussianOperator a v f = IsingPerceptron.gaussianTransform v a f := by
  funext z
  simp only [gaussianOperator, IsingPerceptron.gaussianTransform, div_eq_mul_inv]
  split_ifs <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma fieldEnergy_sub {N : ℕ} (c d : Fin N → ℝ) (σ : Spin N) :
    fieldEnergy c σ - fieldEnergy d σ = ∑ i, (c i - d i) * spinValue (σ i) := by
  simp only [fieldEnergy, ← Finset.sum_sub_distrib, sub_mul]

lemma abs_fieldEnergy_sub_le {N : ℕ} (c d : Fin N → ℝ) (σ : Spin N) :
    |fieldEnergy c σ - fieldEnergy d σ| ≤ ∑ i, |c i - d i| := by
  rw [fieldEnergy_sub]
  calc
    |∑ i, (c i - d i) * spinValue (σ i)| ≤
        ∑ i, |(c i - d i) * spinValue (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i - d i| := by simp only [abs_mul, abs_spinValue, mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

lemma spinVector_norm_sq {N : ℕ} (σ : Spin N) : ‖spinVector σ‖ ^ 2 = N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [spinVector_apply, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma rotated_spin_sq_sum {N : ℕ} (U : Rotation N) (σ : Spin N) :
    (∑ i, (U (spinVector σ) i) ^ 2) = N := by
  rw [← EuclideanSpace.real_norm_sq_eq, U.norm_map, spinVector_norm_sq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma vectorGaussianLaw_moments {N : ℕ} (hN : 0 < N) (v : ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments (vectorGaussianLaw N v : Measure (Fin N → ℝ)) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm := IsingPerceptron.finite_gaussian_exponentialNormMoments
    (P := Measure.pi (fun _ : Fin N => gaussianReal 0 v))
    (X := fun z : Fin N → ℝ => z) measurable_id (fun _ => 0) (fun _ => v)
    (fun i => (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 v) i).map_eq)
  change IsingPerceptron.ExponentialNormMoments
    ((Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map id) at hm
  rw [Measure.map_id] at hm
  exact hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_Overlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap geometry

The finite projected overlaps are Gram matrices. Panchenko's ultrametricity
theorem applies to their limit arrays satisfying the Ghirlanda–Guerra identities.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Overlap restricted to a deterministic spectral coordinate group. -/
def projectedOverlap {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PublishedInputs
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Haar concentration and Gaussian Poincaré inequalities.

Gromov–Milman, *A topological application of the isoperimetric inequality*,
American Journal of Mathematics 105 (1983), 843–854, Section 1.2,
Remark 2, and the special-orthogonal example in Section 3.4 give the
following concentration specialization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Haar concentration for arbitrary
Frobenius-Lipschitz observables on `SO(N)`. The constants are uniform in
dimension, observable, and Lipschitz constant. -/
def HaarConcentrationInput : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
    ∀ L : ℝ, 0 < L →
      (∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) →
    ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {U | f U ≤ m} ∧
      (1 / 2 : ℝ) ≤ μ.real {U | m ≤ f U} ∧
      ∀ r : ℝ, 0 < r →
        μ.real {U | r ≤ |f U - m|} ≤
          C * Real.exp (-c * (N : ℝ) * r ^ 2 / L ^ 2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapBounds
attribute [-simp] _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent bounds for projected spectral overlap kernels. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma projected_spin_sq_sum_le {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ : Spin N) :
    (∑ i ∈ I, U (spinVector σ) i ^ 2) ≤ N := by
  rw [← rotated_spin_sq_sum U σ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun _ _ _ => sq_nonneg _)

lemma projectedOverlap_abs_le_one {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |projectedOverlap U I σ τ| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => U (spinVector σ) i) (fun i => U (spinVector τ) i)
  have hs : (∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i) ^ 2 ≤ (N : ℝ) ^ 2 := by
    apply hcs.trans
    simpa only [pow_two] using
      (mul_le_mul (projected_spin_sq_sum_le U I σ) (projected_spin_sq_sum_le U I τ)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  have ha : |∑ i ∈ I, U (spinVector σ) i * U (spinVector τ) i| ≤ N :=
    (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp (by simpa only [sq_abs] using hs)
  unfold projectedOverlap
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (inv_mul_cancel₀ hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
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

def spectralSpinFeature {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Spin N) (i : I) : ℝ := U (spinVector σ) i / Real.sqrt (N : ℝ)

def spectralMonomialFeature {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (σ : Spin N) (v : SpectralTensorIndex I d) : ℝ :=
  ∏ a, IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) (v a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
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

def spinTensorFeature {N m k : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (σ : Spin N) :
    SpinTensorIndex I degree → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr v => amplitude v.1 * spectralMonomialFeature U I (degree v.1) σ v.2

/-- Variances shared by the coordinates of each spectral monomial. -/
def tensorVarianceProfile {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    SpinTensorIndex I degree → ℝ≥0
  | Sum.inl _ => site
  | Sum.inr v => monomial v.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorRootVariance
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

abbrev TensorGaussianSpace {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) :=
  EuclideanSpace ℝ (Fin (Fintype.card (SpinTensorIndex I degree)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

def uniformSpinPrior (N : ℕ) : ProbabilityMeasure (Spin N) :=
  ⟨(PMF.uniformOfFintype (Spin N)).toMeasure, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

abbrev TensorLabeledData (N n : ℕ) :=
  IsingPerceptron.LabeledTree n × (IsingPerceptron.ForestVertex n → Spin N → ℝ)

abbrev TensorLabeledState (N n : ℕ) := Spin N × IsingPerceptron.LabeledLeaf n

abbrev TensorCoordinateData {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :=
  IsingPerceptron.LabeledTree n × (IsingPerceptron.ForestVertex n → SpinTensorIndex I degree → ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorTerminalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Terminal derivatives and the projected magnetization form of pair paths. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

lemma integral_uniformSpinPrior {N : ℕ} (f : Spin N → ℝ) :
    (∫ σ, f σ ∂(uniformSpinPrior N : Measure (Spin N))) =
      (Fintype.card (Spin N) : ℝ)⁻¹ * ∑ σ, f σ := by
  change (∫ σ, f σ ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [Finset.mul_sum]

lemma integral_uniformSpinGibbs_eq {N : ℕ} (H A : Spin N → ℝ) :
    (∫ σ, A σ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      gibbsAverage (fun _ => 1) H A := by
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite, integral_tilted,
    integral_uniformSpinPrior]
  have hp : referencePartition (uniformSpinPrior N : Measure (Spin N)) H =
      (Fintype.card (Spin N) : ℝ)⁻¹ * finitePartition (fun _ => 1) H := by
    rw [referencePartition, integral_uniformSpinPrior]
    simp only [finitePartition, one_mul]
  change (Fintype.card (Spin N) : ℝ)⁻¹ *
      ∑ σ, (Real.exp (H σ) / referencePartition (uniformSpinPrior N : Measure (Spin N)) H) * A σ = _
  rw [hp, Finset.mul_sum]
  unfold gibbsAverage finiteGibbs
  apply Finset.sum_congr rfl
  intro σ _
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ : finitePartition (fun _ : Spin N => 1) H ≠ 0 :=
    ne_of_gt (finitePartition_pos GibbsReference_one H)
  field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary terminal residual in the cavity spin factor. Its
variance contributes a constant because every Ising spin has norm squared
equal to the number of cavity sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def cavityResidualSpinLog (n : ℕ) (v : ℝ≥0) (c : ℝ) (z : Fin n → ℝ) : ℝ :=
  Real.log ((Fintype.card (Spin n) : ℝ)⁻¹ * ∑ ε : Spin n,
    ∫ w : Fin n → ℝ, Real.exp (fieldEnergy (z + w) ε + (n : ℝ) * c / 2)
      ∂(vectorGaussianLaw n v : Measure (Fin n → ℝ)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityFieldDensity (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  cavityRDerivative rho lam hrho hsum (deficit p r)

def cavityFieldPrimitive (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  ∫ u in 0..r, cavityFieldDensity rho lam hrho hsum p u

def cavityFieldDiagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) : ℝ :=
  cavityFieldPrimitive rho lam hrho hsum p 1

lemma continuous_cavityFieldDensity (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    Continuous (cavityFieldDensity rho lam hrho hsum p) :=
  (continuous_cavityRDerivative rho lam hrho hsum).comp (continuous_deficit p)

lemma cavityFieldPrimitive_nonneg (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ cavityFieldPrimitive rho lam hrho hsum p r :=
  intervalIntegral.integral_nonneg_of_forall hr
    (fun _ => cavityRDerivative_nonneg rho lam hrho hsum _)

lemma cavityFieldPrimitive_mono (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    cavityFieldPrimitive rho lam hrho hsum p a ≤ cavityFieldPrimitive rho lam hrho hsum p b :=
  intervalIntegral.integral_mono_interval le_rfl ha hab
    (ae_of_all _ (fun _ => cavityRDerivative_nonneg rho lam hrho hsum _))
    ((continuous_cavityFieldDensity rho lam hrho hsum p).intervalIntegrable 0 b)

def cavityFieldStep (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath)
    {n : ℕ} (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i) : FieldStep where
  depth := n
  cut := cut
  ordered_cut := hcut
  first := hfirst
  last := hlast
  height := fun i => cavityFieldPrimitive rho lam hrho hsum p (q i)
  nonneg := fun i => cavityFieldPrimitive_nonneg rho lam hrho hsum p (hq0 i)
  ordered_height := fun i _j hij => cavityFieldPrimitive_mono rho lam hrho hsum p (hq0 i) (hq hij)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_positive_growth {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) {a : ℝ} (ha : 0 < a) (v : ℝ) :
    Measurable (gaussianOperator a v F) ∧
      IsingPerceptron.HasLinearGrowth (gaussianOperator a v F) := by
  rw [gaussianOperator_eq_transform]
  exact ⟨IsingPerceptron.measurable_gaussianTransform hF v a,
    IsingPerceptron.gaussianTransform_positive_linearGrowth hF hFG v ha⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma measurable_fieldSpinTransition (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) :
    Measurable (fieldSpinTransition ζ v F a) := by
  have hnum : Measurable (fun p : ℝ × ℝ =>
      Real.exp (ζ * F (p.1 + Real.sqrt (v : ℝ) * p.2)) *
        a (p.1 + Real.sqrt (v : ℝ) * p.2)) := by fun_prop
  have hden : Measurable (fun p : ℝ × ℝ =>
      Real.exp (ζ * F (p.1 + Real.sqrt (v : ℝ) * p.2))) := by fun_prop
  have he : fieldSpinTransition ζ v F a = fun z =>
      (∫ u, Real.exp (ζ * F (z + Real.sqrt (v : ℝ) * u)) *
        a (z + Real.sqrt (v : ℝ) * u) ∂gaussianReal 0 1) /
      (∫ u, Real.exp (ζ * F (z + Real.sqrt (v : ℝ) * u)) ∂gaussianReal 0 1) := by
    funext z
    rw [fieldSpinTransition_eq_standard ζ v hF ha z, gaussianTiltAverage_eq_div]
  rw [he]
  exact hnum.stronglyMeasurable.integral_prod_right'.measurable.div
    hden.stronglyMeasurable.integral_prod_right'.measurable

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

def fieldScalarValue (L : List (ℝ × ℝ≥0)) (F : ℝ → ℝ) : ℝ → ℝ :=
  L.foldr (fun av f => gaussianOperator av.1 av.2 f) F

def fieldScalarMean : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | [], _, a => a
  | av :: L, F, a => fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarMean L F a)

lemma fieldScalarValue_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) :
    Measurable (fieldScalarValue L F) ∧ HasLinearGrowth (fieldScalarValue L F) := by
  induction L with
  | nil => exact ⟨hF, hG⟩
  | cons av L ih =>
    have ht := ih (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
    exact gaussianOperator_positive_growth ht.1 ht.2 (hL av (List.mem_cons_self)) av.2

lemma fieldScalarMean_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) {B : ℝ} (haB : ∀ u, |a u| ≤ B) :
    Measurable (fieldScalarMean L F a) ∧ ∀ z, |fieldScalarMean L F a z| ≤ B := by
  induction L with
  | nil => exact ⟨ha, haB⟩
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := ih htail
    exact ⟨measurable_fieldSpinTransition av.1 av.2 hval.1 hmean.1,
      fieldSpinTransition_bound av.1 av.2 hval.1 hval.2 hmean.2⟩

/-- The entry indexed by `i` is the conditional expectation of the square
of the physical spin mean at level `i`, given the starting position. -/
def fieldScalarSquares : (L : List (ℝ × ℝ≥0)) → (ℝ → ℝ) → (ℝ → ℝ) →
    Fin (L.length + 1) → ℝ → ℝ
  | [], _, a => fun _ z => (a z) ^ 2
  | av :: L, F, a => Fin.cons (fun z => (fieldScalarMean (av :: L) F a z) ^ 2)
      (fun i => fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a i))

@[simp] lemma fieldScalarSquares_zero (L : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) (z : ℝ) :
    fieldScalarSquares L F a 0 z = (fieldScalarMean L F a z) ^ 2 := by
  cases L <;> rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

lemma scalarFieldIncrements_positive (h : FieldStep) :
    ∀ av ∈ scalarFieldIncrements h, 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact fieldIncrement_tail_positive h i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spin sampling and Gaussian transitions for the scalar Ising
recursion. The transition kernels remain probabilities at zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def scalarSpinKernel : Kernel ℝ Bool :=
  ⟨fun z => gibbsProbability (PMF.uniformOfFintype Bool).toMeasure
      (fun σ => z * spinValue σ),
    measurable_gibbsProbability
      (ν := fun _ : ℝ => (PMF.uniformOfFintype Bool).toMeasure)
      (H := fun p : ℝ × Bool => p.1 * spinValue p.2) measurable_const
      (measurable_fst.mul ((measurable_of_finite spinValue).comp measurable_snd))⟩

instance scalarSpinKernel_markov : IsMarkovKernel scalarSpinKernel := by
  constructor
  intro z
  change IsProbabilityMeasure (gibbsProbability (PMF.uniformOfFintype Bool).toMeasure
    (fun σ => z * spinValue σ))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

/-- Spin law at the end of the actual successive tilted Gaussian
transitions, starting from the given scalar field. -/
def fieldTailSpinKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel ℝ Bool
  | [], _ => scalarSpinKernel
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldTailSpinKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldTailSpinKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldTailSpinKernel L hL) := by
  induction L with
  | nil => exact scalarSpinKernel_markov
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-prefix sampling of two scalar Ising spins. After the split
the two tails are independent; before the split they use the same actual
tilted Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldPairSpinKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) → Kernel ℝ (Bool × Bool)
  | [], _, _ => scalarSpinKernel ×ₖ scalarSpinKernel
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldTailSpinKernel (av :: L) hL ×ₖ fieldTailSpinKernel (av :: L) hL)
      (fun j => fieldPairSpinKernel L ht j ∘ₖ
        fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          hreg.1) i

instance fieldPairSpinKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldPairSpinKernel L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (scalarSpinKernel ×ₖ scalarSpinKernel); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldTailSpinKernel (av :: L) hL ×ₖ
        fieldTailSpinKernel (av :: L) hL)
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

def fieldVectorTailEndpointKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel (Fin N → ℝ) (Fin N → ℝ)
  | [], _ => Kernel.id
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldVectorTailEndpointKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

def fieldVectorPairEndpointKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) →
      Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | [], _, _ => Kernel.id ×ₖ Kernel.id
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldVectorTailEndpointKernel N (av :: L) hL ×ₖ
        fieldVectorTailEndpointKernel N (av :: L) hL)
      (fun j => fieldVectorPairEndpointKernel N L ht j ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2
          (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPublishedPairInput
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite vector log-cosh specialization of Panchenko--Talagrand,
C. R. Acad. Sci. Paris I 345 (2007), 653--656, Section 3, Lemma 3.1,
equation (8), p.655, and Corollary 3.2, equation (9), p.656.

Only bounded measurable tests of the common depth and two endpoint fields
are retained. The statement specifies their law under the actual terminal
tilt, before any spins or overlap expectations are evaluated. The finite
marking theorem supplies this hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldStepVariance (h : FieldStep) (i : ℕ) : ℝ≥0 :=
  if hi : i < h.depth then
    ((scalarFieldIncrements h).get ⟨i, by simpa only [scalarFieldIncrements_length] using hi⟩).2
  else 0

def fieldVectorCoordinateLaw (N : ℕ) (h : FieldStep) :
    Measure (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :=
  (labeledCascadeLaw h.depth (chainExponent h.cut) : Measure (LabeledTree h.depth)).prod
    (Measure.infinitePi (fun a : ForestVertex h.depth =>
      (vectorGaussianLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
        Measure (Fin N → ℝ))))

def fieldVectorTiltedPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean (labeledLeafLaw h.depth p.1)
    (fun α => ∑ j, Real.log (Real.cosh (fieldVectorEndpoint N h p z α j)))
    (fun σ : Fin 2 → LabeledLeaf h.depth =>
      Φ (labeledCommonDepth h.depth (σ 0) (σ 1),
        fieldVectorEndpoint N h p z (σ 0), fieldVectorEndpoint N h p z (σ 1)))
    ∂fieldVectorCoordinateLaw N h

def FieldVectorAncestorPairLaw (N : ℕ) (h : FieldStep) : Prop :=
  ∀ z : Fin N → ℝ,
  ∀ Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
    Measurable Φ → (∃ C : ℝ, ∀ p, |Φ p| ≤ C) →
    fieldVectorTiltedPairMean N h z Φ =
      ∫ α : ℕ → LabeledLeaf h.depth,
        ∫ y, Φ ((fieldCommonLevel h α).val, y)
          ∂fieldVectorPairEndpointKernel N (scalarFieldIncrements h)
            (scalarFieldIncrements_positive h)
            (Fin.cast (by rw [scalarFieldIncrements_length]) (fieldCommonLevel h α)) z
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut)

/-- Same published marking result as `PanchenkoTalagrandTensorPairInput`,
specialized to the separable vector terminal used after the cavity change
of variables. No pressure, spin-moment, or limiting assertion is assumed. -/
def PanchenkoTalagrandFieldPairInput : Prop :=
  ∀ N : ℕ, 0 < N → ∀ h : FieldStep, FieldVectorAncestorPairLaw N h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

def cavityFiniteDeficitPath {n : ℕ} (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (i : ℕ) : ℝ := deficit p (q (cavityFiniteLevel n i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariancePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

def cavityFiniteCovariancePath (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (i : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  cavityFiniteCovariance rho lam hrho hsum g (cavityFiniteDeficitPath p q i)

def cavityFiniteNoiseCovariance (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (q : Fin (n + 1) → ℝ)
    (i : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (chainExponent cut i)⁻¹ • (cavityFiniteCovariancePath rho lam hrho hsum g p q i -
    cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1))

def cavityFiniteRootCovariance (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  q 0 • ((1 / finiteSecondResolvent rho lam
    (finiteInverse rho lam hrho hsum (cavityFiniteDeficitPath p q 0))) •
      (cavityFiniteCovariancePath rho lam hrho hsum g p q 0 *
        cavityFiniteCovariancePath rho lam hrho hsum g p q 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualInnovation
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint innovation map for a true cascade leaf and its ordinary
terminal residual. All residual randomness remains outside the cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityQuadraticResidualGibbs {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityQuadraticResidualGibbs n K R s) := by
  let G := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n) ×ₖ
    Kernel.const (NoiseTree (EuclideanSpace ℝ (Fin d)) n) (multivariateGaussian 0 R)
  have hG : Measurable (fun V : NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) := by
    have he : (fun V : NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) = G := by
      funext V
      exact (Kernel.prod_apply (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n)
        (Kernel.const (NoiseTree (EuclideanSpace ℝ (Fin d)) n) (multivariateGaussian 0 R)) V).symm
    rw [he]
    exact G.measurable
  have hw : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  exact measurable_normalizeMass.comp ((measurable_withDensity_fixed hw).comp hG)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodePrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the actual shared Gaussian root, independent forest, and
replica-specific ordinary residuals as one independent node family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityReplicaNodeCovariance {d : ℕ} (n r : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    CavityReplicaNode n r → Matrix (Fin d) (Fin d) ℝ :=
  Sum.elim (fun a => a.elim S₀ (fun v => S (forestVertexDepth n v))) (fun _ => R)

def cavityReplicaNodeJoin {d : ℕ} (n r : ℕ)
    (p : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    CavityReplicaNode n r → EuclideanSpace ℝ (Fin d) :=
  Sum.elim (fun a => a.elim p.1.1 p.1.2) p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaNodeProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite set of Gaussian nodes visited by a tuple of cavity leaves.
Each replica keeps the common root and shared edges, and receives its own
ordinary terminal residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityReplicaNodePath {r : ℕ} (n : ℕ) (v : LabeledLeaf n) (i : Fin r) :
    Finset (CavityReplicaNode n r) := by
  classical
  exact insert (Sum.inr i)
    (Finset.univ.image (fun k : Fin (n + 1) => Sum.inl (nodeAt n v k)))

def cavityReplicaNodeSupport {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n) :
    Finset (CavityReplicaNode n r) := by
  classical
  exact Finset.univ.biUnion (fun i => cavityReplicaNodePath n (σ i) i)

def cavityReplicaNodeWeight {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (i : Fin r) (a : cavityReplicaNodeSupport n σ) : ℝ := by
  classical
  exact if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then 1 else 0

def cavityReplicaGaussianCovariance {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin r → LabeledLeaf n) : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  cavityGaussianNodeCovariance
    (fun a : cavityReplicaNodeSupport n σ => cavityReplicaNodeCovariance n r S₀ R S a)
    (cavityReplicaNodeWeight n σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gaussian law used on the finite spectral side of the
physical replica comparison, with every covariance fixed by the overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityFiniteCanonicalReplicaCovariance {m d n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (σ : Fin r → LabeledLeaf n) : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  fun u v => if u.2 = v.2 then
    (if u.1 = v.1 then spectralGroupDiagonal rho lam hrho hsum p (g u.2) else
      cavityCanonicalCoordinate rho lam hrho hsum p (g u.2)
        (q (cavityFiniteLevel n (labeledCommonDepth n (σ u.1) (σ v.1))))) / rho (g u.2)
      else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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

def spectralJointEntry {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) : SpectralEntry (m + 1) :=
  Fin.lastCases
    ⟨treeOverlap n x.2 y.2, ⟨(by linarith [(treeOverlap_mem n x.2 y.2).1]),
      (treeOverlap_mem n x.2 y.2).2⟩⟩
    (fun a => ⟨projectedOverlap U (I a) x.1 y.1, abs_le.mp (projectedOverlap_abs_le_one U (I a) x.1 y.1)⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat Gaussian coefficients for root and finite-depth tensor marks. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Level zero is the common root mark. Positive levels encode the
corresponding ancestor prefix of the labeled leaf. -/
def tensorLeafCoefficients {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag n x.2)
    (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
      (NNReal.sqrt (v i.1 i.2) : ℝ) * spinTensorFeature U I degree amplitude x.1 i.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's linear enrichment and monomial tree variance increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The root has variance `h 0`; each child adds the next field increment.
For a tree monomial of degree zero the entire variance is at the root. -/
def tensorPathProfile {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (treeDegree : Fin k → ℕ)
    (h : ℕ → ℝ) (i : ℕ) : SpinTensorIndex I degree → ℝ≥0 :=
  tensorVarianceProfile I degree (varianceIncrement h i)
    (fun j => varianceIncrement (monomialPath n (treeDegree j)) i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalBlockLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical spectral-group blocks of finite cascades converge to the
actual Ward-identified spectral array. The auxiliary tree coordinate is
not needed by these physical group observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityCanonicalDiagonal {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) : SpectralEntry m := fun a =>
  ⟨spectralGroupDiagonal ρ eig hρ hρsum p a,
    ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (spectralGroupDiagonal_nonneg ρ eig hρ hρsum p a),
      spectralGroupDiagonal_le_one ρ eig hρ hρsum p a⟩⟩

lemma continuous_cavitySpectralGroupBlock (m r : ℕ) :
    Continuous (cavitySpectralGroupBlock m r) := by
  unfold cavitySpectralGroupBlock
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGroupSelection
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting the assigned special axes from the Gaussian spectral-group
block gives precisely the finite cavity field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityFiniteReplicaSpectralBlock {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin r → LabeledLeaf n) : SpectralBlock m r :=
  cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
    (cavityCanonicalLabel rho lam hrho hsum p)
    (fun i j => q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

lemma cavityStrictLevels_strict {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : Monotone q) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) :
    StrictMono (cavityStrictLevels q ε) := by
  intro i j hij
  have hq' := mul_le_mul_of_nonneg_left (hq hij.le) (sub_nonneg.mpr hε.2)
  have hi := mul_lt_mul_of_pos_left (cavityInteriorLevel_strict n hij) hε.1
  exact add_lt_add_of_le_of_lt hq' hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def cavityStrictUniformLevels (p : OverlapPath) (n : ℕ) : Fin (n + 1) → ℝ :=
  cavityStrictLevels (fun i => uniformCellAverage p n i) (1 / ((n : ℝ) + 1))

lemma cavityStrictUniformLevels_mem (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    cavityStrictUniformLevels p n i ∈ Ioo (0 : ℝ) 1 :=
  cavityStrictLevels_mem _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n) i

lemma cavityStrictUniformLevels_strict (p : OverlapPath) (n : ℕ) :
    StrictMono (cavityStrictUniformLevels p n) :=
  cavityStrictLevels_strict _
    (fun _i _j hij => uniformCellAverage_monotone p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n hij)
    (cavity_uniform_epsilon n)

def cavityStrictUniformPath (p : OverlapPath) (n : ℕ) : OverlapPath where
  val := fun s => cavityStrictUniformLevels p n (cavityUniformLevel n s)
  monotone := (cavityStrictUniformLevels_strict p n).monotone.comp (cavityUniformLevel_monotone n)
  nonneg := fun s => (cavityStrictUniformLevels_mem p n (cavityUniformLevel n s)).1.le
  le_one := fun s => (cavityStrictUniformLevels_mem p n (cavityUniformLevel n s)).2.le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-volume algebra for the coupled cavity comparison.  The
spectral coupling and its Gaussian limit are separate source obligations. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityLogFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin d → ℝ) (ε : Spin n) : ℝ :=
  cavityQuadratic K y + (∑ i, ∑ j, y i * L i j * spinValue (ε j)) +
    cavityQuadratic C (fun j => spinValue (ε j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticOneReplica
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-replica marginal after the quadratic cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityQuadraticResidualKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    Kernel (NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ⟨cavityQuadraticResidualGibbs n K R s, measurable_cavityQuadraticResidualGibbs n K R s⟩

instance cavityQuadraticResidualKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    IsMarkovKernel (cavityQuadraticResidualKernel n K R s) := by
  constructor
  intro V
  change IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R s V)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTilt
attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the two successive tilts with the full cavity factor on
the original leaf/residual/spin prior, with the common root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityRootedLogFactor {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  have hy : ∀ i, Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityRootedField n z.1 i) := fun i =>
    (EuclideanSpace.proj i).measurable.comp ((measurable_cavityRootedField n).comp measurable_fst)
  have he : ∀ i, Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      spinValue (z.2 i)) := by
    intro i
    exact (measurable_of_countable (spinValue : Bool → ℝ)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have hK : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityQuadratic K (cavityRootedField n z.1)) := by
    exact (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (K i j)).mul (hy j)))).const_mul (1 / 2)
  have hL : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      ∑ i, ∑ j, cavityRootedField n z.1 i * L i j * spinValue (z.2 j)) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (L i j)).mul (he j)))
  have hC : Measurable (fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
      cavityQuadratic C (fun i => spinValue (z.2 i))) := by
    exact (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((he i).mul_const (C i j)).mul (he j)))).const_mul (1 / 2)
  exact (hK.add hL).add hC

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullGibbs
attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A total probability-kernel version of the full cavity Gibbs law.
Its fallback on a nonintegrable fiber is irrelevant on the proved full-measure set. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedFullGibbs {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      ((EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k) := by
  let ν := cavityRootedPriorKernel n R ×ₖ Kernel.const _ π
  let V : (EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  let W : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      ((EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
        EuclideanSpace ℝ (Fin d)) × Spin k) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (V p.2))
  have hW : Measurable W :=
    (((measurable_cavityRootedLogFactor n K L C).comp measurable_snd).exp.ennreal_ofReal)
  have hm := measurable_normalizeMass.comp
    (measurable_random_withDensity (ν := ν) (W := W) ν.measurable hW)
  exact ⟨fun ω => normalizeMass ((ν ω).withDensity (fun z => W (ω, z))), hm⟩

instance cavityRootedFullGibbs_markov {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityRootedFullGibbs n K R L C π) := by
  constructor
  intro ω
  exact normalizeMass_probability _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinTiltTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining finite Ising tilt commutes with the actual quadratic
innovation change of variables, including the ordinary residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityLinearResidualPotential {d k : ℕ} (n : ℕ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin d))
    (p : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) : ℝ :=
  cavityLogFactor 0 L C (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinFullLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-factor spin law before and after the quadratic innovation
change of variables. The ordinary residual is part of each probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

def cavityResidualSpinFullLaw {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) (π : Measure (Spin k)) :
    Measure ((NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) :=
  (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π).tilted
      (fun p => cavityLogFactor K L C
        (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTransport
attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Root-retaining transport of the full cavity spin probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityAttachSpinRoot {d k : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d))
    (p : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) :
    CavitySpinState d k n := ((s, p.1), p.2)

def cavityRootedSpinInnovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (p : CavitySpinState d k n) : CavitySpinState d k n :=
  ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ p.1.1,
    cavityResidualInnovationMap n K H b p.1.1 p.1.2), p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection of the actual linear cavity spin tilt to its scalar fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

def cavityResidualFieldProjection {A : Type*} {d k : ℕ}
    (L : Matrix (Fin d) (Fin k) ℝ)
    (p : (A × EuclideanSpace ℝ (Fin d)) × Spin k) :
    (A × (Fin k → ℝ)) × Spin k := ((p.1.1, cavityProjectField L p.1.2), p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled representation of the full cavity spin law and its field projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal NNReal

namespace InvariantIsing

def cavityLabeledSpinMap {d k : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (p : (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k) :
    (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k :=
  ((labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) p.1.1, p.1.2), p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualSpinMarginal
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marginalizing the ordinary residual in the full leaf/spin probability law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def cavitySpinResidualReorder {A : Type*} {N : ℕ}
    (p : (A × (Fin N → ℝ)) × Spin N) : (A × Spin N) × (Fin N → ℝ) :=
  ((p.1.1, p.2), p.1.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTestTransport
attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-depth spin observable survives the full rooted quadratic
innovation change, including the disorder and all replica normalizations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedSpinDepthTest {d k n : ℕ} (a : ℕ → ℝ) (j : Fin k)
    (σ : ℕ → CavitySpinState d k n) : ℝ :=
  a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) *
    (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearSpinEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the full linear cavity spin test under its independent
Euclidean Gaussian forest and root. The covariance assumptions specify
the scalar field path after projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

def cavityLabeledLinearSpinPairMean {d k : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin k) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))
    (fun x : (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1)
        (cavityLeafSum h.depth s (labeledNoiseLeaf _ h.depth
          (p.1, markForestOfCoords _ h.depth p.2) x.1.1) + x.1.2 :
            EuclideanSpace ℝ (Fin d)) x.2)
    (fun σ : Fin 2 → (LabeledLeaf h.depth × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Φ (q (fieldDepthLevel h (labeledCommonDepth h.depth (σ 0).1.1 (σ 1).1.1))) *
        (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))
    ∂cavityLinearFieldCoordinateLaw h S

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedTestMean
attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disintegration of the bounded common-depth spin test over its actual
Gaussian-root and cascade disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRootedSpinTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) (j : Fin k)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  ∫ σ, cavityRootedSpinDepthTest a j σ
    ∂Measure.infinitePi (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityContinuousCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded continuous cutoffs of the actual cavity factor. The radius
cutoff equals one on the inner ball and vanishes outside the next ball. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_cavityLogFactor {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin d) => cavityLogFactor K L C y ε) := by
  unfold cavityLogFactor cavityQuadratic
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditionedFrame
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

def cavityConditionedFrameLaw (n q : ℕ) : Measure (Matrix (Fin n) (Fin q) ℝ) :=
  (cond (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityArrayGood n q)).map
    (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupHaarProjection
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Gaussian projection limit for independent Haar frames in
all spectral groups. The exact finite-dimensional law is obtained before
taking limits; no conditional independence is assumed as an extra input. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGroupHaarFrames {m q : ℕ} {N : Fin m → ℕ}
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (cavityGroupHaarFrames A₀) := by
  apply Measurable.of_eval
  intro a
  exact (((continuous_cavityFrameAction (N a) q).comp
    (continuous_id.prodMk continuous_const)).measurable).comp (measurable_pi_apply a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The paper's finite-spin cavity factor as a bounded continuous replica
test, ready for the actual fresh-Haar / recalculated-cascade comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityCappedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)
      ∂Measure.pi (fun _ => π)

lemma cavityCappedSpinReplicaValue_bound {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    ‖cavityCappedSpinReplicaValue K L C T J π F z‖ ≤ (Real.exp T)^r * ‖F‖ := by
  have hb (ε : Fin r → Spin k) :
      ‖(∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)‖ ≤
        (Real.exp T)^r * ‖F‖ := by
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => π)) (ae_of_all _ hb)
  simpa only [cavityCappedSpinReplicaValue, probReal_univ, mul_one] using h

lemma continuous_cavityCappedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Continuous (cavityCappedSpinReplicaValue K L C T J π F) := by
  have hp (ε : Fin r → Spin k) : Continuous
      (fun z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) =>
        (∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)) := by
    apply Continuous.mul
    · apply continuous_finsetProd
      intro i _
      exact Real.continuous_exp.comp
        (((continuous_cavityLogFactor K L C (ε i)).comp
          ((continuous_apply i).comp (J.continuous.comp continuous_snd))).min continuous_const)
    · exact F.continuous.comp (continuous_fst.prodMk continuous_const)
  unfold cavityCappedSpinReplicaValue
  apply continuous_of_dominated (bound := fun _ => (Real.exp T)^r * ‖F‖)
  · intro z
    exact (measurable_of_countable _).aestronglyMeasurable
  · intro z
    apply ae_of_all
    intro ε
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  · exact integrable_const _
  · exact ae_of_all _ hp

def cavityCappedSpinReplicaTest {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cavityCappedSpinReplicaValue K L C T J π F)
    (continuous_cavityCappedSpinReplicaValue K L C T J π F) ((Real.exp T)^r * ‖F‖)
    (cavityCappedSpinReplicaValue_bound K L C T J π F)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedCappedSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped spin factor in the Haar comparison is exactly the
finite root/forest/residual spin factor after selecting its assigned axes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityCappedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, Real.exp (min (cavityLogFactor K L C
      (WithLp.toLp 2 (fun a => y (i, a))) (ε i)) τ)) * F ε
        ∂Measure.pi (fun _ => π)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cavity model in a fixed measurable state space:
the tree, Gaussian root and forest are disorder; the leaf, ordinary
residual and Ising spin form the configuration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityLabeledDisorderLaw {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    Measure (CavityLabeledDisorder d n) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))))

instance cavityLabeledDisorderLaw_probability {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (cavityLabeledDisorderLaw n b S₀ S) := by
  unfold cavityLabeledDisorderLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityLabeledPriorKernel {d k : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    Kernel (CavityLabeledDisorder d n) (CavityLabeledState d k n) :=
  (((cavityLabeledLeafKernel n).comap Prod.fst measurable_fst) ×ₖ
    Kernel.const _ (multivariateGaussian 0 R)) ×ₖ
    Kernel.const _ π

@[simp] lemma cavityLabeledPriorKernel_apply {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n) :
    cavityLabeledPriorKernel n R π ω =
      (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π) := by
  rw [cavityLabeledPriorKernel, Kernel.prod_apply, Kernel.prod_apply]
  rfl

instance cavityLabeledPriorKernel_markov {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityLabeledPriorKernel n R π) := by
  constructor
  intro ω
  rw [cavityLabeledPriorKernel_apply]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityLabeledField {d : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n)
    (α : LabeledLeaf n) : EuclideanSpace ℝ (Fin d) :=
  ω.2.1 + ∑ i : Fin n, ω.2.2 (edgeAt n α i)

def cavityLabeledEndpoint {d k : ℕ} (n : ℕ)
    (p : CavityLabeledDisorder d n × CavityLabeledState d k n) :
    EuclideanSpace ℝ (Fin d) × Spin k :=
  (cavityLabeledField n p.1 p.2.1.1 + p.2.1.2, p.2.2)

def cavityLabeledPotential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) : CavityLabeledDisorder d n × CavityLabeledState d k n → ℝ :=
  (fun p : EuclideanSpace ℝ (Fin d) × Spin k => cavityLogFactor K L C p.1 p.2) ∘
    cavityLabeledEndpoint n

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledDisorderLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The independent labeled coordinates give the original common-root
noise-cascade disorder law exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

def cavityLabeledNoiseDisorderMap {d : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n) :
    EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n :=
  (ω.2.1, labeledNoiseJoin _ n (ω.1, markForestOfCoords _ n ω.2.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledPriorTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-state finite model prior and potential are exactly the
labeled realization of the original common-root cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

def cavityLabeledRootMap {d k : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n) :
    CavityLabeledState d k n → CavitySpinState d k n :=
  cavityAttachSpinRoot n ω.2.1 ∘ cavityLabeledSpinMap n ω.1 ω.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModelSpinMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

def cavityLabeledSpinDepthMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (a : ℕ → ℝ) (j : Fin k)
    (ω : CavityLabeledDisorder d n) : ℝ :=
  referenceReplicaMean (cavityLabeledPriorKernel n R (uniformSpinPrior k) ω)
    (fun x => cavityLabeledPotential n K L C (ω,x))
    (fun σ : Fin 2 → CavityLabeledState d k n => a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1) *
      (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModelNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and the literal product-prior formula for the finite
cavity numerator used in extra-replica normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityLabeledReplicaTest {m r d k n : ℕ}
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : CavityLabeledDisorder d n × (Fin r → CavityLabeledState d k n)) : ℝ :=
  F (B (fun i => (p.2 i).1.1), fun i => (p.2 i).2)

def cavityLabeledCappedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (τ : ℝ)
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) : ℝ :=
  cavityWeightNumerator (cavityLabeledPriorKernel n R π ω)
    (fun x => Real.exp (min (cavityLabeledPotential n K L C (ω, x)) τ))
    (fun ξ => cavityLabeledReplicaTest B F (ω, ξ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous spectral-block observable used to read the physical
spin overlap from the finite cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavitySpinObservable {m k : ℕ} (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (j : Fin k) :
    SpectralBlock m 2 × (Fin 2 → Spin k) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p => Φ (∑ a, (p.1 0 1 a : ℝ)) *
      (spinValue (p.2 0 j) * spinValue (p.2 1 j)),
      (hΦ.comp (continuous_finsetSum _ (fun a _ => by fun_prop))).mul
        (show Continuous (fun p : SpectralBlock m 2 × (Fin 2 → Spin k) =>
          spinValue (p.2 0 j) * spinValue (p.2 1 j)) from
          (continuous_of_discreteTopology : Continuous (fun ε : Fin 2 → Spin k =>
            spinValue (ε 0 j) * spinValue (ε 1 j))).comp continuous_snd)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictFiniteSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized finite spin identity on the strict uniform
approximants. All finite partition and nondegeneracy premises are proved. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

def cavityStrictUniformField {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (n : ℕ) : FieldStep :=
  cavityFieldStep rho lam hrho hsum (cavityStrictUniformPath p n)
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (cavityStrictUniformLevels p n) (cavityStrictUniformLevels_strict p n).monotone
    (fun i => (cavityStrictUniformLevels_mem p n i).1.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual backward conditional spin mean is the spatial derivative
of the scalar Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma hasDerivAt_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {K : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K)
    (hder : ∀ z, HasDerivAt F (a z) z) (z : ℝ) :
    HasDerivAt (fieldScalarValue L F) (fieldScalarMean L F a z) z := by
  induction L generalizing z with
  | nil => exact hder z
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    exact hasDerivAt_gaussianOperator av.1 av.2 hval.1 hval.2 hmean.1 hK hmean.2
      (ih htail) z

lemma hasDerivAt_fieldScalarLogCosh (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
      (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth hm
    zero_le_one field_abs_tanh_le_one
  intro x
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of the actual scalar spin transition, with a
linearly growing potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldSpinTransition_derivative_bound (ζ : ℝ) (v : ℝ≥0)
    {F D a b : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {C M L : ℝ} (_hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ u, |D u| ≤ C) (hab : ∀ u, |a u| ≤ M) (hbb : ∀ u, |b u| ≤ L)
    (z : ℝ) :
    |fieldSpinTransition ζ v F b z + ζ *
      (fieldSpinTransition ζ v F (fun u => a u * D u) z -
        fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z)| ≤
      L + 2 * |ζ| * M * C := by
  have hAD : ∀ u, |a u * D u| ≤ M * C := fun u => by
    rw [abs_mul]
    exact mul_le_mul (hab u) (hDb u) (abs_nonneg _) hM
  have hb' := fieldSpinTransition_bound ζ v hF hG hbb z
  have ha' := fieldSpinTransition_bound ζ v hF hG hab z
  have hd' := fieldSpinTransition_bound ζ v hF hG hDb z
  have had' := fieldSpinTransition_bound ζ v hF hG hAD z
  refine (abs_add_le _ _).trans (add_le_add hb' ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (|fieldSpinTransition ζ v F (fun u => a u * D u) z| +
        |fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ζ)
    _ ≤ |ζ| * (M * C + M * C) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
      apply add_le_add had'
      rw [abs_mul]
      exact mul_le_mul ha' hd' (abs_nonneg _) hM
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded second derivatives through the actual finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarSecond : List (ℝ × ℝ≥0) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, b => b
  | av :: L, F, a, b => fun z =>
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSecond L F a b) z +
        av.1 * (fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fun u => (fieldScalarMean L F a u) ^ 2) z -
            (fieldScalarMean (av :: L) F a z) ^ 2)

theorem fieldScalarSecond_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {K C : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ C) :
    Measurable (fieldScalarSecond L F a b) ∧
      ∀ z, |fieldScalarSecond L F a b z| ≤ fieldScalarSecondCap L K C := by
  induction L with
  | nil => exact ⟨hb, hbB⟩
  | cons av L ih =>
    have htail (bv) (h : bv ∈ L) := hL bv (List.mem_cons_of_mem av h)
    obtain ⟨hm, hB⟩ := ih htail
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hnew := fieldScalarMean_regular (av :: L) hL hF hG ha haB
    refine ⟨?_, ?_⟩
    · exact (measurable_fieldSpinTransition av.1 av.2 hval.1 hm).add
        (((measurable_fieldSpinTransition av.1 av.2 hval.1 (hmean.1.pow_const 2)).sub
          (hnew.1.pow_const 2)).const_mul av.1)
    · intro z
      have h := fieldSpinTransition_derivative_bound av.1 av.2 hval.1 hval.2
        hK hK hmean.2 hmean.2 hB z
      simpa only [fieldScalarSecond, fieldScalarSecondCap, List.foldr_cons,
        fieldScalarMean, pow_two, mul_assoc] using h

theorem hasDerivAt_fieldScalarMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {K C : ℝ} (hK : 0 ≤ K) (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ C)
    (hd : ∀ z, HasDerivAt F (a z) z) (hdd : ∀ z, HasDerivAt a (b z) z) (z : ℝ) :
    HasDerivAt (fieldScalarMean L F a) (fieldScalarSecond L F a b z) z := by
  induction L generalizing z with
  | nil => exact hdd z
  | cons av L ih =>
    have htail (bv) (h : bv ∈ L) := hL bv (List.mem_cons_of_mem av h)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hsecond := fieldScalarSecond_regular L htail hF hG ha hb hK haB hbB
    have h := hasDerivAt_fieldSpinTransition av.1 av.2 hval.1 hval.2 hmean.1 hmean.1
      hsecond.1 hK hK hmean.2 hmean.2 hsecond.2
      (hasDerivAt_fieldScalarValue L htail hF hG ha hK haB hd) (ih htail) z
    simpa only [fieldScalarMean, fieldScalarSecond, pow_two] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarLogCoshSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded first and second spatial derivatives for the scalar Ising
backward recursion, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldScalarLogCoshSecond_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    Measurable (fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2)) ∧
      ∀ z, |fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z| ≤ fieldScalarSecondCap L 1 1 := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply fieldScalarSecond_regular L hL measurable_logCosh logCosh_linearGrowth
    ht
    (by fun_prop) zero_le_one field_abs_tanh_le_one field_tanh_second_bound

theorem hasDerivAt_fieldScalarLogCoshMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh)
      (fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z) z := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarMean L hL measurable_logCosh logCosh_linearGrowth ht
    (by fun_prop) zero_le_one field_abs_tanh_le_one field_tanh_second_bound
  · intro x
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  · exact field_hasDerivAt_tanh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianFamilyLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine-variance generator needs no separate uniform-growth
hypothesis: the bounded spatial derivative and joint differentiability
produce it on a neighborhood of each positive-variance point. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_local_hasFDerivAt
    {U T X XX : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X) (hXX : Measurable XX)
    {CT CX CXX : ℝ} (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT)
    (hCX : ∀ q, |X q| ≤ CX) (hCXX : ∀ q, |XX q| ≤ CXX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (dx : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y)
    (dxx : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y)
    (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) (hv : 0 < a + v * p.1) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (pairLinear
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => T (p.1, y)) p.2 +
          v / 2 * gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y))
            (fun y => XX (p.1, y) + ζ * (X (p.1, y)) ^ 2) p.2)
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => X (p.1, y)) p.2)) p := by
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX (0, 0))
  have hpair : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hc : ContinuousAt (fun t => U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : ℝ => (t, (0 : ℝ))) (x := p.1)
      (hd (p.1, 0) hp).continuousAt hpair
  have hg := field_parameter_growth_eventually hCX0 hCX dx hc
  have hvcont : ContinuousAt (fun t : ℝ => a + v * t) p.1 := by fun_prop
  have hvset : {t : ℝ | (a + v * p.1) / 2 < a + v * t ∧
      a + v * t < a + v * p.1 + 1} ∈ 𝓝 p.1 :=
    hvcont (Ioo_mem_nhds (by linarith) (by linarith))
  have hset : {t : ℝ | t ∈ I ∧
      (∀ y, |U (t, y)| ≤ |U (p.1, 0)| + 1 + CX * |y|) ∧
      (a + v * p.1) / 2 < a + v * t ∧ a + v * t < a + v * p.1 + 1} ∈ 𝓝 p.1 := by
    filter_upwards [hI.mem_nhds hp, hg, hvset] with t ht hgt hvt
    exact ⟨ht, hgt, hvt⟩
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  exact field_gaussianFamily_hasFDerivAt hJopen hU hT hX hXX
    (K := |U (p.1, 0)| + 1) (L := CX) (by positivity) hCX0
    (fun q hq => (hJsub hq).2.1 q.2)
    (fun q hq => hCT q (hJsub hq).1) hCX hCXX
    (fun q hq => hd q (hJsub hq).1) dx dxx a v ζ
    (m := (a + v * p.1) / 2) (V := a + v * p.1 + 1) (by positivity)
    (fun t ht => (hJsub ht).2.2.1.le)
    (fun t ht => (hJsub ht).2.2.2.le) hpJ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSmoothFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field family carrying exactly the derivatives needed for
finite covariance-coordinate differentiation. No bound on the value is
required: bounded spatial derivative supplies its Gaussian moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

def transform (hI : IsOpen I) (a v ζ : ℝ) (hv : ∀ t ∈ I, 0 < a + v * t) :
    FieldSmoothFamily I where
  U := F.value a v ζ
  X := F.mean a v ζ
  XX := F.curvature a v ζ
  T := F.tangent a v ζ
  KX := F.KX
  KXX := F.KXX + 2 * |ζ| * F.KX ^ 2
  KT := F.KT + |v| / 2 * (F.KXX + |ζ| * F.KX ^ 2)
  mU := F.measurable_value a v ζ
  mX := F.measurable_mean a v ζ
  mXX := F.measurable_curvature a v ζ
  mT := F.measurable_tangent a v ζ
  bX := F.bound_mean a v ζ
  bXX := F.bound_curvature a v ζ
  bT := fun _ hp => F.bound_tangent a v ζ hp
  derivative := fun p hp => field_gaussianFamily_local_hasFDerivAt hI F.mU F.mT F.mX F.mXX
    F.bT F.bX F.bXX F.derivative F.spatial F.second a v ζ hp (hv p.1 hp)
  spatial := F.spatial_value a v ζ
  second := F.spatial_mean a v ζ

end FieldSmoothFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the affine family with the already constructed
finite scalar values and physical conditional means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldAffineIncrements (L : List FieldAffineStep) (t : ℝ) : List (ℝ × ℝ≥0) :=
  L.map fun av => (av.exponent, Real.toNNReal (av.base + av.slope * t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

/-- The original partition with an admissible updated height vector. -/
def fieldWithHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) : FieldStep :=
  { h with height := r, nonneg := hr0, ordered_height := hrmono }

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightCone
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict finite field-height cone and its original FieldStep
representatives. Positive increments give every height and order constraint. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldStepOfStrictHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) : FieldStep :=
  fieldWithHeights h r (fieldStrictHeightCone_nonneg hr) (fieldStrictHeightCone_strictMono hr).monotone

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAdjacentScalarLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjacent and final height-variation families have the same
literal scalar transition lists used in the original finite field model. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAdjacentAffineList (a b ζ η : ℝ) (L : List FieldAffineStep) : List FieldAffineStep :=
  ⟨a, 1, ζ⟩ :: ⟨b, -1, η⟩ :: L

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpatialThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Third spatial differentiation of one actual Gaussian backward step.
The formula is kept as tilted averages, so it also applies to zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldCurvatureTransform (ζ : ℝ) (v : ℝ≥0) (F M Q : ℝ → ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ v F Q z + ζ *
    (fieldSpinTransition ζ v F (fun y => (M y) ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2)

def fieldThirdTransform (ζ : ℝ) (v : ℝ≥0) (F M Q R : ℝ → ℝ) (z : ℝ) : ℝ :=
  (fieldSpinTransition ζ v F R z + ζ *
    (fieldSpinTransition ζ v F (fun y => Q y * M y) z -
      fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F M z)) +
  ζ * ((fieldSpinTransition ζ v F (fun y => 2 * M y * Q y) z + ζ *
    (fieldSpinTransition ζ v F (fun y => (M y) ^ 2 * M y) z -
      fieldSpinTransition ζ v F (fun y => (M y) ^ 2) z *
        fieldSpinTransition ζ v F M z)) -
    2 * fieldSpinTransition ζ v F M z * fieldCurvatureTransform ζ v F M Q z)

lemma hasDerivAt_fieldCurvatureTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    {K C D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C) (bR : ∀ y, |R y| ≤ D)
    (dF : ∀ y, HasDerivAt F (M y) y)
    (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y) (z : ℝ) :
    HasDerivAt (fieldCurvatureTransform ζ v F M Q)
      (fieldThirdTransform ζ v F M Q R z) z := by
  have hm2 : Measurable (fun y => (M y) ^ 2) := hM.pow_const 2
  have hmQ : Measurable (fun y => 2 * M y * Q y) :=
    (measurable_const.mul hM).mul hQ
  have bm2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bmQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have dm2 : ∀ y, HasDerivAt (fun w => (M w) ^ 2) (2 * M y * Q y) y := by
    intro y
    convert (dM y).pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hmean := hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ
    hK hK bM bM bQ dF dM z
  have hmean' : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldCurvatureTransform ζ v F M Q z) z := by
    simpa only [fieldCurvatureTransform, pow_two] using hmean
  have hsecond := hasDerivAt_fieldSpinTransition ζ v hF hG hM hQ hR
    hK hC bM bQ bR dF dQ z
  have hsq := hasDerivAt_fieldSpinTransition ζ v hF hG hM hm2 hmQ
    hK (sq_nonneg K) bM bm2 bmQ dF dm2 z
  have hd := hsecond.add ((hsq.sub (hmean'.pow 2)).const_mul ζ)
  refine hd.congr_deriv (Eq.symm ?_)
  · simp [fieldThirdTransform]

lemma measurable_fieldThirdTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hM : Measurable M)
    (hQ : Measurable Q) (hR : Measurable R) :
    Measurable (fieldThirdTransform ζ v F M Q R) := by
  have hm := measurable_fieldSpinTransition ζ v hF hM
  have hq := measurable_fieldSpinTransition ζ v hF hQ
  have hr := measurable_fieldSpinTransition ζ v hF hR
  have hqm := measurable_fieldSpinTransition ζ v hF (hQ.mul hM)
  have hm2 := measurable_fieldSpinTransition ζ v hF (hM.pow_const 2)
  have hm2m := measurable_fieldSpinTransition ζ v hF ((hM.pow_const 2).mul hM)
  have h2mq : Measurable (fieldSpinTransition ζ v F (fun y => 2 * M y * Q y)) :=
    measurable_fieldSpinTransition ζ v hF ((measurable_const.mul hM).mul hQ)
  exact (hr.add ((hqm.sub (hq.mul hm)).const_mul ζ)).add
    (((h2mq.add ((hm2m.sub (hm2.mul hm)).const_mul ζ)).sub
      ((measurable_const.mul hm).mul
        (hq.add ((hm2.sub (hm.pow_const 2)).const_mul ζ)))).const_mul ζ)

lemma fieldThirdTransform_bound (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {K C D : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C) (bR : ∀ y, |R y| ≤ D)
    (z : ℝ) : |fieldThirdTransform ζ v F M Q R z| ≤ fieldThirdTransformCap ζ K C D := by
  have bm2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bmQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have hfirst := fieldSpinTransition_derivative_bound ζ v hF hG hK hC bM bQ bR z
  have hsecond := fieldSpinTransition_derivative_bound ζ v hF hG hK (sq_nonneg K)
    bM bm2 bmQ z
  have hm := fieldSpinTransition_bound ζ v hF hG bM z
  have hq : |fieldCurvatureTransform ζ v F M Q z| ≤ C + 2 * |ζ| * K ^ 2 := by
    have hh := fieldSpinTransition_derivative_bound ζ v hF hG hK hK bM bM bQ z
    simpa only [fieldCurvatureTransform, pow_two, mul_assoc] using hh
  have hprod : |2 * fieldSpinTransition ζ v F M z * fieldCurvatureTransform ζ v F M Q z| ≤
      2 * K * (C + 2 * |ζ| * K ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) hq
      (abs_nonneg _) (by positivity)
  unfold fieldThirdTransform fieldThirdTransformCap
  refine (abs_add_le _ _).trans (add_le_add hfirst ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hsecond hprod))
    (abs_nonneg ζ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third spatial derivative propagated through the finite scalar
recursion, with an explicit finite bound at every level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarThird : List (ℝ × ℝ≥0) →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, _, c => c
  | av :: L, F, a, b, c => fieldThirdTransform av.1 av.2
      (fieldScalarValue L F) (fieldScalarMean L F a)
      (fieldScalarSecond L F a b) (fieldScalarThird L F a b c)

lemma fieldScalarThird_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {K C D : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C) (bc : ∀ z, |c z| ≤ D) :
    Measurable (fieldScalarThird L F a b c) ∧
      ∀ z, |fieldScalarThird L F a b c z| ≤ fieldScalarThirdCap L K C D := by
  induction L with
  | nil => exact ⟨hc, bc⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := ih ht
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    exact ⟨measurable_fieldThirdTransform av.1 av.2 hv.1 hm.1 hq.1 hr.1,
      fieldThirdTransform_bound av.1 av.2 hv.1 hv.2 hK hC hm.2 hq.2 hr.2⟩

lemma hasDerivAt_fieldScalarSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {K C D : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C) (bc : ∀ z, |c z| ≤ D)
    (dF : ∀ z, HasDerivAt F (a z) z)
    (da : ∀ z, HasDerivAt a (b z) z)
    (db : ∀ z, HasDerivAt b (c z) z) (z : ℝ) :
    HasDerivAt (fieldScalarSecond L F a b) (fieldScalarThird L F a b c z) z := by
  induction L generalizing z with
  | nil => exact db z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    have hd := hasDerivAt_fieldCurvatureTransform av.1 av.2 hv.1 hv.2
      hm.1 hq.1 hr.1 hK hC hm.2 hq.2 hr.2
      (hasDerivAt_fieldScalarValue L ht hF hG ha hK ba dF)
      (hasDerivAt_fieldScalarMean L ht hF hG ha hb hK ba bb dF da) (ih ht) z
    exact hd

lemma field_logCosh_third_bound (z : ℝ) :
    |-2 * Real.tanh z / (Real.cosh z) ^ 2| ≤ 2 := by
  have ht := field_abs_tanh_le_one z
  have hq := field_tanh_second_bound z
  have hh : |-2 * Real.tanh z / (Real.cosh z) ^ 2| =
      2 * |Real.tanh z| * |1 / (Real.cosh z) ^ 2| := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_div, abs_one]
    ring
  rw [hh]
  calc
    _ ≤ 2 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hq
      (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

lemma hasDerivAt_fieldScalarLogCoshSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2))
      (fieldScalarThird L (fun z => Real.log (Real.cosh z)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2)
        (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2) z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  apply hasDerivAt_fieldScalarSecond L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  · intro y
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  · exact field_hasDerivAt_tanh
  · exact field_logCosh_third_derivative

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpatialFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth spatial differentiation of the actual Gaussian field step.
The derivative is expressed in bounded tilted averages; no positive-variance
assumption is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTiltSpatial (ζ : ℝ) (v : ℝ≥0) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ v F B z + ζ *
    (fieldSpinTransition ζ v F (fun y => A y * M y) z -
      fieldSpinTransition ζ v F A z * fieldSpinTransition ζ v F M z)

lemma measurable_fieldTiltSpatial (ζ : ℝ) (v : ℝ≥0) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fieldTiltSpatial ζ v F M A B) := by
  exact (measurable_fieldSpinTransition ζ v hF hB).add
    (((measurable_fieldSpinTransition ζ v hF (hA.mul hM)).sub
      ((measurable_fieldSpinTransition ζ v hF hA).mul
        (measurable_fieldSpinTransition ζ v hF hM))).const_mul ζ)

def fieldFourthTransform (ζ : ℝ) (v : ℝ≥0) (F M Q R S : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let D := fieldTiltSpatial ζ v F M
  let q := fieldCurvatureTransform ζ v F M Q z
  let r := fieldThirdTransform ζ v F M Q R z
  D R S z + ζ * (D (fun y => Q y * M y) (fun y => R y * M y + Q y * Q y) z -
    (D Q R z * T M z + T Q z * q)) +
  ζ * ((D (fun y => 2 * M y * Q y) (fun y => 2 * Q y * Q y + 2 * M y * R y) z +
    ζ * (D (fun y => (M y) ^ 2 * M y) (fun y => 3 * (M y) ^ 2 * Q y) z -
      (D (fun y => (M y) ^ 2) (fun y => 2 * M y * Q y) z * T M z +
        T (fun y => (M y) ^ 2) z * q))) -
    2 * (q * q + T M z * r))

lemma hasDerivAt_fieldThirdTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S)
    {K C D E : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (bR : ∀ y, |R y| ≤ D) (bS : ∀ y, |S y| ≤ E)
    (dF : ∀ y, HasDerivAt F (M y) y)
    (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y)
    (dR : ∀ y, HasDerivAt R (S y) y) (z : ℝ) :
    HasDerivAt (fieldThirdTransform ζ v F M Q R)
      (fieldFourthTransform ζ v F M Q R S z) z := by
  have bprod {A B : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
      (ba : ∀ y, |A y| ≤ a) (bb : ∀ y, |B y| ≤ b) (y : ℝ) :
      |A y * B y| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (ba y) (bb y) (abs_nonneg _) ha
  have bsq : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bQM := bprod hC bQ bM
  have b2MQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have bM3 := bprod (sq_nonneg K) bsq bM
  have bQM' : ∀ y, |R y * M y + Q y * Q y| ≤ D * K + C * C := by
    intro y
    exact (abs_add_le _ _).trans (add_le_add (bprod hD bR bM y) (bprod hC bQ bQ y))
  have b2MQ' : ∀ y, |2 * Q y * Q y + 2 * M y * R y| ≤ 2 * C * C + 2 * K * D := by
    intro y
    rw [show 2 * Q y * Q y + 2 * M y * R y =
      2 * (Q y * Q y) + 2 * (M y * R y) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bprod hC bQ bQ y) (by norm_num : (0 : ℝ) ≤ 2)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bprod hK bM bR y) (by norm_num : (0 : ℝ) ≤ 2)
  have bM3' : ∀ y, |3 * (M y) ^ 2 * Q y| ≤ 3 * K ^ 2 * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bsq y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have dQM (y : ℝ) : HasDerivAt (fun x => Q x * M x) (R y * M y + Q y * Q y) y :=
    (dQ y).mul (dM y)
  have d2MQ (y : ℝ) : HasDerivAt (fun x => 2 * M x * Q x)
      (2 * Q y * Q y + 2 * M y * R y) y := by
    convert ((dM y).const_mul 2).mul (dQ y) using 1
    all_goals try with_reducible_and_instances rfl
  have dM3 (y : ℝ) : HasDerivAt (fun x => (M x) ^ 2 * M x)
      (3 * (M y) ^ 2 * Q y) y := by
    convert ((dM y).pow 2).mul (dM y) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.pow_apply]
    ring
  have dM2 (y : ℝ) : HasDerivAt (fun x => (M x) ^ 2) (2 * M y * Q y) y := by
    convert (dM y).pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have ht (A B : ℝ → ℝ) (ha : Measurable A) (hb : Measurable B)
      {a b : ℝ} (ha0 : 0 ≤ a) (ba : ∀ y, |A y| ≤ a) (bb : ∀ y, |B y| ≤ b)
      (dab : ∀ y, HasDerivAt A (B y) y) :
      HasDerivAt (fieldSpinTransition ζ v F A) (fieldTiltSpatial ζ v F M A B z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM ha hb hK ha0 bM ba bb dF dab z
  have hm := ht M Q hM hQ hK bM bQ dM
  have hm' : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldCurvatureTransform ζ v F M Q z) z := by
    simpa only [fieldTiltSpatial, fieldCurvatureTransform, pow_two] using hm
  have hq := ht Q R hQ hR hC bQ bR dQ
  have hr := ht R S hR hS hD bR bS dR
  have hqm := ht _ _ (hQ.mul hM) ((hR.mul hM).add (hQ.mul hQ))
    (mul_nonneg hC hK) bQM bQM' dQM
  have h2mq := ht _ _ ((measurable_const.mul hM).mul hQ)
    (((measurable_const.mul hQ).mul hQ).add ((measurable_const.mul hM).mul hR))
    (by positivity) b2MQ b2MQ' d2MQ
  have hm3 := ht _ _ ((hM.pow_const 2).mul hM) ((measurable_const.mul (hM.pow_const 2)).mul hQ)
    (by positivity) bM3 bM3' dM3
  have hm2 := ht _ _ (hM.pow_const 2) ((measurable_const.mul hM).mul hQ)
    (sq_nonneg K) bsq b2MQ dM2
  have hcurv := hasDerivAt_fieldCurvatureTransform ζ v hF hG hM hQ hR hK hC bM bQ bR dF dM dQ z
  have hd := (hr.add ((hqm.sub (hq.mul hm')).const_mul ζ)).add
    (((h2mq.add ((hm3.sub (hm2.mul hm')).const_mul ζ)).sub
      ((hm'.mul hcurv).const_mul 2)).const_mul ζ)
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    change fieldThirdTransform ζ v F M Q R y =
      (fieldSpinTransition ζ v F R y + ζ *
        (fieldSpinTransition ζ v F (fun u => Q u * M u) y -
          fieldSpinTransition ζ v F Q y * fieldSpinTransition ζ v F M y)) +
      ζ * ((fieldSpinTransition ζ v F (fun u => 2 * M u * Q u) y + ζ *
        (fieldSpinTransition ζ v F (fun u => M u ^ 2 * M u) y -
          fieldSpinTransition ζ v F (fun u => M u ^ 2) y * fieldSpinTransition ζ v F M y)) -
        2 * (fieldSpinTransition ζ v F M y * fieldCurvatureTransform ζ v F M Q y))
    simp only [fieldThirdTransform]
    ring
  · rfl

lemma measurable_fieldFourthTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hM : Measurable M)
    (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S) :
    Measurable (fieldFourthTransform ζ v F M Q R S) := by
  have hm := measurable_fieldSpinTransition ζ v hF hM
  have hq := measurable_fieldSpinTransition ζ v hF hQ
  have hm2 := measurable_fieldSpinTransition ζ v hF (hM.pow_const 2)
  have hc : Measurable (fieldCurvatureTransform ζ v F M Q) :=
    hq.add ((hm2.sub (hm.pow_const 2)).const_mul ζ)
  have hr := measurable_fieldThirdTransform ζ v hF hM hQ hR
  have h1 := measurable_fieldTiltSpatial ζ v hF hM hR hS
  have h2 := measurable_fieldTiltSpatial ζ v hF hM (hQ.mul hM)
    ((hR.mul hM).add (hQ.mul hQ))
  have h3 := measurable_fieldTiltSpatial ζ v hF hM hQ hR
  have h4 := measurable_fieldTiltSpatial ζ v hF hM (((measurable_const (a := (2 : ℝ))).mul hM).mul hQ)
    ((((measurable_const (a := (2 : ℝ))).mul hQ).mul hQ).add
      (((measurable_const (a := (2 : ℝ))).mul hM).mul hR))
  have h5 := measurable_fieldTiltSpatial ζ v hF hM ((hM.pow_const 2).mul hM)
    (((measurable_const (a := (3 : ℝ))).mul (hM.pow_const 2)).mul hQ)
  have h6 := measurable_fieldTiltSpatial ζ v hF hM (hM.pow_const 2)
    (((measurable_const (a := (2 : ℝ))).mul hM).mul hQ)
  exact (h1.add ((h2.sub ((h3.mul hm).add (hq.mul hc))).const_mul ζ)).add
    (((h4.add ((h5.sub ((h6.mul hm).add (hm2.mul hc))).const_mul ζ)).sub
      (((hc.mul hc).add (hm.mul hr)).const_mul 2)).const_mul ζ)

lemma fieldFourthTransform_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {K C D E : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (bR : ∀ y, |R y| ≤ D) (bS : ∀ y, |S y| ≤ E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |fieldFourthTransform ζ v F M Q R S z| ≤ B := by
  have mM : MagneticUniformBound M := ⟨K, hK, bM⟩
  have mQ : MagneticUniformBound Q := ⟨C, hC, bQ⟩
  have mR : MagneticUniformBound R := ⟨D, (abs_nonneg _).trans (bR 0), bR⟩
  have mS : MagneticUniformBound S := ⟨E, (abs_nonneg _).trans (bS 0), bS⟩
  have hT (A : ℝ → ℝ) (ha : MagneticUniformBound A) :
      MagneticUniformBound (fieldSpinTransition ζ v F A) := by
    obtain ⟨a, ha0, ha⟩ := ha
    exact ⟨a, ha0, fieldSpinTransition_bound ζ v hF hG ha⟩
  have hD (A B : ℝ → ℝ) (ha : MagneticUniformBound A) (hb : MagneticUniformBound B) :
      MagneticUniformBound (fieldTiltSpatial ζ v F M A B) := by
    obtain ⟨a, ha0, ha⟩ := ha
    obtain ⟨b, hb0, hb⟩ := hb
    exact ⟨b + 2 * |ζ| * a * K, by positivity,
      fieldSpinTransition_derivative_bound ζ v hF hG hK ha0 bM ha hb⟩
  have mM2 : MagneticUniformBound (fun y => (M y) ^ 2) := by
    simpa only [pow_two] using magnetic_uniform_mul mM mM
  have m2MQ := magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mM) mQ
  have mQnew : MagneticUniformBound (fieldCurvatureTransform ζ v F M Q) := by
    have he : (fun z => fieldSpinTransition ζ v F Q z + ζ *
        (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
          fieldSpinTransition ζ v F M z * fieldSpinTransition ζ v F M z)) =
        fieldCurvatureTransform ζ v F M Q := by
      funext z
      simp only [fieldCurvatureTransform, pow_two]
    rw [← he]
    exact magnetic_uniform_add (hT Q mQ) (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub (hT _ mM2) (magnetic_uniform_mul (hT M mM) (hT M mM))))
  have mRnew : MagneticUniformBound (fieldThirdTransform ζ v F M Q R) := by
    have hb := fieldThirdTransform_bound ζ v hF hG hK hC bM bQ bR
    exact ⟨_, (abs_nonneg _).trans (hb 0), hb⟩
  have m1 := hD R S mR mS
  have m2 := hD _ _ (magnetic_uniform_mul mQ mM)
    (magnetic_uniform_add (magnetic_uniform_mul mR mM) (magnetic_uniform_mul mQ mQ))
  have m3 := hD Q R mQ mR
  have m4 := hD _ _ m2MQ
    (magnetic_uniform_add
      (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mQ) mQ)
      (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mM) mR))
  have m5 := hD _ _ (magnetic_uniform_mul mM2 mM)
    (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 3) mM2) mQ)
  have m6 := hD _ _ mM2 m2MQ
  exact magnetic_uniform_add
    (magnetic_uniform_add m1 (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub m2
        (magnetic_uniform_add (magnetic_uniform_mul m3 (hT M mM))
          (magnetic_uniform_mul (hT Q mQ) mQnew)))))
    (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub
        (magnetic_uniform_add m4 (magnetic_uniform_mul (magnetic_uniform_const ζ)
          (magnetic_uniform_sub m5
            (magnetic_uniform_add (magnetic_uniform_mul m6 (hT M mM))
              (magnetic_uniform_mul (hT _ mM2) mQnew)))))
        (magnetic_uniform_mul (magnetic_uniform_const 2)
          (magnetic_uniform_add (magnetic_uniform_mul mQnew mQnew)
            (magnetic_uniform_mul (hT M mM) mRnew)))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fourth spatial derivative through every finite backward
level. Its global bound is finite for each fixed finite field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarFourth : List (ℝ × ℝ≥0) →
    (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, _, _, _, d => d
  | av :: L, F, a, b, c, d => fieldFourthTransform av.1 av.2
      (fieldScalarValue L F) (fieldScalarMean L F a)
      (fieldScalarSecond L F a b) (fieldScalarThird L F a b c)
      (fieldScalarFourth L F a b c d)

lemma fieldScalarFourth_regular (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c d : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    {K C D E : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C)
    (bc : ∀ z, |c z| ≤ D) (bd : ∀ z, |d z| ≤ E) :
    Measurable (fieldScalarFourth L F a b c d) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |fieldScalarFourth L F a b c d z| ≤ B := by
  induction L with
  | nil => exact ⟨hd, E, (abs_nonneg _).trans (bd 0), bd⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    obtain ⟨hs, B, hB, bs⟩ := ih ht
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    exact ⟨measurable_fieldFourthTransform av.1 av.2 hv.1 hm.1 hq.1 hr.1 hs,
      fieldFourthTransform_bounded av.1 av.2 hv.1 hv.2 hK hC hm.2 hq.2 hr.2 bs⟩

lemma hasDerivAt_fieldScalarThird (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a b c d : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    {K C D E : ℝ} (hK : 0 ≤ K)
    (ba : ∀ z, |a z| ≤ K) (bb : ∀ z, |b z| ≤ C)
    (bc : ∀ z, |c z| ≤ D) (bd : ∀ z, |d z| ≤ E)
    (dF : ∀ z, HasDerivAt F (a z) z)
    (da : ∀ z, HasDerivAt a (b z) z)
    (db : ∀ z, HasDerivAt b (c z) z)
    (dc : ∀ z, HasDerivAt c (d z) z) (z : ℝ) :
    HasDerivAt (fieldScalarThird L F a b c)
      (fieldScalarFourth L F a b c d z) z := by
  induction L generalizing z with
  | nil => exact dc z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha ba
    have hq := fieldScalarSecond_regular L ht hF hG ha hb hK ba bb
    have hr := fieldScalarThird_regular L ht hF hG ha hb hc hK ba bb bc
    obtain ⟨hs, B, hB, bs⟩ := fieldScalarFourth_regular L ht hF hG ha hb hc hd hK ba bb bc bd
    have hC : 0 ≤ fieldScalarSecondCap L K C := (abs_nonneg _).trans (hq.2 0)
    have hD : 0 ≤ fieldScalarThirdCap L K C D := (abs_nonneg _).trans (hr.2 0)
    exact hasDerivAt_fieldThirdTransform av.1 av.2 hv.1 hv.2 hm.1 hq.1 hr.1 hs hK hC hD
      hm.2 hq.2 hr.2 bs
      (hasDerivAt_fieldScalarValue L ht hF hG ha hK ba dF)
      (hasDerivAt_fieldScalarMean L ht hF hG ha hb hK ba bb dF da)
      (hasDerivAt_fieldScalarSecond L ht hF hG ha hb hc hK ba bb bc dF da db)
      (ih ht) z

lemma field_logCosh_fourth_derivative (z : ℝ) :
    HasDerivAt (fun y : ℝ => -2 * Real.tanh y / (Real.cosh y) ^ 2)
      (fieldLogCoshFourth z) z := by
  have hd := ((field_hasDerivAt_tanh z).const_mul (-2)).mul
    (field_logCosh_third_derivative z)
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  · simp only [fieldLogCoshFourth, div_eq_mul_inv]
    ring

lemma field_logCosh_fourth_bound (z : ℝ) : |fieldLogCoshFourth z| ≤ 6 := by
  have ht := field_abs_tanh_le_one z
  have hq := field_tanh_second_bound z
  have ht2 : |(Real.tanh z) ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hq2 : |(1 / (Real.cosh z) ^ 2) ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) hq 2
  unfold fieldLogCoshFourth
  refine (abs_add_le _ _).trans ?_
  have hb1 : |-2 * (1 / (Real.cosh z) ^ 2) ^ 2| ≤ 2 := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hb2 : |4 * (Real.tanh z) ^ 2 * (1 / (Real.cosh z) ^ 2)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      4 * |Real.tanh z ^ 2| * |1 / Real.cosh z ^ 2| ≤ 4 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht2 (by norm_num)) hq (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  linarith

lemma hasDerivAt_fieldScalarLogCoshThird (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarThird L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2))
      (fieldScalarFourth L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) (fun y => -2 * Real.tanh y / (Real.cosh y) ^ 2)
        fieldLogCoshFourth z) z := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hf : Measurable fieldLogCoshFourth := by
    unfold fieldLogCoshFourth
    fun_prop
  apply hasDerivAt_fieldScalarThird L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) hf zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
  · intro y
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  · exact field_hasDerivAt_tanh
  · exact field_logCosh_third_derivative
  · exact field_logCosh_fourth_derivative

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldTerminal
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained-block terminal payoff. Its prior mass is not
renormalized; the Lipschitz and growth estimates include that fixed mass. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma restrictedSpinLog_le_add {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H K : Spin N → ℝ) (c : ℝ) (h : ∀ σ ∈ S, H σ ≤ K σ + c) :
    restrictedSpinLog S H ≤ restrictedSpinLog S K + c := by
  rw [← restrictedSpinLog_add_const S hS K c]
  exact restrictedSpinLog_mono hS (Finset.Subset.refl _) h

lemma abs_restrictedSpinLog_sub_le {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H K : Spin N → ℝ) (c : ℝ) (h : ∀ σ ∈ S, |H σ - K σ| ≤ c) :
    |restrictedSpinLog S H - restrictedSpinLog S K| ≤ c := by
  have h₁ := restrictedSpinLog_le_add S hS H K c (fun σ hσ => by
    have hh := (abs_le.mp (h σ hσ)).2
    linarith)
  have h₂ := restrictedSpinLog_le_add S hS K H c (fun σ hσ => by
    have hh := (abs_le.mp (h σ hσ)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def restrictedFieldTerminal {N : ℕ} (S : Finset (Spin N)) (z : Fin N → ℝ) : ℝ :=
  restrictedSpinLog S (fieldEnergy z)

lemma restrictedFieldTerminal_difference {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z y : Fin N → ℝ) :
    |restrictedFieldTerminal S z - restrictedFieldTerminal S y| ≤ ∑ i, |z i - y i| :=
  abs_restrictedSpinLog_sub_le S hS _ _ _ (fun σ _ => abs_fieldEnergy_sub_le z y σ)

lemma restrictedFieldTerminal_norm_difference {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z y : Fin N → ℝ) :
    |restrictedFieldTerminal S z - restrictedFieldTerminal S y| ≤ N * ‖z - y‖ := by
  apply (restrictedFieldTerminal_difference S hS z y).trans
  calc
    _ ≤ ∑ _i : Fin N, ‖z - y‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - y) i)
    _ = _ := by simp

lemma continuous_restrictedFieldTerminal {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Continuous (restrictedFieldTerminal S) := by
  apply LipschitzWith.continuous (K := (N : ℝ≥0))
  apply LipschitzWith.of_dist_le_mul
  intro z y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_natCast] using
    restrictedFieldTerminal_norm_difference S hS z y

lemma restrictedFieldTerminal_linearGrowth {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    HasLinearGrowth (restrictedFieldTerminal S) := by
  refine ⟨|restrictedFieldTerminal S 0|, N, abs_nonneg _, Nat.cast_nonneg _, fun z => ?_⟩
  have hb := restrictedFieldTerminal_norm_difference S hS z 0
  simp only [sub_zero] at hb
  have hh := abs_add_le (restrictedFieldTerminal S z - restrictedFieldTerminal S 0)
    (restrictedFieldTerminal S 0)
  rw [sub_add_cancel] at hh
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldRecursion
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vector Gaussian recursion for a constrained cavity block.
Regularity follows from the terminal's finite-spin estimates, with no
assumption on the number of cascade levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def restrictedFieldRecursion {N : ℕ} (S : Finset (Spin N)) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) : (Fin N → ℝ) → ℝ :=
  cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (restrictedFieldTerminal S)

lemma restrictedFieldRecursion_regular {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    Measurable (restrictedFieldRecursion S n b v) ∧
      HasLinearGrowth (restrictedFieldRecursion S n b v) := by
  have hm := (continuous_restrictedFieldTerminal S hS).measurable
  exact ⟨measurable_cascadeRecursion n b _ (fun _ => measurable_fst.add measurable_snd) hm,
    cascadeRecursion_linearGrowth n b _ (fun i _ => vectorGaussianLaw_moments hN (v i))
      hm (restrictedFieldTerminal_linearGrowth S hS) hb⟩

def constrainedBlockValue {N : ℕ} (S : Finset (Spin N)) (h : FieldStep) : ℝ :=
  (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut)
    (fieldStepVariance h) z
    ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))) -
      h.height (Fin.last h.depth) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalSpinWeights
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite canonical weights used in the projection estimates are
exactly the physical Gibbs probabilities, including the uniform prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem integral_uniformSpinGibbs_canonical {N : ℕ} (H A : Spin N → ℝ) :
    (∫ σ, A σ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      ∑ σ, finiteCanonicalWeights H σ * A σ := by
  rw [integral_uniformSpinGibbs_eq]
  simp only [gibbsAverage, finiteGibbs, finitePartition, one_mul, finiteCanonicalWeights]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained terminal spin distribution is the physical Gibbs
law conditioned on the allowed spins. Its entropy cost is exactly the
loss in log partition functions, retaining the original cube mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spinGibbs_mass_finset {N : ℕ} (H : Spin N → ℝ) (S : Finset (Spin N)) :
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S =
      (∑ σ ∈ S, Real.exp (H σ)) / ∑ σ, Real.exp (H σ) := by
  classical
  rw [← integral_indicator_one (μ := gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)
    S.measurableSet, integral_uniformSpinGibbs_canonical]
  simp only [Set.indicator, Pi.one_apply, Finset.mem_coe,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [finiteCanonicalWeights, Finset.sum_div]

lemma spinGibbs_mass_pos {N : ℕ} (H : Spin N → ℝ) (S : Finset (Spin N)) (hS : S.Nonempty) :
    0 < (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S := by
  rw [spinGibbs_mass_finset]
  exact div_pos (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS) (sum_exp_pos H)

def restrictedSpinLaw {N : ℕ} (S : Finset (Spin N)) (H : Spin N → ℝ) : Measure (Spin N) :=
  cond (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) S

lemma restrictedSpinLaw_probability {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) : IsProbabilityMeasure (restrictedSpinLaw S H) := by
  apply cond_isProbabilityMeasure
  exact (measureReal_ne_zero_iff).mp (spinGibbs_mass_pos H S hS).ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three spatial derivatives of a bounded continuation through a single
actual Gaussian transition. These are the derivatives needed to close the
inverse-coordinate continuation at the two mean-spin endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    (F M Q A B C : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let D := fieldTiltSpatial ζ v F M
  D B C z + ζ * (D (fun y => A y * M y) (fun y => B y * M y + A y * Q y) z -
    (D A B z * T M z + T A z * D M Q z))

def magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    (F M Q R A B C D : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let S := fieldTiltSpatial ζ v F M
  magneticContinuationSecond ζ v F M Q B C D z + ζ *
    (magneticContinuationSecond ζ v F M Q
      (fun y => A y * M y) (fun y => B y * M y + A y * Q y)
      (fun y => C y * M y + 2 * B y * Q y + A y * R y) z -
      (magneticContinuationSecond ζ v F M Q A B C z * T M z +
        2 * S A B z * S M Q z +
        T A z * magneticContinuationSecond ζ v F M Q M Q R z))

lemma hasDerivAt_magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    {K L a b c : ℝ} (hK : 0 ≤ K) (_hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ L)
    (bA : ∀ y, |A y| ≤ a) (bB : ∀ y, |B y| ≤ b) (bC : ∀ y, |C y| ≤ c)
    (dF : ∀ y, HasDerivAt F (M y) y) (dM : ∀ y, HasDerivAt M (Q y) y)
    (dA : ∀ y, HasDerivAt A (B y) y) (dB : ∀ y, HasDerivAt B (C y) y)
    (z : ℝ) :
    HasDerivAt (fieldTiltSpatial ζ v F M A B)
      (magneticContinuationSecond ζ v F M Q A B C z) z := by
  have bAM : ∀ y, |A y * M y| ≤ a * K := by
    intro y
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) ha
  have bAM' : ∀ y, |B y * M y + A y * Q y| ≤ b * K + a * L := by
    intro y
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hb
    · rw [abs_mul]
      exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) ha
  have htA := hasDerivAt_fieldSpinTransition ζ v hF hG hM hA hB hK ha bM bA bB dF dA z
  have htB := hasDerivAt_fieldSpinTransition ζ v hF hG hM hB hC hK hb bM bB bC dF dB z
  have htM := hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ hK hK bM bM bQ dF dM z
  have htAM := hasDerivAt_fieldSpinTransition ζ v hF hG hM (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ)) hK (mul_nonneg ha hK) bM bAM bAM'
    dF (fun y => (dA y).mul (dM y)) z
  exact htB.add ((htAM.sub (htA.mul htM)).const_mul ζ)

lemma hasDerivAt_magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    {K L J a b c d : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ L) (bR : ∀ y, |R y| ≤ J)
    (bA : ∀ y, |A y| ≤ a) (bB : ∀ y, |B y| ≤ b)
    (bC : ∀ y, |C y| ≤ c) (bD : ∀ y, |D y| ≤ d)
    (dF : ∀ y, HasDerivAt F (M y) y) (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y)
    (dA : ∀ y, HasDerivAt A (B y) y) (dB : ∀ y, HasDerivAt B (C y) y)
    (dC : ∀ y, HasDerivAt C (D y) y) (z : ℝ) :
    HasDerivAt (magneticContinuationSecond ζ v F M Q A B C)
      (magneticContinuationThird ζ v F M Q R A B C D z) z := by
  have bprod {U V : ℝ → ℝ} {u w : ℝ} (hu : 0 ≤ u)
      (bu : ∀ y, |U y| ≤ u) (bv : ∀ y, |V y| ≤ w) (y : ℝ) :
      |U y * V y| ≤ u * w := by
    rw [abs_mul]
    exact mul_le_mul (bu y) (bv y) (abs_nonneg _) hu
  have bAM := bprod ha bA bM
  have bAM' (y : ℝ) : |B y * M y + A y * Q y| ≤ b * K + a * L :=
    (abs_add_le _ _).trans (add_le_add (bprod hb bB bM y) (bprod ha bA bQ y))
  have bAM'' (y : ℝ) : |C y * M y + 2 * B y * Q y + A y * R y| ≤
      c * K + 2 * b * L + a * J := by
    have h2 : |2 * B y * Q y| ≤ 2 * b * L := by
      rw [show 2 * B y * Q y = 2 * (B y * Q y) by ring, abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (bprod hb bB bQ y) (by norm_num : (0 : ℝ) ≤ 2)
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (bprod hc bC bM y) h2)) (bprod ha bA bR y))
  have dAM (y : ℝ) : HasDerivAt (fun x => A x * M x)
      (B y * M y + A y * Q y) y := (dA y).mul (dM y)
  have dAM' (y : ℝ) : HasDerivAt (fun x => B x * M x + A x * Q x)
      (C y * M y + 2 * B y * Q y + A y * R y) y := by
    convert ((dB y).mul (dM y)).add ((dA y).mul (dQ y)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hSA := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hA hB hC
    hK hL ha hb bM bQ bA bB bC dF dM dA dB z
  have hSB := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hB hC hD
    hK hL hb hc bM bQ bB bC bD dF dM dB dC z
  have hSM := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hM hQ hR
    hK hL hK hL bM bQ bM bQ bR dF dM dM dQ z
  have hSAM := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ
    (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))
    (((hC.mul hM).add ((measurable_const.mul hB).mul hQ)).add (hA.mul hR))
    hK hL (mul_nonneg ha hK) (by positivity) bM bQ bAM bAM' bAM''
    dF dM dAM dAM' z
  change HasDerivAt (fieldTiltSpatial ζ v F M (fun y => A y * M y)
      (fun y => B y * M y + A y * Q y))
    (magneticContinuationSecond ζ v F M Q (fun y => A y * M y)
      (fun y => B y * M y + A y * Q y)
      (fun y => C y * M y + 2 * B y * Q y + A y * R y) z) z at hSAM
  have hTA : HasDerivAt (fieldSpinTransition ζ v F A)
      (fieldTiltSpatial ζ v F M A B z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM hA hB hK ha bM bA bB dF dA z
  have hTM : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldTiltSpatial ζ v F M M Q z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ hK hK bM bM bQ dF dM z
  have hh := hSB.add ((hSAM.sub ((hSA.mul hTM).add (hTA.mul hSM))).const_mul ζ)
  refine hh.congr_deriv (Eq.symm ?_)
  · dsimp only [magneticContinuationThird]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and finite spatial derivative bounds for the actual
Gaussian continuation formulas through order three. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

namespace MagneticContinuationBound

lemma transition (ζ : ℝ) (v : ℝ≥0) {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : MagneticContinuationBound A) :
    MagneticContinuationBound (fieldSpinTransition ζ v F A) := by
  obtain ⟨K, hK, bK⟩ := hA
  exact ⟨K, hK, fieldSpinTransition_bound ζ v hF hG bK⟩

lemma spatial (ζ : ℝ) (v : ℝ≥0) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) :
    MagneticContinuationBound (fieldTiltSpatial ζ v F M A B) := by
  obtain ⟨K, hK, bK⟩ := hM
  obtain ⟨L, hL, bL⟩ := hA
  obtain ⟨C, hC, bC⟩ := hB
  exact ⟨C + 2 * |ζ| * L * K, by positivity,
    fieldSpinTransition_derivative_bound ζ v hF hG hK hL bK bL bC⟩

end MagneticContinuationBound

lemma measurable_magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F)
    (hM : Measurable M) (hQ : Measurable Q)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    Measurable (magneticContinuationSecond ζ v F M Q A B C) := by
  have hS := measurable_fieldTiltSpatial ζ v hF hM hB hC
  have hSA := measurable_fieldTiltSpatial ζ v hF hM hA hB
  have hSM := measurable_fieldTiltSpatial ζ v hF hM hM hQ
  have hSAM := measurable_fieldTiltSpatial ζ v hF hM (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ))
  have hTA := measurable_fieldSpinTransition ζ v hF hA
  have hTM := measurable_fieldSpinTransition ζ v hF hM
  exact hS.add ((hSAM.sub ((hSA.mul hTM).add (hTA.mul hSM))).const_mul ζ)

lemma magneticContinuationSecond_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B)
    (hC : MagneticContinuationBound C) :
    MagneticContinuationBound (magneticContinuationSecond ζ v F M Q A B C) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticContinuationBound.transition ζ v hF hG hA
  have D {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticContinuationBound.spatial ζ v hF hG hM hA hB
  exact (D hB hC).add ((MagneticContinuationBound.const ζ).mul
    ((D (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))).sub
      (((D hA hB).mul (T hM)).add ((T hA).mul (D hM hQ)))))

lemma measurable_magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) :
    Measurable (magneticContinuationThird ζ v F M Q R A B C D) := by
  have h1 := measurable_magneticContinuationSecond ζ v hF hM hQ hB hC hD
  have h2 := measurable_magneticContinuationSecond ζ v hF hM hQ (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ))
    (((hC.mul hM).add (((measurable_const (a := (2 : ℝ))).mul hB).mul hQ)).add (hA.mul hR))
  have h3 := measurable_magneticContinuationSecond ζ v hF hM hQ hA hB hC
  have h4 := measurable_magneticContinuationSecond ζ v hF hM hQ hM hQ hR
  have hTA := measurable_fieldSpinTransition ζ v hF hA
  have hTM := measurable_fieldSpinTransition ζ v hF hM
  have hSA := measurable_fieldTiltSpatial ζ v hF hM hA hB
  have hSM := measurable_fieldTiltSpatial ζ v hF hM hM hQ
  exact h1.add ((h2.sub (((h3.mul hTM).add
    ((measurable_const.mul hSA).mul hSM)).add (hTA.mul h4))).const_mul ζ)

lemma magneticContinuationThird_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hR : MagneticContinuationBound R) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C)
    (hD : MagneticContinuationBound D) :
    MagneticContinuationBound (magneticContinuationThird ζ v F M Q R A B C D) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticContinuationBound.transition ζ v hF hG hA
  have S {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticContinuationBound.spatial ζ v hF hG hM hA hB
  have D2 {A B C : ℝ → ℝ} (hA : MagneticContinuationBound A)
      (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C) :=
    magneticContinuationSecond_bounded ζ v hF hG hM hQ hA hB hC
  have hb2 := (hB.mul hM).add (hA.mul hQ)
  have hb3 := ((hC.mul hM).add
    (((MagneticContinuationBound.const 2).mul hB).mul hQ)).add (hA.mul hR)
  exact (D2 hB hC hD).add ((MagneticContinuationBound.const ζ).mul
    ((D2 (hA.mul hM) hb2 hb3).sub
      ((((D2 hA hB hC).mul (T hM)).add
        ((((MagneticContinuationBound.const 2).mul (S hA hB)).mul (S hM hQ)))).add
          ((T hA).mul (D2 hM hQ hR)))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded third-order spatial jet for the finite Ising continuation.
Only the square and actual Gaussian transition operations are required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

namespace MagneticContinuationJet

def transition (A P : MagneticContinuationJet) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) : MagneticContinuationJet where
  value := fieldSpinTransition ζ v F A.value
  first := fieldTiltSpatial ζ v F P.value A.value A.first
  second := magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second
  third := magneticContinuationThird ζ v F P.value P.first P.second
    A.value A.first A.second A.third
  mValue := measurable_fieldSpinTransition ζ v hF A.mValue
  mFirst := measurable_fieldTiltSpatial ζ v hF P.mValue A.mValue A.mFirst
  mSecond := measurable_magneticContinuationSecond ζ v hF P.mValue P.mFirst
    A.mValue A.mFirst A.mSecond
  mThird := measurable_magneticContinuationThird ζ v hF P.mValue P.mFirst P.mSecond
    A.mValue A.mFirst A.mSecond A.mThird
  bValue := A.bValue.transition ζ v hF hG
  bFirst := MagneticContinuationBound.spatial ζ v hF hG P.bValue A.bValue A.bFirst
  bSecond := magneticContinuationSecond_bounded ζ v hF hG P.bValue P.bFirst
    A.bValue A.bFirst A.bSecond
  bThird := magneticContinuationThird_bounded ζ v hF hG P.bValue P.bFirst P.bSecond
    A.bValue A.bFirst A.bSecond A.bThird
  dValue := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := A.bValue
    obtain ⟨C, _, bC⟩ := A.bFirst
    exact hasDerivAt_fieldSpinTransition ζ v hF hG P.mValue A.mValue A.mFirst
      hK hL bK bL bC dF A.dValue z
  dFirst := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := P.bFirst
    obtain ⟨a, ha, ba⟩ := A.bValue
    obtain ⟨b, hb, bb⟩ := A.bFirst
    obtain ⟨c, _, bc⟩ := A.bSecond
    exact hasDerivAt_magneticContinuationSecond ζ v hF hG P.mValue P.mFirst
      A.mValue A.mFirst A.mSecond hK hL ha hb bK bL ba bb bc dF P.dValue
      A.dValue A.dFirst z
  dSecond := fun z => by
    obtain ⟨K, hK, bK⟩ := P.bValue
    obtain ⟨L, hL, bL⟩ := P.bFirst
    obtain ⟨J, _, bJ⟩ := P.bSecond
    obtain ⟨a, ha, ba⟩ := A.bValue
    obtain ⟨b, hb, bb⟩ := A.bFirst
    obtain ⟨c, hc, bc⟩ := A.bSecond
    obtain ⟨d, _, bd⟩ := A.bThird
    exact hasDerivAt_magneticContinuationThird ζ v hF hG P.mValue P.mFirst P.mSecond
      A.mValue A.mFirst A.mSecond A.mThird hK hL ha hb hc bK bL bJ ba bb bc bd
      dF P.dValue P.dFirst A.dValue A.dFirst A.dSecond z

end MagneticContinuationJet
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFourJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One additional bounded spatial derivative, exactly as needed to
differentiate the inverse-coordinate curvature equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

namespace MagneticContinuationFourJet

def transitionFourth (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (z : ℝ) : ℝ :=
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  R.third z + ζ * (W.third z - (U.third z * V.value z +
    3 * U.second z * V.first z + 3 * U.first z * V.second z + U.value z * V.third z))

lemma transition_third_eq (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
    let V := P.transition P ζ v F hF hG dF
    let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
    let R := A.slope.transition P ζ v F hF hG dF
    U.third = fun z => R.second z + ζ * (W.second z -
      (U.second z * V.value z + 2 * U.first z * V.first z + U.value z * V.second z)) := by
  rfl

lemma transitionFourth_measurable (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    Measurable (A.transitionFourth P ζ v F hF hG dF) := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  exact R.mThird.add ((W.mThird.sub ((((U.mThird.mul V.mValue).add
    ((measurable_const.mul U.mSecond).mul V.mFirst)).add
      ((measurable_const.mul U.mFirst).mul V.mSecond)).add (U.mValue.mul V.mThird))).const_mul ζ)

lemma transitionFourth_bounded (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticContinuationBound (A.transitionFourth P ζ v F hF hG dF) := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  exact R.bThird.add ((MagneticContinuationBound.const ζ).mul
    (W.bThird.sub ((((U.bThird.mul V.bValue).add
      (((MagneticContinuationBound.const 3).mul U.bSecond).mul V.bFirst)).add
        (((MagneticContinuationBound.const 3).mul U.bFirst).mul V.bSecond)).add
          (U.bValue.mul V.bThird))))

lemma transition_hasDerivAt_third (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (z : ℝ) :
    HasDerivAt (A.toMagneticContinuationJet.transition P ζ v F hF hG dF).third
      (A.transitionFourth P ζ v F hF hG dF z) z := by
  let U := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  let V := P.transition P ζ v F hF hG dF
  let W := (A.toMagneticContinuationJet.mul P).transition P ζ v F hF hG dF
  let R := A.slope.transition P ζ v F hF hG dF
  rw [transition_third_eq]
  have hd := (R.dSecond z).add (((W.dSecond z).sub
    ((((U.dSecond z).mul (V.dValue z)).add
      (((U.dFirst z).const_mul 2).mul (V.dFirst z))).add
        ((U.dValue z).mul (V.dSecond z)))).const_mul ζ)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [transitionFourth]
  ring

def transition (A : MagneticContinuationFourJet) (P : MagneticContinuationJet)
    (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) : MagneticContinuationFourJet where
  toMagneticContinuationJet := A.toMagneticContinuationJet.transition P ζ v F hF hG dF
  fourth := A.transitionFourth P ζ v F hF hG dF
  mFourth := A.transitionFourth_measurable P ζ v F hF hG dF
  bFourth := A.transitionFourth_bounded P ζ v F hF hG dF
  dThird := A.transition_hasDerivAt_third P ζ v F hF hG dF

end MagneticContinuationFourJet
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal conditional squared means of the finite Ising recursion
have bounded spatial derivatives through order three. The ordinary root
Gaussian is retained in the statement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticLogCoshMeanJet (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1) :
    MagneticContinuationJet := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hf : Measurable fieldLogCoshFourth := by unfold fieldLogCoshFourth; fun_prop
  have hM := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hQ := fieldScalarLogCoshSecond_regular L hL
  have hR := fieldScalarThird_regular L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound
  have hS := fieldScalarFourth_regular L hL measurable_logCosh logCosh_linearGrowth
    hm (by fun_prop) (by fun_prop) hf zero_le_one field_abs_tanh_le_one
    field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
  refine {
    value := fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh
    first := fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2)
    second := fieldScalarThird L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2) (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2)
    third := fieldScalarFourth L (fun z => Real.log (Real.cosh z)) Real.tanh
      (fun z => 1 / (Real.cosh z) ^ 2) (fun z => -2 * Real.tanh z / (Real.cosh z) ^ 2)
      fieldLogCoshFourth
    mValue := hM.1
    mFirst := hQ.1
    mSecond := hR.1
    mThird := hS.1
    bValue := ⟨1, zero_le_one, hM.2⟩
    bFirst := ⟨_, (abs_nonneg _).trans (hQ.2 0), hQ.2⟩
    bSecond := ⟨_, (abs_nonneg _).trans (hR.2 0), hR.2⟩
    bThird := hS.2
    dValue := hasDerivAt_fieldScalarLogCoshMean L hL
    dFirst := hasDerivAt_fieldScalarLogCoshSecond L hL
    dSecond := hasDerivAt_fieldScalarLogCoshThird L hL }

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

def logCoshMeanFourJet : MagneticContinuationFourJet where
  toMagneticContinuationJet := magneticLogCoshMeanJet [] (by simp)
  fourth := fun z => 16 * Real.tanh z * (1 / Real.cosh z ^ 2) ^ 2 -
    8 * Real.tanh z ^ 3 * (1 / Real.cosh z ^ 2)
  mFourth := by
    simp only [Real.tanh_eq]
    fun_prop
  bFourth := by
    let P := magneticLogCoshMeanJet [] (by simp)
    have hM := P.bValue
    have hQ := P.bFirst
    change MagneticContinuationBound Real.tanh at hM
    change MagneticContinuationBound (fun z => 1 / Real.cosh z ^ 2) at hQ
    have hM3 : MagneticContinuationBound (fun z => Real.tanh z ^ 3) := by
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using (hM.mul hM).mul hM
    have hQ2 : MagneticContinuationBound (fun z => (1 / Real.cosh z ^ 2) ^ 2) := by
      simpa only [pow_two] using hQ.mul hQ
    exact (((MagneticContinuationBound.const 16).mul hM).mul hQ2).sub
      (((MagneticContinuationBound.const 8).mul hM3).mul hQ)
  dThird := fun z => by
    change HasDerivAt fieldLogCoshFourth _ z
    have hM := field_hasDerivAt_tanh z
    have hQ := field_logCosh_third_derivative z
    have hd := ((hQ.pow 2).const_mul (-2)).add (((hM.pow 2).const_mul 4).mul hQ)
    convert (config := {transparency := .instances, preTransparency := .instances}) hd using 1
    · rfl
    · simp only [div_eq_mul_inv, Pi.pow_apply]
      ring

lemma fieldScalarMean_has_bounded_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    ∃ J : MagneticContinuationFourJet,
      J.value = fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => exact ⟨logCoshMeanFourJet, rfl⟩
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    obtain ⟨J, hJ⟩ := ih ht
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hd : ∀ z, HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
        (J.value z) z := by
      rw [hJ]
      exact hasDerivAt_fieldScalarLogCosh L ht
    refine ⟨J.transition J.toMagneticContinuationJet av.1 av.2 _ hv.1 hv.2 hd, ?_⟩
    change fieldSpinTransition av.1 av.2 _ J.value = _
    rw [hJ]
    rfl

def magneticLogCoshMeanFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : MagneticContinuationFourJet :=
  (fieldScalarMean_has_bounded_fourJet L hL).choose

lemma magneticLogCoshMeanFourJet_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    (magneticLogCoshMeanFourJet L hL).toMagneticContinuationJet = magneticLogCoshMeanJet L hL := by
  apply MagneticContinuationJet.eq_of_value_eq
  exact (fieldScalarMean_has_bounded_fourJet L hL).choose_spec

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar curvature satisfies the differentiated heat equation.
The computation uses only four derivatives of the finite scalar value. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatCurvature (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F P.first q.2 + ζ *
    (gaussianTiltAverage q.1 ζ F (fun y => (P.value y) ^ 2) q.2 -
      (gaussianTiltAverage q.1 ζ F P.value q.2) ^ 2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint heat derivatives of the mean spin and of a bounded continuation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticHeatMean (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage q.1 ζ F P.value q.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-tail Gaussian slabs have a unique bias at every
interior prescribed magnetization. These are the inverse coordinates used
in the finite-step parabolic comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabMean (L : List (ℝ × ℝ≥0)) (ζ v : ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ (Real.toNNReal v)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
    (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh) z

def magneticScalarSlabBias (L : List (ℝ × ℝ≥0)) (ζ v s : ℝ) : ℝ :=
  Function.invFun (magneticScalarSlabMean L ζ v) s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial and variance derivatives of the genuine finite-tail inverse
curvature. The minimizing bias is constructed by coercivity, and no
inverse-regularity assumption remains in these statements. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarInverseCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  magneticHeatCurvature (magneticLogCoshMeanJet L hL)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ
    (v, magneticScalarSlabBias L ζ v s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual slab inverse curvature extends continuously to both spin
endpoints. The uniform bound by 1-s² gives joint boundary continuity in
the variance parameter without an asymptotic expansion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticScalarCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseCurvature L hL ζ q.1 q.2 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverse-coordinate PDE of a finite Gaussian slab, with
spatial derivatives and inverse regularity discharged. Time here denotes
applied variance; reversing it gives the manuscript's backward equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) : MagneticContinuationJet :=
  let P := magneticLogCoshMeanJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  P.transition P ζ (Real.toNNReal v)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x))) hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)

def magneticScalarInverseSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  J.second b / J.first b

def magneticScalarInverseSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  J.third b / (J.first b) ^ 2 - (J.second b) ^ 2 / (J.first b) ^ 3

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded observables continued in the inverse mean coordinate.
Both spatial derivatives and the drift cancellation follow from the finite
Gaussian field, with no inverse-regularity assumptions left over. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabContinuation (L : List (ℝ × ℝ≥0))
    (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  magneticHeatMean A (fieldScalarValue L (fun z => Real.log (Real.cosh z))) ζ
    (v, magneticScalarSlabBias L ζ v s)

def magneticScalarSlabContinuationJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v : ℝ) : MagneticContinuationJet :=
  let P := magneticLogCoshMeanJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  A.transition P ζ (Real.toNNReal v)
    (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)

def magneticScalarSlabContinuationSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  K.first b / J.first b

def magneticScalarSlabContinuationSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  K.second b / (J.first b) ^ 2 - K.first b * J.second b / (J.first b) ^ 3

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarSlabEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform endpoint decay of the actual finite-tail square continuation.
The variance may vary arbitrarily as the prescribed spin tends to ±1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let z := magneticScalarSlabBias L ζ v s
  K.second z - K.first z * (J.second z / J.first z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabClosedDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-spin-interval derivatives of the finite slab. The two endpoints
are constant zero in time, while all spatial derivatives are used only
in the open spin interval. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticScalarSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseSlope L hL ζ q.1 q.2 else 0

def closedMagneticScalarSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseSecond L hL ζ q.1 q.2 else 0

def closedMagneticScalarTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ q) ^ 2 / 2 * closedMagneticScalarSecond L hL ζ q +
    ζ * (closedMagneticScalarCurvature L hL ζ q) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives of q²Hᵤᵤ. Multiplying by q² removes the first-order
term from the differentiated inverse-coordinate continuation equation. -/

noncomputable section

namespace InvariantIsing

def magneticWeightedJetFirst (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.third z - (A.second z * P.second z + A.first z * P.third z) / P.first z +
    A.first z * (P.second z) ^ 2 / (P.first z) ^ 2

def magneticWeightedJetSecond (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.fourth z - A.third z * P.second z / P.first z -
    2 * A.second z * P.third z / P.first z +
    2 * A.second z * (P.second z) ^ 2 / (P.first z) ^ 2 -
    A.first z * P.fourth z / P.first z +
    3 * A.first z * P.second z * P.third z / (P.first z) ^ 2 -
    2 * A.first z * (P.second z) ^ 3 / (P.first z) ^ 3

def magneticWeightedInverseSecond (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  magneticWeightedJetSecond P A z / (P.first z) ^ 2 -
    magneticWeightedJetFirst P A z * P.second z / (P.first z) ^ 3

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarWeightedPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted continuation equation specialized to the actual finite
Ising tail. Its inverse coordinate is the proved minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticLogCoshMeanFourJet_derivative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
      ((magneticLogCoshMeanFourJet L hL).value z) z := by
  have he := congrArg MagneticContinuationJet.value (magneticLogCoshMeanFourJet_eq L hL)
  rw [he]
  exact hasDerivAt_fieldScalarLogCosh L hL z

def magneticScalarSlabFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) : MagneticContinuationFourJet :=
  let P := magneticLogCoshMeanFourJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  P.transition P.toMagneticContinuationJet ζ (Real.toNNReal v)
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF.1 hF.2
    (magneticLogCoshMeanFourJet_derivative L hL)

def magneticScalarSlabContinuationFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v : ℝ) :
    MagneticContinuationFourJet :=
  let P := magneticLogCoshMeanFourJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  A.transition P.toMagneticContinuationJet ζ (Real.toNNReal v)
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF.1 hF.2
    (magneticLogCoshMeanFourJet_derivative L hL)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous extension of the actual weighted continuation to the
closed spin interval, uniformly with respect to the slab variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabWeighted L hL A ζ p.1 p.2 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spatial derivatives and the uniformly bounded potential of the
weighted inverse-coordinate continuation equation. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarWeightedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabFourJet L hL ζ v
  let K := magneticScalarSlabContinuationFourJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  magneticWeightedJetFirst J K b / J.first b

def magneticScalarWeightedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) : ℝ :=
  magneticWeightedInverseSecond (magneticScalarSlabFourJet L hL ζ v)
    (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v s)

def magneticScalarWeightedPotential (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  magneticScalarInverseCurvature L hL ζ v s * magneticScalarInverseSecond L hL ζ v s +
    2 * ζ * magneticScalarInverseCurvature L hL ζ v s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-strip derivative data for the weighted continuation. At either
spin endpoint the continued function is identically zero in time. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticWeightedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedSlope L hL A ζ p.1 p.2 else 0

def closedMagneticWeightedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedSecond L hL A ζ p.1 p.2 else 0

def closedMagneticWeightedPotential (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedPotential L hL ζ p.1 p.2 else 0

def closedMagneticWeightedTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2 *
    closedMagneticWeightedSecond L hL A ζ p +
      closedMagneticWeightedPotential L hL ζ p *
        closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_ConstrainedBlockBias
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact bias cancellation on a constrained block and identification of
the unrestricted block with the average scalar field functional. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def biasedConstrainedBlockValue {N : ℕ} (S : Finset (Spin N)) (h : FieldStep)
    (b : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * (∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut)
    (fieldStepVariance h) z
    ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) -
      h.height (Fin.last h.depth) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalPairRootLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-site factorization at the biased shared root. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

def biasedFieldLevelSpinPair (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) : Measure (Bool × Bool) :=
  fieldPairSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
      gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))

instance biasedFieldLevelSpinPair_probability (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) :
    IsProbabilityMeasure (biasedFieldLevelSpinPair h b i) := by
  unfold biasedFieldLevelSpinPair
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapTestDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single diagonal of finite cavity depths works for every continuous
overlap test. Compactness is used only on the overlap interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

def compactOverlapTestExtension (f : CompactOverlapTest) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (Set.projIcc 0 1 zero_le_one x))
    (f.continuous.comp continuous_projIcc) ‖f‖
    (fun x => f.norm_coe_le_norm (Set.projIcc 0 1 zero_le_one x))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity error bound for the actual finite Gaussian perturbation:
the spectral/tree monomials, their amplitudes and dimension cutoff are
kept explicit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityPerturbationCoefficients {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (depth : ℕ)
    (x : Spin N × LabeledLeaf depth) : ℕ →₀ ℝ :=
  tensorLeafCoefficients U I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
      depth (fun j => enumeratedTreeDegree m j) (fun _ => 0) i) x

def cavityPerturbationKernel {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) (j : ℕ) : ℝ :=
  (∏ a, projectedOverlap U (I a) x.1 y.1 ^ enumeratedSpectralDegree m j a) *
    treeOverlap depth x.2 y.2 ^ enumeratedTreeDegree m j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinIsometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed site permutations act on the actual Ising cube and its
projected overlaps. Their pair-spin observables have no sign factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

def cavitySignedSpinPermutation {N : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) : Equiv.Perm (Spin N) where
  toFun σ i := if flip i then !(σ (p i)) else σ (p i)
  invFun σ i := if flip (p.symm i) then !(σ (p.symm i)) else σ (p.symm i)
  left_inv σ := by
    funext i
    cases h : flip (p.symm i) <;> simp_all
  right_inv σ := by
    funext i
    cases h : flip i <;> simp_all

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded disorder-dependent replica averages and finite sums. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityFullDisorderTest {N m depth : ℕ} (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, referenceReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    (F U) ∂gaussianCoordinates ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinSplit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact product prior obtained by separating the cavity sites.
The leaf coordinate is preserved by the split. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def cavitySpinSplit (N n : ℕ) : Spin (N + n) ≃ Spin N × Spin n where
  toFun σ := (fun i => σ (Fin.castAdd n i), fun j => σ (Fin.natAdd N j))
  invFun p := Fin.addCases p.1 p.2
  left_inv σ := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    ext i <;> simp

@[simp] lemma cavitySpinSplit_left {N n : ℕ} (σ : Spin (N+n)) (i : Fin N) :
    (cavitySpinSplit N n σ).1 i = σ (Fin.castAdd n i) := rfl

@[simp] lemma cavitySpinSplit_right {N n : ℕ} (σ : Spin (N+n)) (i : Fin n) :
    (cavitySpinSplit N n σ).2 i = σ (Fin.natAdd N i) := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseRestrictedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted base/cavity test in the exact product coordinates:
the shared cascade leaf stays with the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

def cavityPairLeafSwap {N n depth : ℕ}
    (x : (Spin N × Spin n) × LabeledLeaf depth) :
    (Spin N × LabeledLeaf depth) × Spin n := ((x.1.1,x.2),x.1.2)

def cavityPairLeafUnswap {N n depth : ℕ}
    (x : (Spin N × LabeledLeaf depth) × Spin n) :
    (Spin N × Spin n) × LabeledLeaf depth := ((x.1.1,x.2),x.1.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianKernel
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable Gaussian kernel used by finite cavity marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

def cavityGaussianKernel {a L : Type*} [Fintype a] [DecidableEq a]
    [MeasurableSpace L] : Kernel (L × Matrix a a ℝ) (EuclideanSpace ℝ a) where
  toFun p := multivariateGaussian 0 p.2
  measurable' := measurable_multivariateGaussian.comp
    (measurable_const.prodMk measurable_snd)

instance instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel {a L : Type*} [Fintype a] [DecidableEq a] [MeasurableSpace L] :
    IsMarkovKernel (cavityGaussianKernel (a := a) (L := L)) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ a) p.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianMarkedLaw
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint law of an overlap label and its Gaussian cavity marks.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a]
  [MetricSpace L] [MeasurableSpace L] [BorelSpace L]

omit [Fintype a] [DecidableEq a] [MetricSpace L] [BorelSpace L] in
lemma measurable_cavityGaussianMarkedMap :
    Measurable (cavityGaussianMarkedMap (a := a) (L := L)) :=
  measurable_fst.fst.prodMk measurable_snd

def cavityGaussianMarkedLaw (Q : ProbabilityMeasure (L × Matrix a a ℝ)) :
    ProbabilityMeasure (L × EuclideanSpace ℝ a) :=
  ⟨((Q : Measure _).compProd cavityGaussianKernel).map cavityGaussianMarkedMap,
    (Measure.isProbabilityMeasure_map_iff
      measurable_cavityGaussianMarkedMap.aemeasurable).mpr inferInstance⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockMarkedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian marks attached to a sampled spectral block. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

variable {m r q : ℕ} {E : Type*} [MeasurableSpace E]

def cavityBlockMarkedLaw (Q : ProbabilityMeasure E) (ρ : Fin m → ℝ)
    (b : E → SpectralBlock m r) :
    ProbabilityMeasure (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  cavityGaussianMarkedLaw (Q.mapAE (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityExtraReplicaPrefix
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extra replicas are tested by restriction to the original prefix.
This preserves the actual finite spectral observable when passing from
numerator moments to normalized cavity-spin expectations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityReplicaPrefixTest {m r d : ℕ} (k : ℕ)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ) :
    SpectralBlock m (r + k) × (Fin (r + k) → Spin d) →ᵇ ℝ :=
  F.compContinuous ⟨fun z =>
    ((fun i j => z.1 (Fin.castAdd k i) (Fin.castAdd k j)),
      fun i => z.2 (Fin.castAdd k i)), by fun_prop⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedSpinNumerator
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spin-prior numerators for the selected physical Haar projections.
The shared projection matrix remains outside the replica product measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityProjectedSpinTest {m r d : ℕ} {X : Type*}
    (B : (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ)
    (ξ : Fin r → X × Spin d) : ℝ :=
  F (B (fun i => (ξ i).1), fun i => (ξ i).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unnormalized cavity-column projections are precisely physical
spectral projections at the added sites. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityFullSpecialCoordinates {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (σ : Spin (N + n)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((cavityEigenspaceFrame
    (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) * B).transpose *ᵥ
      (specialRotation U (spinVector σ)).ofLp)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCoefficientProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded continuous test detects deviations of the three cavity
coefficients. Weak convergence to deterministic coefficients therefore
gives the probability estimate required by the replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFactorDeviation {d n : ℕ} (A B : CavityFactorBlocks d n) : ℝ :=
  cavityFactorSize (A.1-B.1) (A.2.1-B.2.1) (A.2.2-B.2.2)

lemma continuous_cavityFactorDeviation {d n : ℕ} (B : CavityFactorBlocks d n) :
    Continuous (fun A => cavityFactorDeviation A B) := by
  unfold cavityFactorDeviation cavityFactorSize
  have hK : Continuous (fun A : CavityFactorBlocks d n => A.1 - B.1) :=
    continuous_fst.sub continuous_const
  have hL : Continuous (fun A : CavityFactorBlocks d n => A.2.1 - B.2.1) :=
    (continuous_fst.comp continuous_snd).sub continuous_const
  have hC : Continuous (fun A : CavityFactorBlocks d n => A.2.2 - B.2.2) :=
    (continuous_snd.comp continuous_snd).sub continuous_const
  exact (((continuous_cavityMatrixMass d d).comp hK).add
    ((continuous_cavityMatrixMass d n).comp hL)).add
      ((continuous_cavityMatrixMass n n).comp hC)

lemma cavityFactorDeviation_nonneg {d n : ℕ} (A B : CavityFactorBlocks d n) :
    0 ≤ cavityFactorDeviation A B := cavityFactorSize_nonneg _ _ _

@[simp] lemma cavityFactorDeviation_self {d n : ℕ} (A : CavityFactorBlocks d n) :
    cavityFactorDeviation A A = 0 := by
  simp [cavityFactorDeviation, cavityFactorSize, cavityMatrixMass]

def cavityFactorDeviationTest {d n : ℕ} (A₀ : CavityFactorBlocks d n)
    (δ : ℝ) (hδ : 0 < δ) : CavityFactorBlocks d n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun A => min 1 (cavityFactorDeviation A A₀ / δ))
    (continuous_const.min ((continuous_cavityFactorDeviation A₀).div_const δ)) 1
    (fun A => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (le_min (by norm_num) (div_nonneg (cavityFactorDeviation_nonneg A A₀) hδ.le))]
      exact min_le_left _ _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cavity factor coefficients as functions of the compression
grams, with their limit at the deterministic scalar compression. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySmallFactorBlocks {s d n : ℕ}
    (D : Matrix (Fin s) (Fin s) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ) :
    CavityFactorBlocks d n :=
  (B.transpose * D * B - A₀, B.transpose * D * T, T.transpose * D * T)

def cavityCompressionFactorBlocks {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : CavityFactorBlocks d n :=
  cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam) (Matrix.diagonal lam₀)
    (cavityConcreteComplement e B₀ M) (cavitySpectralStack M)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint labeled spectral projectors and special axes of the physical
base model. Labels are retained even for repeated spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityLabeledProjectorAction {N m d : ℕ} (V : Orthogonal N)
    (p : CavityProjectorFrame N m d) : CavityProjectorFrame N m d :=
  (fun a => cavityConjugate V (p.1 a), (V : Matrix (Fin N) (Fin N) ℝ) * p.2)

def cavityPhysicalLabeledProjectors {N n m d : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (U : Orthogonal (N+n)) : CavityProjectorFrame N m d :=
  (fun a => cavityPhysicalBase g (fun b => if b=a then 1 else 0) B
      (Matrix.diagonal (fun j => if a₀ j=a then 1 else 0)) U,
    cavityPhysicalSpecial g B U)

def cavityCanonicalProjectorFrame {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) : CavityProjectorFrame N m d :=
  (fun a => Matrix.diagonal (fun j => Sum.elim
      (fun w => if w.1=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0) (e.symm j)),
    cavityCanonicalSpecial e)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projector coordinates give the same Gaussian covariance as the
eigenbasis coordinates, without choosing an eigenbasis measurably. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityProjectorSpinCoordinate {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (σ : Spin N) (i : Fin N) : ℝ := (P *ᵥ (fun j => spinValue (σ j))) i / Real.sqrt (N:ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullProjectionMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full perturbed Gibbs law has at most unit mean squared
spectral projection at every physical site. No cutoff is imposed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityProjectionSiteTest {N depth : ℕ} (J : Finset (Fin N)) (j : Fin N)
    (U : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff control in the full perturbed model. The bad compression
event is paid for only by its probability, never by an inverse moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def cavityProjectionAxesTest {N m k depth : ℕ} (I : Fin m → Finset (Fin N))
    (axes : Fin k → Fin N) (U : SpecialOrthogonal N)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  ∑ t : Fin m × Fin k, cavityProjectionSiteTest (I t.1) (axes t.2) U σ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
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

def cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) (x : Spin N × LabeledLeaf depth) : ℝ :=
  rotatedEnergy eig (specialRotation p.1) x.1 +
    cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2

def cavityFullCutoffDisorderTest {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, cavityCutoffReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (cavityFullHamiltonian eig I u (U, g)) (s U) (F U) ∂gaussianCoordinates ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cavity reweighting of the original perturbed spin model.
Both Hamiltonians contain the same Gaussian disorder coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationHamiltonian {N m depth : ℕ} (U : Rotation N)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (z : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) : ℝ :=
  rotatedEnergy eig U x.1 + cylinderField (cavityPerturbationCoefficients U I u depth x) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the actual Gaussian Hamiltonian in an
orthogonal eigenbasis, the disorder and the spin/leaf state. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavityRotation_eval {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Measurable (fun V : Orthogonal N => matrixRotation V⁻¹ x i) := by
  change Measurable (fun V : Orthogonal N => ∑ j, (V : Matrix (Fin N) (Fin N) ℝ) j i * x j)
  have hm : Measurable (fun V : Orthogonal N => (V : Matrix (Fin N) (Fin N) ℝ)) :=
    measurable_subtype_coe
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hm)).mul_const _

lemma measurable_cavityRotation_spinTensor {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (σ : Spin N) (i : SpinTensorIndex I degree) :
    Measurable (fun V : Orthogonal N =>
      spinTensorFeature (matrixRotation V⁻¹) I degree amplitude σ i) := by
  cases i with
  | inl i => exact measurable_const
  | inr v =>
    apply Measurable.const_mul
    unfold spectralMonomialFeature tensorFeature spectralSpinFeature
    apply Finset.measurable_prod
    intro a _
    apply Finset.measurable_prod
    intro j _
    exact (measurable_cavityRotation_eval (spinVector σ) (v.2 a j)).div_const _

lemma measurable_cavityRotation_perturbation {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : Orthogonal N × (ℕ → ℝ) =>
      cylinderField (cavityPerturbationCoefficients (matrixRotation p.1⁻¹) I u depth x) p.2) := by
  simp only [cavityPerturbationCoefficients, tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_cavityRotation_spinTensor I _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

lemma measurable_cavityRotationHamiltonian {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (fun p : (Orthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) =>
      cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun V : Orthogonal N =>
      rotatedEnergy eig (matrixRotation V⁻¹) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_cavityRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityRotation_perturbation I u x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorTensor
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor features built directly from labeled spectral projectors.
They give an eigenbasis-free representation of the actual Gaussian
perturbation, with exactly its original covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

def cavityProjectorMonomial {N m : ℕ} (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (degree : Fin m → ℕ) (σ : Spin N)
    (v : SpectralTensorIndex (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree) : ℝ :=
  ∏ a, tensorFeature (degree a) (fun i : (Finset.univ : Finset (Fin N)) =>
    cavityProjectorSpinCoordinate (Q a) σ (i : Fin N)) (v a)

def cavityProjectorSpinFeature {N m : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (degree : Fin N → Fin m → ℕ) (amp : Fin N → ℝ) (σ : Spin N) :
    CavityProjectorTensorIndex N m degree → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr w => amp w.1 * cavityProjectorMonomial Q (degree w.1) σ w.2

def cavityProjectorPerturbation {N m depth : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) (u : ℕ → ℝ)
    (x : Spin N × LabeledLeaf depth) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag depth x.2)
    (fun i : Fin (depth+1) × CavityProjectorTensorIndex N m (fun j => enumeratedSpectralDegree m j) =>
      (NNReal.sqrt (tensorPathProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N)))
        (fun j : Fin N => enumeratedSpectralDegree m j) depth
        (fun j => enumeratedTreeDegree m j) (fun _ => 0) i.1 i.2) : ℝ) *
        cavityProjectorSpinFeature Q (fun j => enumeratedSpectralDegree m j)
          (tensorPerturbationAmplitude N (fun j => u j)) x.1 i.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorHamiltonian
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base Gibbs law expressed using its labeled projectors.
This makes the law a measurable function of the data in the joint
projector/frame Haar factorization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityProjectorEnergy {N m : ℕ} (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (c : Fin m → ℝ) (σ : Spin N) : ℝ :=
  (1/2 : ℝ) * ∑ a, c a * ((fun i => spinValue (σ i)) ⬝ᵥ
    (Q a *ᵥ (fun i => spinValue (σ i))))

def cavityProjectorHamiltonian {N m depth : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) (c : Fin m → ℝ)
    (u : ℕ → ℝ) (z : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) : ℝ :=
  cavityProjectorEnergy Q c x.1 + cylinderField (cavityProjectorPerturbation Q u x) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCavity
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
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

def cavityFrameCoordinates {N d : ℕ} (S : Matrix (Fin N) (Fin d) ℝ)
    (σ : Spin N) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (S.transpose *ᵥ (fun i => spinValue (σ i)))

def cavityProjectorCavityMean {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t D : ℝ) (A : CavityFactorBlocks d n)
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n))
    (fun x => cavityProjectorHamiltonian p.1 c u z x.1 +
      t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2)
    {x | 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} F ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedNorm
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special base coordinates have total squared norm
equal to the number of reservoir spins. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityRetainedBaseOverlap {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (U : SpecialOrthogonal (N + n)) (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin (N + n)) (Fin (k a)) ℝ)
    (J : Fin m → Finset (Fin d)) (a : Fin m) (σ τ : Spin (N + n)) : ℝ :=
  (((R a).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp) ⬝ᵥ
    ((R a).transpose *ᵥ (specialRotation U (spinVector τ)).ofLp) +
      ∑ j ∈ J a, cavityFullSpecialCoordinates g B U σ j *
        cavityFullSpecialCoordinates g B U τ j) / N

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected columns in spectral groups and their exact spin coordinates.
These are the vectors to which the fresh-frame Gaussian limit applies. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupSpinCoordinates {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N)
    (a : Fin m) (σ : Spin N) : Fin (k a) → ℝ :=
  fun j => ((V : Matrix (Fin N) (Fin N) ℝ).transpose *ᵥ
    (fun i => spinValue (σ i))) (e ⟨a,j⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cavity comparison for the actual Ising energies and tensor
perturbations. The reference law may include a countable cascade leaf. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityJoinedSpin {N n : ℕ} (x : Spin N × Spin n) : Spin (N + n) :=
  Fin.append x.1 x.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderTestComparison
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the actual full/base cutoff comparison over the coupled
spectral geometry. No uniformity in the unbounded interaction energy is
needed: the explicit error depends only on the geometric cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def cavityBaseCutoffReplicaMean {N n m depth r : ℕ}
    (U : Rotation (N + n)) (V : Rotation N)
    (J : Fin m → Finset (Fin N)) (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
    (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ) : ℝ :=
  cavityCylinderReplicaMean ν
    (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.val.1.1 +
      t * (rotatedEnergy eig U (cavityJoinedSpin x.val.1) - rotatedEnergy eig₀ V x.val.1.1))
    (fun x => cavityPerturbationCoefficients V J u depth (x.val.1.1, x.val.2)) Φ

def cavityFullCutoffReplicaMean {N n m depth r : ℕ}
    (U : Rotation (N + n)) (I : Fin m → Finset (Fin (N + n)))
    (eig : Fin (N + n) → ℝ) (v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
    (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ) : ℝ :=
  cavityCylinderReplicaMean ν
    (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.val.1))
    (fun x => cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.val.1, x.val.2)) Φ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped logarithmic cavity factor in physical projector
coordinates, including the vanishing quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityProjectorCappedLog {N n m d depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (t cap δ : ℝ) (A : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (min (t * cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
      δ * (1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2))
    ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
      (uniformSpinPrior n)).tilted (fun x => cavityProjectorHamiltonian p.1 c u z x.1))
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained-projector coupling supplies the geometric error
needed for every bounded replica test on a fixed special-coordinate cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityGeometricWeight {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (U : SpecialOrthogonal (N + n))
    (x : Spin N × Spin n) : ℝ :=
  1 + ‖cavityFullSpecialCoordinates g B U (cavityJoinedSpin x)‖ ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
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

def cavityOriginalGeometricMean {N n m d depth : ℕ}
    (g : Fin (N+n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (T : LabeledTree depth) (eig : Fin (N+n) → ℝ) (u : ℕ → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (U : SpecialOrthogonal (N+n)) : ℝ :=
  ∫ z, cavityCutoffReplicaMean
    (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
    (cavityRotationHamiltonian (specialRotation U) eig (cavitySpectralGroup g) u z)
    {x | cavityGeometricWeight g (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
      (cavitySpinSplit N n x.1) ≤ D}
    (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityOrientationLift {N : ℕ} (hN : 0 < N) :
    Measurable (cavityOrientationLift hN) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun U : Orthogonal N =>
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) i j)
  simp only [cavityOrientationSign, Matrix.diagonal_mul]
  by_cases hi : i = (⟨0, hN⟩ : Fin N)
  · simp only [ite_eq_left hi]
    exact (continuous_subtype_val.matrix_det.measurable).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe))
  · simp only [ite_eq_right hi, one_mul]
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalGroupCutoffLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
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

def cavityCanonicalGroupCutoffMean {N n m d depth : ℕ}
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
    (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
      (cavityRotationHamiltonian (matrixRotation V⁻¹)
        (diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
          (cavitySpectralGroup (fun i => (E.symm i).1)) v t)
        (cavitySpectralGroup (fun i => (E.symm i).1)) u z)).prod (uniformSpinPrior n))
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpinModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable physical cavity model, with original disorder and fresh
Haar frames outside the replica prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityHaarSpinPriorKernel {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] : Kernel (Ω × U) (X × Spin k) :=
  let νK := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  (νK.comap Prod.fst measurable_fst).prod (Kernel.const _ π)

@[simp] lemma cavityHaarSpinPriorKernel_apply {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (p : Ω × U) :
    cavityHaarSpinPriorKernel ν hν π p = (ν p.1).prod π := by
  let νK : Kernel Ω X := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  change (νK.comap Prod.fst measurable_fst).prod (Kernel.const (Ω × U) π) p = _
  rw [Kernel.prod_apply]
  rfl

instance cavityHaarSpinPriorKernel_isMarkov {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {k : ℕ}
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityHaarSpinPriorKernel (U := U) ν hν π) := by
  constructor
  intro p
  rw [cavityHaarSpinPriorKernel_apply]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityHaarSpinPotential {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) : ℝ :=
  cavityLogFactor K L C
    (cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1) p.2.2

def cavityHaarSpinReplicaTest {m r k : ℕ} {Ω X U : Type*}
    (B : Ω → (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (p : (Ω × U) × (Fin r → X × Spin k)) : ℝ :=
  cavityProjectedSpinTest (B p.1.1) F p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hard spatial restrictions of the actual capped spin replica test.
Their only discontinuity lies on the maximum-radius boundary. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityRestrictedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, if 1+‖J z.2 i‖^2 ≤ 1+B^2 then
      Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T) else 0) * F (z.1, ε)
      ∂Measure.pi (fun _ => π)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedRestrictedSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected finite Gaussian field preserves the hard replica
cutoff, as well as its capped spin factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityRestrictedFlatSpinValue {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ B : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) : ℝ :=
  if ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2
  then cavityCappedFlatSpinValue K L C τ π F y else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRestrictedFactor
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary boundedness and product identities for the restricted
finite-spin factor used in the actual cavity Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) : ℝ :=
  if 1+‖y‖^2 ≤ 1+B^2 then Real.exp (min (cavityLogFactor K L C y ε) T) else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarRestrictedWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded restricted factor as a measurable function of the
original disorder, fresh group rotation, base state and cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) : ℝ :=
  cavityRestrictedFactor K L C T B
    (cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1) p.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalGram
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-frame covariance is the physical projected overlap divided
by the finite spectral-group mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityPhysicalReplicaVectors {N m r : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N) :
    (a : Fin m) → Fin r → Fin (d a) → ℝ :=
  fun a i k => U (spinVector (σ i)) (e a k)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationProbability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual measurable base spin/leaf Gibbs probability, with its
rotation, cascade weights and Gaussian disorder all retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationProbability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    Measure (Spin N × LabeledLeaf depth) :=
  gibbsProbability (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    (cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.2)

instance cavityRotationProbability_probability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    IsProbabilityMeasure (cavityRotationProbability eig I u p) :=
  gibbsProbability_probability _ _

lemma measurable_cavityRotationProbabilityHamiltonian {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (fun p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth)) =>
      cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2) := by
  let π : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth)) → (Orthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) := fun p => ((p.1.1.1,p.1.2),p.2)
  have hπ : Measurable π :=
    (measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd
  have hb := measurable_cavityRotationHamiltonian (N := N) (m := m) (depth := depth) eig I u
  have hh := hb.comp hπ
  exact hh

lemma measurable_cavityRotationProbability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (cavityRotationProbability (depth := depth) eig I u) := by
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let H : Ω × X → ℝ := fun p =>
    cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure (labeledSpinReference depth
      (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd
  have hH : Measurable H := measurable_cavityRotationProbabilityHamiltonian eig I u
  exact measurable_gibbsProbability (ν := ν) (H := H) hν hH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationArray
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral array of the concrete base rotation/Gaussian Gibbs
law. The same rotation supplies its overlaps and cavity coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityProjectedOverlap {N : ℕ} (I : Finset (Fin N)) (σ τ : Spin N) :
    Measurable (fun V : Orthogonal N => projectedOverlap (matrixRotation V⁻¹) I σ τ) := by
  unfold projectedOverlap
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (measurable_cavityRotation_eval (spinVector σ) i).mul
    (measurable_cavityRotation_eval (spinVector τ) i)

lemma measurable_cavitySpectralJointEntry {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) :
    Measurable (fun V : Orthogonal N => spectralJointEntry (matrixRotation V⁻¹) I depth x y) := by
  apply Measurable.of_eval
  intro a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [spectralJointEntry, Fin.lastCases_last]
    exact measurable_const
  · simp only [spectralJointEntry, Fin.lastCases_castSucc]
    exact (measurable_cavityProjectedOverlap (I a) x.1 y.1).subtype_mk

def cavityRotationEntry {N m depth : ℕ} (I : Fin m → Finset (Fin N))
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (x y : Spin N × LabeledLeaf depth) : SpectralEntry (m+1) :=
  spectralJointEntry (matrixRotation p.1.1⁻¹) I depth x y

lemma measurable_cavityRotationEntry {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) :
    Measurable (fun p => cavityRotationEntry I p x y) :=
  (measurable_cavitySpectralJointEntry I x y).comp measurable_fst.fst

def cavityRotationArrayLaw {N m depth : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree depth)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    ProbabilityMeasure (SpectralArray (m+1)) :=
  ⟨(disorderReplicaLaw ((μ.prod ρ).prod gaussianCoordinates)
    (cavityRotationProbability eig I u) (measurable_cavityRotationProbability eig I u)).map
      (cavitySampledEntryArray (cavityRotationEntry I)),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavitySampledEntryArray (cavityRotationEntry I)
        (measurable_cavityRotationEntry I)).aemeasurable).mpr inferInstance⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationVectors
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable physical group vectors and their covariance in the actual
base Gibbs disorder space. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationVectors {N m depth : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (a : Fin m) (x : Spin N × LabeledLeaf depth) : Fin (k a) → ℝ :=
  cavityGroupSpinCoordinates k e p.1.1 a x.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarLogObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped logarithmic observable in the actual fresh-Haar Gibbs
model, with its measurable original prior and quadratic penalty. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityHaarLogObservable {m q d n : ℕ} {dims : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace X] (ν : Ω → Measure X)
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (dims a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (dims a)) (Fin q) ℝ)
    (B : Ω → CavityFactorBlocks d n) (t cap δ : ℝ)
    (p : Ω × ((a : Fin m) → Orthogonal (dims a))) : ℝ :=
  Real.log (∫ x, Real.exp
    (min (t*cavityLogFactor (B p.1).1 (B p.1).2.1 (B p.1).2.2
      (cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1) x.2) cap -
      δ*(1+‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^2))
    ∂(ν p.1).prod (uniformSpinPrior n : Measure (Spin n)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical fresh-group logarithmic observable and its
finite-volume measurability and boundedness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing


def cavityCanonicalHaarLog {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (B : CavityFactorBlocks d n)
    (p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a)))) : ℝ :=
  let E := cavityBaseGroupEquiv k e a₀
  let dims := cavityBaseGroupDimension k a₀
  let eig := diagonalPerturbedEigenvalues (fun i => lam (E.symm i).1)
    (cavitySpectralGroup (fun i => (E.symm i).1)) v t
  cavityHaarLogObservable
    (cavityRotationProbability eig (cavitySpectralGroup (fun i => (E.symm i).1)) u)
    (fun j => (a₀ j,j)) (cavityRotationVectors dims E)
    (cavityCanonicalGroupFrame k e a₀ hk) (fun _ => B) t cap δ p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTightness
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the actual special-coordinate cutoff from bounded tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySpecialCutoff {N n m d depth : ℕ} (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (R : ℝ) (U : SpecialOrthogonal (N + n)) : Set (Spin (N + n) × LabeledLeaf depth) :=
  {x | ‖cavityFullSpecialCoordinates g (B U) U x.1‖ ≤ R}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBlockProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extraction of cavity coefficients from the full small compression
matrix. This lets the proved Haar compression law act on the actual
factor coefficients, including the subtracted base diagonal. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityFactorBlocksFromMatrix {d n : ℕ} (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (M : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) : CavityFactorBlocks d n :=
  (M.submatrix Sum.inl Sum.inl - A₀, M.submatrix Sum.inl Sum.inr,
    M.submatrix Sum.inr Sum.inr)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySiteSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact site-symmetry identity used for cavity self-consistency.
It is a statement about the full two-replica law, before any cutoff. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

def cavityTotalSpinOverlap {N : ℕ} (x : Spin N × Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, spinValue (x.1 i) * spinValue (x.2 i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSiteIdentity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity-spin insertion identity for the actual full perturbed
model, before any restriction of its Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityFullTest {N m depth : ℕ} (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  ∫ U, ∫ g, referenceReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g) F
    ∂gaussianCoordinates ∂μ

def cavityReplicaOverlap {N depth : ℕ} (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  cavityTotalSpinOverlap ((σ 0).1, (σ 1).1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarMarkedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint probability laws for the physical fresh Haar marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {m r q : ℕ} {N : Fin m → ℕ} {X L : Type*}
  [MeasurableSpace X] [MetricSpace L] [MeasurableSpace L]
  [BorelSpace L] [SecondCountableTopology L]

omit [MetricSpace L] [BorelSpace L] [SecondCountableTopology L] in
lemma measurable_cavityHaarMarkedMap (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (cavityHaarMarkedMap l v A₀) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hc : Continuous (fun p :
      ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) =>
      cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  exact (hl.comp measurable_fst).prodMk (hc.measurable.comp
    ((hv.comp measurable_fst).prodMk
      ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd)))

def cavityHaarMarkedLaw (P : Measure X) [IsProbabilityMeasure P]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    ProbabilityMeasure (L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  ⟨(P.prod (Measure.pi μ)).map (cavityHaarMarkedMap l v A₀),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavityHaarMarkedMap l hl v hv A₀).aemeasurable).mpr inferInstance⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common depths alone are preserved by the same-root quadratic innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedDepthTest {d k n : ℕ} (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n) : ℝ :=
  a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded common-depth observable disintegrated over root and forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRootedDepthTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  ∫ σ, cavityRootedDepthTest a σ
    ∂Measure.infinitePi (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledDepthMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

def cavityLabeledDepthMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (a : ℕ → ℝ)
    (ω : CavityLabeledDisorder d n) : ℝ :=
  referenceReplicaMean (cavityLabeledPriorKernel n R (uniformSpinPrior k) ω)
    (fun x => cavityLabeledPotential n K L C (ω,x))
    (fun σ : Fin 2 → CavityLabeledState d k n => a (labeledCommonDepth n (σ 0).1.1 (σ 1).1.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledRestrictedModel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite labeled Gibbs numerator with its hard spatial
restriction and fixed logarithmic cap. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityLabeledRestrictedWeight {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    CavityLabeledDisorder d n × CavityLabeledState d k n → ℝ :=
  (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ cavityLabeledEndpoint n

def cavityLabeledRestrictedNumerator {m r d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T Bcut : ℝ) (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) (ω : CavityLabeledDisorder d n) : ℝ :=
  cavityWeightNumerator (cavityLabeledPriorKernel n R π ω)
    (fun x => cavityLabeledRestrictedWeight n K L C T Bcut (ω,x))
    (fun ξ => cavityLabeledReplicaTest B F (ω,ξ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearDepthEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

def cavityLabeledLinearDepthPairMean {d k : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ) (s : EuclideanSpace ℝ (Fin d))
    (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean
    (((labeledLeafLaw h.depth p.1).prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogNormalizerTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full cavity logarithmic normalizer splits into the quadratic
normalizer and the linear normalizer under the same innovation map. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

def cavityRootedLogNormalizer {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  Real.log (∫ z, Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2)
    ∂(cavityRootedPriorKernel n R ω).prod π)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityNormalizerIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite root, positive-level and ordinary residual pieces of the
quadratic normalizer are the integral of D_p(r) R'(D_p(r)). -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityNormalizerDensity {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) (r : ℝ) : ℝ :=
  deficit p r * cavityRDerivative rho lam hrho hsum (deficit p r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientationArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete base-rotation array is exactly the namespaced tensor
array after orienting its inverse eigenbasis. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityOrientedBaseLaw {N : ℕ} (hN : 0 < N) (μ : Measure (Orthogonal N)) :
    Measure (SpecialOrthogonal N) :=
  μ.map (fun V => cavityOrientationLift hN V⁻¹)

instance cavityOrientedBaseLaw_probability {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (cavityOrientedBaseLaw hN μ) :=
  (Measure.isProbabilityMeasure_map_iff
    ((measurable_cavityOrientationLift hN).comp measurable_inv).aemeasurable).mpr inferInstance

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientedFamily
attribute [-instance] _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An all-size version of the oriented physical law. The zero-dimensional
case is only a harmless placeholder for sequences indexed by all naturals. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

def cavityOrientedFamily (μ : (N : ℕ) → Measure (Orthogonal N)) (N : ℕ) :
    Measure (SpecialOrthogonal N) :=
  if h : 0 < N then cavityOrientedBaseLaw h (μ N) else Measure.dirac 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapObservable
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous ordinary-overlap observable, without a spin insertion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityOverlapObservable {m k : ℕ} (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    SpectralBlock m 2 × (Fin 2 → Spin k) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p => Φ (∑ a, (p.1 0 1 a : ℝ)) ,
      hΦ.comp (continuous_finsetSum _ (fun a _ => by fun_prop))⟩


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

def cavityProjectorLogPartition {N m depth : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ) (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp (cavityProjectorHamiltonian Q c u z x)
    ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomHaarLog
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability
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

def cavityRandomHaarLog {Z : Type*} {N n m d depth : ℕ}
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (hk : ∀ a, d ≤ k a) (lam v : Fin m → ℝ) (u : ℕ → ℝ)
    (t cap δ : ℝ) (A : Z → CavityFactorBlocks d n)
    (p : (Z × ((Orthogonal N × LabeledTree depth) × (ℕ → ℝ))) ×
      ((a : Fin m) → Orthogonal (cavityBaseGroupDimension k a₀ a))) : ℝ :=
  cavityCanonicalHaarLog k e a₀ hk lam v u t cap δ (A p.1.1) (p.1.2,p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRotationLogMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-volume expected logarithmic partition function is
measurable and integrable in the orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityRotationLogMean {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (V : Orthogonal N) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z x)
    ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root-averaged scalar spin recursion occurring after the cavity
quadratic change of measure, in the manuscript's field normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def cavityScalarCascadeMean (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (root residual : ℝ≥0) (c : ℝ) : ℝ :=
  ∫ z : Fin N → ℝ, cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (cavityResidualSpinLog N residual c) z
      ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySplitSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-model cavity-spin observable can be evaluated using the
base overlap, since the discarded-site error is uniformly small. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFullSpinInsertion {N depth : ℕ} (Φ : ℝ → ℝ) (site : Fin N)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  Φ (cavityReplicaOverlap σ) * (spinValue ((σ 0).1 site) * spinValue ((σ 1).1 site))

def cavitySplitSpinInsertion {N n depth : ℕ} (Φ : ℝ → ℝ) (site : Fin n)
    (σ : Fin 2 → Spin (N+n) × LabeledLeaf depth) : ℝ :=
  Φ (cavityTotalSpinOverlap ((cavitySpinSplit N n (σ 0).1).1,
    (cavitySpinSplit N n (σ 1).1).1)) *
      (spinValue ((σ 0).1 (Fin.natAdd N site)) * spinValue ((σ 1).1 (Fin.natAdd N site)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySplitOverlapTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full and retained ordinary-overlap observables differ uniformly
by a vanishing amount, also under the random-tree Gibbs average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFullOverlapInsertion {N depth : ℕ} (Φ : ℝ → ℝ)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  Φ (cavityReplicaOverlap σ)

def cavitySplitOverlapInsertion {N n depth : ℕ} (Φ : ℝ → ℝ)
    (σ : Fin 2 → Spin (N+n) × LabeledLeaf depth) : ℝ :=
  Φ (cavityTotalSpinOverlap ((cavitySpinSplit N n (σ 0).1).1,
    (cavitySpinSplit N n (σ 1).1).1))


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictMarkedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite strict-cascade law with its recalculated Gaussian
marks, including the spectral block labels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def cavityPathReplicaBlock {m r : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    JointArray → SpectralBlock m r :=
  fun x => cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
    (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x)

def cavityStrictMarkedLaw {m r q : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) (n : ℕ) :
    ProbabilityMeasure (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  cavityBlockMarkedLaw
    (cascadeCompactLaw n (chainExponent (uniformCut n))
      (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))) ρ
    (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityValueFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted layer-cake identity in the cavity value calculation.
Atoms of the overlap distribution are retained through the strict tail. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

def cavityTailMoment (p : OverlapPath) (r : ℝ) : ℝ :=
  ∫ s, if r < p s then p s else 0 ∂pathMeasure

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized constrained prior gives exactly the conditional Gibbs
law. Its log normalizer retains the original cube mass as an explicit
constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def restrictedSpinPrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    ProbabilityMeasure (Spin N) :=
  ⟨restrictedSpinLaw S (fun _ => 0), restrictedSpinLaw_probability S hS _⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def consecutiveBlockConstraint (n K : ℕ) (C : Finset (Spin n)) : Finset (Spin (K*n)) :=
  Finset.univ.filter (fun σ => ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (b,i))) ∈ C)

lemma mem_consecutiveBlockConstraint {n K : ℕ} (C : Finset (Spin n)) (σ : Spin (K*n)) :
    σ ∈ consecutiveBlockConstraint n K C ↔
      ∀ b : Fin K, (fun i : Fin n => σ (finProdFinEquiv (b,i))) ∈ C := by
  simp [consecutiveBlockConstraint]

lemma consecutiveBlockConstraint_nonempty {n K : ℕ} (C : Finset (Spin n)) (hC : C.Nonempty) :
    (consecutiveBlockConstraint n K C).Nonempty := by
  obtain ⟨τ,hτ⟩ := hC
  refine ⟨fun i => τ (finProdFinEquiv.symm i).2, ?_⟩
  rw [mem_consecutiveBlockConstraint]
  intro b
  simpa using hτ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedProductPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product decomposition for constrained cavity blocks. The
normalization cost is the sum of the two original cube-mass costs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def cavityProductSlice {N n : ℕ} (S : Finset (Spin N)) (T : Finset (Spin n)) :
    Finset (Spin (N+n)) :=
  (S ×ˢ T).map (cavitySpinSplit N n).symm.toEmbedding

lemma mem_cavityProductSlice {N n : ℕ} (S : Finset (Spin N)) (T : Finset (Spin n))
    (σ : Spin (N+n)) : σ ∈ cavityProductSlice S T ↔
      (cavitySpinSplit N n σ).1 ∈ S ∧ (cavitySpinSplit N n σ).2 ∈ T := by
  simp [cavityProductSlice]

lemma cavityProductSlice_nonempty {N n : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (T : Finset (Spin n)) (hT : T.Nonempty) : (cavityProductSlice S T).Nonempty := by
  obtain ⟨σ,hσ⟩ := hS
  obtain ⟨τ,hτ⟩ := hT
  refine ⟨(cavitySpinSplit N n).symm (σ,τ), ?_⟩
  rw [mem_cavityProductSlice]
  simpa using And.intro hσ hτ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockSplit
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the last consecutive constrained block gives exactly the
base/cavity product constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def consecutiveBlockJoin (n K : ℕ) : Spin (K*n+n) ≃ Spin ((K+1)*n) where
  toFun σ := fun i => σ (Fin.cast (Nat.succ_mul K n) i)
  invFun σ := fun i => σ (Fin.cast (Nat.succ_mul K n).symm i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedEndpointKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

def restrictedTailEndpointKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) →
      Kernel (Fin N → ℝ) (Fin N → ℝ)
  | 0, _, _, _ => Kernel.id
  | n + 1, b, v, hb =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    restrictedTailEndpointKernel hN S hS n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1

def restrictedPairEndpointKernel {N : ℕ} (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) :
    (n : ℕ) → (b : ℕ → ℝ) → (v : ℕ → ℝ≥0) → (∀ i < n, 0 < b i) → Fin (n + 1) →
      Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | 0, _, _, _, _ => Kernel.id ×ₖ Kernel.id
  | n + 1, b, v, hb, i =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    let hbs := fun j hj => hb (j + 1) (by omega)
    let hreg := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    Fin.cases (restrictedTailEndpointKernel hN S hS (n + 1) b v hb ×ₖ
        restrictedTailEndpointKernel hN S hS (n + 1) b v hb)
      (fun j => restrictedPairEndpointKernel hN S hS n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs) hreg.1) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFieldPublishedInput
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Panchenko--Talagrand (2007), Lemma 3.1 (8), p.655 and Corollary
3.2 (9), p.656, specialized to the actual finite constrained terminal.
The hypothesis concerns only the marked endpoint law; no pressure,
spin expectation, or limiting assertion is an input. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def restrictedFieldTiltedPairMean {N : ℕ} (S : Finset (Spin N))
    (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean (labeledLeafLaw h.depth p.1)
    (fun α => restrictedFieldTerminal S (fieldVectorEndpoint N h p z α))
    (fun σ : Fin 2 → LabeledLeaf h.depth =>
      Φ (labeledCommonDepth h.depth (σ 0) (σ 1),
        fieldVectorEndpoint N h p z (σ 0), fieldVectorEndpoint N h p z (σ 1)))
    ∂fieldVectorCoordinateLaw N h

def RestrictedFieldAncestorPairLaw {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) : Prop :=
  ∀ z : Fin N → ℝ,
  ∀ Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
    Measurable Φ → (∃ C : ℝ, ∀ p, |Φ p| ≤ C) →
    restrictedFieldTiltedPairMean S h z Φ =
      ∫ α : ℕ → LabeledLeaf h.depth,
        ∫ y, Φ ((fieldCommonLevel h α).val, y)
          ∂restrictedPairEndpointKernel hN S hS h.depth (chainExponent h.cut)
            (fieldStepVariance h)
            (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
            (fieldCommonLevel h α) z
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut)

/-- The same published marking theorem, with a nonempty finite spin
constraint retained inside the terminal log partition. -/
def PanchenkoTalagrandRestrictedFieldPairInput : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep),
    RestrictedFieldAncestorPairLaw hN S hS h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tensor perturbation with a fixed spin/leaf prior.
The prior may be a normalized spin constraint; it is independent of the rotation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorTensorLog {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (p : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x, Real.exp (rotatedEnergy eig (specialRotation p.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorLeafCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) ∂ν)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact perturbation minima for a fixed constrained spin/leaf prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def priorPerturbationPressureMean {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ p, priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) n
      (fun j => enumeratedTreeDegree m j) h i) p ∂μ.prod gaussianCoordinates

def priorPerturbationObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  -priorPerturbationPressureMean μ ν eig c I t h u v +
    ∑ j : Fin N, perturbationWeight j*(u j-3/2)^2 + ∑ a, (v a-3/2)^2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedZeroTreeArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical constrained array law with the trivial auxiliary tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def restrictedZeroTreePrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Measure (Spin N × LabeledLeaf 0) :=
  labeledSpinReference 0 (restrictedSpinPrior S hS : Measure (Spin N)) PUnit.unit

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedRotationLogMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-volume expected logarithmic partition function is
measurable and integrable in the orthogonal disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def restrictedRotationLogMean {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (V : Orthogonal N) : ℝ :=
  ∫ z, Real.log (∫ x, Real.exp
    (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z x)
    ∂labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

def offsetBlockConstraint {r n : ℕ} (K : ℕ) (R : Finset (Spin r))
    (C : Finset (Spin n)) : Finset (Spin (r+K*n)) :=
  cavityProductSlice R (consecutiveBlockConstraint n K C)

lemma offsetBlockConstraint_nonempty {r n K : ℕ} (R : Finset (Spin r))
    (hR : R.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) :
    (offsetBlockConstraint K R C).Nonempty :=
  cavityProductSlice_nonempty R hR _ (consecutiveBlockConstraint_nonempty C hC)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetAffineIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact constrained increment on each affine dimension progression. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

def affineRestrictedIncrement {m n : ℕ} (hm : 2 ≤ m) (_hn : 0 < n)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) (lam : Fin m → ℝ)
    (u : (r : ℕ) → Fin (cavityPrefixAffineSize n (m*n-n+n+3) c r) → ℝ)
    (v : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  let N := cavityPrefixAffineSize n (m*n-n+n+3) c r
  let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
  let S := offsetBlockConstraint (r+(m*n-n+n+3)) R Cset
  let hS := offsetBlockConstraint_nonempty R hR Cset hCset
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  (∫ z, restrictedRotationLogMean (cavityProductSlice S Cset)
    (cavityProductSlice_nonempty S hS Cset hCset) z.2
    (diagonalPerturbedEigenvalues (fun i => lam (g (N+n) i))
      (cavitySpectralGroup (g (N+n))) (v r) 1)
    (cavitySpectralGroup (g (N+n))) (cavityBaseAmplitude (u r)) z.1 ∂(μ (N+n)).prod θ) -
  ∫ z, restrictedRotationLogMean S hS z.2
    (diagonalPerturbedEigenvalues (fun i => lam (g N i)) (cavitySpectralGroup (g N)) (v r) 1)
    (cavitySpectralGroup (g N)) (cavityBaseAmplitude (u r)) z.1 ∂(μ N).prod θ


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_ContactModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prior-independent joint modulus for centered contact pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal
namespace InvariantIsing

def contactModulus {N m n : ℕ} (K : ℝ) (p q : TensorContactParameter N m n) : ℝ :=
  (K/2)*|p.1-q.1|+
    2*∑ i : Fin (n+1),
      |(NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)-
        (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ)| *
      ((NNReal.sqrt (varianceIncrement (finiteFieldPath p.2.1) i) : ℝ)+
        (NNReal.sqrt (varianceIncrement (finiteFieldPath q.2.1) i) : ℝ))+
    2*(N : ℝ)⁻¹*tensorAmplitudeModulus (tensorPerturbationAmplitude N p.2.2.1)
      (tensorPerturbationAmplitude N q.2.2.1)+perturbationScale N*∑ a, |p.2.2.2 a-q.2.2.2 a|+
    |finiteFieldPath p.2.1 n-finiteFieldPath q.2.1 n|/2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-depth vector cascade marking by independent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

section Coordinates
variable {ι : Type} [Fintype ι]

def cascadeSeedTree : (n : ℕ) → (ℕ → ℝ) →
    (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) → (ι → ℝ) →
      NoiseTree unitInterval n → NoiseTree (ι → ℝ) n
  | 0, _, _, _, _ => PUnit.unit
  | n+1, b, ψ, z, T =>
    (sigmaPart ((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod
      (noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)))) T).map
        (fun p => (p.1, (ψ 0 z p.2.1,
          cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
            (z+ψ 0 z p.2.1) p.2.2)))

end Coordinates
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bilinear Gaussian comparison behind the sharp rectangular upper edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

def bilinearMatrixCoefficient {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (x : X) : BilinearGaussianIndex N m → ℝ
  | .inl (.inl (i,j)) => u x i*v x j
  | .inl (.inr _) => 1
  | .inr _ => 0

def bilinearVectorCoefficient {X : Type*} {N m : ℕ}
    (u : X → EuclideanSpace ℝ (Fin N)) (v : X → EuclideanSpace ℝ (Fin m))
    (x : X) : BilinearGaussianIndex N m → ℝ
  | .inl _ => 0
  | .inr (.inl i) => u x i
  | .inr (.inr j) => v x j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldHeightDerivative
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual height-direction envelope differentiation at fixed magnetization.
The bias response is obtained by implicit differentiation of the finite
physical mean, using its strictly positive curvature. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

/-- The centered constrained field value on the strict height cone. -/
def constrainedHeightFieldValue (h : FieldStep) (s : ℝ)
    (r : Fin (h.depth + 1) → ℝ) : ℝ :=
  if hrs : r ∈ fieldStrictHeightCone h.depth then
    constrainedFieldValue (fieldStepOfStrictHeights h r hrs) s else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite square continuation on the closed spin interval. Its two
endpoint values are one, and its time derivatives there vanish. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticContinuation (L : List (ℝ × ℝ≥0))
    (A : MagneticContinuationJet) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuation L A ζ p.1 p.2 else 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationClosedPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-interval derivative data for finite inverse-coordinate square
continuations, with a zero second derivative chosen at the endpoints. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticContinuationSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuationSlope L hL A ζ p.1 p.2 else 0

def closedMagneticContinuationSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuationSecond L hL A ζ p.1 p.2 else 0

def closedMagneticContinuationTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2 * closedMagneticContinuationSecond L hL A ζ p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAffineIncrementLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A physical constrained block has eventually large cavity increments whenever
the proposed pressure level is below the magnetic variational value. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

def affineConstrainedObjective {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (spec c : Fin m → ℕ) (hspec : ∑ a, spec a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) (lam : Fin m → ℝ) (j : ℕ)
    (u : Fin (cavityPrefixAffineSize n (m*n-n+n+3) c j) → ℝ) (v : Fin m → ℝ) : ℝ :=
  let M := cavityPrefixAffineSize n (m*n-n+n+3) c j
  let g := cavityAffineLabel (by omega : 0 < m) spec c hspec M
  priorPerturbationObjective (cavityOrientedBaseLaw (by
    have hh := cavityRationalSize_ge_three n (m*n-n) j hn;
    exact lt_of_lt_of_le (by norm_num : 0<3)
      (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
    (restrictedZeroTreePrior (offsetBlockConstraint (j+(m*n-n+n+3)) R Cset)
      (offsetBlockConstraint_nonempty R hR Cset hCset))
    (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) u v

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternPublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marchenko–Pastur and Davidson–Szarek estimates for Gaussian-pattern matrices.
MP1967, Theorem1 and examples pp.459,461, gives the displayed law and empirical
limit. DS2001, TheoremII.13, gives the edge-excess and uniform-integrability
consequences for the Gaussian rectangular matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
universe u
namespace InvariantIsing

/-- The fixed-aspect-ratio Gaussian specialization of MP1967, Theorem1. -/
structure MarchenkoPasturInput (α : ℝ) (_hα : 0 < α) : Prop where
  probability : IsProbabilityMeasure (marchenkoPasturMeasure α)
  support_bound : (marchenkoPasturMeasure α).support ⊆ Icc (marchenkoPasturLower α) (marchenkoPasturB α)
  left_mem : marchenkoPasturLower α∈(marchenkoPasturMeasure α).support
  right_mem : marchenkoPasturB α∈(marchenkoPasturMeasure α).support
  measurable_eigenvalues : ∀ N, Measurable
    (gaussianPatternEigenvalues (N := N) (m := gaussianPatternCount α N))
  weak : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k)
        (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) atTop
      (fun _ => LevyProkhorov.ofMeasure
        (scaledSpectralLaw ⟨marchenkoPasturMeasure α,probability⟩ c))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramEmpiricalTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the physical matrix resolvent with the empirical spectral transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma continuous_positiveResolventTest {t : ℝ} (ht : 0 < t) :
    Continuous (positiveResolventTest t) := by
  unfold positiveResolventTest
  apply continuous_const.div (continuous_const.add (continuous_id.max continuous_const))
  intro x
  exact ne_of_gt (add_pos_of_pos_of_nonneg ht (le_max_right x 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialValue
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability
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

def haarPolynomialValue {N : ℕ} (p : MatrixPolynomial N) (U : SpecialOrthogonal N) : ℝ :=
  matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) p

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

lemma reflectionNormalSegment_nonzero {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : 0 ≤ inner ℝ v w)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : reflectionNormalSegment v w t ≠ 0 := by
  by_cases h1 : t = 1
  · simpa [reflectionNormalSegment,h1] using hw
  have hinner : 0 < inner ℝ v (reflectionNormalSegment v w t) := by
    simp only [reflectionNormalSegment,inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 h1)) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
      (mul_nonneg ht.1 hvw)
  intro hz
  rw [hz,inner_zero_right] at hinner
  exact lt_irrefl _ hinner

def reflectionNormalSquare {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) : ℝ :=
  ∑ i, (reflectionNormalSegment v w t i)^2

def reflectionNormalSquareDeriv {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) : ℝ :=
  ∑ i, 2*reflectionNormalSegment v w t i*(w i-v i)

lemma reflectionNormalSquare_eq {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    reflectionNormalSquare v w t = ‖reflectionNormalSegment v w t‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma continuous_reflectionNormalSegment_entry {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Continuous (fun t => reflectionNormalSegment v w t i) := by
  change Continuous (fun t : ℝ => (1-t)*v i+t*w i)
  fun_prop

lemma continuous_reflectionNormalSquare {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) :
    Continuous (reflectionNormalSquare v w) := by
  unfold reflectionNormalSquare
  exact continuous_finsetSum _ fun i _ => (continuous_reflectionNormalSegment_entry v w i).pow 2

lemma continuous_reflectionNormalSquareDeriv {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) :
    Continuous (reflectionNormalSquareDeriv v w) := by
  unfold reflectionNormalSquareDeriv
  exact continuous_finsetSum _ fun i _ =>
    (continuous_const.mul (continuous_reflectionNormalSegment_entry v w i)).mul continuous_const

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

def reflectionSegmentDerivative {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j =>
  -((2*((w i-v i)*reflectionNormalSegment v w t j+
      reflectionNormalSegment v w t i*(w j-v j)))*reflectionNormalSquare v w t-
      (2*reflectionNormalSegment v w t i*reflectionNormalSegment v w t j)*
        reflectionNormalSquareDeriv v w t)/(reflectionNormalSquare v w t)^2

lemma continuousOn_reflectionSegmentDerivative {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : 0 ≤ inner ℝ v w) (i j : Fin N) :
    ContinuousOn (fun t => reflectionSegmentDerivative v w t i j) (Icc (0:ℝ) 1) := by
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : reflectionNormalSquare v w t ≠ 0 := by
    rw [reflectionNormalSquare_eq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr
      (reflectionNormalSegment_nonzero v w hv hw hvw ht))
  have hn (k : Fin N) : ContinuousOn (fun t => reflectionNormalSegment v w t k)
      (Icc (0:ℝ) 1) := (continuous_reflectionNormalSegment_entry v w k).continuousOn
  have hs : ContinuousOn (reflectionNormalSquare v w) (Icc (0:ℝ) 1) :=
    (continuous_reflectionNormalSquare v w).continuousOn
  have hd : ContinuousOn (reflectionNormalSquareDeriv v w) (Icc (0:ℝ) 1) :=
    (continuous_reflectionNormalSquareDeriv v w).continuousOn
  dsimp only [reflectionSegmentDerivative,Matrix.of_apply]
  exact ((((continuousOn_const.mul
    ((continuousOn_const.mul (hn j)).add ((hn i).mul continuousOn_const))).mul hs).sub
      (((continuousOn_const.mul (hn i)).mul (hn j)).mul hd)).neg).div (hs.pow 2)
        (fun t ht => pow_ne_zero _ (hq t ht))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactResolventTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvents as a separating family for compact nonnegative spectral laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

def compactResolventTest (R : ℝ) (t : {t : ℝ // 0 < t}) : Icc (0 : ℝ) R →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => positiveResolventTest t x,
      (continuous_positiveResolventTest t.property).comp continuous_subtype_val⟩

end InvariantIsing

end

end OAI
end


