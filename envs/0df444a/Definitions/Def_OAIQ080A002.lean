-- Prove2me | Definitions.Def_OAIQ080A002
-- name    : OAIQ080A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:11:05.359797+00:00
-- url     : https://prove2.me/theorems/ab3a2db9-8aac-42f5-8a60-1d953caa8fc0
-- title:
--   Definitions bundle OAIQ080A002 of the split of OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 591 declarations of OpenAI's Lean: 395 definitions, 2 inductive types or structures, 66 instances and 128 theorems. The definitions and types are `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.pairTranslation`, `OAI.BoltzmannNonuniqueness.Compactness.boundedPairWeight`, `OAI.BoltzmannNonuniqueness.JetDatum.label`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.kineticProfile`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.subsequence`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximationEntropyBudget`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.characteristicClippedFiniteGain`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.characteristicClippedPhysicalGain`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.clippedFiniteGain`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.clippedPhysicalGain`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.clippedPostRate`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.collisionComparisonError`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.collisionMassClip`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.collisionOperator`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyCompactMajorant`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyErrorCoefficient`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyGauge`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyMarginal`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.entropyTruncation`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.extendedDissipation`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.extendedProduction`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.finitePositiveSource`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.gaussianShift`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialEntropyBudget`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.kineticSource`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.linearComparisonError`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.linearMoment`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.linearRenormalizedField`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.logRegularizationConstant`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.massRegularizedPostRate`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.massRegularizedPreRate`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.normalizedGainExcess`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.normalizedRateExcess`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.normalizer`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.pairBall`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.physicalCharacteristicFrequency`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.physicalCharacteristicGain` and 357 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Boltzmann_Approximation_MassNormalizedCollisionLimits`, `Boltzmann_Approximation_MildConservation`, `Boltzmann_Approximation_PositiveAccessAngles`, `Boltzmann_Approximation_PositiveContributionsIntegrable`, `Boltzmann_Approximation_PositiveIntegralPasting`, `Boltzmann_Approximation_PositiveIntegralWindow`, `Boltzmann_Approximation_PositiveRestrictedChain`, `Boltzmann_Approximation_PositiveSourceFormula`, `Boltzmann_Approximation_PositiveVolterra`, `Boltzmann_Approximation_RegularizedCollisionDifference`, `Boltzmann_Approximation_RegularizedLogBounds`, `Boltzmann_Branching_BoundedAverageCompactness`, `Boltzmann_Branching_BoundedCollisionBlocks`, `Boltzmann_Branching_BoundedEntryPortion`, `Boltzmann_Branching_BoundedGeometricBlock`, `Boltzmann_Branching_BoundedMeshStep`, `Boltzmann_Branching_CellLocalizedSource`, `Boltzmann_Branching_CharacteristicPhysicalGain`, `Boltzmann_Branching_ClampedMildAE`, `Boltzmann_Branching_ClippedCharacteristicGain`, `Boltzmann_Branching_ClippedColdFiniteLimit`, `Boltzmann_Branching_ComplexWeakL2Diagonal`, `Boltzmann_Branching_DampedBoundedEndpointTransport`, `Boltzmann_Branching_DampedBranchingBlocks`, `Boltzmann_Branching_DampedCollisionHistories`, `Boltzmann_Branching_DampedEndpointHistories`, `Boltzmann_Branching_DampedLateBoxPhysicalBlock`, `Boltzmann_Branching_EnergyTruncation`, `Boltzmann_Branching_HalfGaussianMoment`, `Boltzmann_Branching_HotPositiveRegion`, `Boltzmann_Branching_HotWindowInput`, `Boltzmann_Branching_InteriorCell`, `Boltzmann_Branching_LateBoxAccessMeasure`, `Boltzmann_Branching_LimitFullPositiveSurvival`, `Boltzmann_Branching_MediumStateCollision`, `Boltzmann_Branching_NormalGainMeasureActions`, `Boltzmann_Branching_PerturbedFiniteBlock`, `Boltzmann_Branching_PhaseDecompositionNorm`, `Boltzmann_Branching_PhaseSourceMeasure`, `Boltzmann_Branching_PublishedInputs`, `Boltzmann_Branching_RadialReflectionChangeVariables`, `Boltzmann_Branching_RationalUniformApproximation`, `Boltzmann_Branching_RedundantParameterSupport`, `Boltzmann_Branching_RedundantPlaneIntegral`, `Boltzmann_Branching_ReferenceAngularCharts`, `Boltzmann_Branching_ReferenceBranchingHistories`, `Boltzmann_Branching_ReferenceCollisionGeometry`, `Boltzmann_Branching_ReferenceFlightLaws`, `Boltzmann_Branching_ReferenceGrowthBlocks`, `Boltzmann_Branching_ReferenceHistoryMoments`, `Boltzmann_Branching_ReferenceMinorization`, `Boltzmann_Branching_RegularChart`, `Boltzmann_Branching_RelativeEntropyMarginal`, `Boltzmann_Branching_RestrictedCone`, `Boltzmann_Branching_ScaledBoundedEvent`, `Boltzmann_Branching_SeedEscapeMeasure`, `Boltzmann_Branching_SlopedChart`, `Boltzmann_Branching_SmallFirstGain`, `Boltzmann_Branching_SpaceTimeEssSup`, `Boltzmann_Branching_SpacetimeFourierCoordinates`, `Boltzmann_Branching_SpacetimeRelativeEntropy`, `Boltzmann_Branching_ThreeSelectedIntegral`, `Boltzmann_Branching_TimeSourceCumulative`, `Boltzmann_Branching_TransportCutoff`, `Boltzmann_Branching_TruncatedExponential`, `Boltzmann_Branching_TwoCoreLimit`, `Boltzmann_Branching_WeightedHotGain`, `Boltzmann_Branching_WeightedJetSolutions`, `Boltzmann_Branching_WeightedJetStability`, `Boltzmann_Branching_WeightedNetLoss`, `Boltzmann_Branching_WidthTails`, `Boltzmann_Branching_WindowCollisionMarginal`, `Boltzmann_Branching_WindowLocalizedSource`, `Boltzmann_Collision_AngularPairTests`, `Boltzmann_Collision_CarlemanIdentity`, `Boltzmann_Collision_CarlemanNormalCoordinates`, `Boltzmann_Collision_CarlemanOperator`, `Boltzmann_Collision_CollisionComparisonError`, `Boltzmann_Collision_CollisionConservation`, `Boltzmann_Collision_CollisionMeasure`, `Boltzmann_Collision_CollisionParameterShuffle`, `Boltzmann_Collision_FourierCompactness`, `Boltzmann_Collision_MityaginDischarge`, `Boltzmann_Collision_MityaginPublished`, `Boltzmann_Collision_SheetGain`, `Boltzmann_Collision_SheetIntervals`, `Boltzmann_Collision_SphereDirectionAbsolute`, `Boltzmann_Collision_TransverseAverage`, `Boltzmann_Collision_VelocityAverageDifference`, `Boltzmann_Collision_VelocityCutoffEntropyError`, `Boltzmann_Collision_VelocityPolynomialBounds`, `Boltzmann_Collision_VelocityWeight`, `Boltzmann_Compactness_EntropyDissipationAverage`, `Boltzmann_Compactness_EntropyIntegralBalance`, `Boltzmann_Compactness_EntropyUniformIntegrability`, `Boltzmann_Compactness_FiniteEntryPhaseBound`, `Boltzmann_Compactness_FiniteRatesWindowUI`, `Boltzmann_Compactness_FiniteThermalLimit`, `Boltzmann_Compactness_KineticEntropyErrorLimit`, `Boltzmann_Compactness_KineticWindowL1`, `Boltzmann_Compactness_LocalizedBlockComparison`, `Boltzmann_Compactness_LocalizedDampedBalance`, `Boltzmann_Compactness_LocalizedGainSmoothingAE`, `Boltzmann_Compactness_NormalizedCollisionRates`, `Boltzmann_Compactness_PairPatchIdentity`, `Boltzmann_Compactness_PeriodicFiniteMild`, `Boltzmann_Compactness_PeriodicInitialEntropyLimit`, `Boltzmann_Compactness_PeriodicJointBudgetLimit`, `Boltzmann_Compactness_PeriodicLinearApproximation`, `Boltzmann_Compactness_PeriodicMildApproximation`, `Boltzmann_Compactness_PeriodicMomentEntropy`, `Boltzmann_Compactness_PeriodicStrongAverages`, `Boltzmann_Compactness_PeriodicWeakCompactness`, `Boltzmann_Compactness_PhysicalDissipationBridge`, `Boltzmann_Compactness_PhysicalEntropyProduction`, `Boltzmann_Compactness_PhysicalEvolution`, `Boltzmann_Compactness_PhysicalFrequencyWindow`, `Boltzmann_Compactness_PhysicalGainTransport`, `Boltzmann_Compactness_PhysicalGlobalRenormalized`, `Boltzmann_Compactness_PhysicalLinearContinuous`, `Boltzmann_Compactness_SelectedOriginDeletion`, `Boltzmann_Compactness_StrongCompactPairTests`, `Boltzmann_Compactness_UniformGain`, `Boltzmann_Compactness_WeakL1Operations`, `Boltzmann_Jets_BeamNormalCharacteristicIdentity`, `Boltzmann_Jets_BeamNormalOutgoing`, `Boltzmann_Jets_GeometricLocalizedEntry`, `Boltzmann_Jets_GeometricPositiveCompact`, `Boltzmann_Jets_JetCoreMomentBound`, `Boltzmann_Jets_JetPeriodicDatum`, `Boltzmann_Jets_OriginMeshLimit`, `Boltzmann_Jets_TorusCharacteristic`, `Boltzmann_Jets_TorusChart`, `Boltzmann_Jets_TorusTransport`.
--
--   **Imports.** It imports the published bundle `Def_BoltzmannNonuniqueness`; the bundles `OAIQ080A000` and `OAIQ080A001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.normalized_cutoff_hot_gain_bound_q80`, `OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80`, `OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.positive_coefficient_subsequence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.loss_measure_compact_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.pairLimit_eq_product_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.vanishing_physical_collision_error_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_euclideanHotSource_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_hotSource_cylinder_integrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.CompactFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_traces_and_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.cold_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.hot_net_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.DormantLimit.central_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_axial_escape_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_large_velocity_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.characteristic_error_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_discrepancy_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_path_integrable_full_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_comparison_error_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_gain_discrepancy_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_eq_density_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_le_full_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.normalized_gain_strong_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_energy_le_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_entropy_dissipation_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_momentum_conservation_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_renormalized_field_along_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_survival_lower_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_globalCollisionLimit_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass_q80`, `OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80`, `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit_q80`, `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80` and `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80`; the proofs of `OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.normalized_cutoff_hot_gain_bound_q80`, `OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80`, `OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_mesh_average_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_spacetime_weakStar_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldLabelAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_positive_fraction_mass_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_proportional_loss_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.positive_coefficient_subsequence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.gain_measure_separated_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.loss_measure_compact_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.pairLimit_eq_product_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.vanishing_physical_collision_error_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_euclideanHotSource_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_hotSource_cylinder_integrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.uniform_late_zero_parameters_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.CompactFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_traces_and_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.cold_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.hot_net_source_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily.weak_limit_moment_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.DormantLimit.central_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_gainLoss_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_spacetime_outer_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_separated_cap_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_axial_escape_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_large_velocity_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt_envelope_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80`, `OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.characteristic_error_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_discrepancy_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_path_integrable_full_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_comparison_error_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_gain_discrepancy_L1_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_eq_density_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_le_full_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.normalized_gain_strong_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_energy_le_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_entropy_dissipation_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_kinetic_dissipation_lt_top_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_momentum_conservation_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_renormalized_field_along_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_survival_lower_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_globalCollisionLimit_q80`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass_q80`, `OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80`, `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_limit_q80`, `OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80`, `OAI.BoltzmannNonuniqueness.nonuniqueness`, `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80` and `OAI.BoltzmannNonuniqueness.periodicExistenceInput_q80`.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit 1581d4c

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000
import Definitions.Def_OAIQ080A001

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem sphereArea_univ : sphereArea univ = ENNReal.ofReal (4 * Real.pi) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact sphereArea_real_univ

theorem gaussian_polar_identity (g : Velocity) :
    (∫ x : Velocity, |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) * (1 / 2) := by
  let F : Velocity → ℝ := fun x => |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)
  let H := homeomorphUnitSphereProd Velocity
  have hpolar := (volume : Measure Velocity).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => F (H.symm p))
  change (∫ x, F x) = _
  calc
    (∫ x : Velocity, F x) =
        ∫ x : ({0}ᶜ : Set Velocity), F x ∂((volume : Measure Velocity).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ p : Sphere × Ioi (0 : ℝ), F ((p.2 : ℝ) • (p.1 : Velocity))
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      simpa only [sphereArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hpolar
    _ = ∫ p : Sphere × Ioi (0 : ℝ),
        |inner ℝ g (p.1 : Velocity)| * ((p.2 : ℝ) * Real.exp (-(p.2 : ℝ) ^ 2))
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      apply integral_congr_ae
      filter_upwards [] with p
      have hω : ‖(p.1 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
      have hr : (0 : ℝ) < p.2 := p.2.property
      simp [F, inner_smul_right, norm_smul, Real.norm_eq_abs, hω, abs_of_pos hr, mul_assoc,
        mul_left_comm, mul_comm]
    _ = (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) *
        (∫ r : Ioi (0 : ℝ), (r : ℝ) * Real.exp (-(r : ℝ) ^ 2)
          ∂Measure.volumeIoiPow 2) :=
      integral_prod_mul (fun ω : Sphere => |inner ℝ g (ω : Velocity)|)
        (fun r : Ioi (0 : ℝ) => (r : ℝ) * Real.exp (-(r : ℝ) ^ 2))
    _ = _ := by rw [gaussian_radial_weighted]

/-- The normal-parametrized hard-sphere angular integral has coefficient `2 * π`. -/
theorem integral_abs_inner_sphereArea (g : Velocity) :
    (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) = 2 * Real.pi * ‖g‖ := by
  have hp := gaussian_polar_identity g
  rw [gaussian_linear_integral] at hp
  linarith

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PublishedInputs
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published analytic input for periodic hard-sphere nonuniqueness

`GLPS1988Proposition3` expresses the velocity-localized, time-dependent specialization of Proposition 3
of F. Golse, P.-L. Lions, B. Perthame and R. Sentis, "Regularity of the moments of the solution of
a transport equation", J. Functional Analysis 76 (1988), 110–125, pp. 115–116,
DOI: 10.1016/0022-1236(88)90051-1. The passage to evolution equations is explained in their
Remark (2), p. 119. In their notation, the velocity measure is supported on velocities `(1,v)`;
compact velocity support supplies their nonconcentration condition (2.14).

This compactness statement applies to uniformly integrable sources with bounded velocity
support, independently of the cap and branching constructions.

The global continuation input is Theorem 4.1 of C. D. Levermore and N. Masmoudi,
"From the Boltzmann equation to an incompressible Navier–Stokes–Fourier system",
Arch. Rational Mech. Anal. 196 (2010), 753–809, pp. 765–767,
DOI: 10.1007/s00205-009-0254-5. The elementary entropy estimate converts that
continuation theorem to separate gain and loss integrability.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

/-- The damped free-transport resolvent, with the incoming characteristic parametrization. -/
def transportResolvent (r : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  ∫ s in Ici (0 : ℝ), Real.exp (-s) * r ((z.1.1 - s, z.1.2 - s • z.2), z.2)

/-- A velocity average of the damped free-transport resolvent. -/
def resolventAverage (r : KineticPhase → ℝ) (ψ : Velocity → ℝ) (z : SpaceTime) : ℝ :=
  ∫ v, ψ v * transportResolvent r (z, v)

/-- Local `L¹` convergence is stated with the extended `L¹` seminorm, so that an undefined
Bochner integral cannot make a nonintegrable error appear to have zero norm. -/
def LocalL1Converges (f : ℕ → SpaceTime → ℝ) (g : SpaceTime → ℝ) : Prop :=
  LocallyIntegrable g ∧
    ∀ K : Set SpaceTime, IsCompact K →
      Tendsto (fun n => eLpNorm (fun z => f n z - g z) 1 (volume.restrict K))
        atTop (𝓝 0)

/-- A sequential specialization of GLPS (1988), Proposition 3, with the evolution-equation
extension in Remark (2), p. 119. Boundedness and uniform integrability are both contained in
`UniformIntegrable`. The hypothesis has no relation to the novel branching construction. -/
def GLPS1988Proposition3 : Prop :=
  ∀ (r : ℕ → KineticPhase → ℝ) (R : ℝ), 0 < R →
    (∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), R < ‖z.2‖ → r n z = 0) →
    UniformIntegrable r 1 volume →
    ∀ ψ : Velocity → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ (φ : ℕ → ℕ) (g : SpaceTime → ℝ), StrictMono φ ∧
        LocalL1Converges (fun n => resolventAverage (r (φ n)) ψ) g

/-! ## Scalar estimates in the reference branching process

The uniform distribution of a spherical coordinate gives a lower bound for
retention in the speed-five ball and a positive branching potential.
-/

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceCollisionGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.incomingChart_zero _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.normalChart_zero _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The hard-sphere offspring sphere and reference collision rate

The one-child sphere law gives geometric identities for conservation of
momentum and energy, and bounds for the two-beam collision frequency.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_energy (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 = (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 +
      (‖v - w‖ / 2) * inner ℝ (v + w) n := by
  unfold child
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_one,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (norm_nonneg _), hn,
    real_inner_smul_left, real_inner_smul_right, mul_one, mul_pow, div_pow]
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

/-- The radius of the squared-speed interval appearing in the uniform sphere law. -/
def energyRadius (v w : V) : ℝ := ‖v - w‖ * ‖v + w‖

theorem energyRadius_le (v w : V) : energyRadius v w ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have hpar : ‖v - w‖ ^ 2 + ‖v + w‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    ring
  have hsq := sq_nonneg (‖v - w‖ - ‖v + w‖)
  unfold energyRadius
  nlinarith only [hpar, hsq]

theorem two_beam_distance_lower (v e : V) (he : ‖e‖ = 1) :
    2 ≤ ‖v - e‖ + ‖v + e‖ := by
  have h : ‖(v + e) - (v - e)‖ ≤ ‖v + e‖ + ‖v - e‖ := norm_sub_le _ _
  have hid : (v + e) - (v - e) = (2 : ℝ) • e := by module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), he] at h
  linarith

theorem two_beam_distance_upper (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    ‖v - e‖ + ‖v + e‖ ≤ 12 := by
  have hl := norm_sub_le v e
  have hr := norm_add_le v e
  rw [he] at hl hr
  linarith

/-- Collision frequency of a particle in the two unit-strength reference beams. -/
def frequency (v e : V) : ℝ := 2 * Real.pi * (‖v - e‖ + ‖v + e‖)

theorem frequency_lower (v e : V) (he : ‖e‖ = 1) :
    4 * Real.pi ≤ frequency v e := by
  have h := mul_le_mul_of_nonneg_left (two_beam_distance_lower v e he)
    (by positivity : 0 ≤ 2 * Real.pi)
  dsimp only [frequency]
  nlinarith only [h]

theorem frequency_upper (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    frequency v e ≤ 24 * Real.pi := by
  have h := mul_le_mul_of_nonneg_left (two_beam_distance_upper v e he hv)
    (by positivity : 0 ≤ 2 * Real.pi)
  dsimp only [frequency]
  nlinarith only [h]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The normalized outgoing-sphere kernel for reference collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance sphereProbability_isProbability : IsProbabilityMeasure sphereProbability := by
  constructor
  rw [sphereProbability,Measure.smul_apply,smul_eq_mul,sphereArea_univ]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem child_measurable : Measurable (fun z : (V × V) × Sphere =>
    child z.1.1 z.1.2 z.2.1) := by
  unfold child
  fun_prop

instance outgoing_isMarkov : IsMarkovKernel outgoing :=
  Kernel.IsMarkovKernel.map _ child_measurable

theorem outgoing_apply (p : V × V) :
    outgoing p = sphereProbability.map (fun n : Sphere => child p.1 p.2 n.1) := by
  ext s hs
  rw [outgoing,Kernel.map_apply' _ child_measurable p hs,
    Kernel.id_prod_apply' _ p (child_measurable hs),Kernel.const_apply,
    Measure.map_apply (by unfold child; fun_prop) hs]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two-beam reference jump law and its sign probabilities -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def plusProbability (e v : V) : ℝ := ‖v-e‖/(‖v-e‖+‖v+e‖)

theorem plusProbability_mem (e v : V) : plusProbability e v ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact div_le_one_of_le₀ (by linarith [norm_nonneg (v+e)]) (by positivity)

def plusKernel (e : V) : Kernel V V :=
  outgoing.comap (fun v => (v,e)) (measurable_id.prodMk measurable_const)

def minusKernel (e : V) : Kernel V V :=
  outgoing.comap (fun v => (v,-e)) (measurable_id.prodMk measurable_const)

instance plusKernel_isMarkov (e : V) : IsMarkovKernel (plusKernel e) := by
  unfold plusKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance minusKernel_isMarkov (e : V) : IsMarkovKernel (minusKernel e) := by
  unfold minusKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def referenceJump (e : V) : Kernel V V :=
  Kernel.withDensity (plusKernel e) (fun v _ => ENNReal.ofReal (plusProbability e v))+
    Kernel.withDensity (minusKernel e) (fun v _ => ENNReal.ofReal (1-plusProbability e v))

theorem plusProbability_measurable (e : V) : Measurable (plusProbability e) := by
  unfold plusProbability
  fun_prop

instance referenceJump_isMarkov (e : V) : IsMarkovKernel (referenceJump e) := by
  constructor
  intro v
  constructor
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  change (referenceJump e v) univ = 1
  simp only [referenceJump,add_apply,Measure.add_apply,
    Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm]
  rw [withDensity_apply _ MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ,lintegral_const,measure_univ,mul_one]
  rw [← ENNReal.ofReal_add (plusProbability_mem e v).1 (sub_nonneg.mpr (plusProbability_mem e v).2)]
  simp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Normalization of the reference histories retained in the velocity ball -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def referenceRegion : Set V := Metric.closedBall 0 5

theorem referenceRegion_measurable : MeasurableSet referenceRegion :=
  Metric.isClosed_closedBall.measurableSet

def retention (e v : V) : ℝ≥0∞ := referenceJump e v referenceRegion

theorem retention_measurable (e : V) : Measurable (retention e) :=
  (referenceJump e).measurable_coe referenceRegion_measurable

theorem retention_le_one (e v : V) : retention e v ≤ 1 := by
  exact prob_le_one

theorem retention_ne_top (e v : V) : retention e v ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (retention_le_one e v)

def retainedJump (e : V) : Kernel V V :=
  Kernel.withDensity ((referenceJump e).restrict referenceRegion_measurable)
    (fun v _ => (retention e v)⁻¹)

theorem retainedJump_apply (e v : V) :
    retainedJump e v = (retention e v)⁻¹ • (referenceJump e v).restrict referenceRegion := by
  rw [retainedJump,Kernel.withDensity_apply _
    (((retention_measurable e).comp measurable_fst).inv),withDensity_const,
    Kernel.restrict_apply]

theorem retainedJump_region (e v : V) (hp : retention e v ≠ 0) :
    retainedJump e v referenceRegion = 1 := by
  rw [retainedJump_apply,Measure.smul_apply,
    Measure.restrict_apply referenceRegion_measurable]
  simp only [inter_self,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (retention_ne_top e v)

def retainedRate (e v : V) : ℝ := 2*(retention e v).toReal*frequency v e

def retainedPotential (e v : V) : ℝ := retainedRate e v-frequency v e

theorem retention_toReal_mem (e v : V) : (retention e v).toReal ∈ Icc (0:ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  exact (ENNReal.toReal_le_toReal (retention_ne_top e v) ENNReal.one_ne_top).mpr
    (retention_le_one e v)

theorem retainedRate_le (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    retainedRate e v ≤ 48*Real.pi := by
  have hu := frequency_upper v e he hv
  have hp := (retention_toReal_mem e v).2
  have hν : 0 ≤ frequency v e := by unfold frequency; positivity
  have hm := mul_le_mul_of_nonneg_right hp hν
  dsimp only [retainedRate]
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # First moments of the reference sphere law for retention bounds -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphere_inner_integrable (g : V) :
    Integrable (fun n : Sphere => inner ℝ g (n : V)) sphereProbability := by
  apply (integrable_const ‖g‖).mono'
    ((continuous_const.inner continuous_subtype_val).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun n => by
    simpa only [Real.norm_eq_abs,mem_sphere_zero_iff_norm.mp n.2,mul_one] using
      abs_real_inner_le_norm g (n : V))

theorem sphere_inner_integral (g : V) :
    (∫ n : Sphere, inner ℝ g (n : V) ∂sphereProbability) = 0 := by
  have h := sphereArea_antipodal.integral_comp (Homeomorph.neg Sphere).measurableEmbedding
    (fun n : Sphere => inner ℝ g (n : V))
  change (∫ n : Sphere, inner ℝ g ((-n : Sphere) : V) ∂sphereArea) =
    ∫ n : Sphere, inner ℝ g (n : V) ∂sphereArea at h
  simp only [coe_neg_sphere,inner_neg_right,integral_neg] at h
  have hz : (∫ n : Sphere, inner ℝ g (n : V) ∂sphereArea) = 0 := by linarith
  rw [sphereProbability,integral_smul_measure,hz,smul_zero]

theorem sphere_abs_inner_integral (g : V) :
    (∫ n : Sphere, |inner ℝ g (n : V)| ∂sphereProbability) = ‖g‖/2 := by
  rw [sphereProbability,integral_smul_measure,smul_eq_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity),integral_abs_inner_sphereArea]
  field_simp
  ring

theorem sphere_abs_inner_integrable (g : V) :
    Integrable (fun n : Sphere => |inner ℝ g (n : V)|) sphereProbability :=
  (sphere_inner_integrable g).abs

theorem sphere_positive_inner_integral (g : V) :
    (∫ n : Sphere, max (inner ℝ g (n : V)) 0 ∂sphereProbability) = ‖g‖/4 := by
  have he (x : ℝ) : max x 0 = (|x|+x)/2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx,abs_of_nonneg hx]; ring
    · rw [max_eq_right (le_of_not_ge hx),abs_of_nonpos (le_of_not_ge hx)]; ring
  simp_rw [he]
  rw [integral_div,integral_add (sphere_abs_inner_integrable g) (sphere_inner_integrable g),
    sphere_abs_inner_integral,sphere_inner_integral]
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A positive retention margin from first spherical moments

A first-moment bound retains at least `35/48` of the offspring in the
radius-five ball, giving a strictly positive branching potential.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_escape_coarse (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (outgoing (v,e)).real referenceRegionᶜ ≤ (13 : ℝ)/48 := by
  let g : V := (‖v-e‖/2) • (v+e)
  let U : Set Sphere := {n | child v e n.1 ∉ referenceRegion}
  have hU : MeasurableSet U := referenceRegion_measurable.compl.preimage
    (show Measurable (fun n : Sphere => child v e n.1) from by unfold child; fun_prop)
  have hg : ‖g‖ ≤ 13 := by
    have hrad := energyRadius_le v e
    have hv2 := (sq_le_sq₀ (norm_nonneg v) (by norm_num)).mpr hv
    rw [he] at hrad
    dsimp only [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    dsimp only [energyRadius] at hrad
    nlinarith
  have hpoint (n : Sphere) : U.indicator (fun _ => (1 : ℝ)) n ≤ max (inner ℝ g (n : V)) 0/12 := by
    by_cases hn : n ∈ U
    · rw [indicator_of_mem hn]
      have hnorm : ‖(n : V)‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
      have hchild : 5 < ‖child v e n.1‖ := by
        simpa only [U,referenceRegion,mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,not_le] using hn
      have henergy := child_energy v e n.1 hnorm
      have hv2 := (sq_le_sq₀ (norm_nonneg v) (by norm_num)).mpr hv
      have hinner : inner ℝ g (n : V) = (‖v-e‖/2)*inner ℝ (v+e) (n : V) := by
        simp only [g,real_inner_smul_left]
      rw [he,← hinner] at henergy
      have hlinear : 12 < inner ℝ g (n : V) := by nlinarith
      have hmax := le_max_left (inner ℝ g (n : V)) 0
      linarith
    · rw [indicator_of_notMem hn]
      exact div_nonneg (le_max_right _ _) (by norm_num)
  have himax : Integrable (fun n : Sphere => max (inner ℝ g (n : V)) 0) sphereProbability :=
    (sphere_abs_inner_integrable g).mono'
      (((continuous_const.inner continuous_subtype_val).max continuous_const).aestronglyMeasurable)
      (ae_of_all _ (fun n => by
        rw [Real.norm_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)))
  have hineq := integral_mono ((integrable_const (1 : ℝ)).indicator hU)
    (himax.div_const 12) hpoint
  have hiU := integral_indicator_one (μ := sphereProbability) hU
  change (∫ n : Sphere, U.indicator (fun _ => (1 : ℝ)) n ∂sphereProbability) = _ at hiU
  rw [hiU,integral_div,sphere_positive_inner_integral] at hineq
  have hmeasure : (outgoing (v,e)).real referenceRegionᶜ = sphereProbability.real U := by
    rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop)
      referenceRegion_measurable.compl]
    rfl
  rw [hmeasure]
  linarith

theorem outgoing_retention_coarse (v e : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (35 : ℝ)/48 ≤ (outgoing (v,e)).real referenceRegion := by
  have h := outgoing_escape_coarse v e he hv
  rw [measureReal_compl referenceRegion_measurable,probReal_univ] at h
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A positive branching potential from the coarse retention estimate -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_real (e v : V) (s : Set V) :
    (referenceJump e v).real s =
      plusProbability e v*(outgoing (v,e)).real s+
        (1-plusProbability e v)*(outgoing (v,-e)).real s := by
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  have heq : referenceJump e v =
      ENNReal.ofReal (plusProbability e v) • outgoing (v,e)+
        ENNReal.ofReal (1-plusProbability e v) • outgoing (v,-e) := by
    simp only [referenceJump,add_apply,Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm,
      withDensity_const]
    rfl
  rw [Measure.real,heq,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)).ne
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)).ne]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (plusProbability_mem e v).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (plusProbability_mem e v).2),Measure.real]

theorem retention_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    (35 : ℝ)/48 ≤ (retention e v).toReal := by
  have hp := outgoing_retention_coarse v e he hv
  have hm := outgoing_retention_coarse v (-e) (by simpa using he) hv
  have hpl := mul_le_mul_of_nonneg_left hp (plusProbability_mem e v).1
  have hml := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr (plusProbability_mem e v).2)
  change (35 : ℝ)/48 ≤ (referenceJump e v).real referenceRegion
  rw [referenceJump_real]
  linarith

theorem retention_ne_zero_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    retention e v ≠ 0 := by
  intro hz
  have h := retention_coarse e v he hv
  rw [hz,ENNReal.toReal_zero] at h
  norm_num at h

theorem retainedPotential_coarse (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) :
    11*Real.pi/6 ≤ retainedPotential e v := by
  have hp := retention_coarse e v he hv
  have hν := frequency_lower v e he
  have hν0 : 0 ≤ frequency v e := by unfold frequency; positivity
  have h₁ := mul_le_mul_of_nonneg_right hp hν0
  have h₂ := mul_le_mul_of_nonneg_left hν (by norm_num : (0:ℝ) ≤ 11/24)
  dsimp only [retainedPotential,retainedRate]
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Sphere probability is invariant under velocity isometries -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : Sphere ≃ᵐ Sphere where
  toFun n := ⟨e n,by simpa only [mem_sphere_zero_iff_norm,e.norm_map] using n.2⟩
  invFun n := ⟨e.symm n,by simpa only [mem_sphere_zero_iff_norm,e.symm.norm_map] using n.2⟩
  left_inv n := by apply Subtype.ext; exact e.symm_apply_apply n
  right_inv n := by apply Subtype.ext; exact e.apply_symm_apply n
  measurable_toFun := (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Unit-sphere curves preserve tangent derivatives under normalization -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalize_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → V} {f' : E →L[ℝ] V} {x : E} (hf : HasFDerivAt f f' x)
    (hn : ‖f x‖ = 1) (ht : ∀ v, inner ℝ (f x) (f' v) = 0) :
    HasFDerivAt (fun y => NormedSpace.normalize (f y)) f' x := by
  have hs := hf.norm_sq.sqrt (by rw [hn]; norm_num)
  have hnorm : HasFDerivAt (fun y => ‖f y‖) (0 : E →L[ℝ] ℝ) x := by
    convert hs using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · ext v
      simp [ht]
  have hi := (hasDerivAt_inv (by rw [hn]; norm_num)).comp_hasFDerivAt x hnorm
  have h := hi.smul hf
  refine h.congr_fderiv ?_
  ext v
  simp [hn]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Three independent output directions at the minorization collision -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def minorizationDirections : Fin 3 → V :=
  ![(1/4 : ℝ) • (firstAxis+3 • beamAxis),
    (Real.sqrt 2/2) • secondAxis,(1/2 : ℝ) • (firstAxis-beamAxis)]

theorem minorizationDirections_independent : LinearIndependent ℝ minorizationDirections := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have h₀ := congrArg (fun v : V => v 0) hg
  have h₁ := congrArg (fun v : V => v 1) hg
  have h₂ := congrArg (fun v : V => v 2) hg
  simp [minorizationDirections,Fin.sum_univ_succ,firstAxis,secondAxis,beamAxis,
    EuclideanSpace.single] at h₀ h₁ h₂
  have hg₁ : g 1 = 0 := by
    have hp : 0 < Real.sqrt 2/2 := by positivity
    nlinarith
  norm_num at h₀ h₂
  fin_cases i <;> dsimp <;> linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeFourierCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hilbert coordinates for the evolution transport Fourier transform -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def spacetimeHilbertEquiv : SpaceTime ≃ᵐ FourierSpace := MeasurableEquiv.toLp 2 _

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-!
# The transverse singularity in the velocity majorant

Section 3 uses `H(v) = exp(-‖v‖²) * ⟨v⟩^(-100) * (1 + ‖v̄‖^(-q))`.
Thus its polynomial factor is `(1 + ‖v‖²)^(-50)`. The values assigned on
the velocity axis use Mathlib's real-power convention and do not affect
Lebesgue integrability.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.VelocityWeight

def gaussianMajorant (β q : ℝ) (v : Velocity) : ℝ :=
  Real.exp (-β * ‖v‖ ^ 2) * (1 + singularity q (transverse v))

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Transverse angular averages

The angular singularity in `ker:transverse-expectation` is integrable when
`q < 2`. Gaussian Cartesian integration and polar coordinates prove this
without choosing a trigonometric chart on the unit circle.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.TransverseAverage

instance circleArea_isFiniteMeasure : IsFiniteMeasure circleArea := by
  unfold circleArea
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianPower (q : ℝ) (e x : Transverse) : ℝ :=
  |inner ℝ e x| ^ (1 - q) * Real.exp (-‖x‖ ^ 2)

def cartesianSplit : Transverse ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

end BoltzmannNonuniqueness.TransverseAverage

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A nonsingular three-dimensional coordinate map for a collision plane

The third coordinate is the coefficient of the normal, rather than distance
along the unit normal. This normalization cancels the length of the normal in
the redundant-parameter density. The transverse normal must be nonzero, just
as in the graph chart used by the actual gain kernel.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

def coordinateMatrix (n : V) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-n 1, n 0, 0;
      n 0*n 2/r, n 1*n 2/r, -(n 0^2+n 1^2)/r;
      n 0/normSq n, n 1/normSq n, n 2/normSq n]

def coordinates (n : V) (r : ℝ) : V →ₗ[ℝ] V := (coordinateMatrix n r).toLin'

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Integrating the redundant coordinate in the collision plane -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

def splitThree : V ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanNormalCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy algebra on a Carleman collision plane

These are the exact geometric and Gaussian identities used in Section 3.
The coarea/disintegration formula expressing the gain as a plane integral
is a separate theorem and is not assumed or asserted here.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The unobserved outgoing velocity is fixed by momentum conservation. -/
def companionVelocity (p ξ v : Velocity) : Velocity := p + ξ - v

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanOperator
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative Carleman gain

Gamba, Panferov and Villani, *Upper Maxwellian bounds for the spatially
homogeneous Boltzmann equation*, Arch. Ration. Mech. Anal. 194 (2009),
253–282, Appendix C, Lemma 16 and the hard-sphere remark. The author's
preprint https://www.csun.edu/~panferov/research/umb_5.pdf gives the formula
on pp. 23–24. Their hard-sphere rate is `|g|/(4π)` in outgoing-direction
coordinates. Multiplication by `2π` gives the present absolute-normal
kernel and the coefficient `2` below.

The nonnegative measurable form of that identity is expressed in an explicit
plane chart. Its density formulation includes the plane-chart measure
identification and allows arbitrary nonnegative measurable densities.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.PlaneChart
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- Carleman gain against a possibly singular incoming velocity measure.
The transverse degeneracy set has measure zero for the sheet laws used here. -/
def chartGain (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  2 * ∫⁻ p : Velocity,
    ENNReal.ofReal (‖normal v p‖⁻¹) *
      ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (chart v p z s) ∂volume ∂volume ∂c

/-- Restriction in the actual incoming velocity and the two chart coordinates. -/
def chartRegionGain (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity)
    (S : Set (Velocity × (ℝ × ℝ))) : ℝ≥0∞ := by
  classical
  exact 2 * ∫⁻ p : Velocity, ENNReal.ofReal (‖normal v p‖⁻¹) *
    ∫⁻ z : ℝ, ∫⁻ s : ℝ, S.indicator
      (fun y => h (chart v y.1 y.2.1 y.2.2)) (p, (z, s)) ∂volume ∂volume ∂c

def normalizedChartGain (c : Measure Velocity) (q : ℝ) (v : Velocity) : ℝ≥0∞ :=
  chartGain c (fun ξ => ENNReal.ofReal (VelocityWeight.H q ξ / VelocityWeight.H q v)) v

namespace Published

/-- The application-specific nonnegative form of the published Carleman identity.
For densities the zero transverse-normal set is Lebesgue null. The statement
does not assert equality for arbitrary singular incoming measures. -/
def GPV2009CarlemanInput : Prop :=
  ∀ f g : Velocity → ℝ≥0∞, Measurable f → Measurable g →
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain f g v = chartGain (volume.withDensity f) g v

end Published

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- Linearity holds even before imposing the unit-normal condition. -/
def scatterLinearMap (ω : Velocity) :
    (Velocity × Velocity) →ₗ[ℝ] (Velocity × Velocity) where
  toFun := scatterPair ω
  map_add' p q := by
    apply Prod.ext
    · simp only [scatterPair, scatterLeft, normalComponent, Prod.fst_add, Prod.snd_add,
        inner_sub_left, inner_add_left]
      module
    · simp only [scatterPair, scatterRight, normalComponent, Prod.fst_add, Prod.snd_add,
        inner_sub_left, inner_add_left]
      module
  map_smul' c p := by
    apply Prod.ext
    · simp only [scatterPair, scatterLeft, normalComponent, Prod.smul_fst, Prod.smul_snd,
        inner_sub_left, real_inner_smul_left, RingHom.id_apply]
      module
    · simp only [scatterPair, scatterRight, normalComponent, Prod.smul_fst, Prod.smul_snd,
        inner_sub_left, real_inner_smul_left, RingHom.id_apply]
      module

/-- A unit-normal collision is a linear involution. -/
def scatterLinearEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    (Velocity × Velocity) ≃ₗ[ℝ] (Velocity × Velocity) :=
  LinearEquiv.ofInvolutive (scatterLinearMap ω) (scatterPair_involutive ω hω)

/-- The collision linear equivalence transported to the Euclidean pair norm. -/
def scatterEuclideanLinearEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    EuclideanVelocityPair ≃ₗ[ℝ] EuclideanVelocityPair :=
  ((WithLp.linearEquiv 2 ℝ (Velocity × Velocity)).trans (scatterLinearEquiv ω hω)).trans
    (WithLp.linearEquiv 2 ℝ (Velocity × Velocity)).symm

/-- Conservation of total kinetic energy makes the collision map an isometry. -/
def scatterLinearIsometryEquiv (ω : Velocity) (hω : ‖ω‖ = 1) :
    EuclideanVelocityPair ≃ₗᵢ[ℝ] EuclideanVelocityPair where
  toLinearEquiv := scatterEuclideanLinearEquiv ω hω
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact scatter_energy p.fst p.snd ω hω

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedLogBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable logarithmic majorant for positive regularized densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def logarithmicMajorant (q B p δ : ℝ) (v : Velocity) : ℝ :=
  (B^(p-1)/(p-1))*H q v^p+
    (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2)*H q v

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A regularization-independent integrable bound for relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def entropyPowerMajorant (q B p : ℝ) (v : Velocity) : ℝ :=
  (B^p/(p-1))*H q v^p+
    (|-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2)*B*H q v+maxwellian v

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Probability sheets and their exponential tilts

An elementary sheet is the coordinate pushforward of a centered transverse
Gaussian (or the atom at zero) and an arbitrary axial probability law. The axial
exponential-moment hypothesis is recorded explicitly. All domination statements
below are inequalities of measures, so they also apply to nonnegative kernels.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.SheetTails

namespace BoltzmannNonuniqueness.SheetMeasures

def transverseLaw (d : ℝ) : Measure Transverse :=
  if d = 0 then Measure.dirac 0 else gaussianLaw d

def sheetLaw (d : ℝ) (ρ : Measure ℝ) : Measure Velocity :=
  (transverseLaw d |>.prod ρ).map join

def transverseTilt (d : ℝ) : Measure Transverse :=
  (transverseLaw d).withDensity (fun p => ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2)))

def tiltedSheet (d : ℝ) (ρ : Measure ℝ) : Measure Velocity :=
  (sheetLaw d ρ).withDensity (fun p => ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2)))

end BoltzmannNonuniqueness.SheetMeasures

end

end

section

/-!
# Geometric and Gaussian bounds for the gain of an elementary sheet

The ball integrals below use the actual three-dimensional collision chart.
The sheet laws may have an atomic transverse component and arbitrary axial
probability laws. No gain bound is included among the hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures

namespace BoltzmannNonuniqueness.SheetGain

def weightRatio (q : ℝ) (v ξ : Velocity) : ℝ≥0∞ :=
  ENNReal.ofReal (W q ξ / W q v)

def ballChartFiber (q : ℝ) (v p : Velocity) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
    ∫⁻ z : ℝ, ∫⁻ s : ℝ,
      if ‖PlaneChart.chart v p z s - v‖ ≤ R then
        weightRatio q v (PlaneChart.chart v p z s) else 0

end BoltzmannNonuniqueness.SheetGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform elementary-sheet gain estimates

The incoming exponential tilt and the Gaussian in the companion velocity
are kept separate. All regions below refer to the complete normalized
kernel, including its singular velocity weight.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.UniformGain

def exponentialTilt (p : Velocity) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2))

def shell (v : Velocity) (R : ℝ) : Set Coordinates :=
  {y | R < radius v y ∧ radius v y ≤ 2 * R}

def incomingTail (u : ℝ) : Set Velocity := {p | u < ‖p‖}

def companionTail (v : Velocity) (u : ℝ) : Set Coordinates :=
  {y | u < ‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖}

end BoltzmannNonuniqueness.UniformGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetIntervals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Probability mixtures and domination by sheets

Elementary sheets are the actual Gaussian/atomic transverse product laws.
The uniform estimate survives probability mixing and measure domination.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.SheetClass

/-- The elementary class allows both zero transverse width and arbitrary axial atoms. -/
def IsElementary (L : ℝ) (c : Measure Velocity) : Prop :=
  ∃ (d : ℝ) (ρ : Measure ℝ), 0 ≤ d ∧ d ≤ 1 / 8 ∧ IsProbabilityMeasure ρ ∧
    AxialMoment ρ L ∧ c = sheetLaw d ρ

end BoltzmannNonuniqueness.SheetClass

end

end

section

/-!
# Uniform removal of the kernel's velocity tails

The bound and its limit do not depend on the elementary sheet or the
outgoing velocity. They give the first tightness assertion in Section 3.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SheetTotal

namespace BoltzmannNonuniqueness.SheetTightness

def tailRegion (v : Velocity) (N : ℕ) : Set Coordinates :=
  {y | 2 * ((N : ℝ) + 1) < radius v y}

def tailBound (q L : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (shellConstant q L * shellTerm (k + N))

end BoltzmannNonuniqueness.SheetTightness

end

end

section

/-!
# Axial interval bounds for the full sheet kernel

The chart coordinate is shifted by the outgoing axial velocity. The interval
restriction below is therefore exactly a restriction on the incoming axial
velocity, and its bound is uniform over all axial probability laws.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetIntervals

def intervalRegion (v : Velocity) (R a b : ℝ) : Set Coordinates :=
  ballRegion v R ∩ {y | y.2.1 ∈ Ioc (a - axial v) (b - axial v)}

def intervalFiber (q : ℝ) (v p : Velocity) (R a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
    ∫⁻ z in Ioc (a - axial v) (b - axial v), ∫⁻ s : ℝ,
      if ‖PlaneChart.chart v p z s - v‖ ≤ R then
        weightRatio q v (PlaneChart.chart v p z s) else 0

end BoltzmannNonuniqueness.SheetIntervals

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

def cube : Set Velocity := {x | ∀ i, x i ∈ interval}

end BoltzmannNonuniqueness.TorusChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

def label (i : Index) : JetLattice.Label := ⟨i.1, i.2, 0⟩

end BoltzmannNonuniqueness.JetDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Published weak compactness input for the two kinetic measure spaces

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Transactions of the AMS 47 (1940), 323–392, Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.
Publisher: https://www.ams.org/journals/tran/1940-047-03/S0002-9947-1940-0002020-4/S0002-9947-1940-0002020-4.pdf

The hypothesis below is the sequential weak-compactness consequence for the
one- and two-velocity spaces used here. `UniformIntegrable` includes the common
L¹ bound; `UnifTight` supplies the necessary control at infinity. We require
both, including on the infinite velocity spaces. No Boltzmann equation,
nonlinear identification, or admissible solution is assumed by this input.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

def L1WeakCompactnessInput (μ : Measure X) : Prop :=
  ∀ f : ℕ → X → ℝ, (∀ n, Measurable (f n)) →
    UniformIntegrable f 1 μ → UnifTight f 1 μ →
    ∃ (φ : ℕ → ℕ) (g : X → ℝ), StrictMono φ ∧
      WeakL1Converges μ (fun n => f (φ n)) g

/-- Only the two kinetic measure spaces needed in the limit construction. -/
def DunfordPettis1940Theorem321 : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    L1WeakCompactnessInput ((AnnularEnvelope.timePositionVolume T).prod
      (volume : Measure BoltzmannNonuniqueness.Velocity)) ∧
    L1WeakCompactnessInput ((AnnularEnvelope.timePositionVolume T).prod
      (volume : Measure (BoltzmannNonuniqueness.Velocity × BoltzmannNonuniqueness.Velocity)))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreMomentBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exponential velocity moments of the actual cold supersolutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.SheetClass

def exponentialMoment (μ : Measure Velocity) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (Real.exp (2*‖v‖^2)) ∂μ

end BoltzmannNonuniqueness.SheetClass

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HalfGaussianMoment
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half-Gaussian velocity moments for the hot weight and cold cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.VelocityMoment

def moment (f : Velocity → ℝ) : ℝ≥0∞ := ∫⁻ v, ENNReal.ofReal (weight v*f v)

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityPolynomialBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Hard-sphere pair rates controlled by the half-Gaussian moment -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

def pairMoment (f : Velocity → ℝ) : ℝ≥0∞ :=
  ∫⁻ p : Velocity × Velocity, ENNReal.ofReal ((1+‖p.1‖+‖p.2‖)*f p.1*f p.2)

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalGainMeasureActions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual normal-angle gain kernel for measurable cold partner measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

instance normalParameters_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalParameters K) := by unfold normalParameters; infer_instance

end BoltzmannNonuniqueness

end

end

section

/-! # Rotation covariance of the weighted normal-reflection law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

def normalReflectionLaw (e : Sphere) : Measure Sphere :=
  (sphereArea.withDensity (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1|)).map
    (normalReflection e)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RadialReflectionChangeVariables
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A polynomial radial extension of the normal-angle reflection map

On the positive hemisphere this quadratic map is injective. Its radial coordinate
is squared, allowing the angular change of variables to be proved in ambient space.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def radialReflection (e : Sphere) (x : Velocity) : Velocity :=
  ‖x‖^2 • e.1 - (2*inner ℝ e.1 x) • x

end BoltzmannNonuniqueness

end

end

section

/-! # Derivative of the ambient polynomial reflection map -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def radialReflectionDerivative (e : Sphere) (x : Velocity) : Velocity →L[ℝ] Velocity :=
  ((2:ℝ) • innerSL ℝ x).smulRight e.1 -
    ((2*inner ℝ e.1 x) • ContinuousLinearMap.id ℝ Velocity + ((2:ℝ) • innerSL ℝ e.1).smulRight x)

def northSphere : Sphere :=
  ⟨EuclideanSpace.single 0 1,by simp [EuclideanSpace.single]⟩

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereDirectionAbsolute
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A measurable direction map with an arbitrary value at zero -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness

def sphereDirection (e : Sphere) (x : Velocity) : Sphere :=
  if hx : x = 0 then e else
    ⟨NormedSpace.normalize x,mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩

end BoltzmannNonuniqueness

end

end

section

/-! # Lifting sphere tests to the unit velocity ball -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

def sphereBallLift (e : Sphere) (f : Sphere → ℝ≥0∞) (x : Velocity) : ℝ≥0∞ :=
  if ‖x‖ < 1 then f (sphereDirection e x) else 0

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # The angular change of variables on one normal hemisphere -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

def positiveReflectionTest (e : Sphere) (f : Sphere → ℝ≥0∞) (n : Sphere) : ℝ≥0∞ :=
  if 0 < inner ℝ e.1 n.1 then
    ENNReal.ofReal (inner ℝ e.1 n.1)*f (normalReflection e n) else 0

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceAngularCharts
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local unit-sphere coordinates at the minorization collision -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def minorizationChart (z : V) : V := child (incomingChart z) beamAxis (normalChart z)

theorem incomingChart_hasFDerivAt : HasFDerivAt incomingChart incomingTangent 0 := by
  apply normalize_fderiv ((incomingTangent.hasFDerivAt).const_add firstAxis)
  · simpa using axis_norms.1
  · intro z
    simp [incomingTangent,inner_smul_right,first_beam_inner]

theorem normalChart_hasFDerivAt : HasFDerivAt normalChart normalTangent 0 := by
  apply normalize_fderiv ((normalTangent.hasFDerivAt).const_add minorizationNormal)
  · simpa using minorizationNormal_norm
  · intro z
    simp [normalTangent,minorizationNormal,inner_add_left,inner_add_right,
      inner_sub_right,inner_smul_left,inner_smul_right,
      firstAxis,secondAxis,beamAxis,EuclideanSpace.inner_single_left,
      EuclideanSpace.single]

theorem normalChart_contDiffAt : ContDiffAt ℝ 1 normalChart 0 := by
  have h : ContDiffAt ℝ 1 (fun z => minorizationNormal+normalTangent z) (0 : V) :=
    (contDiff_const.add normalTangent.contDiff).contDiffAt
  have hn : minorizationNormal+normalTangent 0 ≠ 0 := by
    simpa using norm_ne_zero_iff.mp (by rw [minorizationNormal_norm]; norm_num)
  exact (h.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn) |>.smul h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The full derivative of the reference collision chart -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def minorizationDerivative : V →L[ℝ] V :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (minorizationDirections i)

theorem incomingChart_distance_derivative :
    HasFDerivAt (fun z => ‖incomingChart z-beamAxis‖)
      ((-1/Real.sqrt 2 : ℝ) • (EuclideanSpace.proj 0 : V →L[ℝ] ℝ)) 0 := by
  have hs := (incomingChart_hasFDerivAt.sub_const beamAxis).norm_sq.sqrt
    (by rw [incomingChart_zero,first_beam_norms.2]; positivity)
  have hfe : (fun z => ‖incomingChart z-beamAxis‖) = fun y => √(‖incomingChart y-beamAxis‖ ^ 2) :=
    funext fun z => (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hfe]
  refine hs.congr_fderiv ?_
  · ext z
    simp only [incomingChart_zero,first_beam_norms.2,
      Real.sqrt_sq (Real.sqrt_nonneg 2),smul_apply,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,incomingTangent,
      ContinuousLinearMap.smulRight_apply,inner_smul_right,inner_sub_left,
      first_beam_inner,real_inner_self_eq_norm_sq,axis_norms.2.2,one_pow]
    simp only [smul_eq_mul]
    ring

theorem minorizationChart_hasFDerivAt :
    HasFDerivAt minorizationChart minorizationDerivative 0 := by
  have hn : HasFDerivAt (fun z => ‖incomingChart z-beamAxis‖/2)
      ((1/2 : ℝ) • ((-1/Real.sqrt 2 : ℝ) • (EuclideanSpace.proj 0 : V →L[ℝ] ℝ))) 0 := by
    convert incomingChart_distance_derivative.const_smul (1/2 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  have h := ((incomingChart_hasFDerivAt.add_const beamAxis).const_smul (1/2 : ℝ)).add
    (hn.smul normalChart_hasFDerivAt)
  refine h.congr_fderiv ?_
  · ext1 z
    simp only [minorizationDerivative,
      ContinuousLinearMap.smulRight_apply,Fin.sum_univ_three,minorizationDirections,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      add_apply,smul_apply,
      incomingTangent,normalTangent,
      incomingChart_zero,normalChart_zero,first_beam_norms.2,minorizationNormal]
    have hroot : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simp only [smul_smul,smul_add,smul_sub,smul_eq_mul]
    ext i
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    field_simp
    rw [hsq]
    ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A radial extension of the outgoing angular chart -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def normalRadialChart (z : V) : V := ((1/2 : ℝ)+z 0) • normalChart z

def normalRadialDerivative : V →L[ℝ] V :=
  (EuclideanSpace.proj 0).smulRight minorizationNormal + (1/2 : ℝ) • normalTangent

theorem normalRadialDerivative_injective : Function.Injective normalRadialDerivative := by
  intro x y h
  have hz : normalRadialDerivative (x-y) = 0 := by rw [map_sub,h,sub_self]
  have h₀ := congrArg (fun z : V => z 0) hz
  have h₁ := congrArg (fun z : V => z 1) hz
  have h₂ := congrArg (fun z : V => z 2) hz
  simp [normalRadialDerivative,normalTangent,minorizationNormal,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.single] at h₀ h₁ h₂
  have hp : 0 < (Real.sqrt 2)⁻¹ := by positivity
  have hz₀ : x 0-y 0 = 0 := by nlinarith [h₀,h₂]
  have hz₁ : x 1-y 1 = 0 := by simpa using h₁
  have hz₂ : x 2-y 2 = 0 := by nlinarith [h₀,h₂]
  ext i
  fin_cases i
  · exact sub_eq_zero.mp hz₀
  · exact sub_eq_zero.mp hz₁
  · exact sub_eq_zero.mp hz₂

def normalRadialEquiv : V ≃L[ℝ] V :=
  (LinearEquiv.ofBijective normalRadialDerivative.toLinearMap
    ⟨normalRadialDerivative_injective,
      LinearMap.surjective_of_injective normalRadialDerivative_injective⟩).toContinuousLinearEquiv

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Radial volume estimates for the outgoing angular chart -/

noncomputable section

open MeasureTheory Set Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalTangent_inner (z : V) : inner ℝ minorizationNormal (normalTangent z) = 0 := by
  simp [normalTangent,minorizationNormal,inner_add_left,inner_add_right,
    inner_sub_right,inner_smul_left,inner_smul_right,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single]

theorem normalChart_norm (z : V) : ‖normalChart z‖ = 1 := by
  apply NormedSpace.norm_normalize
  intro h
  have hi : inner ℝ minorizationNormal (minorizationNormal+normalTangent z) = 1 := by
    rw [inner_add_right,real_inner_self_eq_norm_sq,minorizationNormal_norm,normalTangent_inner]
    norm_num
  rw [h,inner_zero_right] at hi
  norm_num at hi

def angularSphere (z : V) : Sphere :=
  ⟨normalChart z,mem_sphere_zero_iff_norm.mpr (normalChart_norm z)⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A local inverse of the physical reference collision chart -/

noncomputable section

open scoped Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minorizationDerivative_injective :
    Function.Injective minorizationDerivative := by
  intro x y h
  have hz : minorizationDerivative (x-y) = 0 := by rw [map_sub,h,sub_self]
  have hs : ∑ i : Fin 3, ((x-y) i) • minorizationDirections i = 0 := by
    simpa only [minorizationDerivative,sum_apply,
      ContinuousLinearMap.smulRight_apply,EuclideanSpace.coe_proj] using hz
  ext i
  have hi := Fintype.linearIndependent_iff.mp minorizationDirections_independent
    (fun j => (x-y) j) hs i
  exact sub_eq_zero.mp hi

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Splitting the inactive radial coordinate from angular parameters -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularSplit : V ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

def parameterSphere (p : ℝ × ℝ) : Sphere :=
  angularSphere (WithLp.toLp 2 ![0,p.1,p.2])

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Rotating the outgoing chart to the incoming transverse direction -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def angularRotationLinear : V →L[ℝ] V :=
  (-(Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ)+EuclideanSpace.proj 2)).smulRight firstAxis +
  (EuclideanSpace.proj 1).smulRight secondAxis +
  ((Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ)-EuclideanSpace.proj 2)).smulRight beamAxis

theorem angularRotationLinear_norm (v : V) : ‖angularRotationLinear v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,angularRotationLinear,
    firstAxis,secondAxis,beamAxis,EuclideanSpace.single]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith

def angularRotationIsometry : V →ₗᵢ[ℝ] V where
  toLinearMap := angularRotationLinear.toLinearMap
  norm_map' := angularRotationLinear_norm

def angularRotation : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofSurjective angularRotationIsometry
    (LinearMap.surjective_of_injective angularRotationIsometry.injective)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The incoming angular patch uses the same probability measure bound -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def incomingParameterSphere : (ℝ × ℝ) → Sphere :=
  sphereRotation angularRotation ∘ parameterSphere

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision chart with preceding velocity and unused angle as parameters -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev CollisionParameters := V × ℝ
abbrev CollisionFamilySpace := CollisionParameters × V

def collisionParameterBase : CollisionParameters := (beamAxis,0)
def collisionFamilyBase : CollisionFamilySpace := (collisionParameterBase,0)
def incidentDirection (t : ℝ) (z : V) : V :=
  NormedSpace.normalize (firstAxis+t • secondAxis+incomingTangent z)
def collisionFamily (p : CollisionParameters) (z : V) : V :=
  child (child p.1 (-beamAxis) (incidentDirection p.2 z)) beamAxis (normalChart z)
def collisionFamilyExtension (w : CollisionFamilySpace) : CollisionFamilySpace :=
  (w.1,collisionFamily w.1 w.2)

theorem child_opposite_beam (n : V) : child beamAxis (-beamAxis) n = n := by
  have he : beamAxis-(-beamAxis) = (2 : ℝ) • beamAxis := by module
  simp only [child,add_neg_cancel,smul_zero,he,norm_smul,Real.norm_ofNat,axis_norms.2.2,
    mul_one,div_self (by norm_num : (2 : ℝ) ≠ 0),one_smul,zero_add]

theorem collisionFamily_slice (z : V) :
    collisionFamily collisionParameterBase z = minorizationChart z := by
  simp [collisionFamily,collisionParameterBase,incidentDirection,child_opposite_beam,
    incomingChart,minorizationChart]

theorem normalize_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : D → V} {x : D} (hf : ContDiffAt ℝ 1 f x) (hne : f x ≠ 0) :
    ContDiffAt ℝ 1 (fun y => NormedSpace.normalize (f y)) x :=
  ((hf.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).smul hf

theorem child_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f g n : D → V} {x : D} (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x)
    (hn : ContDiffAt ℝ 1 n x) (hne : f x ≠ g x) :
    ContDiffAt ℝ 1 (fun y => child (f y) (g y) (n y)) x := by
  exact (ContDiffAt.const_smul (1/2 : ℝ) (hf.add hg)).add
    ((((hf.sub hg).norm ℝ (sub_ne_zero.mpr hne)).div contDiffAt_const (by norm_num)).smul hn)

theorem incidentDirection_contDiffAt :
    ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => incidentDirection w.1.2 w.2)
      collisionFamilyBase := by
  apply normalize_contDiffAt
  · change ContDiffAt ℝ 1
      (fun w : CollisionFamilySpace => firstAxis+w.1.2 • secondAxis+incomingTangent w.2) _
    fun_prop
  · change firstAxis+(0 : ℝ) • secondAxis+incomingTangent 0 ≠ 0
    simp only [zero_smul,add_zero,map_zero]
    exact norm_ne_zero_iff.mp (by rw [axis_norms.1]; norm_num)

theorem collisionFamily_contDiffAt :
    ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => collisionFamily w.1 w.2)
      collisionFamilyBase := by
  apply child_contDiffAt
  · apply child_contDiffAt
    · fun_prop
    · exact contDiffAt_const
    · exact incidentDirection_contDiffAt
    · change beamAxis ≠ -beamAxis
      intro h
      have hz : beamAxis = 0 := by
        have he : (2 : ℝ) • beamAxis = 0 := by
          simpa only [two_smul,neg_add_cancel] using congrArg (fun v : V => v+beamAxis) h
        exact (smul_eq_zero.mp he).resolve_left (by norm_num)
      have := axis_norms.2.2
      rw [hz,norm_zero] at this
      norm_num at this
  · exact contDiffAt_const
  · exact normalChart_contDiffAt.comp (f := fun w : CollisionFamilySpace => w.2)
      collisionFamilyBase contDiffAt_snd
  · change child beamAxis (-beamAxis) (incidentDirection 0 0) ≠ beamAxis
    rw [child_opposite_beam]
    have hv : incidentDirection 0 0 = firstAxis := by
      simp [incidentDirection,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]
    rw [hv]
    intro h
    have hi := first_beam_inner
    rw [h,real_inner_self_eq_norm_sq,axis_norms.2.2] at hi
    norm_num at hi

theorem collisionFamilyExtension_contDiffAt :
    ContDiffAt ℝ 1 collisionFamilyExtension collisionFamilyBase :=
  (by fun_prop : ContDiffAt ℝ 1 (fun w : CollisionFamilySpace => w.1) collisionFamilyBase).prodMk
    collisionFamily_contDiffAt

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision family has an invertible derivative including its parameters -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def collisionFamilyDerivative : CollisionFamilySpace →L[ℝ] CollisionFamilySpace :=
  fderiv ℝ collisionFamilyExtension collisionFamilyBase

theorem collisionFamilyExtension_hasFDerivAt :
    HasFDerivAt collisionFamilyExtension collisionFamilyDerivative collisionFamilyBase :=
  (collisionFamilyExtension_contDiffAt.differentiableAt (by norm_num)).hasFDerivAt

theorem collisionFamilyDerivative_fst (w : CollisionFamilySpace) :
    (collisionFamilyDerivative w).1 = w.1 := by
  have hf : (ContinuousLinearMap.fst ℝ CollisionParameters V).comp collisionFamilyDerivative =
      ContinuousLinearMap.fst ℝ CollisionParameters V :=
    collisionFamilyExtension_hasFDerivAt.fst.unique hasFDerivAt_fst
  exact congrArg (fun f : CollisionFamilySpace →L[ℝ] CollisionParameters => f w) hf

theorem collisionFamilyDerivative_slice (z : V) :
    collisionFamilyDerivative (0,z) = (0,minorizationDerivative z) := by
  have h := collisionFamilyExtension_hasFDerivAt.comp (0 : V)
    (hasFDerivAt_prodMk_right collisionParameterBase (0 : V))
  have hs : HasFDerivAt (fun z : V => (collisionParameterBase,minorizationChart z))
      (collisionFamilyDerivative.comp (ContinuousLinearMap.inr ℝ CollisionParameters V)) 0 := by
    simpa only [Function.comp_def,collisionFamilyExtension,collisionFamily_slice] using! h
  have hh := hs.unique ((hasFDerivAt_const collisionParameterBase (0 : V)).prodMk
    minorizationChart_hasFDerivAt)
  exact congrArg (fun f : V →L[ℝ] CollisionFamilySpace => f z) hh

theorem collisionFamilyDerivative_injective : Function.Injective collisionFamilyDerivative := by
  intro x y hxy
  have hu : collisionFamilyDerivative (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  have hp : (x-y).1 = 0 := by
    rw [← collisionFamilyDerivative_fst]
    exact congrArg Prod.fst hu
  have he : x-y = (0,(x-y).2) := Prod.ext hp rfl
  rw [he,collisionFamilyDerivative_slice] at hu
  have hz : (x-y).2 = 0 := minorizationDerivative_injective (by
    simpa using congrArg Prod.snd hu)
  exact sub_eq_zero.mp (Prod.ext hp hz)

def collisionFamilyLinearEquiv : CollisionFamilySpace ≃L[ℝ] CollisionFamilySpace :=
  (LinearEquiv.ofBijective collisionFamilyDerivative.toLinearMap
    ⟨collisionFamilyDerivative_injective,
      LinearMap.surjective_of_injective collisionFamilyDerivative_injective⟩).toContinuousLinearEquiv

theorem collisionFamilyExtension_hasStrictFDerivAt :
    HasStrictFDerivAt collisionFamilyExtension
      (collisionFamilyLinearEquiv : CollisionFamilySpace →L[ℝ] CollisionFamilySpace)
      collisionFamilyBase := by
  apply collisionFamilyExtension_contDiffAt.hasStrictFDerivAt' _ (by norm_num)
  exact collisionFamilyExtension_hasFDerivAt

def collisionFamilyLocalEquiv : OpenPartialHomeomorph CollisionFamilySpace CollisionFamilySpace :=
  collisionFamilyExtension_hasStrictFDerivAt.toOpenPartialHomeomorph collisionFamilyExtension

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Volume-preserving coordinates for the four collision angles -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyCoordinates : (ℝ × V) ≃ᵐ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) angularSplit).trans
    MeasurableEquiv.prodAssoc.symm

def twoCollisionMap (v : V) (p : Sphere × Sphere) : V :=
  child (child v (-beamAxis) (p.1 : V)) beamAxis (p.2 : V)

def familyChart (v : V) (p : (ℝ × ℝ) × (ℝ × ℝ)) : V :=
  twoCollisionMap v (incomingParameterSphere p.1,parameterSphere p.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Averaging the uniform collision-chart volume estimate over the unused angle -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyWindowMeasure (a δ : ℝ) : Measure (ℝ × V) :=
  (volume.restrict (Ioo (-δ) δ)).prod (volume.restrict (ball (0 : V) a))

def familyWindowMap (v : V) (w : ℝ × V) : V := collisionFamily (v,w.1) w.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A collision window on which both chosen beam probabilities stay positive -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

def firstCollisionFamily (w : CollisionFamilySpace) : V :=
  child w.1.1 (-beamAxis) (incidentDirection w.1.2 w.2)

def localCollisionCore : Set V := ball firstAxis (1/4)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceMinorization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The angular window is dominated while retaining its intermediate-velocity support -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyWindowAngles (w : ℝ × V) : Sphere × Sphere :=
  (incomingParameterSphere (w.1,w.2 0),parameterSphere (w.2 1,w.2 2))

def firstAngleSet (v : V) : Set (Sphere × Sphere) :=
  {p | child v (-beamAxis) (p.1 : V) ∈ localCollisionCore}

def localTwoCollisionLaw (v : V) : Measure V :=
  ((sphereProbability.prod sphereProbability).restrict (firstAngleSet v)).map (twoCollisionMap v)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The retained reference law as a Markov kernel on its bounded state space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev RetainedState := {v : V // v ∈ referenceRegion}

theorem retainedState_norm (v : RetainedState) : ‖(v : V)‖ ≤ 5 := by
  simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right] using v.2

def stateKernel : Kernel RetainedState RetainedState :=
  ((retainedJump beamAxis).comap (Subtype.val : RetainedState → V) measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe referenceRegion_measurable)

instance stateKernel_isMarkov : IsMarkovKernel stateKernel := by
  apply Kernel.IsMarkovKernel.comapRight
  intro v
  rw [Kernel.comap_apply,Subtype.range_coe]
  exact retainedJump_region _ _ (retention_ne_zero_coarse _ _ axis_norms.2.2 (retainedState_norm v))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A constant-rate uniformization of the retained velocity dynamics -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateRate (v : RetainedState) : ℝ := retainedRate beamAxis v.1

def jumpFraction (v : RetainedState) : ℝ := stateRate v/(48*Real.pi)

theorem stateRate_measurable : Measurable stateRate := by
  unfold stateRate retainedRate
  exact ((measurable_const.mul ((retention_measurable beamAxis).comp
    measurable_subtype_coe).ennreal_toReal).mul (by unfold frequency; fun_prop))

theorem stateRate_bounds (v : RetainedState) : 4*Real.pi ≤ stateRate v ∧ stateRate v ≤ 48*Real.pi := by
  have hp := retainedPotential_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)
  have hf := frequency_lower v.1 beamAxis axis_norms.2.2
  dsimp only [retainedPotential] at hp
  exact ⟨by dsimp [stateRate] <;> linarith [Real.pi_pos],
    retainedRate_le _ _ axis_norms.2.2 (retainedState_norm v)⟩

theorem jumpFraction_measurable : Measurable jumpFraction := stateRate_measurable.div_const _

theorem jumpFraction_bounds (v : RetainedState) : (1/12 : ℝ) ≤ jumpFraction v ∧ jumpFraction v ≤ 1 := by
  have hb := stateRate_bounds v
  constructor
  · rw [jumpFraction,le_div_iff₀ (by positivity : 0 < 48*Real.pi)]
    linarith [hb.1]
  · rw [jumpFraction,div_le_one (by positivity : 0 < 48*Real.pi)]
    exact hb.2

def uniformizedKernel : Kernel RetainedState RetainedState :=
  Kernel.withDensity stateKernel (fun v _ => ENNReal.ofReal (jumpFraction v)) +
    Kernel.withDensity Kernel.id (fun v _ => ENNReal.ofReal (1-jumpFraction v))

theorem uniformizedKernel_apply (v : RetainedState) : uniformizedKernel v =
    ENNReal.ofReal (jumpFraction v) • stateKernel v +
      ENNReal.ofReal (1-jumpFraction v) • Measure.dirac v := by
  have hp : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (jumpFraction v))) := (jumpFraction_measurable.comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (1-jumpFraction v))) :=
    (measurable_const.sub (jumpFraction_measurable.comp measurable_fst)).ennreal_ofReal
  simp only [uniformizedKernel,add_apply,Kernel.withDensity_apply _ hp,
    Kernel.withDensity_apply _ hm,withDensity_const,Kernel.id_apply]

instance uniformizedKernel_isMarkov : IsMarkovKernel uniformizedKernel := by
  constructor
  intro v
  constructor
  rw [uniformizedKernel_apply,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [measure_univ,Measure.dirac_apply_of_mem (mem_univ v),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (by linarith [(jumpFraction_bounds v).1])
    (sub_nonneg.mpr (jumpFraction_bounds v).2)]
  simp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The positive collision kernel after adding a constant attenuation clock -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateFrequency (v : RetainedState) : ℝ := frequency v.1 beamAxis

def statePotential (v : RetainedState) : ℝ := stateRate v-stateFrequency v

def branchingKernel : Kernel RetainedState RetainedState :=
  Kernel.withDensity stateKernel (fun v _ => ENNReal.ofReal (stateRate v)) +
    Kernel.withDensity Kernel.id (fun v _ => ENNReal.ofReal (48*Real.pi-stateFrequency v))

instance branchingKernel_isSFinite : IsSFiniteKernel branchingKernel := by
  unfold branchingKernel
  have hr : IsSFiniteKernel (Kernel.withDensity stateKernel
      (fun v (_ : RetainedState) => ENNReal.ofReal (stateRate v))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro v u
    exact ENNReal.ofReal_ne_top
  have hs : IsSFiniteKernel (Kernel.withDensity Kernel.id
      (fun v (_ : RetainedState) => ENNReal.ofReal (48*Real.pi-stateFrequency v))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro v u
    exact ENNReal.ofReal_ne_top
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Three-step common volume on the bounded reference state space -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateBallMeasure (δ : ℝ) : Measure RetainedState :=
  (volume.restrict (ball (0 : V) δ)).comap (Subtype.val : RetainedState → V)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Reversal symmetry on the bounded state space and the uniformized chain -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateNeg : RetainedState ≃ᵐ RetainedState where
  toFun v := ⟨-v.1,by simpa [referenceRegion,mem_closedBall,dist_zero_right] using v.2⟩
  invFun v := ⟨-v.1,by simpa [referenceRegion,mem_closedBall,dist_zero_right] using v.2⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe.neg
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe.neg

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A nonzero symmetric common part of all three-step transition laws -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance uniformizedKernel_pow_isMarkov (n : ℕ) : IsMarkovKernel (uniformizedKernel^n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    have heq : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [heq]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Measurable symmetric averages of the actual uniformized velocity chain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def chainAverage (n : ℕ) (f : RetainedState → V) (v : RetainedState) : V :=
  ∫ u, f u ∂(uniformizedKernel^n) v

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint value and velocity truncation controlled by absolute entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def entropyGauge (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p*(1+‖p.2‖^2+|Real.log (f p)|)

def entropyTruncation (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  if ‖p.2‖ ≤ R ∧ f p ≤ Real.exp R then f p else 0

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L¹ continuity of free transport on the physical torus -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

local instance instRegularPhaseVolume_r432bee_1 : (volume : Measure Phase).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
def continuousFlight (t : ℝ) : C(Phase,Phase) :=
  ⟨flight t,continuous_flight.comp (continuous_const.prodMk continuous_id)⟩

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Integrals in characteristic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def flightEquiv (t : ℝ) : Phase ≃ᵐ Phase where
  toFun := flight t
  invFun := flight (-t)
  left_inv := flight_neg t
  right_inv := neg_flight t
  measurable_toFun := measurable_flight.comp (measurable_const.prodMk measurable_id)
  measurable_invFun := measurable_flight.comp (measurable_const.prodMk measurable_id)

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Uniform bounds for periodic tests on a finite time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness

def fundamentalCube : Set Velocity :=
  WithLp.toLp 2 '' (univ.pi (fun _ : Fin 3 => Icc (0:ℝ) 1))

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveAccessAngles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed positive set of angular pairs reaching the target velocity ball -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def accessAngles (κ ρ : ℝ) : Set (Sphere × Sphere) :=
  twoCollisionMap beamAxis ⁻¹' ball (κ • firstAxis) ρ ∩ firstAngleSet beamAxis

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityCutoffEntropyError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of the linear velocity moment from entropy and energy -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def linearMoment (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := (1+‖p.2‖)*f p

def velocityLinearCut (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  if ‖p.2‖ ≤ R then linearMoment f p else 0

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedCollisionRates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Passing the first-velocity-moment weight through normalized-pair convergence -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def boundedPairWeight (R : ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then pairVelocityWeight z else 0

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairPatchIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L1 continuity of translations on the outgoing velocity-pair space -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance pairTranslationHaar_r432bee_1 : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) :=
  Measure.prod.instIsAddHaarMeasure _ _
local instance pairTranslationRegular_r432bee_1 : (volume : Measure (Velocity × Velocity)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
def pairTranslation (a : Velocity × Velocity) : C(Velocity × Velocity,Velocity × Velocity) :=
  ⟨fun p => p+a,continuous_id.add continuous_const⟩

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TransportCutoff
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of smooth kinetic cutoffs along free characteristics -/

noncomputable section

open Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def transportDerivative (χ : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  fderiv ℝ χ z ((1,z.2),0)

end BoltzmannNonuniqueness.TransportCutoff

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedGainSmoothingAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Causal localized transport sources and their velocity support -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def localizedSource (U : ℝ) (χ f Q : KineticPhase → ℝ) (z : KineticPhase) : ℝ :=
  if z.1.1 ∈ Icc 0 U then χ z*Q z+(transportDerivative χ z+χ z)*f z else 0

end BoltzmannNonuniqueness.TransportCutoff

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedCollisionDifference
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff collision error of positive Gaussian regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness

def gaussianRegularization (δ : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  f v+δ*Real.exp (-2*‖v‖^2)

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The integrable entropy error caused by positive regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def entropyErrorCoefficient (q A b : ℝ) : ℝ :=
  tiltConstant*(2*A+tiltConstant)*
    (HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)

end BoltzmannNonuniqueness

end

end

section

/-! # Finite Gaussian relative entropy controls the required datum class -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

def entropyGaussian (v : Velocity) : ℝ :=
  maxwellian v * Real.exp ((1+‖v‖^2)/4)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticEntropyErrorLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The Gaussian entropy error is integrable on a finite kinetic base -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def gaussianRegularizedDensity (δ : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p+δ*Real.exp (-2*‖p.2‖^2)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceFlightLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The constant-rate reference transition law as an actual Poisson mixture -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def poissonKernel (r : ℝ≥0) : Kernel RetainedState RetainedState :=
  Kernel.sum (fun n => Kernel.withDensity (uniformizedKernel^n)
    (fun _ _ => (poissonMeasure r) {n}))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly bounded sums of the expected velocities of the discrete chain -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.ReferenceGeometry

def velocitySum (n : ℕ) (v : RetainedState) : V :=
  ∑ k ∈ Finset.range (n+1), chainAverage k (fun u => (u : V)) v

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Position-preserving jumps and deterministic flights of the reference process -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev FlightState := V × RetainedState

def freeFlight (t : ℝ) (z : FlightState) : FlightState := (z.1+t • (z.2 : V),z.2)

theorem freeFlight_measurable : Measurable (fun p : ℝ × FlightState => freeFlight p.1 p.2) := by
  unfold freeFlight
  fun_prop

def freeFlightKernel (t : ℝ) : Kernel FlightState FlightState :=
  Kernel.deterministic (freeFlight t) (freeFlight_measurable.comp (measurable_const.prodMk measurable_id))

instance freeFlightKernel_isMarkov (t : ℝ) : IsMarkovKernel (freeFlightKernel t) := inferInstanceAs
  (IsMarkovKernel (Kernel.deterministic (freeFlight t) _))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lebesgue waiting-time choices for finite collision histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev TimeFlightState := ℝ × FlightState

def waitingDensity (p : TimeFlightState) (s : ℝ) : ℝ≥0∞ := (Ioc 0 p.1).indicator 1 s

def waitingTime : Kernel TimeFlightState ℝ :=
  Kernel.withDensity (Kernel.const TimeFlightState (volume : Measure ℝ)) waitingDensity

instance waitingTime_isSFinite : IsSFiniteKernel waitingTime := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro p s
  by_cases h : s ∈ Ioc 0 p.1 <;> simp [waitingDensity,h]

def advanceState (p : TimeFlightState) (s : ℝ) (u : RetainedState) : TimeFlightState :=
  (p.1-s,((freeFlight s p.2).1,u))

theorem advanceState_measurable :
    Measurable (fun q : (TimeFlightState × ℝ) × RetainedState => advanceState q.1.1 q.1.2 q.2) := by
  unfold advanceState freeFlight
  fun_prop

def jumpAfterWait : Kernel (TimeFlightState × ℝ) TimeFlightState :=
  (Kernel.id ×ₖ uniformizedKernel.comap (fun q : TimeFlightState × ℝ => q.1.2.2)
    (by fun_prop)).map (fun q => advanceState q.1.1 q.1.2 q.2)

instance jumpAfterWait_isMarkov : IsMarkovKernel jumpAfterWait :=
  Kernel.IsMarkovKernel.map _ advanceState_measurable

def historyStep : Kernel TimeFlightState TimeFlightState :=
  jumpAfterWait ∘ₖ (Kernel.id ×ₖ waitingTime)

instance historyStep_isSFinite : IsSFiniteKernel historyStep := by unfold historyStep; infer_instance

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual finite free-flight and collision-history kernels -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def finishFlight (p : TimeFlightState) : FlightState := freeFlight p.1 p.2

theorem finishFlight_measurable : Measurable finishFlight := freeFlight_measurable

instance historyStep_pow_isSFinite (n : ℕ) : IsSFiniteKernel (historyStep^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    have heq : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
      simpa only [pow_one] using Kernel.pow_add historyStep n 1
    rw [heq]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def historyKernel (n : ℕ) : Kernel TimeFlightState FlightState :=
  (historyStep^n).map finishFlight

instance historyKernel_isSFinite (n : ℕ) : IsSFiniteKernel (historyKernel n) := by
  unfold historyKernel
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply finishFlight_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual free-flight law with a fixed Poisson collision rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightKernel (rate T : ℝ≥0) : Kernel FlightState FlightState :=
  Kernel.sum (fun n => Kernel.withDensity
    ((historyKernel n).comap (fun z => ((T : ℝ),z)) (by fun_prop))
    (fun _ _ => flightWeight rate T n))

instance flightKernel_isSFinite (rate T : ℝ≥0) : IsSFiniteKernel (flightKernel rate T) := by
  unfold flightKernel
  have hi (n : ℕ) : IsSFiniteKernel (Kernel.withDensity
      ((historyKernel n).comap (fun z => ((T : ℝ),z)) (by fun_prop))
      (fun _ _ => flightWeight rate T n)) :=
    by
      apply Kernel.IsSFiniteKernel.withDensity
      intro p q
      exact ENNReal.ofReal_ne_top
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Jointly measurable flight laws with remaining time as a kernel input -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightFamily (rate : ℝ≥0) : Kernel TimeFlightState FlightState :=
  Kernel.sum (fun n => Kernel.withDensity (historyKernel n)
    (fun p _ => realFlightWeight rate n p.1))

instance flightFamily_isSFinite (rate : ℝ≥0) : IsSFiniteKernel (flightFamily rate) := by
  unfold flightFamily
  have hi (n : ℕ) : IsSFiniteKernel (Kernel.withDensity (historyKernel n)
      (fun p _ => realFlightWeight rate n p.1)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p z
    exact ENNReal.ofReal_ne_top
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exponential first-event kernel on remaining-time flight states -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def renewalDensity (rate : ℝ≥0) (p q : TimeFlightState) : ℝ≥0∞ :=
  ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*(p.1-q.1)))

def renewalStep (rate : ℝ≥0) : Kernel TimeFlightState TimeFlightState :=
  Kernel.withDensity historyStep (renewalDensity rate)

instance renewalStep_isSFinite (rate : ℝ≥0) : IsSFiniteKernel (renewalStep rate) := by
  unfold renewalStep
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Factorial remainder bounds for the actual first-event kernel -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance renewalStep_pow_isSFinite (rate : ℝ≥0) (n : ℕ) : IsSFiniteKernel (((renewalStep rate)^n)) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The reference flight with a constant positive branching potential -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def weightedFlight (rate : ℝ≥0) (c : ℝ) (f : FlightState → ℝ≥0∞)
    (p : TimeFlightState) : ℝ≥0∞ :=
  growthWeight c p.1 * ∫⁻ z, f z ∂flightFamily rate p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Damped finite collision histories for the positive reference gain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def eventAfterWait (K : Kernel RetainedState RetainedState) :
    Kernel (TimeFlightState × ℝ) TimeFlightState :=
  (Kernel.id ×ₖ K.comap (fun q : TimeFlightState × ℝ => q.1.2.2)
    (by fun_prop)).map (fun q => advanceState q.1.1 q.1.2 q.2)

def rawEventStep (K : Kernel RetainedState RetainedState) : Kernel TimeFlightState TimeFlightState :=
  eventAfterWait K ∘ₖ (Kernel.id ×ₖ waitingTime)

instance eventAfterWait_isSFinite (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    IsSFiniteKernel (eventAfterWait K) := by unfold eventAfterWait; infer_instance

instance rawEventStep_isSFinite (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    IsSFiniteKernel (rawEventStep K) := by unfold rawEventStep; infer_instance

def eventDensity (rate : ℝ≥0) (p q : TimeFlightState) : ℝ≥0∞ :=
  clockSurvival rate (p.1-q.1)

def eventStep (rate : ℝ≥0) (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    Kernel TimeFlightState TimeFlightState :=
  Kernel.withDensity (rawEventStep K) (eventDensity rate)

instance eventStep_isSFinite (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] : IsSFiniteKernel (eventStep rate K) := by
  unfold eventStep
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

instance eventStep_pow_isSFinite (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel ((eventStep rate K)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive finite-history exhaustion for a bounded reference subsolution -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

def eventHistory (rate : ℝ≥0) (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K]
    (D : TimeFlightState → ℝ≥0∞) (n : ℕ) (p : TimeFlightState) : ℝ≥0∞ :=
  ∫⁻ q, D q ∂((eventStep rate K)^n) p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponentially growing reference flight is dominated by actual positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightSeed (rate : ℝ≥0) (f : FlightState → ℝ≥0∞) (p : TimeFlightState) : ℝ≥0∞ :=
  clockSurvival rate p.1*f (finishFlight p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Pointwise collision-rate stability for merely measurable partner fields -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumFrequency (v w_plus w_minus : V) (b_plus b_minus : ℝ) : ℝ :=
  2*Real.pi*(b_plus*‖v-w_plus‖+b_minus*‖v-w_minus‖)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Coupled positive histories with two beam marks and self-retention marks -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def markedChild (m : HistoryMark) (v wp wm n : V) : V :=
  if m = 0 then v else child v (if m = 1 then wp else wm) n

def markedRate (m : HistoryMark) (v wp wm : V) (bp bm : ℝ) : ℝ :=
  if m = 0 then 48*Real.pi-mediumFrequency v wp wm bp bm
  else if m = 1 then 4*Real.pi*bp*‖v-wp‖ else 4*Real.pi*bm*‖v-wm‖

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceHistoryMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable extension of retained-state observables to the physical velocity space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem state_projection_exists :
    ∃ f : V → RetainedState, Measurable f ∧ ∀ v : RetainedState, f v.1 = v :=
  referenceRegion_measurable.exists_measurable_proj ⟨0,by simp [referenceRegion]⟩

def stateProjection : V → RetainedState := Classical.choose state_projection_exists

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Explicit mark-and-angle formula for one positive reference event -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def markedReferenceWeight (v : RetainedState) (m : HistoryMark) (n : Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (markedRate m v.1 beamAxis (-beamAxis) 1 1) *
    referenceRegion.indicator 1 (markedChild m v.1 beamAxis (-beamAxis) n.1)

def markedReferenceState (v : RetainedState) (m : HistoryMark) (n : Sphere) : RetainedState :=
  stateProjection (markedChild m v.1 beamAxis (-beamAxis) n.1)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite time-and-angle parameter measures for the selected positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def eventParameterMeasure (T : ℝ) : Measure EventParameter :=
  (volume.restrict (Ioc 0 T)).prod sphereProbability

instance eventParameterMeasure_isFinite (T : ℝ) : IsFiniteMeasure (eventParameterMeasure T) := by
  unfold eventParameterMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def referenceParameterState (p : TimeFlightState) (m : HistoryMark) (a : EventParameter) :
    TimeFlightState := advanceState p a.1 (markedReferenceState p.2.2 m a.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A fixed finite parameter measure including the three event marks -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev MarkedEventParameter := HistoryMark × EventParameter

def markedEventMeasure (T : ℝ) : Measure MarkedEventParameter :=
  Measure.count.prod (eventParameterMeasure T)

instance markedEventMeasure_isFinite (T : ℝ) : IsFiniteMeasure (markedEventMeasure T) := by
  unfold markedEventMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def markedParameterState (p : TimeFlightState) (a : MarkedEventParameter) : TimeFlightState :=
  referenceParameterState p a.1 a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed finite products of time, mark and angle parameters -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ParameterWord : ℕ → Type
  | 0 => PUnit
  | n+1 => MarkedEventParameter × ParameterWord n

abbrev parameterWordMeasurable : (n : ℕ) → MeasurableSpace (ParameterWord n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := parameterWordMeasurable n
    exact inferInstanceAs (MeasurableSpace (MarkedEventParameter × ParameterWord n))

attribute [instance] parameterWordMeasurable

def parameterWordMeasure (T : ℝ) : (n : ℕ) → Measure (ParameterWord n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => (markedEventMeasure T).prod (parameterWordMeasure T n)

instance parameterWordMeasure_isFinite (T : ℝ) (n : ℕ) : IsFiniteMeasure (parameterWordMeasure T n) := by
  induction n with
  | zero => change IsFiniteMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    let _ := ih
    change IsFiniteMeasure ((markedEventMeasure T).prod (parameterWordMeasure T n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def parameterWordState : (n : ℕ) → TimeFlightState → ParameterWord n → TimeFlightState
  | 0,p,_ => p
  | n+1,p,a => parameterWordState n (markedParameterState p a.1) a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exact mean displacement of each finite collision history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def historyMean (n : ℕ) (p : TimeFlightState) : V :=
  ∫ z, z.1-p.2.1 ∂historyKernel n p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Translation of the exact second displacement moment -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def historySecondMoment (n : ℕ) (p : TimeFlightState) : ℝ :=
  ∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceGrowthBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Displacement geometry for the three intervals of a branching block -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def blockTarget (x : V) (A κ d : ℝ) : Set FlightState :=
  {w | ‖w.1-(x+(κ*A) • firstAxis)‖ < 3*d*κ*A/4 ∧ ‖(w.2 : V)‖ < 2}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The probability of a flight, a transverse refresh, and a straight final segment -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def terminalBlock (rate : ℝ≥0) (τ : ℝ) : Kernel FlightState FlightState :=
  freeFlightKernel τ ∘ₖ flightKernel rate 1

def driftBlock (rate T : ℝ≥0) (τ : ℝ) : Kernel FlightState FlightState :=
  terminalBlock rate τ ∘ₖ flightKernel rate T

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference collision kernel at a larger constant damping -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def branchingAt (C : ℝ≥0) : Kernel RetainedState RetainedState :=
  branchingKernel + Kernel.id.withDensity (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))

instance branchingAt_sFinite (C : ℝ≥0) : IsSFiniteKernel (branchingAt C) := by
  have : IsSFiniteKernel (Kernel.id.withDensity
      (fun (_ : RetainedState) (_ : RetainedState) => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold branchingAt
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Strict endpoint margins survive finite-path perturbations -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalBlockTarget (x : V) (A κ d : ℝ) : Set (V × V) :=
  {w | ‖w.1-(x+(κ*A) • firstAxis)‖ < d*κ*A ∧ ‖w.2‖ < 5}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PerturbedFiniteBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive marked histories in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def embedFlightState (p : TimeFlightState) : PhysicalFlightState := (p.1,(p.2.1,p.2.2.1))

def mediumPoint (endTime : ℝ) (p : PhysicalFlightState) (s : ℝ) : ℝ × V :=
  (endTime-p.1+s,p.2.1+s • p.2.2)

def mediumParameterState (b : BeamCoefficients) (endTime : ℝ) (p : PhysicalFlightState)
    (a : MarkedEventParameter) : PhysicalFlightState :=
  let x := mediumPoint endTime p a.2.1
  (p.1-a.2.1,(x.2,markedChild a.1 p.2.2 (b.plusPartner x) (b.minusPartner x) a.2.2.1))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite parameter words in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumWordState (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → PhysicalFlightState
  | 0,p,_ => p
  | n+1,p,a => mediumWordState b endTime n (mediumParameterState b endTime p a.1) a.2

def GoodReferenceWord : (n : ℕ) → TimeFlightState → ParameterWord n → Prop
  | 0,_,_ => True
  | n+1,p,a => a.1.2.1 ∈ Ioc 0 p.1 ∧
      markedChild a.1.1 p.2.2.1 beamAxis (-beamAxis) a.1.2.2.1 ∈ referenceRegion ∧
      GoodReferenceWord n (markedParameterState p a.1) a.2

def WordNearby (b : BeamCoefficients) (endTime ε : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → Prop
  | 0,_,_ => True
  | n+1,p,a =>
      ‖b.plusPartner (mediumPoint endTime p a.1.2.1)-beamAxis‖ ≤ ε ∧
      ‖b.minusPartner (mediumPoint endTime p a.1.2.1)-(-beamAxis)‖ ≤ ε ∧
      |b.plusDensity (mediumPoint endTime p a.1.2.1)-1| ≤ ε ∧
      |b.minusDensity (mediumPoint endTime p a.1.2.1)-1| ≤ ε ∧
      WordNearby b endTime ε n (mediumParameterState b endTime p a.1) a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local coefficient control suffices along every retained finite word -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def BeamNear (b : BeamCoefficients) (ε : ℝ) (p : ℝ × V) : Prop :=
  ‖b.plusPartner p-beamAxis‖ ≤ ε ∧ ‖b.minusPartner p-(-beamAxis)‖ ≤ ε ∧
    |b.plusDensity p-1| ≤ ε ∧ |b.minusDensity p-1| ≤ ε

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint margins for the same finite marked parameters in the nearby medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def finishMediumFlight (p : PhysicalFlightState) : V × V :=
  (p.2.1+p.1 • p.2.2,p.2.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricPositiveCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual active cold measure equals the normalized two-beam measure -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamMeasure (b : BeamCoefficients) (p : ℝ × V) : Measure V :=
  ENNReal.ofReal (b.plusDensity p) • Measure.dirac (b.plusPartner p)+
    ENNReal.ofReal (b.minusDensity p) • Measure.dirac (b.minusPartner p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MediumStateCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive marked collision kernel of a measurable two-beam medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev MediumState := (ℝ × V) × V

def markedChildKernel (b : BeamCoefficients) (m : HistoryMark) : Kernel MediumState V :=
  if m = 0 then Kernel.deterministic Prod.snd measurable_snd
  else outgoing.comap (fun z => (z.2,if m = 1 then b.plusPartner z.1 else b.minusPartner z.1))
    (measurable_snd.prodMk (by
      split
      · exact b.plusPartner_measurable.comp measurable_fst
      · exact b.minusPartner_measurable.comp measurable_fst))

instance markedChildKernel_isMarkov (b : BeamCoefficients) (m : HistoryMark) :
    IsMarkovKernel (markedChildKernel b m) := by
  unfold markedChildKernel
  split <;> infer_instance

def mediumMarkedRate (b : BeamCoefficients) (m : HistoryMark) (z : MediumState) : ℝ≥0∞ :=
  ENNReal.ofReal (markedRate m z.2 (b.plusPartner z.1) (b.minusPartner z.1)
    (b.plusDensity z.1) (b.minusDensity z.1))

def mediumMarkedKernel (b : BeamCoefficients) (m : HistoryMark) : Kernel MediumState V :=
  Kernel.withDensity (markedChildKernel b m) (fun z _ => mediumMarkedRate b m z)

instance mediumMarkedKernel_isSFinite (b : BeamCoefficients) (m : HistoryMark) :
    IsSFiniteKernel (mediumMarkedKernel b m) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro z v
  exact ENNReal.ofReal_ne_top

def mediumCollisionKernel (b : BeamCoefficients) : Kernel MediumState V :=
  mediumMarkedKernel b 0+mediumMarkedKernel b 1+mediumMarkedKernel b 2

instance mediumCollisionKernel_isSFinite (b : BeamCoefficients) :
    IsSFiniteKernel (mediumCollisionKernel b) := by
  unfold mediumCollisionKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEntropyProduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regularized entropy estimate in physical time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def cutoffPhysicalSource (b : ℝ) (F : Evolution) (z : ℝ × Phase) : ℝ :=
  CutoffLipschitz.collision b (fun v => F z.1 (z.2.1,v)) z.2.2

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedCollisionBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The event kernel with all intermediate velocities in the physical box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumVelocityBox : Set PhysicalFlightState := {q | ‖q.2.2‖ ≤ 6}

theorem mediumVelocityBox_measurable : MeasurableSet mediumVelocityBox := by
  unfold mediumVelocityBox
  exact measurableSet_le (by fun_prop) measurable_const

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The regularized entropy balance for a bounded mild cutoff solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def regularizedRelativeEntropyDensity (δ : ℝ) (f : Density) (p : Phase) : ℝ :=
  scalarRelativeEntropy (maxwellian p.2) (f p+δ*Real.exp (-2*‖p.2‖^2))

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedCollisionHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Marked reference and medium weights with an additional holding intensity -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def holdingWeight (C : ℝ≥0) (m : HistoryMark) : ℝ≥0∞ :=
  if m = 0 then ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) else 0

def dampedReferenceWeight (C : ℝ≥0) (v : RetainedState) (m : HistoryMark) (n : Sphere) : ℝ≥0∞ :=
  markedReferenceWeight v m n+holdingWeight C m

def dampedParameterDensity (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter) : ℝ≥0∞ :=
  waitingDensity p a.2.1*clockSurvival C a.2.1*dampedReferenceWeight C p.2.2 a.1 a.2.2

def dampedMediumParameterDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (a : MarkedEventParameter) : ℝ≥0∞ :=
  let x := mediumPoint endTime p a.2.1
  (Ioc 0 p.1).indicator 1 a.2.1*clockSurvival C a.2.1*
    (ENNReal.ofReal (markedRate a.1 p.2.2 (b.plusPartner x) (b.minusPartner x)
      (b.plusDensity x) (b.minusDensity x))+holdingWeight C a.1)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite positive weights at a common enlarged damping rate -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedWordDensity (C : ℝ≥0) : (n : ℕ) → TimeFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => dampedParameterDensity C p a.1 *
      dampedWordDensity C n (markedParameterState p a.1) a.2

def dampedMediumWordDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => dampedMediumParameterDensity C b endTime p a.1 *
      dampedMediumWordDensity C b endTime n (mediumParameterState b endTime p a.1) a.2

def DampedWordCoefficientClose (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞) :
    (n : ℕ) → TimeFlightState → PhysicalFlightState → ParameterWord n → Prop
  | 0,_,_,_ => True
  | n+1,p,q,a =>
      dampedParameterDensity C p a.1 ≤ M ∧ dampedMediumParameterDensity C b endTime q a.1 ≤ M ∧
      dampedParameterDensity C p a.1 ≤ dampedMediumParameterDensity C b endTime q a.1+η ∧
      DampedWordCoefficientClose C b endTime M η n (markedParameterState p a.1)
        (mediumParameterState b endTime q a.1) a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical two-beam collision law with the additional holding mark -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumCollision (C : ℝ≥0) (b : BeamCoefficients) : Kernel MediumState V :=
  mediumCollisionKernel b+(Kernel.deterministic Prod.snd measurable_snd).withDensity
    (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))

instance dampedMediumCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) :
    IsSFiniteKernel (dampedMediumCollision C b) := by
  have : IsSFiniteKernel ((show Kernel MediumState V from Kernel.deterministic (fun z : MediumState => z.2) measurable_snd).withDensity
      (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z v
    exact ENNReal.ofReal_ne_top
  unfold dampedMediumCollision
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def dampedMediumStateCollision (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.id ×ₖ (dampedMediumCollision C b).comap
    (fun p => ((endTime-p.1,p.2.1),p.2.2)) (by fun_prop)).map
      (fun q => (q.1.1,(q.1.2.1,q.2)))

instance dampedMediumStateCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedMediumStateCollision C b endTime) := by
  unfold dampedMediumStateCollision
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed mark, time and angle integrals at the larger damping rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedReferenceParameterDensity (C : ℝ≥0) (p : TimeFlightState)
    (m : HistoryMark) (a : EventParameter) : ℝ≥0∞ := dampedParameterDensity C p (m,a)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer at the same enlarged reference and physical damping -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumBlockIntegrand (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  dampedMediumWordDensity C b endTime n (embedFlightState p) a *
    (clockSurvival C q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The damped one-event kernel for finite marked histories in a measurable medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumEventDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (_ : PhysicalFlightState) (p : PhysicalFlightState × MarkedEventParameter) : ℝ≥0∞ :=
  dampedMediumParameterDensity C b endTime p.1 p.2

def dampedMediumEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
    (dampedMediumEventDensity C b endTime)).map (fun p => mediumParameterState b endTime p.1 p.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite medium words whose collision velocities stay in the physical box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedWordDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a =>
      let q := mediumParameterState b endTime p a.1
      dampedMediumParameterDensity C b endTime p a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1 q *
          dampedBoundedWordDensity C b endTime n q a.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Integrability along the actual damped transport lines in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def lineShear (w : FourierSpace) (p : ℝ × FourierSpace) : ℝ × FourierSpace :=
  (p.1,p.2-p.1 • w)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Passing the Fourier integral through damped transport along a line -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] dampedLineResolvent

def fourierLineKernel (f : FourierSpace → ℂ) (w k : FourierSpace) (p : ℝ × FourierSpace) : ℂ :=
  𝐞 (-inner ℝ p.2 k) • (Real.exp (-p.1) • f (p.2-p.1 • w))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Finite medium histories equal powers of the actual marked event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumFlightSeed (C : ℝ≥0) (f : V × V → ℝ≥0∞) (p : PhysicalFlightState) : ℝ≥0∞ :=
  clockSurvival C p.1*f (finishMediumFlight p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The event kernel with all intermediate velocities in the physical box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumEventKernel C b endTime T).restrict mediumVelocityBox_measurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer of reference blocks with every velocity kept bounded -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedBlockIntegrand (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  dampedBoundedWordDensity C b endTime n (embedFlightState p) a *
    (clockSurvival C q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

def dampedBoundedBlockMass (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N,
    ∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseDecompositionNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Global norm continuity for the clamped local construction -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem time_idempotent {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    PositiveIntegral.time T (PositiveIntegral.time T t) = PositiveIntegral.time T t :=
  GaussianLocal.time_eq (PositiveIntegral.time_bounds hT t)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralPasting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Restricting and translating the damped mild integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_eq_at_time {T U t : ℝ} (ht : t ∈ Icc 0 T) (hu : t ≤ U)
    (L : ℝ) (f₀ : JetPrototype.Phase → ℝ) {g h : ℝ × JetPrototype.Phase → ℝ}
    (hgh : ∀ r ∈ Icc 0 t, ∀ p, g (r,p) = h (r,p)) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,p) = value U L JetBarrier.flight f₀ h (t,p) := by
  unfold value
  rw [GaussianLocal.time_eq ht,GaussianLocal.time_eq ⟨ht.1,hu⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  dsimp only
  rw [hgh r hr]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual positive H-weighted local cutoff solutions

Only the published Carleman input is used to remove the fixed negligible
set of output velocities. Local existence itself is constructed in Lean.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedLocal

def physical (q : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  H q z.2.2 * f z

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The collision source only depends on its current time slice -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

def timeSlice (F : ℝ × JetPrototype.Phase → ℝ) (s : ℝ) : ℝ × JetPrototype.Phase → ℝ :=
  fun u => F (s,u.2)

def paste (s : ℝ) (F G : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  if u.1 ≤ s then F u else G (u.1-s,u.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedNetLoss
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Almost-everywhere invariance of the colored forcing along spacetime -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

abbrev spacetimeVolume : Measure (ℝ × JetPrototype.Phase) :=
  (volume : Measure ℝ).prod FlightMeasure.phaseVolume

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Measurability and representative invariance of the physical loss frequency -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

def lossFrequency (q b : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.frequency q b (GaussianLocal.state F) ((u.1,u.2.1),u.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdFiniteLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The clipping is inactive almost everywhere for a mild total solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

def ColdMildAE (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) (c : ℝ × JetPrototype.Phase → ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (fun p => c (t,p)) =ᵐ[FlightMeasure.phaseVolume]
    (fun p => PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (t,p))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpaceTimeEssSup
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Essential uniform size for bounded spacetime representatives -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.SpaceTimeEssSup

def size (f : ℝ × JetPrototype.Phase → ℝ) : ℝ :=
  (eLpNorm f ∞ WeightedLocal.spacetimeVolume).toReal

end BoltzmannNonuniqueness.SpaceTimeEssSup

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restarting an a.e. mild equation on a bounded time window -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

def window (s U : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  f (s+time U u.1,u.2)

end BoltzmannNonuniqueness.PositiveIntegral

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClampedMildAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a mild representative constantly beyond its time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

def clampTime (T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  F (PositiveIntegral.time T u.1,u.2)

theorem measurable_clampTime {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (T : ℝ) :
    Measurable (clampTime T F) := by
  apply hFm.comp
  unfold PositiveIntegral.time
  fun_prop

theorem forcing_clampTime (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) :
    forcing q b L (clampTime T F) u = forcing q b L F (PositiveIntegral.time T u.1,u.2) := rfl

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetStability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common positive local time for bounded weighted data -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocalControl

def sourceBound (q b A : ℝ) : ℝ := HotApplication.realBound q*(2*A)^2+damping q b A*(2*A)

def lipschitz (q b A : ℝ) : ℝ :=
  2*(2*A)*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+damping q b A

def lifespan (q b A : ℝ) : ℝ := min (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1))

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Restricting a mild solution to a shorter time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem MildAE.restrict_clamp {q b L T S : ℝ} (_hS : 0 ≤ S) (hST : S ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : MildAE q b L T f₀ F) : MildAE q b L S f₀ (clampTime S F) := by
  intro t ht
  filter_upwards [hF t ⟨ht.1,ht.2.trans hST⟩] with p hp
  change F (PositiveIntegral.time S t,p) = _
  rw [GaussianLocal.time_eq ht,hp]
  apply PositiveIntegral.value_eq_at_time ⟨ht.1,ht.2.trans hST⟩ ht.2
  intro r hr p
  rw [forcing_clampTime,GaussianLocal.time_eq ⟨hr.1,hr.2.trans ht.2⟩]

theorem clampTime_idempotent {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    clampTime T F (PositiveIntegral.time T u.1,u.2) = clampTime T F u := by
  change F (PositiveIntegral.time T (PositiveIntegral.time T u.1),u.2) = _
  rw [PhaseEssSup.time_idempotent hT]
  rfl

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform positive local interval from an essentially bounded time slice -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

def clippedSlice (A : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (s : ℝ)
    (p : JetPrototype.Phase) : ℝ := min (F (s,p)) A

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMildApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive periodic mild states and finite-step continuation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

namespace PeriodicMildState

def restrict {q b L T R S : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hS : 0 ≤ S) (hST : S ≤ T) :
    PeriodicMildState q b L S R f₀ where
  value := clampTime S F.value
  measurable_value := measurable_clampTime F.measurable_value S
  value_bounds u := F.value_bounds _
  mild := F.mild.restrict_clamp hS hST
  clamped := clampTime_idempotent hS F.value
  periodic n := by
    funext u
    exact congrFun (F.periodic n) (PositiveIntegral.time S u.1,u.2)

def initial {q b L A : ℝ} (hA : 0 ≤ A) {f₀ : JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (hper : ∀ n p, f₀ (shift (JetCopyDatum.displacement n) p) = f₀ p) :
    PeriodicMildState q b L 0 (2*A) f₀ where
  value u := f₀ u.2
  measurable_value := hf₀m.comp measurable_snd
  value_bounds u := ⟨(hf₀ u.2).1,(hf₀ u.2).2.trans (by linarith)⟩
  mild := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    apply ae_of_all
    intro p
    simp [PositiveIntegral.value,PositiveIntegral.time,JetBarrier.flight]
  clamped _ := rfl
  periodic n := funext (fun u => hper n u.2)

end PeriodicMildState

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Closedness of the cap under convergence of bounded seed parameters -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

def affineSeed (f ψ : JetPrototype.Phase → ℝ) (ell : ℝ) (p : JetPrototype.Phase) : ℝ :=
  f p+ell*ψ p

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Uniform compact-velocity logarithmic bounds for positive regularization -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def logRegularizationConstant (N B : ℝ) : ℝ :=
  |Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1)|

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicFiniteMild
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The common pre/post multiplier in the conservative approximation -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def rateMultiplier {X : Type*} (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  attenuation N (rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrability of the bounded collision rates without a quadratic moment assumption -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def pairBall (N : ℝ) : Set (Velocity × Velocity) :=
  Metric.closedBall 0 N ×ˢ Metric.closedBall 0 N

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The bounded collision operator is stable under positive Gaussian shifts -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def gaussianShift (δ : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p+δ*maxwellian p.2

def collisionOperator (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p-loss N f p

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Vanishing Gaussian error in the actual approximate entropy production -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def entropyErrorCoefficient (μ : Measure X) (N : ℝ) : ℝ :=
  μ.real univ*(volume : Measure Velocity).real (Metric.closedBall 0 N)*
    (2*rateLipschitz N*maxwellian 0)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing entropy regularization from supported bounded densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def entropyCompactMajorant (N C : ℝ) (v : Velocity) : ℝ :=
  (Metric.closedBall (0:Velocity) N).indicator (fun _ => C) v+maxwellian v

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicInitialEntropyLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual bounded initial approximations for the global construction -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_measurable (N : ℝ) {f : Density} (hf : Measurable f) :
    Measurable (initialApproximation N f) := by
  unfold initialApproximation
  exact Measurable.ite (measurableSet_le measurable_snd.norm measurable_const)
    (measurable_const.min (measurable_const.max hf)) measurable_const

theorem initialApproximation_bounds {N : ℝ} (hN : 0 ≤ N) (f : Density) (p : Phase) :
    0 ≤ initialApproximation N f p ∧ initialApproximation N f p ≤ N := by
  unfold initialApproximation
  split_ifs
  · exact ⟨le_min hN (le_max_left _ _),min_le_left _ _⟩
  · exact ⟨le_rfl,hN⟩

theorem initialApproximation_support (N : ℝ) (f : Density) (p : Phase) (hp : N < ‖p.2‖) :
    initialApproximation N f p = 0 := by
  simp only [initialApproximation,ite_eq_right_iff]
  intro h
  exact False.elim ((not_le_of_gt hp) h)

theorem exists_initial_approximation_solution {N T : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f : Density} (hf : Measurable f) :
    Nonempty (BoundedCutoffSolution N T (initialApproximation N f)) :=
  exists_supported_cutoff_solution hN hT (initialApproximation_measurable N hf)
    (initialApproximation_bounds hN.le f) (initialApproximation_support N f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Measurable spacetime form of the bounded positive collision source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def kineticSource (N : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  positiveSource N (fun p : (ℝ × Position) × Velocity => F (p.1.1,(p.1.2,p.2)))
    ((z.1,z.2.1),z.2.2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Retaining the nonnegative dissipation in the approximate entropy identity -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def positiveProduction (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (1/4:ℝ)*collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
    (regularizedPostRate N f z-regularizedPreRate N f z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The extended dissipation of the actual symmetric regularization -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def extendedProduction (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (windowKernel N z*rateMultiplier N f z)*extendedEntropyProduction
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))

def extendedDissipation (μ : Measure X) (N : ℝ) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedProduction N f z
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual regularized collision rates have a vanishing entropy tail -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def normalizedRateExcess (N R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPostRate N f z/(1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)-
    R*(regularizedPreRate N f z/(1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrability of both normalized regularized rates before angular averaging -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def normalizer (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := 1+f p/maxwellian p.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy control of the actual angularly averaged normalized gain tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r432bee_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def normalizedGainExcess (N R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p/normalizer f p-R*(loss N f p/normalizer f p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotWindowInput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published weak compactness input on local blow-up windows

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Trans. AMS 47 (1940), Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.

Sequential weak compactness applies on bounded time and spatial windows
in the nonperiodic dilation coordinates. Uniform integrability includes the common
L¹ bound, and uniform tightness controls the unbounded velocity variable.
The input does not assert compatibility of the local limits, a transport
equation, velocity averaging, or any nonlinear limit identification.
-/

noncomputable section

namespace BoltzmannNonuniqueness.Published

def DunfordPettis1940HotWindows : Prop :=
  ∀ A R : ℝ, 0 ≤ A → 0 ≤ R →
    L1WeakCompactnessInput (JetCopyDatum.AttainedCapSequence.hotWindowVolume A R)

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TruncatedExponential
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Recovering the half-Gaussian moment from bounded velocity weights -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

def truncatedWeight (n : ℕ) (v : Velocity) : ℝ := min (weight v) (n : ℝ)

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RegularChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular chart volume and transverse inverse-distance averaging -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain

namespace BoltzmannNonuniqueness.RegularChart

def ballMass (v p : Velocity) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, ∫⁻ s : ℝ, if ‖chart v p z s - v‖ ≤ R then 1 else 0

end BoltzmannNonuniqueness.RegularChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite time measures obtained by testing characteristic phase -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeakTime

def timeSource (μ : Measure (ℝ × Phase)) (φ : Phase → ℝ) : Measure ℝ :=
  (positiveDensityMeasure μ (fun z => φ z.2)).map Prod.fst

def phaseProjection (F : ℝ × Phase → ℝ) (φ : Phase → ℝ) (t : ℝ) : ℝ :=
  ∫ p, φ p*F (t,p)

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Integrating a local term pasted to a time-translated global term -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def timePaste (T : ℝ) (a b : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  if z.1 ≤ T then a z else b (z.1-T,z.2)

end BoltzmannNonuniqueness

end

end

section

/-! # Restricting local L¹ convergence to the physical time interval -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

def timeSpaceVolume (T : ℝ) : Measure SpaceTime :=
  (volume.restrict (Icc 0 T)).prod volume

def TimeLocalL1Converges (T : ℝ) (f : ℕ → SpaceTime → ℝ) (g : SpaceTime → ℝ) : Prop :=
  LocallyIntegrable g ∧ ∀ K : Set SpaceTime, IsCompact K →
    Tendsto (fun n => eLpNorm (fun z => f n z-g z) 1 ((timeSpaceVolume T).restrict K)) atTop (𝓝 0)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseSourceMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characteristic phase measures and their time-slab increments -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def phaseSlice (F : ℝ × Phase → ℝ) (t : ℝ) : Measure Phase :=
  positiveDensityMeasure volume (fun p => F (t,p))

def phaseIncrement (μ : Measure (ℝ × Phase)) (s t : ℝ) : Measure Phase :=
  (μ.restrict (Prod.fst ⁻¹' Ioc s t)).map Prod.snd

instance phaseIncrement_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ] (s t : ℝ) :
    IsFiniteMeasure (phaseIncrement μ s t) := by unfold phaseIncrement; infer_instance

end BoltzmannNonuniqueness.WeakTime

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RationalUniformApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform entropy-controlled approximation by rational renormalizations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def rationalApproximation (k : ℝ) (hk : 1 ≤ k) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  maxwellian p.2*(Renormalization.rational k hk).toFun (f p/maxwellian p.2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMomentEntropy
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # One entropy and moment budget for all finite regularized approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialEntropyBudget (f : Density) : ℝ :=
  initialEntropyCoefficient*(∫ p, entropyMoment f p)+(∫ p : Phase, maxwellian p.2)

def approximationEntropyBudget (f : Density) : ℝ :=
  (1+4*entropyMomentCoefficient)*initialEntropyBudget f+
    4*entropyMomentCoefficient*(∫ p : Phase, entropyGaussian p.2)+(∫ p : Phase, maxwellian p.2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual cutoff solution sequence with growing horizons and uniform entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def approximatingSolution (f : Density) (hfm : Measurable f) (n : ℕ) :
    BoundedCutoffSolution ((n:ℝ)+1) ((n:ℝ)+1) (initialApproximation ((n:ℝ)+1) f) :=
  Classical.choice (exists_initial_approximation_solution (by positivity) (by positivity) hfm)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeRelativeEntropy
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrating a uniform entropy budget over a bounded time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def spacetimeEntropy (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  F z*(1+‖z.2.2‖^2+|Real.log (F z)|)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Relative entropy and the absolute entropy moment in spacetime -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def spacetimeRelativeEntropy (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  scalarRelativeEntropy (maxwellian z.2.2) (F z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RelativeEntropyMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonnegative entropy marginal and its finite-entropy interpretation -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

def entropyMarginal (F : ℝ × Phase → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (F (t,p)))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongCompactPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong stability of positive survival factors from L1 convergence of the rates -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

def timeSurvival (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  Real.exp (-timePrimitive μ f z)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong convergence of physical survival kernels with two time endpoints -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

def twoTimeSurvival (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) : ℝ :=
  Real.exp (-max 0 (timeDifference (timePrimitive μ f) z))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveVolterra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite logarithmic bound for repeated positive gains

The bound omits the factorial improvement: for a fixed number of gains this
polynomial bound suffices for the small-lower-time remainder in §8.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def iterate (a : ℝ) (K : Kernel KineticPhase Velocity)
    (f : KineticPhase → ℝ≥0∞) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => step a K (iterate a K f n)

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Restricting an input to the time slab preserves its backward Volterra values -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def onSlab (a T : ℝ) (f : KineticPhase → ℝ≥0∞) (z : KineticPhase) : ℝ≥0∞ :=
  {z : KineticPhase | z.1.1 ∈ Icc a T}.indicator f z

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPositiveRegion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Published weak compactness on the required two-velocity windows

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Trans. AMS 47 (1940), Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.

This is the same sequential weak compactness consequence as `HotWindowInput`,
specialized to the two-velocity measure needed for the hot pair product.
Uniform integrability includes the common L¹ bound. Uniform tightness controls
the velocity tails. No product factorization or nonlinear identification is
part of this published input.
-/

noncomputable section

namespace BoltzmannNonuniqueness.Published

def DunfordPettis1940HotPairWindows : Prop :=
  ∀ A R : ℝ, 0 ≤ A → 0 ≤ R →
    L1WeakCompactnessInput (JetCopyDatum.AttainedCapSequence.hotPairWindowVolume A R)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SlopedChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chart estimates using a nonzero axial slope -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.AffineSlices

namespace BoltzmannNonuniqueness.SlopedChart

def rectangleFiber (q : ℝ) (v p : Velocity) (C D m S : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ,
    if |offset v p - slope v p * z - C| ≤ D then
      ∫⁻ s in Icc (m - S) (m + S), weightRatio q v (chart v p z s)
    else 0

def smallFiber (q : ℝ) (v p : Velocity) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ,
    if ‖transverse (chart v p z s)‖ < δ then weightRatio q v (chart v p z s) else 0

end BoltzmannNonuniqueness.SlopedChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WidthTails
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing transverse tails as the sheet width tends to zero -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetTails
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.WidthTails

def incomingTail (U : ℝ) : Set Velocity := {p | U < ‖transverse p‖}

end BoltzmannNonuniqueness.WidthTails

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmallFirstGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform small-input bound for small transverse incoming velocities -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SlopedChart
open BoltzmannNonuniqueness.AffineSlices

namespace BoltzmannNonuniqueness.SmallInputGeometry

def fiber (q : ℝ) (v p : Velocity) (R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ,
    if ‖chart v p z s - v‖ ≤ R ∧ ‖transverse (chart v p z s)‖ < δ then
      weightRatio q v (chart v p z s) else 0

end BoltzmannNonuniqueness.SmallInputGeometry

end

end

section

/-! # Uniform small-input estimates off the axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SmallInput

def region (v : Velocity) (R δ : ℝ) : Set Coordinates :=
  ballRegion v R ∩ {y | ‖transverse (chart v y.1 y.2.1 y.2.2)‖ < δ}

def lowIncoming (r : ℝ) : Set Velocity := {p | ‖transverse p‖ ≤ r / 4}

def lowRegion (v : Velocity) (r R δ : ℝ) : Set Coordinates :=
  region v R δ ∩ (lowIncoming r ×ˢ univ)

def highRegion (v : Velocity) (R U : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (WidthTails.incomingTail U ×ˢ univ)

end BoltzmannNonuniqueness.SmallInput

end

end

section

/-! # Vanishing input mass near the axis for thin sheets -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SmallInput

namespace BoltzmannNonuniqueness.SmallInputLimit

def lowBound (q L r R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * (ENNReal.ofReal (4 * L) *
    (2 * ENNReal.ofReal (AffineSlices.rectangleConstant q δ δ /
      SmallInputGeometry.threshold r R)))

def highBound (q L R U d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * (ENNReal.ofReal ((8 * d ^ 2 / U ^ 2) * L) * ballBound q R)

def smallRegion (v : Velocity) (δ : ℝ) : Set Coordinates :=
  {y | ‖transverse (chart v y.1 y.2.1 y.2.2)‖ < δ}

end BoltzmannNonuniqueness.SmallInputLimit

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LateBoxAccessMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The fourth-power mass cap in the expanding branching boxes -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def lateBoxCapConstant (q κ d : ℝ) : ℝ :=
  (Real.pi*4/3)*(d*κ)^3*(∫ v : V, H q v)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive mass with the entry velocities eventually reaches the growing box -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def entryVelocityRegion (κ d : ℝ) : Set (V × V) :=
  {p | ‖p.2-κ • firstAxis‖ < d*κ/4 ∧ ‖p.2‖ < 5}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusCharacteristic
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Transfer of the actual cap sequence to the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.TorusKineticChart

def cellVolume (T : ℝ) : Measure Published.KineticPhase :=
  ((volume.restrict (Icc 0 T)).prod (volume.restrict TorusChart.cube)).prod volume

def chart (z : (ℝ × Position) × Velocity) : Published.KineticPhase :=
  ((z.1.1,TorusChart.representative z.1.2),z.2)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Actual pair-product compactness in the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

def pairCellVolume (T : ℝ) : Measure (Published.SpaceTime × (Velocity × Velocity)) :=
  ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict TorusChart.cube)).prod volume

def pairChart (z : (ℝ × Position) × (Velocity × Velocity)) :
    Published.SpaceTime × (Velocity × Velocity) :=
  ((z.1.1,TorusChart.representative z.1.2),z.2)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Euclidean representatives of the actual torus weak limits -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

def liftDensity (g : (ℝ × Position) × Velocity → ℝ) (z : Published.KineticPhase) : ℝ :=
  g ((z.1.1,torusProjection z.1.2),z.2)

def liftPair (W : (ℝ × Position) × (Velocity × Velocity) → ℝ)
    (z : Published.SpaceTime × (Velocity × Velocity)) : ℝ :=
  W ((z.1.1,torusProjection z.1.2),z.2)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # The constructed approximations satisfy the characteristic equation on the torus -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TorusFlight

def initialDensity (q : ℝ) (f₀ : JetPrototype.Phase → ℝ) (p : Phase) : ℝ :=
  H q p.2*f₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative p))

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CellLocalizedSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite spacetime measure of the fundamental cell -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusKineticChart

def baseVolume (T : ℝ) : Measure Published.SpaceTime :=
  (volume.restrict (Icc 0 T)).prod (volume.restrict TorusChart.cube)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Uniform integrability of actual localized Euclidean transport sources -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.TorusKineticChart

def region (U : ℝ) : Set KineticPhase := (Icc 0 U ×ˢ TorusChart.cube) ×ˢ univ

end BoltzmannNonuniqueness.TorusKineticChart

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WindowLocalizedSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Localization of uniformly integrable sources on positive-time Euclidean windows -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def kineticWindow (a A R : ℝ) : Set KineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : Velocity) R) ×ˢ univ

def kineticWindowVolume (a A R : ℝ) : Measure KineticPhase :=
  ((volume.restrict (Icc a A)).prod (volume.restrict (Metric.closedBall (0 : Velocity) R))).prod volume

end BoltzmannNonuniqueness.TransportCutoff

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ComplexWeakL2Diagonal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Restricting the complex L2 norm to a physical window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def complexL2Restriction (K : Set FourierSpace) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Lp ℂ 2 (volume.restrict K) :=
  ((Lp.memLp a).restrict K).toLp a

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_InteriorCell
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact smooth spacetime cutoffs covering almost all of the physical cell -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.TorusKineticChart

def interiorRegion : Set Published.SpaceTime := Ioi (0 : ℝ) ×ˢ interior TorusChart.cube

end BoltzmannNonuniqueness.TorusKineticChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityAverageDifference
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint integrability for damped velocity-dependent characteristic lines -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def velocityLineShear (s : ℝ) (p : Velocity × FourierSpace) : Velocity × FourierSpace :=
  (p.1,p.2-s • characteristicDirection p.1)

theorem velocityLineShear_measurePreserving (s : ℝ) :
    MeasurePreserving (velocityLineShear s) (volume : Measure (Velocity × FourierSpace)) volume := by
  unfold velocityLineShear
  apply (MeasurePreserving.id (volume : Measure Velocity)).skew_product
    (g := fun v x => x-s • characteristicDirection v)
    (μc := (volume : Measure FourierSpace)) (μd := (volume : Measure FourierSpace))
  · unfold characteristicDirection
    fun_prop
  · exact ae_of_all _ (fun v => (measurePreserving_add_right volume
      (-(s • characteristicDirection v))).map_eq)

def velocityTimeShear (p : ℝ × (Velocity × FourierSpace)) : ℝ × (Velocity × FourierSpace) :=
  (p.1,velocityLineShear p.1 p.2)

theorem velocityTimeShear_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving velocityTimeShear (μ.prod (volume : Measure (Velocity × FourierSpace)))
      (μ.prod volume) := by
  unfold velocityTimeShear
  apply (MeasurePreserving.id μ).skew_product
    (g := velocityLineShear)
    (μc := (volume : Measure (Velocity × FourierSpace)))
    (μd := (volume : Measure (Velocity × FourierSpace)))
  · unfold velocityLineShear characteristicDirection
    fun_prop
  · exact ae_of_all _ (fun s => (velocityLineShear_measurePreserving s).map_eq)

theorem velocityLine_integrable {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    Integrable (fun p : ℝ × (Velocity × FourierSpace) =>
      Real.exp (-p.1) • r (velocityLineShear p.1 p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  exact (velocityTimeShear_measurePreserving _).integrable_comp_of_integrable
    ((integrableOn_exp_neg_Ioi 0).smul_prod hr)

theorem velocityLineResolvent_integrable {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) : Integrable (velocityLineResolvent r) :=
  (velocityLine_integrable hr).integral_prod_right

theorem velocityLineAverage_integrable {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) : Integrable (velocityLineAverage r) :=
  (velocityLineResolvent_integrable hr).integral_prod_right

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticWindowL1
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure-preserving coordinates for the partial Fourier argument -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

def kineticFourierEquiv : KineticPhase ≃ᵐ Velocity × FourierSpace :=
  MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl Velocity).prodCongr spacetimeHilbertEquiv)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The Fourier-coordinate average is the original physical resolvent average -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def fourierSource (r : KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (p : Velocity × FourierSpace) : ℂ := (ψ p.1*r (p.2.ofLp,p.1) : ℝ)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_FourierCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Finite-measure cutoffs of L2 Fourier data -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace BoltzmannNonuniqueness.Published

def complexL2Cutoff (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : Lp ℂ 2 (volume : Measure FourierSpace) :=
  ((Lp.memLp a).indicator hS).toLp (S.indicator a)

def fourierBandApprox (S : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : FourierSpace → ℂ :=
  𝓕⁻ (S.indicator a)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A finite Fourier window evaluates by an L2 pairing -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def fourierBandTest (S : Set FourierSpace) (x : FourierSpace) : FourierSpace → ℂ :=
  S.indicator (fun k => (𝐞 (-inner ℝ k x) : ℂ))

theorem fourierBandTest_memLp (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (x : FourierSpace) : MemLp (fourierBandTest S x) 2 volume := by
  have hb : MemLp (S.indicator (fun _ : FourierSpace => (1 : ℂ))) 2 volume :=
    memLp_indicator_const _ hS _ (Or.inr hfinite.ne)
  have hm : Measurable (fourierBandTest S x) := by
    apply Measurable.indicator _ hS
    fun_prop
  apply hb.of_le hm.aestronglyMeasurable
  exact ae_of_all _ (fun k => by
    by_cases hk : k ∈ S <;> simp [fourierBandTest,hk,Circle.norm_coe])

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalFrequencyWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite Fourier windows for the physical spacetime coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def physicalFrequencyWindow (N : ℕ) : Set FourierSpace :=
  {k | ‖physicalFourierFrequency k‖ ≤ N}

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # An L1 density bound on a fixed elastic collision window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_1_r432bee_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def windowPartner (R : ℝ) (q : Velocity × Sphere) : ℝ :=
  (Metric.closedBall (0:Velocity) R).indicator (fun _ => 1) q.1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The same finite collision window contains all four collision legs -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def windowSingleDensity (R : ℝ) (f : X × Velocity → ℝ) :
    ((X × (Velocity × Velocity)) × Sphere) → ℝ :=
  (collisionWindow R).indicator (fun z => f (z.1.1,z.1.2.1))

def windowDensitySum (R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  windowSingleDensity R f z + windowSingleDensity R f (particleSwap z) +
    windowSingleDensity R f (scatterTriple z) +
    windowSingleDensity R f (particleSwap (scatterTriple z))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MassNormalizedCollisionLimits
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual finite collision rates divided by the same spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

def massRegularizedPreRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPreRate N f z/(1+fiberMass volume f z.1.1)

def massRegularizedPostRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPostRate N f z/(1+fiberMass volume f z.1.1)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong mass coefficients on bounded collision windows -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

def collisionMassClip (K : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  massClip K (fiberMass volume f z.1.1)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable local mass tests and cancellation of their collision source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def massTestIntegrand (F : Evolution) (φ : MassTest) (z : ℝ × Phase) : ℝ :=
  F z.1 z.2*φ.transportDerivative z.1 z.2+
    collision (F z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalDissipationBridge
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The regularized entropy-dissipation estimate in time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def regularizedKineticDissipation (T b δ : ℝ) (F : Evolution) : ℝ :=
  ∫ z, CollisionCompactness.positiveCutoffProduction b
    (gaussianRegularizedDensity δ (kineticDensity F)) z
    ∂((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))).prod sphereArea

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteRatesWindowUI
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Regularized entropy inequality for the actual periodic finite approximations -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

namespace WeightedLocalControl.PeriodicMildState

def torusEvolution {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀) : Evolution :=
  fun t p => JetCopyDatum.torusPhysical q F.value ((t,p.1),p.2)

end WeightedLocalControl.PeriodicMildState
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WindowCollisionMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak collision marginals and uniform integrability on a fixed elastic window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def windowCollisionMarginal (R : ℝ) (r : (X × (Velocity × Velocity)) × Sphere → ℝ)
    (p : X × Velocity) : ℝ :=
  ∫ q, (collisionWindow R).indicator r (collisionGrouping.symm (p,q))
    ∂((volume : Measure Velocity).prod sphereArea)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TwoCoreLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Reordering the two positive gain steps into their collision-time integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def pairMass (K : Kernel Published.KineticPhase Velocity) (z : Published.KineticPhase)
    (t₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, K ((t₂,z.1.2-(z.1.1-t₂) • w),w) univ ∂K z

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantParameterSupport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The redundant coordinates recover the actual graph-chart velocity -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.RedundantPlane

def tangentOffset (v p : Velocity) : ℝ :=
  inner ℝ (quarterTurn (direction (normal v p))) (transverse v)

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_MityaginPublished
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published scalar analytic zero-set input

B. S. Mityagin, *The Zero Set of a Real Analytic Function*, Mathematical
Notes 107(3) (2020), 529–530, DOI 10.1134/S0001434620030189.
The author preprint arXiv:1512.07276, Proposition 0, states the corresponding
connected-open-domain zero-set theorem. Here it is specialized to the twenty
real coordinates of the five-gain parameter space, as a conditional
zero-set nullity statement.
-/

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Published

def Mityagin2020FiveGainParameters : Prop :=
  ∀ (U : Set FiveGainMap.Parameters), IsOpen U → IsPreconnected U →
    ∀ f : FiveGainMap.Parameters → ℝ, AnalyticOnNhd ℝ f U →
      (∃ q ∈ U, f q ≠ 0) → volume {q ∈ U | f q = 0} = 0

end BoltzmannNonuniqueness.Published

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteThermalLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Expansion of a finite selected gain into its collision-label tuples -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def chosenGainChain {I : Type*} (a : ℝ) (K : ℕ → I → Kernel KineticPhase Velocity)
    (weight : ℕ → I → KineticPhase → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞) (i : ℕ) :
    (n : ℕ) → (Fin n → I) → KineticPhase → ℝ≥0∞
  | 0, _ => f
  | n+1, labels => step a (K i (labels 0)) (fun z => weight i (labels 0) z *
      chosenGainChain a K weight f (i+1) n (Fin.tail labels) z)

def finiteGainChain {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity)
    (weight : ℕ → I → KineticPhase → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞)
    (i : ℕ) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => fun z => ∑ j : I, step a (K i j) (fun y => weight i j y *
      finiteGainChain a K weight f (i+1) n y) z

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveRestrictedChain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Successive velocity restrictions in a finite positive gain chain

The retained sets may differ at each collision. Deleted mass is estimated only
at endpoints in the preceding retained set, as required for successive
nonaxial thresholds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def restrictedChain (a : ℝ) (K : Kernel KineticPhase Velocity)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (f : KineticPhase → ℝ≥0∞) (i : ℕ) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => step a (K.restrict (hS (i+1))) (restrictedChain a K S hS f (i+1) n)

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EnergyTruncation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded velocity truncations determine the full energy inequality -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

def truncatedEnergyWeight (n : ℕ) (p : Phase) : ℝ := min (‖p.2‖^2) (n:ℝ)

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RestrictedCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded velocity chain stays in its backward spatial cone -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def inSpatialCone (X T V : ℝ) (z : KineticPhase) : Prop :=
  ‖z.1.2‖ ≤ X+(T-z.1.1)*V

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded sources give bounded L2 velocity averages -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem dampedLineResolvent_norm_le {f : FourierSpace → ℂ} {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (w x : FourierSpace) : ‖dampedLineResolvent f w x‖ ≤ B := by
  have h := norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).mul_const B)
    (ae_of_all _ (fun s : ℝ => show ‖Real.exp (-s) • f (x-s • w)‖ ≤ Real.exp (-s)*B by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hf _) (Real.exp_pos _).le))
  simpa only [dampedLineResolvent,integral_mul_const,integral_exp_neg_Ioi_zero,one_mul] using h

theorem velocityLineResolvent_support {r : Velocity × FourierSpace → ℂ} {R : ℝ}
    (hs : ∀ p, R < ‖p.1‖ → r p = 0) (v : Velocity) (x : FourierSpace) (hv : R < ‖v‖) :
    velocityLineResolvent r (v,x) = 0 := by
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun s => by simp only [hs (v,_) hv,smul_zero,Pi.zero_apply])

theorem velocityLineAverage_norm_le {r : Velocity × FourierSpace → ℂ} {R B : ℝ}
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) (x : FourierSpace) :
    ‖velocityLineAverage r x‖ ≤ volume.real (Metric.closedBall (0 : Velocity) R)*B := by
  have he : velocityLineAverage r x =
      ∫ v in Metric.closedBall (0 : Velocity) R, velocityLineResolvent r (v,x) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    exact velocityLineResolvent_support hs v x
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hv)
  rw [he]
  have hfinite : volume (Metric.closedBall (0 : Velocity) R) < ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top
  have h := norm_setIntegral_le_of_norm_le_const
    (f := fun v => velocityLineResolvent r (v,x)) hfinite
    (fun v _ => dampedLineResolvent_norm_le (fun y => hb (v,y)) (characteristicDirection v) x)
  simpa only [mul_comm] using h

theorem velocityLineAverage_memLp_two {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B : ℝ}
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) :
    MemLp (velocityLineAverage r) 2 volume :=
  integrable_bounded_memLp_two (velocityLineAverage_integrable hr)
    (velocityLineAverage_norm_le hb hs)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedAverageCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual bounded-source averages are sequentially compact in local L2 -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology
namespace BoltzmannNonuniqueness.Published

def boundedAverageL2 {R B : ℝ} (r : Velocity × FourierSpace → ℂ) (hr : Integrable r)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) :
    Lp ℂ 2 (volume : Measure FourierSpace) :=
  (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicWeakCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single nonnegative global weak limit of the actual periodic approximants -/
noncomputable section
open MeasureTheory Filter Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

structure GlobalWeakLimit (f : Density) (hfm : Measurable f) where
  indices : ℕ → ℕ
  increasing : StrictMono indices
  density : ℝ × Phase → ℝ
  measurable : Measurable density
  nonnegative : ∀ z, 0 ≤ density z
  weighted_weak : Published.WeakL1Converges (finiteTimeMeasure.prod volume)
    (fun n => (approximatingSolution f hfm (indices n)).density) density

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Weak velocity averages of the same global periodic limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def GlobalWeakLimit.kineticProfile {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (p : (ℝ × Position) × Velocity) : ℝ :=
  G.density (p.1.1,(p.1.2,p.2))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass-normalized pair compactness for the actual global approximation sequence -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation

def GlobalWeakLimit.subsequence {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {φ : ℕ → ℕ} (hφ : StrictMono φ) : GlobalWeakLimit f hfm where
  indices := G.indices ∘ φ
  increasing := G.increasing.comp hφ
  density := G.density
  measurable := G.measurable
  nonnegative := G.nonnegative
  weighted_weak := G.weighted_weak.comp hφ.tendsto_atTop

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicJointBudgetLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single global collision limit retains its strong masses and physical rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

structure GlobalCollisionLimit (f : Density) (hfm : Measurable f) where
  weakLimit : GlobalWeakLimit f hfm
  mass_strong : ∀ T : ℝ, 0 ≤ T → Tendsto (fun n => eLpNorm (fun z =>
        Compactness.fiberMass volume (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile z-
        Compactness.fiberMass volume weakLimit.kineticProfile z)
        1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0)
  normalized_pairs : ∀ T : ℝ, 0 ≤ T → Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume
        (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
      (Compactness.normalizedPair volume weakLimit.kineticProfile)
  finite_rates : ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((weakLimit.indices n:ℝ)+1)
          (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
        (massNormalizedPreRate weakLimit.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((weakLimit.indices n:ℝ)+1)
          (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
        (massNormalizedPostRate weakLimit.kineticProfile)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedCharacteristicGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual gain limits with bounded spatial mass and a fixed elastic window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def clippedFiniteGain (N K R : ℝ) (f : X × Velocity → ℝ) : X × Velocity → ℝ :=
  windowCollisionMarginal R (fun z => collisionMassClip K f z*massRegularizedPostRate N f z)

def clippedPhysicalGain (K R : ℝ) (f : X × Velocity → ℝ) : X × Velocity → ℝ :=
  windowCollisionMarginal R (fun z => collisionMassClip K f z*massNormalizedPostRate f z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing the mass and elastic-window cutoffs from a physical gain fiber -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def clippedPostRate (K R : ℝ) (f : X × Velocity → ℝ) :
    (X × (Velocity × Velocity)) × Sphere → ℝ :=
  (collisionWindow R).indicator (fun z => collisionMassClip K f z*massNormalizedPostRate f z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual clipped gain converges along the same free characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

def characteristicClippedFiniteGain (N K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  TorusFlight.along (TorusFlight.regroup (clippedFiniteGain N K R f))

def characteristicClippedPhysicalGain (K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  TorusFlight.along (TorusFlight.regroup (clippedPhysicalGain K R f))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicStrongAverages
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual physical frequencies and survival along torus characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

def physicalCharacteristicFrequency (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (kineticFrequency f))

def physicalCharacteristicSurvival (T : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  Published.timeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual initial contribution converges with its physical survival factor -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness

def survivingInitial (T : ℝ) (f : Density) (u : (ℝ × Position) × Velocity → ℝ)
    (z : ℝ × Phase) : ℝ := physicalCharacteristicSurvival T u z*f z.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveContributionsIntegrable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual positive gain integrals converge with their physical survival factors -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def finitePositiveSource (T N K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (characteristicClippedFiniteGain N K R f)

def physicalPositiveSource (T K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (characteristicClippedPhysicalGain K R f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicPhysicalGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The full physical gain is the almost-everywhere limit on characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

def physicalCharacteristicGain (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (gainDensity f))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionComparisonError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four physical errors in positive characteristic comparison -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def collisionComparisonError (N M : ℝ) (F H : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  |(gain N F p-gain M H p)/(1+F p+H p)|+
  |(lossDensity F p-loss N F p)/(1+F p)|+
  |(lossDensity H p-loss M H p)/(1+H p)|+
  |kineticFrequency F p-kineticFrequency H p|

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LimitFullPositiveSurvival
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual weak limit retains the full physical positive characteristic source -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalFullPositiveSource (T : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (physicalCharacteristicGain f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalLinearContinuous
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual linear characteristic profile is a lower solution for the weak limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalLinearProfile (f₀ : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (z : ℝ × Phase) : ℝ :=
  TransportPrimitive.linearSolution (f₀ z.2)
    (fun s => physicalCharacteristicFrequency F (s,z.2))
    (fun s => physicalCharacteristicGain F (s,z.2)) z.1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable tested fields for the actual linear characteristic equation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def linearRenormalizedField (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (β : Renormalization) (φ : KineticTest) (z : ℝ × Phase) : ℝ :=
  maxwellian z.2.2*β.toFun (physicalLinearProfile f F z/maxwellian z.2.2)*
    φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)+
  derivWithin β.toFun (Ici 0) (physicalLinearProfile f F z/maxwellian z.2.2)*
    (physicalCharacteristicGain F z-physicalCharacteristicFrequency F z*physicalLinearProfile f F z)*
    φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicLinearApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Comparing each positive approximation to the actual linear limit profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open TransportPrimitive

def linearComparisonError {N H : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (f : Density)
    (F : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) : ℝ :=
  |(S.characteristicGain z-physicalCharacteristicGain F z)/
    (1+S.density (z.1,TorusFlight.flight z.1 z.2)+max 0 (physicalLinearProfile f F z))|+
  |S.characteristicLossDefect z/(1+S.density (z.1,TorusFlight.flight z.1 z.2))|+
  |physicalCharacteristicFrequency S.kineticProfile z-physicalCharacteristicFrequency F z|

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEvolution
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common entropy-moment budget for every characteristic time -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalEntropyBudget (f : Density) : ℝ :=
  (1+4*entropyMomentCoefficient)*relativeEntropy f+
    4*entropyMomentCoefficient*(∫ p : Phase, entropyGaussian p.2)+
      (∫ p : Phase, maxwellian p.2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The measurable nonnegative evolution defined by the characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalEvolution (f : Density) (F : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  fun t p => max 0 (physicalLinearProfile f F (t,TorusFlight.flight (-t) p))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Damped free waiting in physical flight coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalAdvance (p : PhysicalFlightState) (s : ℝ) : PhysicalFlightState :=
  (p.1-s,(p.2.1+s • p.2.2,p.2.2))

def physicalWaitingWeight (C : ℝ≥0) (q : PhysicalFlightState × ℝ) : ℝ≥0∞ :=
  {q : PhysicalFlightState × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1}.indicator
    (fun q => clockSurvival C q.2) q

def physicalWaitingKernel (C : ℝ≥0) : Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const PhysicalFlightState (volume : Measure ℝ))
    (fun _ q => physicalWaitingWeight C q)).map (fun q => physicalAdvance q.1 q.2)

instance physicalWaitingKernel_sFinite (C : ℝ≥0) : IsSFiniteKernel (physicalWaitingKernel C) := by
  have : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const PhysicalFlightState (volume : Measure ℝ))
      (fun _ q => physicalWaitingWeight C q)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p q
    by_cases hq : 0 < q.2 ∧ q.2 ≤ q.1.1
    · simp [physicalWaitingWeight,hq,clockSurvival]
    · simp [physicalWaitingWeight,hq]
  unfold physicalWaitingKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One marked physical collision after waiting with a prescribed damping rate -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalMarkedCollision (b : BeamCoefficients) (endTime : ℝ) (m : HistoryMark) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.id ×ₖ (mediumMarkedKernel b m).comap
    (fun p => ((endTime-p.1,p.2.1),p.2.2)) (by fun_prop)).map
      (fun q => (q.1.1,(q.1.2.1,q.2)))

instance physicalMarkedCollision_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) : IsSFiniteKernel (physicalMarkedCollision b endTime m) := by
  unfold physicalMarkedCollision
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalMarkedEvent (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) : Kernel PhysicalFlightState PhysicalFlightState :=
  physicalMarkedCollision b endTime m ∘ₖ physicalWaitingKernel C

instance physicalMarkedEvent_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) : IsSFiniteKernel (physicalMarkedEvent b endTime C m) := by
  unfold physicalMarkedEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Selected physical words lie below the full positive collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalMarkedWord (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    List HistoryMark → Kernel PhysicalFlightState PhysicalFlightState
  | [] => Kernel.id
  | m::ms => physicalMarkedWord b endTime C ms ∘ₖ physicalMarkedEvent b endTime C m

instance physicalMarkedWord_sFinite (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) : IsSFiniteKernel (physicalMarkedWord b endTime C ms) := by
  induction ms with
  | nil => change IsSFiniteKernel Kernel.id; infer_instance
  | cons m ms ih =>
    change IsSFiniteKernel (physicalMarkedWord b endTime C ms ∘ₖ physicalMarkedEvent b endTime C m)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Time and angle parameters for a selected physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalEventMeasure : Measure EventParameter := volume.prod sphereProbability

instance physicalEventMeasure_sFinite : SFinite physicalEventMeasure := by
  unfold physicalEventMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalParameterWeight (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter) : ℝ≥0∞ :=
  physicalWaitingWeight C (p,a.1) *
    mediumMarkedRate b m (mediumPoint endTime p a.1,p.2.2)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Gain-only physical histories with a chosen damping constant -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalBeamCollision (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  physicalMarkedCollision b endTime 1+physicalMarkedCollision b endTime 2

instance physicalBeamCollision_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (physicalBeamCollision b endTime) := by
  unfold physicalBeamCollision
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalBeamEvent (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  physicalBeamCollision b endTime ∘ₖ physicalWaitingKernel C

instance physicalBeamEvent_sFinite (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    IsSFiniteKernel (physicalBeamEvent b endTime C) := by
  unfold physicalBeamEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Damped endpoints of the gain-only physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance physicalBeamEvent_pow_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) : IsSFiniteKernel ((physicalBeamEvent b endTime C)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    change IsSFiniteKernel (((physicalBeamEvent b endTime C)^n) ∘ₖ physicalBeamEvent b endTime C)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalGainEndpoint (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) (n : ℕ) :
    Kernel PhysicalFlightState (V × V) :=
  (Kernel.withDensity ((physicalBeamEvent b endTime C)^n)
    (fun _ p => clockSurvival C p.1)).map finishMediumFlight

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedEndpointHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Constant damping exposes a positive measure source -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.WeakTime

def timeWeightedDensity (a b C : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  slabExponential a b C z.1*F z

def timeWeightedSource (a b C : ℝ) (μ : Measure (ℝ × Phase)) : Measure (ℝ × Phase) :=
  positiveDensityMeasure μ (fun z => slabExponential a b C z.1)

def dampedResidual (a b C : ℝ) (F L : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  slabExponential a b C z.1*(C*F z-L z)

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Fixed time-window representations of the bounded event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedPhysicalEvent (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C).restrict mediumVelocityBox_measurable

instance dampedBoundedPhysicalEvent_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedBoundedPhysicalEvent C b endTime) := by
  unfold dampedBoundedPhysicalEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)


end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Collision-time integrals for the positive Duhamel source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

def dampedSourceIncrement (a b C s t : ℝ) (μ : Measure (ℝ × Phase)) : Measure Phase :=
  ENNReal.ofReal (Real.exp (-C*t)) • phaseIncrement (timeWeightedSource a b C μ) s t

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # The damped residence-time kernel along a free characteristic -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def residenceWeight (C b : ℝ) (q : (ℝ × Phase) × ℝ) : ℝ≥0∞ :=
  {p : (ℝ × Phase) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ b}.indicator
    (fun p => ENNReal.ofReal (Real.exp (C*(p.1.1-p.2)))) q

def residenceKernel (C b : ℝ) : Kernel (ℝ × Phase) (ℝ × Phase) :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const (ℝ × Phase) (volume : Measure ℝ))
    (fun _ q => residenceWeight C b q)).map (fun q => (q.2,q.1.2))

instance residenceKernel_sFinite (C b : ℝ) : IsSFiniteKernel (residenceKernel C b) := by
  have : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const (ℝ × Phase) (volume : Measure ℝ))
      (fun _ q => residenceWeight C b q)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z q
    by_cases hq : q.1.1 < q.2 ∧ q.2 ≤ b
    · simp [residenceWeight,hq]
    · simp [residenceWeight,hq]
  unfold residenceKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Initial phase measures and their free-flight occupation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def phaseSeed (s : ℝ) (μ : Measure Phase) : Measure (ℝ × Phase) :=
  μ.map (fun p => (s,p))

instance phaseSeed_sFinite (s : ℝ) (μ : Measure Phase) [SFinite μ] : SFinite (phaseSeed s μ) := by
  unfold phaseSeed
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Terminal phase slices of a positive source history -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

def phaseEndpointKernel (C t : ℝ) : Kernel (ℝ × Phase) Phase :=
  (Kernel.deterministic Prod.snd measurable_snd).withDensity
    (fun z _ => ENNReal.ofReal (Real.exp (C*(z.1-t))))

instance phaseEndpointKernel_sFinite (C t : ℝ) : IsSFiniteKernel (phaseEndpointKernel C t) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionParameterShuffle
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regrouping collision times and outgoing angles preserves their product law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def splitThreeEvents (q : ThreeEvents) : ThreeWaits × ThreeAngles :=
  ((q.1.1,(q.2.1.1,q.2.2.1)),(q.1.2,(q.2.1.2,q.2.2.2)))

def joinThreeEvents (s : ThreeWaits) (a : ThreeAngles) : ThreeEvents :=
  ((s.1,a.1),((s.2.1,a.2.1),(s.2.2,a.2.2)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_OriginMeshLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cost of removing collisions close to a transverse origin -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PositiveIteration

def nearOriginKernel (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity) :
    Kernel KineticPhase Velocity := by
  classical
  exact Kernel.piecewise (nearOriginRegion_measurable c ρ) K 0

instance nearOriginKernel_sFinite (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] : IsSFiniteKernel (nearOriginKernel c ρ K) := by
  unfold nearOriginKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance awayOriginKernel_sFinite (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] : IsSFiniteKernel (awayOriginKernel c ρ K) := by
  unfold awayOriginKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedOriginDeletion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Fixed products for selected physical collision words -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev collisionWordMeasurable : (n : ℕ) → MeasurableSpace (CollisionWord n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := collisionWordMeasurable n
    exact inferInstanceAs (MeasurableSpace (EventParameter × CollisionWord n))

attribute [instance] collisionWordMeasurable

def collisionWordMeasure : (n : ℕ) → Measure (CollisionWord n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => physicalEventMeasure.prod (collisionWordMeasure n)

instance collisionWordMeasure_sFinite (n : ℕ) : SFinite (collisionWordMeasure n) := by
  induction n with
  | zero => change SFinite (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    let := ih
    change SFinite (physicalEventMeasure.prod (collisionWordMeasure n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def selectedWordState (b : BeamCoefficients) (endTime : ℝ) :
    (ms : List HistoryMark) → PhysicalFlightState → CollisionWord ms.length → PhysicalFlightState
  | [],p,_ => p
  | m::ms,p,a => selectedWordState b endTime ms (mediumParameterState b endTime p (m,a.1)) a.2

def selectedWordDensity (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    (ms : List HistoryMark) → PhysicalFlightState → CollisionWord ms.length → ℝ≥0∞
  | [],_,_ => 1
  | m::ms,p,a => physicalParameterWeight b endTime C m p a.1 *
      selectedWordDensity b endTime C ms (mediumParameterState b endTime p (m,a.1)) a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ThreeSelectedIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three selected collisions as one time and angle integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def threeSelectedIntegrand (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState) (F : PhysicalFlightState → ℝ≥0∞)
    (q : ThreeEvents) : ℝ≥0∞ :=
  let a : CollisionWord 3 := (q.1,(q.2.1,(q.2.2,PUnit.unit)))
  selectedWordDensity b endTime C [m₀,m₁,m₂] p a *
    F (selectedWordState b endTime [m₀,m₁,m₂] p a)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGlobalRenormalized
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Remaining-flight time and characteristic spacetime coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightCharacteristicEquiv (endTime : ℝ) : PhysicalFlightState ≃ᵐ (ℝ × WeakTime.Phase) where
  toFun p := (endTime-p.1,(p.2.1-(endTime-p.1) • p.2.2,p.2.2))
  invFun z := (endTime-z.1,(z.2.1+z.1 • z.2.2,z.2.2))
  left_inv p := by
    ext <;> simp
  right_inv z := by
    ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : PhysicalFlightState =>
      (endTime-p.1,(p.2.1-(endTime-p.1) • p.2.2,p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × WeakTime.Phase =>
      (endTime-z.1,(z.2.1+z.1 • z.2.2,z.2.2)))
    fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The positive physical entry histories reach the late growth box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def velocityPhaseBall (κ ρ : ℝ) : Set (V × V) := {p | p.2 ∈ ball (κ • firstAxis) ρ}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGainTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical gain histories in the characteristic coordinates of the hot balance -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamCharacteristicKernel (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  transportedKernel (flightCharacteristicEquiv endTime).symm (physicalBeamCollision b endTime)

instance beamCharacteristicKernel_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (beamCharacteristicKernel b endTime) := by
  unfold beamCharacteristicKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_BeamNormalOutgoing
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Space-time coordinates normalized by the local cold density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def normalizedPoint (ρ t₀ : ℝ) (x₀ : V) (p : ℝ × V) : ℝ × V :=
  (t₀+p.1/ρ,x₀+ρ⁻¹ • p.2)

theorem normalizedPoint_measurable (ρ t₀ : ℝ) (x₀ : V) :
    Measurable (normalizedPoint ρ t₀ x₀) := by
  unfold normalizedPoint
  fun_prop

def BeamCoefficients.normalized (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V) : BeamCoefficients where
  plusPartner := b.plusPartner ∘ normalizedPoint ρ t₀ x₀
  minusPartner := b.minusPartner ∘ normalizedPoint ρ t₀ x₀
  plusDensity := b.plusDensity ∘ normalizedPoint ρ t₀ x₀
  minusDensity := b.minusDensity ∘ normalizedPoint ρ t₀ x₀
  plusPartner_measurable := b.plusPartner_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  minusPartner_measurable := b.minusPartner_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  plusDensity_measurable := b.plusDensity_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  minusDensity_measurable := b.minusDensity_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical beam source in characteristic variables has no terminal-time dependence -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicBeamPoint (z : ℝ × WeakTime.Phase) : ℝ × V :=
  (z.1,z.2.1+z.1 • z.2.2)

def characteristicBeamJump (z : ℝ × WeakTime.Phase) (v : V) : ℝ × WeakTime.Phase :=
  (z.1,(z.2.1+z.1 • z.2.2-z.1 • v,v))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two atomic cold beams as a measurable partner kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamPartnerKernel (b : BeamCoefficients) : Kernel (ℝ × V) V :=
  (Kernel.deterministic b.plusPartner b.plusPartner_measurable).withDensity
    (fun p _ => ENNReal.ofReal (b.plusDensity p))+
  (Kernel.deterministic b.minusPartner b.minusPartner_measurable).withDensity
    (fun p _ => ENNReal.ofReal (b.minusDensity p))

instance beamPartnerKernel_sFinite (b : BeamCoefficients) : IsSFiniteKernel (beamPartnerKernel b) := by
  have hp : IsSFiniteKernel ((Kernel.deterministic b.plusPartner b.plusPartner_measurable).withDensity
      (fun p _ => ENNReal.ofReal (b.plusDensity p))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  have hn : IsSFiniteKernel ((Kernel.deterministic b.minusPartner b.minusPartner_measurable).withDensity
      (fun p _ => ENNReal.ofReal (b.minusDensity p))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold beamPartnerKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The atomic beam's genuine normal-angle collision law in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamNormalCharacteristicKernel (b : BeamCoefficients) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  transportedKernel characteristicEquiv (normalPhaseGainKernel (beamPartnerKernel b))

instance beamNormalCharacteristicKernel_sFinite (b : BeamCoefficients) :
    IsSFiniteKernel (beamNormalCharacteristicKernel b) := by
  unfold beamNormalCharacteristicKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ScaledBoundedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact local density normalization of physical flight states -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightScaleEquiv (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V) :
    PhysicalFlightState ≃ᵐ PhysicalFlightState where
  toFun p := (ρ*p.1,(ρ • (p.2.1-x₀),p.2.2))
  invFun p := (p.1/ρ,(x₀+ρ⁻¹ • p.2.1,p.2.2))
  left_inv p := by
    apply Prod.ext
    · simp [hρ]
    · apply Prod.ext
      · simp [smul_smul,hρ]
      · rfl
  right_inv p := by
    apply Prod.ext
    · field_simp
    · apply Prod.ext
      · simp [smul_smul,hρ]
      · rfl
  measurable_toFun := by
    change Measurable (fun p : PhysicalFlightState => (ρ*p.1,(ρ • (p.2.1-x₀),p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : PhysicalFlightState => (p.1/ρ,(x₀+ρ⁻¹ • p.2.1,p.2.2)))
    fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBoundedEndpointTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Enlarged-damping physical histories in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  transportedKernel (flightCharacteristicEquiv endTime).symm (dampedMediumStateCollision C b endTime)

instance dampedCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedCharacteristicKernel C b endTime) := by
  unfold dampedCharacteristicKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The enlarged-damping characteristic kernel is gain plus positive retention -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicBeamFrequency (b : BeamCoefficients) (z : ℝ × WeakTime.Phase) : ℝ :=
  mediumFrequency z.2.2 (b.plusPartner (characteristicBeamPoint z))
    (b.minusPartner (characteristicBeamPoint z))
    (b.plusDensity (characteristicBeamPoint z)) (b.minusDensity (characteristicBeamPoint z))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical collision intensity and clock normalize by the same density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedDensityScaledCollision (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumStateCollision C b endTime).withDensity (fun _ _ => ENNReal.ofReal (ρ : ℝ))

instance dampedDensityScaledCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedDensityScaledCollision C b endTime ρ) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

def dampedDensityScaledEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  dampedDensityScaledCollision C b endTime ρ ∘ₖ physicalWaitingKernel (ρ*C)

instance dampedDensityScaledEventKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedDensityScaledEventKernel C b endTime ρ) := by
  unfold dampedDensityScaledEventKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local density normalization preserves the bounded physical event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedDensityScaledEvent (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedDensityScaledEventKernel C b endTime ρ).restrict mediumVelocityBox_measurable

instance dampedBoundedDensityScaledEvent_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    IsSFiniteKernel (dampedBoundedDensityScaledEvent C b endTime ρ) := by
  unfold dampedBoundedDensityScaledEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The density-scaled physical histories use the same scaled characteristic clock -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def densityScaledCharacteristicKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) :
    Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase) :=
  (dampedCharacteristicKernel C b endTime).withDensity (fun _ _ => ENNReal.ofReal (ρ : ℝ))

instance densityScaledCharacteristicKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) : IsSFiniteKernel (densityScaledCharacteristicKernel C b endTime ρ) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedGeometricBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite-speed cone of the velocity-truncated physical histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedFlightCone (p q : PhysicalFlightState) : Prop :=
  0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.2‖ ≤ 6 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A nonzero density has a bounded positive portion away from the velocity axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def seedPortion (n : ℕ) : Set (Velocity × Velocity) :=
  {p | ‖p.1‖ ≤ n ∧ ‖p.2‖ ≤ n ∧ 1/((n : ℝ)+1) ≤ ‖transverse p.2‖}

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_BeamNormalCharacteristicIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A density-scaled normal-angle beam source with its exact loss complement -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def scaledBeamNormalKernel (b : BeamCoefficients) (ρ : ℝ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  (beamNormalCharacteristicKernel b).withDensity (fun _ _ => ENNReal.ofReal ρ)

instance scaledBeamNormalKernel_sFinite (b : BeamCoefficients) (ρ : ℝ) :
    IsSFiniteKernel (scaledBeamNormalKernel b ρ) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

def beamNormalRetainedKernel (b : BeamCoefficients) (ρ C : ℝ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  positiveSourceKernel (scaledBeamNormalKernel b ρ) (fun _ => 1)
    (fun z => C-ρ*characteristicBeamFrequency b z)

instance beamNormalRetainedKernel_sFinite (b : BeamCoefficients) (ρ C : ℝ) :
    IsSFiniteKernel (beamNormalRetainedKernel b ρ C) := by
  unfold beamNormalRetainedKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedDampedBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Localizing the physical normal-angle source above the cold spatial cutoff -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def coldCharacteristicDomain (a η l : ℝ) : Set CharacteristicPhase :=
  {z | a ≤ z.1 ∧ 0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ ∧
    Real.exp η*l < ‖transverse (z.2.1+z.1 • z.2.2)‖}

theorem coldCharacteristicDomain_measurable (a η l : ℝ) :
    MeasurableSet (coldCharacteristicDomain a η l) := by
  have hx : Measurable (fun z : CharacteristicPhase => ‖transverse (z.2.1+z.1 • z.2.2)‖) := by
    exact ChartKernel.measurable_transverse.norm.comp (by fun_prop)
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const hx).inter (measurableSet_lt measurable_const hx))

def localizedNormalBeamKernel (b : BeamCoefficients) (ρ C a η l : ℝ)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B) :
    Kernel CharacteristicPhase CharacteristicPhase := by
  classical
  exact Kernel.piecewise (coldCharacteristicDomain_measurable a η l)
    ((beamNormalRetainedKernel b ρ C).restrict hB) 0

instance localizedNormalBeamKernel_sFinite (b : BeamCoefficients) (ρ C a η l : ℝ)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B) :
    IsSFiniteKernel (localizedNormalBeamKernel b ρ C a η l hB) := by
  unfold localizedNormalBeamKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The localized normal-angle collision law in physical flight coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedNormalCollision (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  transportedKernel (flightCharacteristicEquiv T)
    (localizedNormalBeamKernel b ρ C a η l hΩ)

instance localizedNormalCollision_sFinite (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalCollision b ρ C T a η l hΩ) := by
  unfold localizedNormalCollision
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite bounded physical histories are dominated by the localized actual angular histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedNormalPhysicalEvent (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  localizedNormalCollision b ρ C T a η l hΩ ∘ₖ physicalWaitingKernel (Real.toNNReal C)

instance localizedNormalPhysicalEvent_sFinite (b : BeamCoefficients) (ρ C T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalPhysicalEvent b ρ C T a η l hΩ) := by
  unfold localizedNormalPhysicalEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SeedEscapeMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably many compact phase cutoffs preserving the positive seed -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def seedPhaseBump (n : ℕ) : ContDiffBump (0 : WeakTime.Phase) :=
  ⟨(n : ℝ)+1,(n : ℝ)+2,by positivity,by linarith⟩

def seedPhaseCutoff (n : ℕ) : WeakTime.Phase → ℝ := seedPhaseBump n

end BoltzmannNonuniqueness

end

end

section

/-! # The surviving seed gives positive physical mass outside any fixed hole -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness

def seedEscapeRegion (n : ℕ) (L t : ℝ) : Set (Velocity × Velocity) :=
  {p | L < ‖transverse p.1‖ ∧ ‖p.1‖ ≤ (n : ℝ)*(1+t) ∧ ‖p.2‖ ≤ n}

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntryPortion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded portions of the entry velocities have one uniform late-box arrival time -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

def entryPhasePortion (κ ρ : ℝ) (n : ℕ) : Set WeakTime.Phase :=
  velocityPhaseBall κ ρ ∩ {p | ‖p‖ ≤ (n:ℝ)}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedLateBoxPhysicalBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact physical-time mass of each finite normalized branching block -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedDensityScaledBlockMass (C : ℝ≥0) (b : BeamCoefficients) (endTime ρ : ℝ)
    (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ q,
    clockSurvival (Real.toNNReal ρ*C) q.1 *
      (physicalBlockTarget x Δ κ d).indicator 1 (finishMediumFlight q)
    ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) (Δ,(x,(v : V)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Removing the symmetric average from the nonnegative gain -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness

def rawNonnegativeGain (f g : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  ∫⁻ w : Velocity, ∫⁻ n : Sphere,
    ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)*g (scatterRight v w n)
    ∂sphereArea

def rawGainIntegrand (f g : Velocity → ℝ≥0∞) (v : Velocity) (p : Velocity × Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel v p.1 p.2)*f (scatterLeft v p.1 p.2)*g (scatterRight v p.1 p.2)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_MityaginDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Twenty-dimensional analytic zero-set nullity

One-dimensional isolated zeros, Fubini along lines through a nonzero point,
and the analytic identity principle give the required specialization of
Mityagin's Proposition 0.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace BoltzmannNonuniqueness.Published

def fiveGainParameterEquiv : FanPhase ≃L[ℝ] FiveGainMap.Parameters :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [FanPhase,FanRemainder,FiveGainMap.Parameters,FiveGainMap.V,
      Module.finrank_pi_fintype])

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteEntryPhaseBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Reachable regions for a fixed finite number of physical gain collisions -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

def finiteFlightCone (N n : ℕ) (h R : ℝ) (x : V) (p : PhysicalFlightState) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ h ∧ ‖p.2.2‖ ≤ R+2*((N:ℝ)-n) ∧
    ‖p.2.1-x‖ ≤ (h-p.1)*(R+2*N)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One compact phase cutoff contains all short entry histories in a fixed time window -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

def phaseBallCore (M : ℝ) : Set CharacteristicPhase := {z | ‖z.2‖ ≤ M}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedBlockComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Retaining the actual open-left collision-time window in physical histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalCollisionWindow (s T : ℝ) : Set PhysicalFlightState := {p | T-p.1 ∈ Ioc s T}

theorem physicalCollisionWindow_measurable (s T : ℝ) : MeasurableSet (physicalCollisionWindow s T) :=
  (measurable_const.sub measurable_fst) measurableSet_Ioc

def localizedNormalWindowEvent (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (localizedNormalPhysicalEvent b ρ C T a η l hΩ).restrict (physicalCollisionWindow_measurable s T)

instance localizedNormalWindowEvent_sFinite (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    IsSFiniteKernel (localizedNormalWindowEvent b ρ C T a η l s hΩ) := by
  unfold localizedNormalWindowEvent
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The finite physical branching block lies below the actual angular endpoint histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def localizedHistoryBlockMass (b : BeamCoefficients) (ρ C T a η l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (A : Set (V × V))
    (N : ℕ) (z : ℝ × WeakTime.Phase) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ q, A.indicator 1 (EuclideanFlight.flight T q)
    ∂(WeakTime.phaseEndpointKernel C T ∘ₖ
      ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
        (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
          WeakTime.residenceKernel C T)^n)) z

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricLocalizedEntry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual geometric coefficients on the cone visited by a finite history -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicHistoryCore (t₀ R : ℝ) (x : V) : Set (ℝ × WeakTime.Phase) :=
  {z | ‖z.2.1+t₀ • z.2.2-x‖ ≤ R ∧ ‖z.2.2‖ ≤ 6}

theorem characteristicHistoryCore_measurable (t₀ R : ℝ) (x : V) :
    MeasurableSet (characteristicHistoryCore t₀ R x) := by
  unfold characteristicHistoryCore
  have hx : Measurable (fun z : ℝ × WeakTime.Phase => ‖z.2.1+t₀ • z.2.2-x‖) := by fun_prop
  have hv : Measurable (fun z : ℝ × WeakTime.Phase => ‖z.2.2‖) := by fun_prop
  exact (measurableSet_le hx measurable_const).inter (measurableSet_le hv measurable_const)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end


