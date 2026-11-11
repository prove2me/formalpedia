-- Prove2me | Definitions.Def_OAIQ233A000
-- name    : OAIQ233A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:29:55.199844+00:00
-- url     : https://prove2.me/theorems/f5b2e978-a47f-4f02-aaa3-77a8f1c62c46
-- title:
--   Definitions bundle OAIQ233A000 of the split of OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 763 declarations of OpenAI's Lean: 557 definitions, 18 inductive types or structures, 26 instances and 162 theorems. The definitions and types are `CS`, `CS.deriv`, `CS.neg`, `CS.scale`, `CS.smul`, `Mertens.E₁`, `Mertens.E₁p`, `Mertens.E₁Λ`, `Mertens.E₂p`, `Mertens.M`, `OAI.TotientAsymptotic.AbnormalCofactor`, `OAI.TotientAsymptotic.Aseries`, `OAI.TotientAsymptotic.BootstrapGood`, `OAI.TotientAsymptotic.CollisionBandConditions`, `OAI.TotientAsymptotic.CommonEndpointComparison`, `OAI.TotientAsymptotic.CommonLargestConditions`, `OAI.TotientAsymptotic.CommonPrimeWitness`, `OAI.TotientAsymptotic.ComparisonHeightBounds`, `OAI.TotientAsymptotic.CountingRegular`, `OAI.TotientAsymptotic.CrossRemoval`, `OAI.TotientAsymptotic.DistinctLargestConditions`, `OAI.TotientAsymptotic.DistinctPrimeWitness`, `OAI.TotientAsymptotic.ExtractedStructureInput`, `OAI.TotientAsymptotic.FailedRowMassBudget`, `OAI.TotientAsymptotic.FailsPositiveSquare`, `OAI.TotientAsymptotic.FailsStrictSlack`, `OAI.TotientAsymptotic.FailsWitnessNormality`, `OAI.TotientAsymptotic.FailsWitnessOmega`, `OAI.TotientAsymptotic.FailsWitnessSquare`, `OAI.TotientAsymptotic.FiniteMap.badPreimages`, `OAI.TotientAsymptotic.FiniteMap.badValues`, `OAI.TotientAsymptotic.FiniteMap.collisionCount`, `OAI.TotientAsymptotic.FiniteMap.fiber`, `OAI.TotientAsymptotic.FiniteMap.multipleValues`, `OAI.TotientAsymptotic.FirstDifferenceAt`, `OAI.TotientAsymptotic.FirstFailedRowAt`, `OAI.TotientAsymptotic.FordComparisonConditions`, `OAI.TotientAsymptotic.FordComparisonParameters`, `OAI.TotientAsymptotic.FordCoordinateConcentrationInput`, `OAI.TotientAsymptotic.FordLemma26Input` and 535 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Fourier`, `IEANTN_Mertens`, `Mathlib_NumberTheory_Sieve_AuxResults`, `Mathlib_NumberTheory_Sieve_Basic`, `Mathlib_NumberTheory_Sieve_Selberg`, `SmoothExistence`, `Sobolev`, `TotientAsymptotic_AbnormalCofactorMass`, `TotientAsymptotic_ActualComparison`, `TotientAsymptotic_ActualComparisonCutoffs`, `TotientAsymptotic_ActualFordData`, `TotientAsymptotic_ActualSuffixMass`, `TotientAsymptotic_ActualSurvivingGeometry`, `TotientAsymptotic_AdditiveCost`, `TotientAsymptotic_AdditiveEnclosure`, `TotientAsymptotic_AdditiveShellUnion`, `TotientAsymptotic_AllPreimageCoverage`, `TotientAsymptotic_AllPrimeTriples`, `TotientAsymptotic_AllShiftedPrimePairs`, `TotientAsymptotic_AttachTail`, `TotientAsymptotic_BandComparison`, `TotientAsymptotic_BandExtraction`, `TotientAsymptotic_BandGrid`, `TotientAsymptotic_BandPrimeError`, `TotientAsymptotic_BandStates`, `TotientAsymptotic_BandUnionCount`, `TotientAsymptotic_Basic`, `TotientAsymptotic_BootstrapCutoffs`, `TotientAsymptotic_BootstrapExceptionalCount`, `TotientAsymptotic_BootstrapGoodValues`, `TotientAsymptotic_BootstrapIndex`, `TotientAsymptotic_BootstrapMajorant`, `TotientAsymptotic_BootstrapRealCount`, `TotientAsymptotic_BoundaryGrid`, `TotientAsymptotic_BoundedRatioValues`, `TotientAsymptotic_CandidateAbundance`, `TotientAsymptotic_CandidateArithmetic`, `TotientAsymptotic_CandidateNormalHead`, `TotientAsymptotic_CandidatePrimeList`, `TotientAsymptotic_CappedLoglogGrid`, `TotientAsymptotic_ChosenCollision`, `TotientAsymptotic_CofactorEnvelope`, `TotientAsymptotic_CofactorExceptions`, `TotientAsymptotic_CofactorGrowth`, `TotientAsymptotic_CofactorShellDecay`, `TotientAsymptotic_CollisionBandData`, `TotientAsymptotic_CollisionCanceled`, `TotientAsymptotic_CollisionClassData`, `TotientAsymptotic_CollisionCount`, `TotientAsymptotic_CollisionCutoff`, `TotientAsymptotic_CollisionGrid`, `TotientAsymptotic_CollisionGridScale`, `TotientAsymptotic_CollisionHeadCount`, `TotientAsymptotic_CollisionTail`, `TotientAsymptotic_CollisionTuples`, `TotientAsymptotic_CommonLargestPrime`, `TotientAsymptotic_CommonPrimeMass`, `TotientAsymptotic_ComparisonSizes`, `TotientAsymptotic_ConcentratedPrefix`, `TotientAsymptotic_ConcentrationExponents`, `TotientAsymptotic_CoordinateActivePrefix`, `TotientAsymptotic_CoordinateCube`, `TotientAsymptotic_CoordinateCutoffs`, `TotientAsymptotic_CoordinateDeviationExponent`, `TotientAsymptotic_CoordinateEnlargement`, `TotientAsymptotic_CoordinateThreshold`, `TotientAsymptotic_DistinctLargestEncoding`, `TotientAsymptotic_DistinctPrimeMass`, `TotientAsymptotic_DistinctPrimeRemoval`, `TotientAsymptotic_DyadicSuffix`, `TotientAsymptotic_ElementaryExceptions`, `TotientAsymptotic_EnlargementTail`, `TotientAsymptotic_ExtractTail`, `TotientAsymptotic_FailedRowCountBound`, `TotientAsymptotic_FailedRowCutoff`, `TotientAsymptotic_FailedRowPrefix`, `TotientAsymptotic_FiniteCoefficient`, `TotientAsymptotic_FiniteMap`, `TotientAsymptotic_FirstCollision`, `TotientAsymptotic_FirstFailedRow`, `TotientAsymptotic_FirstFailedRows`, `TotientAsymptotic_FordBandExponent`, `TotientAsymptotic_FordBandGeometry`, `TotientAsymptotic_FordBandNormality`, `TotientAsymptotic_FordBandSupports`, `TotientAsymptotic_FordFactorization`, `TotientAsymptotic_FordInitialCount`, `TotientAsymptotic_FordInitialFactor`, `TotientAsymptotic_FordLargePrimeCount`, `TotientAsymptotic_FordSimplexEmbedding`, `TotientAsymptotic_FordStateIteration`, `TotientAsymptotic_FordTerminalMass`, `TotientAsymptotic_FullBoxConcentration`, `TotientAsymptotic_FullPrefixRatio`, `TotientAsymptotic_FullPrimeGrid`, `TotientAsymptotic_FullWitnessWeight`, `TotientAsymptotic_GeometricContractedFamily`, `TotientAsymptotic_GeometricCube`, `TotientAsymptotic_GeometricPrimeMass`, `TotientAsymptotic_GoodTuples`, `TotientAsymptotic_GridApproximation`, `TotientAsymptotic_GridVolume`, `TotientAsymptotic_HeadLimitedFamily`, `TotientAsymptotic_HeadLimitedPrimeMass`, `TotientAsymptotic_HeadSquareCase`, `TotientAsymptotic_HeadSquareDiscard`, `TotientAsymptotic_HeadSquareSum`, `TotientAsymptotic_HeavyOmegaMoment`, `TotientAsymptotic_InitialRoughData`, `TotientAsymptotic_InitialRoughEncoding`, `TotientAsymptotic_IntersectionLimit`, `TotientAsymptotic_IntervalOmegaMoment`, `TotientAsymptotic_IntervalSieveDenominator`, `TotientAsymptotic_IntervalSieveModel`, `TotientAsymptotic_LargeFactorNormalityCount`, `TotientAsymptotic_LargeNonNormalValues`, `TotientAsymptotic_LeastPrefix`, `TotientAsymptotic_LocalBadCandidates`, `TotientAsymptotic_LocalBadCover`, `TotientAsymptotic_LocalCandidateAbundance`, `TotientAsymptotic_LocalFullCandidateCount`, `TotientAsymptotic_LocalNormalCandidates`, `TotientAsymptotic_LocalNormalityDecay`, `TotientAsymptotic_LocalNormalityDiscard`, `TotientAsymptotic_LocalNormalityLayer`, `TotientAsymptotic_LocalPrimeGrid`, `TotientAsymptotic_LocalPrimeSupport`, `TotientAsymptotic_LocalRegularPrimeMass`, `TotientAsymptotic_LocalResidualExceptionData`, `TotientAsymptotic_LocalSquareCutoff`, `TotientAsymptotic_LocalSuffixComparisonData`, `TotientAsymptotic_LocalSuffixFamily`, `TotientAsymptotic_LocallyConcentratedFamily`, `TotientAsymptotic_LoglogGrid`, `TotientAsymptotic_LowerPrimeCutoff`, `TotientAsymptotic_Mass`, `TotientAsymptotic_MassMajorant`, `TotientAsymptotic_MassTailSupport`, `TotientAsymptotic_MassUpper`, `TotientAsymptotic_MertensEuler`, `TotientAsymptotic_MovingSmoothCutoff`, `TotientAsymptotic_NormalBandExponent`, `TotientAsymptotic_NormalBandValueCount`, `TotientAsymptotic_NormalHeadDiscard`, `TotientAsymptotic_NormalInternalDiscard`, `TotientAsymptotic_NormalRemainderLayer`, `TotientAsymptotic_NormalityAlignment`, `TotientAsymptotic_NormalityComplement`, `TotientAsymptotic_NormalityDiscard`, `TotientAsymptotic_NormalityGrid`, `TotientAsymptotic_NormalityGridCell`, `TotientAsymptotic_NormalityGridEnvelope`, `TotientAsymptotic_NormalityGridMass`, `TotientAsymptotic_NormalityTilt`, `TotientAsymptotic_Normalization`, `TotientAsymptotic_NormalizedComparison`, `TotientAsymptotic_NormalizedConcentration`, `TotientAsymptotic_NormalizedShell`, `TotientAsymptotic_NormalizedStrictSlack`, `TotientAsymptotic_OmegaDiscard`, `TotientAsymptotic_OmegaInternalDiscard`, `TotientAsymptotic_OmegaPrimeMass`, `TotientAsymptotic_OmegaReciprocal`, `TotientAsymptotic_OmegaRemainderLayer`, `TotientAsymptotic_OrderedFactorizations`, `TotientAsymptotic_OrderedTranslateVolume`, `TotientAsymptotic_PPTActualResidual`, `TotientAsymptotic_PPTBadWitness`, `TotientAsymptotic_PPTCancelCoordinates`, `TotientAsymptotic_PPTComparisonAssembly`, `TotientAsymptotic_PPTComparisonGrid`, `TotientAsymptotic_PPTComparisonScaleDecay`, `TotientAsymptotic_PPTComparisonSum`, `TotientAsymptotic_PPTFactorLabels`, `TotientAsymptotic_PPTFiniteLabels`, `TotientAsymptotic_PPTHeadEdge`, `TotientAsymptotic_PPTHeadSelectedGrid`, `TotientAsymptotic_PPTLocalDimension`, `TotientAsymptotic_PPTLocalValueEnvelope`, `TotientAsymptotic_PPTMaximalSuffix`, `TotientAsymptotic_PPTPrefixEquation`, `TotientAsymptotic_PPTPrefixGrouping`, `TotientAsymptotic_PPTStructureInput`, `TotientAsymptotic_PPTTailAlignment`, `TotientAsymptotic_PPTTotientSquare`, `TotientAsymptotic_PPTWitnessCount`, `TotientAsymptotic_PairedComparisonGrid`, `TotientAsymptotic_PerturbationCost`, `TotientAsymptotic_PhaseBandTransfer`, `TotientAsymptotic_PositiveCoordinateGrid`, `TotientAsymptotic_PositiveSquareDiscard`, `TotientAsymptotic_PrefixBoxGrid`, `TotientAsymptotic_PrefixGapWeights`, `TotientAsymptotic_PrefixGeometry`, `TotientAsymptotic_PrefixPreimage`, `TotientAsymptotic_PrefixProjection`, `TotientAsymptotic_PrefixReciprocals`, `TotientAsymptotic_PrefixRelaxation`, `TotientAsymptotic_PrefixSize`, `TotientAsymptotic_PrefixWeight`, `TotientAsymptotic_PrefixWeights`, `TotientAsymptotic_PrimeBox`, `TotientAsymptotic_PrimeBoxGeometry`, `TotientAsymptotic_PrimeDiscardCutoff`, `TotientAsymptotic_PrimeDivisorValueCount`, `TotientAsymptotic_PrimeExtensionCount`, `TotientAsymptotic_PrimeFactorBands`, `TotientAsymptotic_PrimeGrid`, `TotientAsymptotic_PrimeInterval`, `TotientAsymptotic_PrimeIntervalMass`, `TotientAsymptotic_PrimeMassSplit`, `TotientAsymptotic_PrimeProductValueMass`, `TotientAsymptotic_ProjectedGrid`, `TotientAsymptotic_ProjectedMass`, `TotientAsymptotic_PublishedComparison`, `TotientAsymptotic_PublishedConcentration`, `TotientAsymptotic_PublishedFiber`, `TotientAsymptotic_PublishedNormality`, `TotientAsymptotic_PublishedPrimeCount`, `TotientAsymptotic_QuarterPowerBudget`, `TotientAsymptotic_RegularValueCount`, `TotientAsymptotic_RemainderSplit`, `TotientAsymptotic_RemovePrimeFactor`, `TotientAsymptotic_Renewal`, `TotientAsymptotic_RenewalBackground`, `TotientAsymptotic_RenewalConvolution`, `TotientAsymptotic_RenewalKernel`, `TotientAsymptotic_RenewalMoment`, `TotientAsymptotic_RenewalSeriesAlgebra`, `TotientAsymptotic_RenewalTail`, `TotientAsymptotic_ResidualTupleRecovery`, `TotientAsymptotic_RestoreCommonPrefix`, `TotientAsymptotic_RestrictedPrimeGrid`, `TotientAsymptotic_RestrictedWitnessCount`, `TotientAsymptotic_RowCutoffModel`, `TotientAsymptotic_Scaling`, `TotientAsymptotic_ShellCost`, `TotientAsymptotic_ShiftDivisorMass`, `TotientAsymptotic_ShiftedPrimeCount`, `TotientAsymptotic_ShiftedSieveCRT`, `TotientAsymptotic_ShiftedSieveCount`, `TotientAsymptotic_ShiftedSieveDenominator`, `TotientAsymptotic_ShiftedSieveModel`, `TotientAsymptotic_ShiftedSieveRoots`, `TotientAsymptotic_SieveCutoff`, `TotientAsymptotic_SimplexScaling`, `TotientAsymptotic_SimplexShell`, `TotientAsymptotic_SimplexTilt`, `TotientAsymptotic_SimplexVolume`, `TotientAsymptotic_SmoothCofactorMoment`, `TotientAsymptotic_SmoothResidualMass`, `TotientAsymptotic_SmoothTerminalEncoding`, `TotientAsymptotic_SquareDiscard`, `TotientAsymptotic_SquareInternalDiscard`, `TotientAsymptotic_SquareLayerSum`, `TotientAsymptotic_SquareRemainderLayer`, `TotientAsymptotic_StrictContractionCost`, `TotientAsymptotic_StrictPrefixContraction`, `TotientAsymptotic_StrictSlackCost`, `TotientAsymptotic_StrictSlackDiscard`, `TotientAsymptotic_StrictSlackEnclosure`, `TotientAsymptotic_StrictSlackShell`, `TotientAsymptotic_StructuralInput`, `TotientAsymptotic_StructuredRemainder`, `TotientAsymptotic_SuffixFactorization`, `TotientAsymptotic_SurvivingBlockSize`, `TotientAsymptotic_SurvivingCollision`, `TotientAsymptotic_TailArray`, `TotientAsymptotic_TailBounds`, `TotientAsymptotic_TailBoxAggregation`, `TotientAsymptotic_TailBoxCoordinates`, `TotientAsymptotic_TailCofactor`, `TotientAsymptotic_TailEncoding`, `TotientAsymptotic_TailHeadCount`, `TotientAsymptotic_TailRenewal`, `TotientAsymptotic_TailVolume`, `TotientAsymptotic_TerminalMassSeries`, `TotientAsymptotic_TerminalStateCount`, `TotientAsymptotic_TotientCountingEnvelope`, `TotientAsymptotic_TripleDiscriminant`, `TotientAsymptotic_TripleSieveCRT`, `TotientAsymptotic_TripleSieveCount`, `TotientAsymptotic_TripleSieveDenominator`, `TotientAsymptotic_TripleSieveModel`, `TotientAsymptotic_TripleSieveRoots`, `TotientAsymptotic_TruncatedConcentration`, `TotientAsymptotic_TupleCounting`, `TotientAsymptotic_TupleMassApproximation`, `TotientAsymptotic_TupleRecovery`, `TotientAsymptotic_TupleSuffix`, `TotientAsymptotic_TupleTotients`, `TotientAsymptotic_TwoBandCount`, `TotientAsymptotic_TwoCoordinateCount`, `TotientAsymptotic_TwoPrimeResidualMass`, `TotientAsymptotic_UnbandedCube`, `TotientAsymptotic_UnbandedPrimeGrid`, `TotientAsymptotic_UniformPrefactor`, `TotientAsymptotic_UnionVolume`, `TotientAsymptotic_UniquePrefix`, `TotientAsymptotic_UntruncatedRemainder`, `TotientAsymptotic_ValueOmega`, `TotientAsymptotic_VolumeComparison`, `TotientAsymptotic_WeightedFiber`, `TotientAsymptotic_WeightedMass`, `TotientAsymptotic_WeightedPrimeSet`, `TotientAsymptotic_WitnessAggregation`, `TotientAsymptotic_WitnessCollision`, `TotientAsymptotic_WitnessGrid`, `TotientAsymptotic_WitnessPrefix`, `TotientAsymptotic_WitnessUnionLoss`, `Wiener`.
--
--   **Imports.** It imports the published bundle `Def_TotientAsymptotic`.
--
--   **Imported by** (directly, in this split): the statements `OAI.TotientAsymptotic.actual_block_count`, `OAI.TotientAsymptotic.actual_collision_exponent`, `OAI.TotientAsymptotic.actual_comparison_parameters`, `OAI.TotientAsymptotic.actual_positive_collision_count`, `OAI.TotientAsymptotic.ambient_nonnormal_witness_count`, `OAI.TotientAsymptotic.bad_tuple_discard`, `OAI.TotientAsymptotic.basic_exception_values_negligible`, `OAI.TotientAsymptotic.bootstrap_good_nat_count`, `OAI.TotientAsymptotic.bootstrap_good_value_discard`, `OAI.TotientAsymptotic.bounded_ratio_tuple_weight`, `OAI.TotientAsymptotic.candidate_count_comparison`, `OAI.TotientAsymptotic.candidate_mass_normalized`, `OAI.TotientAsymptotic.candidate_prime_mass_relative`, `OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass`, `OAI.TotientAsymptotic.common_largest_prime_squarefree_mass_bound`, `OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure`, `OAI.TotientAsymptotic.conditional_companion_additive`, `OAI.TotientAsymptotic.conditional_companion_theorem_of_structure`, `OAI.TotientAsymptotic.conditional_main_theorem_of_structure`, `OAI.TotientAsymptotic.coordinate_violation_count`, `OAI.TotientAsymptotic.counting_envelope_real_bound`, `OAI.TotientAsymptotic.exceptional_row_reciprocal_mass`, `OAI.TotientAsymptotic.extractedStructureInput`, `OAI.TotientAsymptotic.failed_row_count_bound`, `OAI.TotientAsymptotic.failed_row_value_count`, `OAI.TotientAsymptotic.fixed_coordinate_grid_bound`, `OAI.TotientAsymptotic.fordCoordinateConcentrationInput`, `OAI.TotientAsymptotic.fordLemma26Input`, `OAI.TotientAsymptotic.ford_raw_count`, `OAI.TotientAsymptotic.ford_raw_count_one`, `OAI.TotientAsymptotic.ford_state_iteration`, `OAI.TotientAsymptotic.ford_structure_value_count`, `OAI.TotientAsymptotic.full_coordinate_count`, `OAI.TotientAsymptotic.full_fiber_scale_family`, `OAI.TotientAsymptotic.full_fiber_scale_of_local_count`, `OAI.TotientAsymptotic.geometric_initial_mass_le_base`, `OAI.TotientAsymptotic.geometric_suffix_mass`, `OAI.TotientAsymptotic.head_square_tuple_discard`, `OAI.TotientAsymptotic.local_bad_suffix_exception_data`, `OAI.TotientAsymptotic.local_full_candidate_count`, `OAI.TotientAsymptotic.local_nonnormal_residual_mass`, `OAI.TotientAsymptotic.local_normal_candidate_abundance`, `OAI.TotientAsymptotic.local_original_count_of_regular`, `OAI.TotientAsymptotic.local_regular_prime_mass`, `OAI.TotientAsymptotic.locally_concentrated_volume_lower`, `OAI.TotientAsymptotic.mass_volume_coefficient_approximation`, `OAI.TotientAsymptotic.normal_internal_reciprocal_discard`, `OAI.TotientAsymptotic.normality_tuple_discard`, `OAI.TotientAsymptotic.omega_internal_reciprocal_discard`, `OAI.TotientAsymptotic.ppt_fixed_bad_coordinate_value_count`, `OAI.TotientAsymptotic.ppt_original_regular_count`, `OAI.TotientAsymptotic.ppt_regular_geometric_count`, `OAI.TotientAsymptotic.ppt_regular_geometric_witness`, `OAI.TotientAsymptotic.ppt_regular_head_witness`, `OAI.TotientAsymptotic.real_coordinate_deviation`, `OAI.TotientAsymptotic.small_head_real_gaussian`, `OAI.TotientAsymptotic.small_terminal_row_count`, `OAI.TotientAsymptotic.square_remainder_case_mass`, `OAI.TotientAsymptotic.strict_slack_tuple_discard`, `OAI.TotientAsymptotic.terminal_band_value_count`, `OAI.TotientAsymptotic.terminal_prefix_mass_count`, `OAI.TotientAsymptotic.tuple_mass_normalized_approximation`, `OAI.TotientAsymptotic.two_coordinate_violation_count`, `OAI.TotientAsymptotic.uncovered_values_negligible`, `OAI.TotientAsymptotic.weighted_boundary_grid_error` and `OAI.TotientAsymptotic.weighted_union_band_removal`; the proofs of `OAI.TotientAsymptotic.actual_block_count`, `OAI.TotientAsymptotic.actual_collision_exponent`, `OAI.TotientAsymptotic.actual_comparison_parameters`, `OAI.TotientAsymptotic.actual_positive_collision_count`, `OAI.TotientAsymptotic.ambient_nonnormal_witness_count`, `OAI.TotientAsymptotic.bad_tuple_discard`, `OAI.TotientAsymptotic.basic_exception_values_negligible`, `OAI.TotientAsymptotic.bootstrap_good_nat_count`, `OAI.TotientAsymptotic.bootstrap_good_value_discard`, `OAI.TotientAsymptotic.bounded_ratio_tuple_weight`, `OAI.TotientAsymptotic.candidate_count_comparison`, `OAI.TotientAsymptotic.candidate_mass_normalized`, `OAI.TotientAsymptotic.candidate_prime_mass_relative`, `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass`, `OAI.TotientAsymptotic.common_largest_prime_squarefree_mass_bound`, `OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure`, `OAI.TotientAsymptotic.conditional_companion_additive`, `OAI.TotientAsymptotic.conditional_companion_theorem_of_structure`, `OAI.TotientAsymptotic.conditional_main_theorem_of_structure`, `OAI.TotientAsymptotic.coordinate_violation_count`, `OAI.TotientAsymptotic.counting_envelope_real_bound`, `OAI.TotientAsymptotic.exceptional_row_reciprocal_mass`, `OAI.TotientAsymptotic.extractedStructureInput`, `OAI.TotientAsymptotic.failed_row_count_bound`, `OAI.TotientAsymptotic.failed_row_value_count`, `OAI.TotientAsymptotic.fixed_coordinate_grid_bound`, `OAI.TotientAsymptotic.fordCoordinateConcentrationInput`, `OAI.TotientAsymptotic.fordLemma26Input`, `OAI.TotientAsymptotic.ford_raw_count`, `OAI.TotientAsymptotic.ford_raw_count_one`, `OAI.TotientAsymptotic.ford_scale_lower`, `OAI.TotientAsymptotic.ford_state_iteration`, `OAI.TotientAsymptotic.ford_structure_value_count`, `OAI.TotientAsymptotic.full_coordinate_count`, `OAI.TotientAsymptotic.full_fiber_scale_family`, `OAI.TotientAsymptotic.full_fiber_scale_of_local_count`, `OAI.TotientAsymptotic.geometric_initial_mass_le_base`, `OAI.TotientAsymptotic.geometric_suffix_mass`, `OAI.TotientAsymptotic.head_square_tuple_discard`, `OAI.TotientAsymptotic.local_bad_suffix_exception_data`, `OAI.TotientAsymptotic.local_full_candidate_count`, `OAI.TotientAsymptotic.local_nonnormal_residual_mass`, `OAI.TotientAsymptotic.local_normal_candidate_abundance`, `OAI.TotientAsymptotic.local_original_count_of_regular`, `OAI.TotientAsymptotic.local_regular_prime_mass`, `OAI.TotientAsymptotic.locally_concentrated_volume_lower`, `OAI.TotientAsymptotic.mass_volume_coefficient_approximation`, `OAI.TotientAsymptotic.normal_internal_reciprocal_discard`, `OAI.TotientAsymptotic.normality_tuple_discard`, `OAI.TotientAsymptotic.omega_internal_reciprocal_discard`, `OAI.TotientAsymptotic.ppt_fixed_bad_coordinate_value_count`, `OAI.TotientAsymptotic.ppt_original_regular_count`, `OAI.TotientAsymptotic.ppt_regular_geometric_count`, `OAI.TotientAsymptotic.ppt_regular_geometric_witness`, `OAI.TotientAsymptotic.ppt_regular_head_witness`, `OAI.TotientAsymptotic.real_coordinate_deviation`, `OAI.TotientAsymptotic.small_head_real_gaussian`, `OAI.TotientAsymptotic.small_terminal_row_count`, `OAI.TotientAsymptotic.smooth_terminal_mass_bound`, `OAI.TotientAsymptotic.square_remainder_case_mass`, `OAI.TotientAsymptotic.strict_slack_tuple_discard`, `OAI.TotientAsymptotic.terminal_band_value_count`, `OAI.TotientAsymptotic.terminal_prefix_mass_count`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.tuple_mass_normalized_approximation`, `OAI.TotientAsymptotic.two_coordinate_violation_count`, `OAI.TotientAsymptotic.uncovered_values_negligible`, `OAI.TotientAsymptotic.weighted_boundary_grid_error`, `OAI.TotientAsymptotic.weighted_totient_asymptotic`, `OAI.TotientAsymptotic.weighted_totient_one_two` and `OAI.TotientAsymptotic.weighted_union_band_removal`.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Fin.Tuple
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic

section
-- module Solutions.OAIQ233_TA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ233_TA.Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance instCoeFunForallReal : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance instCoeRealComplex : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance instNeg : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance instHSMulReal : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

end CS

namespace trunc

instance instCoeFunForallReal : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance instCoeCSOfNatNatReal : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

end trunc

namespace W1

instance instCoeFunForallReal : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (_root_.deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (_root_.deriv g) := hg.iterate_deriv' n 1
    have hfg : _root_.deriv (f - g) = _root_.deriv f - _root_.deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance instSub : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

noncomputable instance instNorm : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance instCoeSchwartzMapRealComplex : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance instCoeCSOfNatNatComplex : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance instHMulCSOfNatNatComplex : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance instHMulCSOfNatNatRealComplex : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

end W21
end

section
-- module Solutions.OAIQ233_TA.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

local instance instCoeForallRealForallComplex_solutions_rb9581e_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simpa using Circle.norm_coe z)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

local instance instCoeForallRealForallComplex_solutions_rb9581e_2 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
end

section
-- module Solutions.OAIQ233_TA.IEANTN_Mertens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace Mertens



open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

attribute [fun_prop] measurable_from_top

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

end Mertens
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_AuxResults
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace Aux

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩


end Aux
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Basic
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => SelbergSieve.selbergTerms s

theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

end LambdaSquared

end SelbergSieve
end
end

section
-- module Solutions.OAIQ233_TA.Mathlib_NumberTheory_Sieve_Selberg
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

end SelbergSieve
end
end

section
-- module Solutions.OAIQ233_TA.SmoothExistence
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic data and renewal coefficients for counting totient values. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic



def R (x : ℝ) (H : ℕ) : ℕ := m x - H
def L (x : ℝ) (H : ℕ) : ℕ := m x - P H

def bandScale (x : ℝ) (i : ℕ) : ℝ :=
  alpha (theta x) * (m x-i : ℕ) * (rho^(m x-i))⁻¹

def xi (x : ℝ) (i : ℕ) : ℝ :=
  1 + (1/10000 : ℝ) * Real.exp (-((m x-i : ℕ) : ℝ) / 40)

structure RemainderDatum (L : ℕ) where
  primes : Fin L → ℕ
  cofactor : ℕ

def remainderPrime {J : ℕ} (η : RemainderDatum J) (i : ℕ) : ℕ :=
  if hi : 1 ≤ i ∧ i ≤ J then η.primes ⟨i-1, by omega⟩ else 1

def remainderCoord {J : ℕ} (x : ℝ) (η : RemainderDatum J) (i : ℕ) : ℝ :=
  if i = 0 then B x else Real.log (Real.log (remainderPrime η i : ℝ))

def IsBasicRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  0 < η.cofactor ∧
  (∀ i ∈ Finset.Icc 1 (L x H),
    (remainderPrime η i).Prime ∧
    (9/10 : ℝ) * bandScale x i ≤ remainderCoord x η i ∧
    remainderCoord x η i ≤ (11/10 : ℝ) * bandScale x i) ∧
  (∀ i ∈ Finset.Icc 0 (L x H),
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i) * remainderCoord x η r) ≤
      (if i = L x H then 1 else xi x i) * remainderCoord x η i) ∧
  largestPrimeFactor η.cofactor ≤ remainderPrime η (L x H) ∧
  Real.log (η.cofactor : ℝ) ≤ Real.exp (2 * bandScale x (L x H))

def remainderTail (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : ℕ :=
  η.cofactor * ∏ i ∈ Finset.Icc (R x H+1) (L x H), remainderPrime η i

structure PrefixDatum (R : ℕ) where
  primes : Fin R → ℕ
  d : ℕ

def IsPrefixDatum (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) : Prop :=
  ∃ η : RemainderDatum (L x H), IsBasicRemainder x H η ∧
    (remainderTail x H η).totient = ζ.d ∧
    ∀ i : Fin (R x H), ζ.primes i = remainderPrime η (i.val+1)

def M (x : ℝ) (H : ℕ) (f : ℝ → ℝ) : ℝ := by
  classical
  exact ∑ᶠ ζ : PrefixDatum (R x H),
    if IsPrefixDatum x H ζ then
      f ((ell ζ.d : ℝ) / ζ.d) / ((ζ.d : ℝ) * ∏ i : Fin (R x H), (ζ.primes i - 1 : ℕ))
    else 0

def massError (x : ℝ) (H : ℕ) (t : ℝ) : ℝ :=
  V t * Real.log x / (t * G x (m x)) - M x H (fun _ => 1) / G x (m x)



end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The published comparison input for the conditional collision proof.

Kevin Ford, *The distribution of totients*, Ramanujan J. 2 (1998), 67–151,
revised arXiv:1104.3264v2 (14 July 2013), Lemma 5.1, pp. 21–22.
The published statement permits `k ≥ 1`, including a single surviving
prime. The author-hosted copy also makes this endpoint explicit:
https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf (Lemma 5.1).
We use its specialization with no auxiliary factors (`l = 0`) and with
the entire left shifted product squarefree above the terminal cutoff. The
latter is already part of the application’s good-witness conditions. All its
cutoff, small-remainder, small-cancelled-product and separation hypotheses
are retained here. Its larger smooth-factor exponent is sufficient for the
application; we do not assume the new comparison proposition of the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def omegaIn (n : ℕ) (U T : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun (p : ℕ) => U < (p : ℝ) ∧ (p : ℝ) ≤ T)).length

/-- Ford's Definition 1, equations (2.1)–(2.2). -/
def IsNormalPrime (S : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ (omegaIn (p-1) 1 S : ℝ) ≤ 2 * B S ∧
  ∀ U T : ℝ, S ≤ U → U < T → T ≤ (p-1 : ℕ) →
    |(omegaIn (p-1) U T : ℝ) - (B T-B U)| < Real.sqrt (B S * B T)

def SquarefreeAbove (n : ℕ) (Z : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → Z < p → ¬ p^2 ∣ n

def partAbove (n : ℕ) (Z : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun (p : ℕ) => Z < (p : ℝ))).prod

structure ShiftedPair (b : ℕ) where
  left : Fin b → ℕ
  right : Fin b → ℕ
  remainder : ℕ

def shiftedProduct {b : ℕ} (p : Fin b → ℕ) : ℕ := ∏ i, (p i-1)

def FordComparisonConditions (b : ℕ) (y S : ℝ) (D r : ℕ)
    (Y U : ℕ → ℝ) (t : ShiftedPair b) : Prop :=
  0 < t.remainder ∧
  (∀ j : Fin b,
    IsNormalPrime S (t.left j) ∧ IsNormalPrime S (t.right j) ∧
    t.left j ≠ t.right j ∧
    U j ≤ largestPrimeFactor (t.left j-1) ∧
    (largestPrimeFactor (t.left j-1) : ℝ) ≤ Y j ∧
    U j ≤ largestPrimeFactor (t.right j-1) ∧
    (largestPrimeFactor (t.right j-1) : ℝ) ≤ Y j ∧
    SquarefreeAbove (t.left j-1) (Y b) ∧
    SquarefreeAbove (t.right j-1) (Y b)) ∧
  D * shiftedProduct t.left = t.remainder * shiftedProduct t.right ∧
  (D * shiftedProduct t.left : ℕ) ≤ y / r ∧
  (largestPrimeFactor t.remainder : ℝ) ≤ Y b ∧
  (∀ hb : 0 < b, (partAbove (t.left ⟨0, hb⟩-1) (Y 1) : ℝ) > Real.sqrt y) ∧
  SquarefreeAbove (shiftedProduct t.left) (Y b)

/-- The cutoff and size restrictions of Ford's published lemma. -/
def FordComparisonParameters (b : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ) : Prop :=
  1 ≤ b ∧ Y 0 = y ∧ Real.exp (Real.exp 1) ≤ S ∧ S ≤ Y b ∧
  (∀ j ∈ Finset.range b, Y (j+1) < U j ∧ U j < Y j) ∧
  Y 1 ≤ y ^ (1 / (10 * B y)) ∧
  (∀ j ∈ Finset.Icc 2 b, 2 * Real.sqrt (B S / B y) <
    B (Y (j-1)) / B y - B (Y j) / B y) ∧
  1 ≤ D ∧ (D : ℝ) ≤ y ^ (1/100 : ℝ) ∧
  (largestPrimeFactor D : ℝ) ≤ Y b ∧
  1 ≤ r ∧ (r : ℝ) ≤ y ^ (1/10 : ℝ)

def comparisonError (b : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.Icc 1 (b-1), (B (Y j) / B y - B (U j) / B y) +
    Real.sqrt (B S / B y) * ∑ i ∈ Finset.Icc 2 b,
      ((i : ℝ) * Real.log i + i)

def fordComparisonBound (C : ℝ) (b : ℕ) (y S : ℝ) (D r : ℕ)
    (Y U : ℕ → ℝ) : ℝ :=
  y / (D*r) * (C * B y)^(6*b) * (b+1 : ℝ)^D.primeFactorsList.length *
    (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1) *
    (Real.log y)^(-2 + (∑ j ∈ Finset.Icc 1 (b-1), a j * (B (Y j) / B y)) +
      comparisonError b y S Y U)


def FordLemma51Input : Prop :=
  ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ (b : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters b y S D r Y U →
      ∀ T : Finset (ShiftedPair b),
        (∀ t ∈ T, FordComparisonConditions b y S D r Y U t) →
        (T.card : ℝ) ≤ fordComparisonBound C b y S D r Y U

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omegaIn_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (U T : ℝ) :
    omegaIn (n*m) U T = omegaIn n U T + omegaIn m U T := by
  unfold omegaIn
  have h := (Nat.perm_primeFactorsList_mul hn hm).filter
    (fun p : ℕ => decide (U < (p : ℝ) ∧ (p : ℝ) ≤ T))
  simpa using h.length_eq

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact double-logarithmic grid for reducing normality to finitely many intervals. -/
noncomputable section
namespace TotientAsymptotic

def normalityGridPoint (j : ℕ) : ℝ := Real.exp (Real.exp j)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common integer endpoint for every interval in the normality grid. -/
noncomputable section
namespace TotientAsymptotic

def normalityGridEnvelope (x : ℝ) : ℕ :=
  ⌈normalityGridPoint (⌊B x⌋₊+1)⌉₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.W21.instNorm
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence, uniqueness and positivity of the renewal parameters. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma a_eq_integral (j : ℕ) :
    a j = ∫ t in (j : ℝ)..(j+1 : ℝ), Real.log t := by
  rw [integral_log]
  unfold a
  ring

lemma a_pos {j : ℕ} (hj : 1 ≤ j) : 0 < a j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  apply intervalIntegral.integral_pos (by linarith)
  · exact continuousOn_id.log fun x hx => by
      change x ≠ 0
      exact ne_of_gt (by linarith [hx.1])
  · intro x hx
    exact (Real.log_pos (by linarith [hx.1])).le
  · exact ⟨j+1, ⟨by linarith, le_rfl⟩, Real.log_pos (by linarith)⟩

lemma a_le_log {j : ℕ} (hj : 1 ≤ j) : a j ≤ Real.log (j+1 : ℝ) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  have hh := intervalIntegral.integral_mono_on (a := (j : ℝ)) (b := (j+1 : ℝ))
    (by linarith) intervalIntegral.intervalIntegrable_log'
    (intervalIntegrable_const (c := Real.log (j+1 : ℝ)))
    (fun x hx => Real.log_le_log (by linarith [hx.1]) hx.2)
  simpa using hh

lemma a_le_index {j : ℕ} (hj : 1 ≤ j) : a j ≤ (j : ℝ) := by
  have hh := Real.log_le_sub_one_of_pos (x := (j+1 : ℝ)) (by positivity)
  exact (a_le_log hj).trans (by linarith)

def renewalSeries (r : ℝ) : ℝ := ∑' n : ℕ, a (n+1) * r^(n+1)

lemma summable_index_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => (n+1 : ℝ)^k * r^(n+1)) := by
  have hh : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^k * r^(n+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^k * r^n) 1).2
    (summable_pow_mul_geometric_of_norm_lt_one k
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1))
  simpa only [Nat.cast_add, Nat.cast_one] using hh

lemma summable_renewal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => a (n+1) * r^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (a_pos (by omega)).le (pow_nonneg hr0 _))
    (fun n => mul_le_mul_of_nonneg_right (a_le_index (by omega)) (pow_nonneg hr0 _))
  simpa using summable_index_geometric hr0 hr1 1

lemma renewalSeries_continuousOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn renewalSeries (Set.Icc 0 r) := by
  apply continuousOn_tsum (u := fun n : ℕ => (n+1 : ℝ) * r^(n+1))
  · intro n
    fun_prop
  · simpa using summable_index_geometric hr0 hr1 1
  · intro n z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (a_pos (by omega)).le
      (pow_nonneg hz.1 _))]
    exact mul_le_mul (by exact_mod_cast a_le_index (j := n+1) (by omega))
      (pow_le_pow_left₀ hz.1 hz.2 _) (pow_nonneg hz.1 _) (by positivity)

lemma renewalSeries_strictMonoOn : StrictMonoOn renewalSeries (Set.Ico 0 1) := by
  intro x hx y hy hxy
  apply Summable.tsum_lt_tsum (i := 0)
  · intro n
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy.le _) (a_pos (by omega)).le
  · simpa using mul_lt_mul_of_pos_left hxy (a_pos (j := 1) le_rfl)
  · exact summable_renewal hx.1 hx.2
  · exact summable_renewal hy.1 hy.2

@[simp] lemma renewalSeries_zero : renewalSeries 0 = 0 := by
  simp [renewalSeries]

lemma renewalSeries_nine_tenths_gt_one : 1 < renewalSeries (9/10) := by
  have hs := summable_renewal (r := 9/10) (by norm_num) (by norm_num)
  have h := hs.sum_le_tsum (Finset.range 2)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (9/10) at h
  norm_num [Finset.sum_range_succ, a] at h
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem renewal_root_exists_unique : ∃! z : ℝ, z ∈ RenewalRootSet := by
  have hc := renewalSeries_continuousOn (r := 9/10) (by norm_num) (by norm_num)
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 9/10)
    (by norm_num) hc ⟨by simp, renewalSeries_nine_tenths_gt_one.le⟩
  have hz0 : 0 < z := by
    have hz_ne : z ≠ 0 := by
      intro h
      subst z
      simp at heq
    exact lt_of_le_of_ne hz.1 (Ne.symm hz_ne)
  have hz1 : z < 1 := lt_of_le_of_lt hz.2 (by norm_num)
  refine ⟨z, ⟨hz0, hz1, heq⟩, ?_⟩
  intro y hy
  have hy' : renewalSeries y = renewalSeries z := hy.2.2.trans heq.symm
  exact renewalSeries_strictMonoOn.injOn ⟨hy.1.le, hy.2.1⟩ ⟨hz0.le, hz1⟩ hy'

lemma rho_mem : rho ∈ RenewalRootSet := by
  obtain ⟨z, hz, hzunique⟩ := renewal_root_exists_unique
  have hs : RenewalRootSet = {z} := Set.eq_singleton_iff_unique_mem.mpr ⟨hz, hzunique⟩
  unfold rho
  rw [hs, csInf_singleton]
  simp

lemma rho_pos : 0 < rho := rho_mem.1
lemma rho_lt_one : rho < 1 := rho_mem.2.1

lemma lam_pos : 0 < lam := by
  apply Real.log_pos
  exact (lt_div_iff₀ rho_pos).2 (by simpa using rho_lt_one)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuralInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal structural inputs from Ford, *The distribution of totients*,
arXiv:1104.3264v2 (14 July 2013), Theorems 10 and 16.

The exceptional sets count values with **some** failing preimage, as in the
convention preceding Theorem 10, p. 5.  Consequently every preimage of a value
outside the exceptional set satisfies the property.  Ford's coordinates in
(4.2), p. 17, are clamped double logarithms.  Theorem 16, (6.1)--(6.2), p. 29,
also supplies the terminal lower bound that allows removing this clamp.

The band center below is Ford's B*rho^i*(1-i/m), not the phase-dependent
`bandScale` in Basic.lean.  Passing between these two centers is an additional
analytic step, governed by the manuscript's equation alpha-comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- Prime factors with multiplicity, largest first, padded by 1. -/
def fordPrime (n i : ℕ) : ℕ := (n.primeFactorsList.reverse[i]?).getD 1

def primeDoubleLog (n i : ℕ) : ℝ := Real.log (Real.log (fordPrime n i : ℝ))

def fordPrimeCoordinate (n i : ℕ) : ℝ := max 0 (primeDoubleLog n i)

def fordBandScale (x : ℝ) (i : ℕ) : ℝ :=
  B x * rho^i * (1 - (i : ℝ) / m x)

def preimageExceptionValues (x : ℝ) (Q : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x⌋₊).filter
    (fun v => ∃ n : ℕ, 0 < n ∧ n.totient = v ∧ ¬ Q n)

def preimageExceptionCount (x : ℝ) (Q : ℕ → Prop) : ℝ :=
  (preimageExceptionValues x Q).card

def fordSimplexCoordinate (x : ℝ) (n i : ℕ) : ℝ :=
  if i = 0 then B x else fordPrimeCoordinate n i

def rawSimplexCoordinate (x : ℝ) (n i : ℕ) : ℝ :=
  if i = 0 then B x else primeDoubleLog n i

/-- The needed consequence of membership in Ford's S_L(xi).  It retains
the last adjacent inequality with coefficient 1 and coordinate ordering. -/
def fordSimplexCondition (x : ℝ) (Ψ n : ℕ) : Prop :=
  let J := m x-Ψ
  2 < fordPrimeCoordinate n J ∧
  (∀ i ∈ Finset.Icc 1 J,
    fordPrimeCoordinate n J ≤ fordPrimeCoordinate n i ∧ fordPrimeCoordinate n i ≤ B x) ∧
  ∀ i ∈ Finset.Ico 0 J,
    (if i+1 = J then fordSimplexCoordinate x n J
     else ∑ r ∈ Finset.Icc (i+1) J, a (r-i) * fordSimplexCoordinate x n r) ≤
      xi x i * fordSimplexCoordinate x n i

/-- The weaker, unclamped simplex used in equation ford-simplex of the manuscript. -/
def extractedSimplexCondition (x : ℝ) (Ψ n : ℕ) : Prop :=
  let J := m x-Ψ
  2 < primeDoubleLog n J ∧
  ∀ i ∈ Finset.Ico 0 J,
    (∑ r ∈ Finset.Icc (i+1) J, a (r-i) * rawSimplexCoordinate x n r) ≤
      xi x i * rawSimplexCoordinate x n i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The comparison of the exact Ford band centers with the phase-dependent
centers in the manuscript, equation `alpha-comparison`.  The ratio is
independent of the retained prime index, so its convergence gives a
uniform comparison over all indices below `m`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def bandCenterRatio (x : ℝ) : ℝ := Real.log (B x) / (lam * m x)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small cofactor cost is subpolynomial in the tail cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def cofactorScale (H : ℕ) : ℝ := (P H : ℝ)*(rho^(P H))⁻¹

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of totient counts and uniform coefficient asymptotics. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Ford's counting-scale bounds, with constants independent of the endpoint. -/
def FordScaleBounds : Prop :=
  ∃ cMinus cPlus : ℝ, 0 < cMinus ∧ ∀ᶠ x : ℝ in atTop,
    cMinus ≤ normalizedCount V x ∧ normalizedCount V x ≤ cPlus

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGeometry
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The triangular slack calculation underlying `lem:simplex` and
`eq:intersection-volume` in the manuscript. These are identities for the
actual renewal coefficients, with no volume or counting estimate assumed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def prefixSlack (N : ℕ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  u i - ∑ j ∈ Finset.range (N+1), if i < j then a (j-i) * u j else 0

def prefixMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then 1 else if i < j then -a (j.val-i.val) else 0

lemma prefixMatrix_upper (N : ℕ) : (prefixMatrix N).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [prefixMatrix, ne_of_gt hji, not_lt_of_ge hji.le]

lemma prefixMatrix_det (N : ℕ) : (prefixMatrix N).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (prefixMatrix_upper N)]
  simp [prefixMatrix]

def prefixLinear (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (prefixMatrix N)

lemma prefixLinear_det (N : ℕ) : LinearMap.det (prefixLinear N) = 1 := by
  rw [prefixLinear, LinearMap.det_toLin']
  exact prefixMatrix_det N

def prefixVector (N : ℕ) (u : ℕ → ℝ) : Fin N → ℝ := fun i => u (i.val+1)

/-- Coordinates indexed from one, extended by zero outside the prefix. -/
def extendPrefix (N : ℕ) (u : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i-1 < N then u ⟨i-1, hi⟩ else 0

/-- The prefix inequalities for a fixed tail threshold, including index zero. -/
def prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {u | (∀ i, C i ≤ prefixLinear N u i) ∧
    (∑ i : Fin N, a (i.val+1) * u i) ≤ B-C₀}

def weightedSimplex (N : ℕ) (T : ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i : Fin N, g (i.val+1) * v i) ≤ T}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary simplex volume used by the prefix mass calculation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def standardSimplex (N : ℕ) (T : ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i) ≤ T}

def simplexSection (N : ℕ) (T : ℝ) : Set (ℝ × (Fin N → ℝ)) :=
  {p | p.1 ∈ Set.Icc 0 T ∧ p.2 ∈ standardSimplex N (T-p.1)}

def weightedScale (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun i : Fin N => g (i.val+1)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit slack-shell bounds for the prefix simplexes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def raiseThreshold {N : ℕ} (C : Fin N → ℝ) (i : Fin N) (t : ℝ) : Fin N → ℝ :=
  Function.update C i (C i+t)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The dominated convolution limit needed for the finite-tail volume asymptotic.
The sole published input here is Ford's bounded renewal error, Lemma 3.7 of
*The distribution of totients*, arXiv:1104.3264v2 (2013), with Ford's constant
lambda denoted by gamma in this development.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def FordRenewalInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |g n-gamma*(rho^n)⁻¹| ≤ C

def normalizedRenewal (n : ℕ) : ℝ := g n*rho^n

def renewalConvolution (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), normalizedRenewal (n-i)*c i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBounds
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite tail bounds and nonnegative coefficients from exponential random variables. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma alpha_le (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) : alpha s ≤ lam / rho := by
  have h : lam * s ≤ lam := by nlinarith [lam_pos, hs.2]
  have he : Real.exp lam = 1 / rho := Real.exp_log (div_pos zero_lt_one rho_pos)
  unfold alpha
  calc
    lam * Real.exp (lam * s) ≤ lam * Real.exp lam :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) lam_pos.le
    _ = lam / rho := by rw [he]; ring

def tailPrimeBound (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp ((11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹))⌉₊

def tailCofactorBound (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp (2 * (lam/rho) * (P H : ℝ) * (rho^(P H))⁻¹))⌉₊

lemma one_le_tailPrimeBound (H : ℕ) : 1 ≤ tailPrimeBound H := by
  have h : (1 : ℝ) ≤ Real.exp
      (Real.exp ((11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹)) :=
    Real.one_le_exp (Real.exp_pos _).le
  exact_mod_cast h.trans (Nat.le_ceil _)

lemma index_inv_pow_mono {h H : ℕ} (hh : h ≤ H) :
    (h : ℝ) * (rho^h)⁻¹ ≤ (H : ℝ) * (rho^H)⁻¹ := by
  have hr := rho_pos
  apply mul_le_mul (by exact_mod_cast hh)
  · exact (inv_le_inv₀ (pow_pos rho_pos _) (pow_pos rho_pos _)).2
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le hh)
  · positivity
  · positivity

lemma witness_prime_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) (i : Fin H) :
    1 ≤ η.Q i ∧ η.Q i ≤ tailPrimeBound H := by
  by_cases hi : i.val < P H
  · rw [hη.1 i hi]
    exact ⟨le_rfl, one_le_tailPrimeBound H⟩
  · have himem : i.val ∈ Finset.Ico (P H) H := by simp; omega
    obtain ⟨hprime, hlo, hhi, hineq⟩ := hη.2.2.1 i.val himem
    have ht : tailPrime η i.val = η.Q i := by simp [tailPrime, i.isLt]
    rw [ht] at hprime
    have hQ : (1 : ℝ) < η.Q i := by exact_mod_cast hprime.one_lt
    have hlog : Real.log (η.Q i : ℝ) > 0 := Real.log_pos hQ
    have hupper : tailLog η i.val ≤
        (11/10 : ℝ) * (lam/rho) * H * (rho^H)⁻¹ := by
      apply hhi.trans
      calc
        _ = (11/10 : ℝ) * alpha s * ((i.val : ℝ) * (rho^i.val)⁻¹) := by ring
        _ ≤ (11/10 : ℝ) * (lam/rho) * ((H : ℝ) * (rho^H)⁻¹) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (alpha_le s hs) (by norm_num)
          · exact index_inv_pow_mono (Nat.le_of_lt i.isLt)
          · have := rho_pos; positivity
          · have := lam_pos; have := rho_pos; positivity
        _ = _ := by ring
    change Real.log (Real.log (tailPrime η i.val : ℝ)) ≤ _ at hupper
    rw [ht] at hupper
    have hh := (Real.log_le_iff_le_exp hlog).1 hupper
    have hh' := (Real.log_le_iff_le_exp (lt_trans zero_lt_one hQ)).1 hh
    have hb : (η.Q i : ℝ) ≤ (tailPrimeBound H : ℝ) := hh'.trans (Nat.le_ceil _)
    exact ⟨hprime.pos, by exact_mod_cast hb⟩

lemma witness_cofactor_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) :
    1 ≤ η.cofactor ∧ η.cofactor ≤ tailCofactorBound H := by
  have hpos : (0 : ℝ) < η.cofactor := by exact_mod_cast hη.2.1
  have hlog : Real.log (η.cofactor : ℝ) ≤
      Real.exp (2 * (lam/rho) * (P H : ℝ) * (rho^(P H))⁻¹) := by
    apply hη.2.2.2.2.trans
    apply Real.exp_le_exp.mpr
    have hr := rho_pos
    gcongr
    exact alpha_le s hs
  have hb : (η.cofactor : ℝ) ≤ (tailCofactorBound H : ℝ) :=
    ((Real.log_le_iff_le_exp hpos).1 hlog).trans (Nat.le_ceil _)
  exact ⟨hη.2.1, by exact_mod_cast hb⟩

def tailUniverse (H : ℕ) : Set (TailDatum H) :=
  {η | (∀ i, η.Q i ∈ Set.Icc 1 (tailPrimeBound H)) ∧
    η.cofactor ∈ Set.Icc 1 (tailCofactorBound H)}

lemma tailUniverse_finite (H : ℕ) : (tailUniverse H).Finite := by
  let F : TailDatum H → (Fin H → ℕ) × ℕ := fun η => (η.Q, η.cofactor)
  have hF : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa [F, Prod.mk.injEq] using h
  have hf := (Set.Finite.pi (fun _ : Fin H => Set.finite_Icc 1 (tailPrimeBound H))).prod
    (Set.finite_Icc 1 (tailCofactorBound H))
  have hp := hf.preimage hF.injOn
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext η
  simp [tailUniverse, F, Pi.le_def, forall_and, and_assoc, and_left_comm, and_comm]

lemma witness_mem_tailUniverse {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) : η ∈ tailUniverse H := by
  exact ⟨fun i => witness_prime_bound hs hη i, witness_cofactor_bound hs hη⟩

theorem finite_tail_data (H : ℕ) :
    {η : TailDatum H | ∃ s ∈ Set.Ico (0 : ℝ) 1, IsWitness H s η}.Finite := by
  apply (tailUniverse_finite H).subset
  rintro η ⟨s, hs, hη⟩
  exact witness_mem_tailUniverse hs hη

lemma witnesses_finite (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    (witnesses H s d).Finite := by
  apply (finite_tail_data H).subset
  intro η hη
  exact ⟨s, hs, hη.1⟩



def tailMass {H : ℕ} (η : TailDatum H) : ℝ := ∑ l ∈ Finset.Ico (P H) H, tailLog η l


open MeasureTheory ProbabilityTheory
open scoped Classical

instance expOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure zero_lt_one

def exponentialProduct : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

instance exponentialProduct_probability : IsProbabilityMeasure exponentialProduct := by
  unfold exponentialProduct
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def witnessEvent {H : ℕ} (s : ℝ) (η : TailDatum H) : Set (ℕ → ℝ) :=
  Set.univ.pi (fun n => Set.Ioi ((gamma / alpha s) * rho^(H+n) * D (H+n) η))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-tail intersection volumes, before prime-box approximation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def tailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    Set (Fin (R x H) → ℝ) :=
  prefixRegion (R x H) (B x) (D (m x) η)
    (fun i => D (m x-(i.val+1)) η)

def tailIntersection (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) :
    Set (Fin (R x H) → ℝ) :=
  {u | ∀ η ∈ T, u ∈ tailPrefixRegion x H η}

def tailBudget (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) : ℝ :=
  maxD (m x) T + ∑ i : Fin (R x H), g (i.val+1) * maxD (m x-(i.val+1)) T

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailRenewal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-tail budget and its renewal-convolution limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def tailSequence {H : ℕ} (T : Finset (TailDatum H)) (n : ℕ) : ℝ :=
  rho^(H+n)*maxD (H+n) T

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous bound for all projected prefix volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def projectedEnvelope (C : ℝ) (H : ℕ) : ℝ := C^H*rho^(H*(H-1)/2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShellCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous summation of the unit-box slack-shell costs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def quadraticShellTail (H : ℕ) : ℝ :=
  ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorShellDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor envelope is absorbed by every polynomial-geometric shell tail. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def polynomialGeometricTail (k : ℕ) (r : ℝ) (H : ℕ) : ℝ :=
  ∑' n : ℕ, ((H+n : ℕ) : ℝ)^k*r^(H+n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCutoff
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact logarithmic cutoff and polynomially separated collision layers. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def collisionCutoff (h : ℕ) : ℕ := ⌈30*Real.log (h : ℝ)⌉₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Mass
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness and order properties of the actual arithmetic prefix mass. -/

noncomputable section
open scoped BigOperators Topology Classical

namespace TotientAsymptotic

def remainderPrimeBound (x : ℝ) (i : ℕ) : ℕ :=
  max 1 ⌈Real.exp (Real.exp ((11/10 : ℝ) * bandScale x i))⌉₊

def remainderCofactorBound (x : ℝ) (H : ℕ) : ℕ :=
  ⌈Real.exp (Real.exp (2 * bandScale x (L x H)))⌉₊

lemma basic_remainder_prime_bound {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) (i : Fin (L x H)) :
    η.primes i ≤ remainderPrimeBound x (i.val+1) := by
  have hi : i.val+1 ∈ Finset.Icc 1 (L x H) := by simp
  have hp := hη.2.1 (i.val+1) hi
  have heq : remainderPrime η (i.val+1) = η.primes i := by
    simp [remainderPrime, i.isLt]
  have hcoord : remainderCoord x η (i.val+1) =
      Real.log (Real.log (η.primes i : ℝ)) := by
    simp only [remainderCoord, Nat.add_one_ne_zero, ↓reduceIte, heq]
  rw [heq] at hp
  have hpos : (1 : ℝ) < η.primes i := by exact_mod_cast hp.1.one_lt
  have hlog := Real.log_pos hpos
  have hu : Real.log (Real.log (η.primes i : ℝ)) ≤ (11/10 : ℝ)*bandScale x (i.val+1) := by
    simpa only [hcoord] using hp.2.2
  have hb := (Real.log_le_iff_le_exp (zero_lt_one.trans hpos)).1
    ((Real.log_le_iff_le_exp hlog).1 hu)
  have hb' : η.primes i ≤ ⌈Real.exp (Real.exp ((11/10 : ℝ)*bandScale x (i.val+1)))⌉₊ := by
    exact_mod_cast hb.trans (Nat.le_ceil _)
  exact hb'.trans (le_max_right _ _)

lemma basic_remainder_cofactor_bound {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    η.cofactor ≤ remainderCofactorBound x H := by
  have hp : (0 : ℝ) < η.cofactor := by exact_mod_cast hη.1
  have hb := (Real.log_le_iff_le_exp hp).1 hη.2.2.2.2
  exact_mod_cast hb.trans (Nat.le_ceil _)

def remainderUniverse (x : ℝ) (H : ℕ) : Set (RemainderDatum (L x H)) :=
  {η | (∀ i, η.primes i ≤ remainderPrimeBound x (i.val+1)) ∧
    η.cofactor ≤ remainderCofactorBound x H}

lemma remainderUniverse_finite (x : ℝ) (H : ℕ) : (remainderUniverse x H).Finite := by
  let F : RemainderDatum (L x H) → (Fin (L x H) → ℕ) × ℕ := fun η => (η.primes, η.cofactor)
  have hF : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa [F, Prod.mk.injEq] using h
  have hf := (Set.Finite.pi (fun i : Fin (L x H) =>
    Set.finite_Iic (remainderPrimeBound x (i.val+1)))).prod
    (Set.finite_Iic (remainderCofactorBound x H))
  have hp := hf.preimage hF.injOn
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext η
  simp [remainderUniverse, F, Pi.le_def]

lemma basicRemainders_finite (x : ℝ) (H : ℕ) :
    {η : RemainderDatum (L x H) | IsBasicRemainder x H η}.Finite := by
  apply (remainderUniverse_finite x H).subset
  intro η hη
  exact ⟨fun i => basic_remainder_prime_bound hη i, basic_remainder_cofactor_bound hη⟩

def prefixOfRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : PrefixDatum (R x H) :=
  ⟨fun i => remainderPrime η (i.val+1), (remainderTail x H η).totient⟩

lemma isPrefixDatum_iff (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) :
    IsPrefixDatum x H ζ ↔ ∃ η : RemainderDatum (L x H),
      IsBasicRemainder x H η ∧ prefixOfRemainder x H η = ζ := by
  constructor
  · rintro ⟨η, hη, hd, hp⟩
    refine ⟨η, hη, ?_⟩
    cases ζ with
    | mk primes d =>
      simp only [prefixOfRemainder, PrefixDatum.mk.injEq]
      exact ⟨funext (fun i => (hp i).symm), hd⟩
  · rintro ⟨η, hη, rfl⟩
    exact ⟨η, hη, rfl, fun _ => rfl⟩

theorem prefixData_finite (x : ℝ) (H : ℕ) :
    {ζ : PrefixDatum (R x H) | IsPrefixDatum x H ζ}.Finite := by
  have h := (basicRemainders_finite x H).image (prefixOfRemainder x H)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext ζ
  simp only [Set.mem_ofPred_eq, Set.mem_image, isPrefixDatum_iff]

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExtractTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite tail witness extracted from a basic remainder. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def extractTail (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : TailDatum H where
  Q h := if h.val < P H then 1 else remainderPrime η (m x-h.val)
  cofactor := η.cofactor

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntersectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual finite-tail intersection volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def intersectionWeight {H : ℕ} (s : ℝ) (T : Finset (TailDatum H)) : ℝ :=
  rho^(H*(H-1)/2)*(gamma/alpha s)^H *
    Real.exp (-(gamma/alpha s) * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite universe for the phase-dependent inclusion-exclusion sums. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def allTailData (H : ℕ) : Finset (TailDatum H) := (finite_tail_data H).toFinset

def tailValueBound (H : ℕ) : ℕ :=
  tailCofactorBound H * (tailPrimeBound H)^(H-P H)

def nonemptyTailSubsets (H : ℕ) : Finset (Finset (TailDatum H)) := by
  classical
  exact (allTailData H).powerset.filter Finset.Nonempty

def finiteTailCoefficient (H : ℕ) (f : ℝ → ℝ) (s : ℝ)
    (F : Finset (TailDatum H) → ℝ) : ℝ := by
  classical
  exact ∑ d ∈ Finset.Icc 1 (tailValueBound H),
    if IsTotient d then f ((ell d : ℝ)/d)/d *
      ∑ T ∈ nonemptyTailSubsets H,
        if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1)*F T else 0
    else 0

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBox
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unit-box prime sums. The conditional input is the one-dimensional Mertens
estimate displayed in the proof of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 3.1, p. 11: the reciprocal-shift sum over
`exp(exp(m-1)) ≤ p < exp(exp(m))` equals `1 + O(exp(-m))`.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def unitPrimeBox (m : ℕ) : Finset ℕ :=
  (Finset.Icc 2 ⌈Real.exp (Real.exp (m : ℝ))⌉₊).filter (fun p =>
    p.Prime ∧ Real.exp (Real.exp ((m : ℝ)-1)) ≤ p ∧
      (p : ℝ) < Real.exp (Real.exp (m : ℝ)))

def unitPrimeWeight (m : ℕ) : ℝ := ∑ p ∈ unitPrimeBox m, (p-1 : ℝ)⁻¹

def FordUnitPrimeBoxInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
    |unitPrimeWeight m-1| ≤ C*Real.exp (-(m : ℝ))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime mass of finite disjoint unions of unit boxes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeBoxTuples {N : ℕ} (m : Fin N → ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => unitPrimeBox (m i))

def reciprocalShiftWeight {N : ℕ} (p : Fin N → ℕ) : ℝ :=
  (∏ i, (p i-1 : ℕ) : ℕ)⁻¹

def gridPrimeTuples {N : ℕ} (K : Finset (Fin N → ℕ)) : Finset (Fin N → ℕ) :=
  K.biUnion primeBoxTuples

def gridPrimeMass {N : ℕ} (K : Finset (Fin N → ℕ)) : ℝ :=
  ∑ p ∈ gridPrimeTuples K, reciprocalShiftWeight p

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassTailSupport
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite tail support and exact grouping of the actual prefix mass. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def prefixDataFinset (x : ℝ) (H : ℕ) : Finset (PrefixDatum (R x H)) :=
  (prefixData_finite x H).toFinset

@[simp] lemma mem_prefixDataFinset {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)} :
    ζ ∈ prefixDataFinset x H ↔ IsPrefixDatum x H ζ := by
  simp [prefixDataFinset]

def prefixPrimeFiber (x : ℝ) (H d : ℕ) : Finset (Fin (R x H) → ℕ) :=
  ((prefixDataFinset x H).filter (fun ζ => ζ.d=d)).image PrefixDatum.primes

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AttachTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconstructing a basic remainder from its prime prefix and finite tail witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def attachTail (x : ℝ) (H : ℕ) (p : Fin (R x H) → ℕ) (η : TailDatum H) :
    RemainderDatum (L x H) where
  primes k := if hk : k.val < R x H then p ⟨k.val, hk⟩
    else tailPrime η (m x-(k.val+1))
  cofactor := η.cofactor

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RemainderSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the prime prefix from its discrete tail thresholds. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primePrefixCoord {J : ℕ} (p : Fin J → ℕ) : Fin J → ℝ :=
  fun i => Real.log (Real.log (p i : ℝ))

def perturbedTailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    Set (Fin (R x H) → ℝ) :=
  {u | (∀ i, D (m x-(i.val+1)) η ≤
      prefixLinear (R x H) u i + (xi x (i.val+1)-1)*u i) ∧
    (∑ i : Fin (R x H), a (i.val+1)*u i) ≤ xi x 0*B x-D (m x) η}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact banded, perturbed regions represented by the arithmetic fibers. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def PrefixPrimeBands (x : ℝ) (H : ℕ) (p : Fin (R x H) → ℕ) : Prop :=
  ∀ i, (p i).Prime ∧ (9/10 : ℝ)*bandScale x (i.val+1) ≤ primePrefixCoord p i ∧
    primePrefixCoord p i ≤ (11/10 : ℝ)*bandScale x (i.val+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixRelaxation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative control of simultaneous perturbations of all prefix inequalities. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def prefixBandRegion (x : ℝ) (H : ℕ) : Set (Fin (R x H) → ℝ) :=
  {u | ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i ∧
    u i ≤ (11/10 : ℝ)*bandScale x (i.val+1)}

def prefixPerturbation (x : ℝ) (H : ℕ) : Fin (R x H) → ℝ :=
  fun i => (xi x (i.val+1)-1)*((11/10 : ℝ)*bandScale x (i.val+1))

def topPerturbation (x : ℝ) : ℝ := (xi x 0-1)*B x

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric volumes of the same disjoint boxes used in the prime sum. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def unitGridCell {N : ℕ} (m : Fin N → ℕ) : Set (Fin N → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico ((m i : ℝ)-1) (m i : ℝ))

def gridRegion {N : ℕ} (K : Finset (Fin N → ℕ)) : Set (Fin N → ℝ) :=
  ⋃ m ∈ K, unitGridCell m

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBoxGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic prime boxes and their real double-logarithmic cells agree. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def gridInner {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    Finset (Fin N → ℕ) := K.filter (fun m => unitGridCell m ⊆ S)

def gridOuter {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    Finset (Fin N → ℕ) := K.filter (fun m => (unitGridCell m ∩ S).Nonempty)

def gridRestrictedPrimeMass {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) : ℝ :=
  ∑ p ∈ (gridPrimeTuples K).filter (fun p => primePrefixCoord p ∈ S), reciprocalShiftWeight p

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite grids covering the actual arithmetic prefix fibers. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def bandGrid (x : ℝ) (H : ℕ) : Finset (Fin (R x H) → ℕ) :=
  (Fintype.piFinset (fun i : Fin (R x H) =>
    Finset.Icc 1 (⌊(11/10 : ℝ)*bandScale x (i.val+1)⌋₊+1))).filter
      (fun m => ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ m i)

def bandedWitnessRegion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  prefixBandRegion x H ∩ ⋃ η ∈ witnesses H (theta x) d, perturbedTailPrefixRegion x H η

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexScaling
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal normalization of the enlarged simplexes used by prime boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def enlargedSimplex (N : ℕ) (B β₀ : ℝ) (β : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧
    (∀ i, (∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0) ≤ β i*u i) ∧
    (∑ i : Fin N, a (i.val+1)*u i) ≤ β₀*B}

def simplexScale {N : ℕ} (κ : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun i => (κ i)⁻¹))

def enlargementScale {N : ℕ} (β : ℕ → ℝ) (i : Fin N) : ℝ :=
  ∏ r ∈ Finset.range (i.val+1), β r

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EnlargementTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two perturbations used for full prime boxes have summable weighted
cost, including after multiplication by the smooth-cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def simplexBoxError (C : ℝ) (h : ℕ) : ℝ :=
  (Real.exp (-(1/40 : ℝ)))^h/10000 + C*(h : ℝ)^2*rho^h

def simplexBoxTail (C : ℝ) (H : ℕ) : ℝ :=
  polynomialGeometricTail 1 (Real.exp (-(1/40 : ℝ))) H/10000 +
    C*polynomialGeometricTail 3 rho H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassMajorant
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing over witnesses is an upper bound, including repeated tail primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def basicRemainderFinset (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainders_finite x H).toFinset

@[simp] lemma mem_basicRemainderFinset {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)} :
    η ∈ basicRemainderFinset x H ↔ IsBasicRemainder x H η := by
  simp [basicRemainderFinset]

def remainderReciprocalWeight {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : ℝ :=
  (η.cofactor.totient : ℝ)⁻¹ * reciprocalShiftWeight η.primes

def fullPrimeTuples (x : ℝ) (H : ℕ) : Finset (Fin (L x H) → ℕ) :=
  (basicRemainderFinset x H).image RemainderDatum.primes

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandPrimeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-independent prime-box error from the retained lower bands. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def bandPrimeError (C c : ℝ) (H : ℕ) : ℝ :=
  Real.exp (C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))-1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime mass versus volume, with all remaining error confined to boundary boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def bandedVolumeMass (x : ℝ) (H : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d *
    (volume (bandedWitnessRegion x H d)).toReal

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullPrimeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full prime tuples are controlled by one enlarged-simplex
volume, with the discrete cofactor kept separate. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def fullPrimeGrid (x : ℝ) (H : ℕ) : Finset (Fin (L x H) → ℕ) :=
  (bandGrid x (P H)).filter (fun b =>
    ∃ p ∈ fullPrimeTuples x H, primePrefixCoord p ∈ unitGridCell b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeEulerProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (p : ℝ)/(p-1)

def MertensProductInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → primeEulerProduct N ≤ C*Real.log N

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailCofactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform reciprocal cofactor envelope at the discrete tail cut. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def exponentialCofactorCap (T : ℝ) : ℕ := ⌈Real.exp (Real.exp T)⌉₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic mass has the required uniform cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def fullPrimeFactor (C K : ℝ) (H : ℕ) : ℝ :=
  (1+bandPrimeError C (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*
    projectedEnvelope K (P H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact suffix totient factorizations for basic witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def suffixPreimage {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) (i : ℕ) : ℕ :=
  η.cofactor*∏ r ∈ Finset.Icc (i+1) (L x H), remainderPrime η r

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tuples, their basic witnesses, and the first differing prime. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

structure TotientTuple (R : ℕ) where
  head : ℕ
  tail : PrefixDatum R

def tuplePrimes {R : ℕ} (τ : TotientTuple R) : Fin (R+1) → ℕ :=
  Fin.cons τ.head τ.tail.primes

def tupleValue {R : ℕ} (τ : TotientTuple R) : ℕ :=
  τ.tail.d*∏ i, (tuplePrimes τ i-1)

def IsBasicTuple (x : ℝ) (H : ℕ) (t : ℝ) (τ : TotientTuple (R x H)) : Prop :=
  τ.head.Prime ∧ x^(9/10 : ℝ) ≤ τ.head ∧ IsPrefixDatum x H τ.tail ∧ (tupleValue τ : ℝ) ≤ t

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite set of distinct arithmetic tuples used in the collision count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def tupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) := by
  classical
  exact (((Finset.range (⌊t⌋₊+2)) ×ˢ prefixDataFinset x H).image
    (fun p => TotientTuple.mk p.1 p.2)).filter (IsBasicTuple x H t)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact comparison data extracted from two basic witnesses for colliding tuples. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def wholeWitnessPrime {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H))
    (i : ℕ) : ℕ := if i=0 then p else remainderPrime η i

def witnessTuple {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) :
    TotientTuple (R x H) := ⟨p, prefixOfRemainder x H η⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GoodTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual good tuples: every basic witness must satisfy the four collision conditions. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def normalityScale (x : ℝ) (i : ℕ) : ℝ :=
  Real.exp (Real.exp ((fordBandScale x i)^(1/3 : ℝ)))

def collisionLastIndex (x : ℝ) (i : ℕ) : ℕ := i+collisionCutoff (m x-i)

def collisionSmoothCutoff (x : ℝ) (i : ℕ) : ℝ :=
  Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x (collisionLastIndex x i)))

def collisionResidual {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) (i : ℕ) : ℕ :=
  (suffixPreimage η (collisionLastIndex x i)).totient

/-- The four conditions in extraction.tex, equation good-conditions. The
coordinates and scales are those of the common original endpoint `x`. -/
def GoodWitnessConditions {x : ℝ} {H : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) : Prop :=
  ∀ i ∈ Finset.Icc 0 (R x H),
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) ≤
      (1-1/((m x-i : ℕ) : ℝ)^4)*remainderCoord x η i ∧
    (∀ j ∈ Finset.Icc i (collisionLastIndex x i),
      IsNormalPrime (normalityScale x i) (wholeWitnessPrime p η j)) ∧
    SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i),
      (wholeWitnessPrime p η j-1)) (collisionSmoothCutoff x i) ∧
    ((collisionResidual η i).primeFactorsList.length : ℝ) ≤
      fordBandScale x i/((m x-i : ℕ) : ℝ)^8

/-- Witnesses are universally quantified; no arbitrary choice can turn a
bad tuple into a good one. -/
def IsGoodTuple (x : ℝ) (H : ℕ) (t : ℝ) (τ : TotientTuple (R x H)) : Prop :=
  IsBasicTuple x H t τ ∧
  ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    prefixOfRemainder x H η = τ.tail → GoodWitnessConditions τ.head η

def goodTupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (IsGoodTuple x H t)

def badTupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  tupleFinset x H t \ goodTupleFinset x H t

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The summable, phase-independent tail in the prefix collision estimate. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The contribution of a suffix at distance `h` from the end, after restoring
its common prefix and integrating the dyadic suffix estimates. -/
def collisionKernel (c : ℝ) (h : ℕ) : ℝ :=
  (h : ℝ)^4 * Real.exp (-c/((h : ℝ)^3*rho^h))

def collisionTail (c : ℝ) (H : ℕ) : ℝ := ∑' n : ℕ, collisionKernel c (H+n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral comparison for reciprocal-weighted dyadic collision slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def dyadicSuffixWeight (σ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-σ*Real.log ((n : ℝ)*Real.log 2))/((n : ℝ)*Real.log 2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedNormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ford, The distribution of totients, revised arXiv:1104.3264v2 (2013),
Lemma 2.6, p. 9. The author-hosted PDF states uniformity for x > 3 and
S > 2: https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf .
Only this count of exceptional primes is assumed. Reciprocal-weight and
actual good-witness discard estimates are derived separately.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => ¬ IsNormalPrime S p)

/-- The precise published exceptional-prime estimate, at integer endpoints. -/
def FordLemma26Input : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → ∀ N : ℕ, 3 < N →
    ((nonNormalPrimes S N).card : ℝ) ≤
      C*(N : ℝ)/Real.log N*(B N)^5*(Real.log S)^(-1/6 : ℝ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDiscardCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common dyadic endpoint for the short suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def discardExponent (b : ℝ) : ℕ := ⌈Real.exp (2*b)⌉₊
def discardPrimeBound (b : ℝ) : ℕ := 2^(discardExponent b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prefix denominators and the size bound needed for largest-prime summation. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def prefixDenominator {n : ℕ} (ζ : PrefixDatum n) : ℕ :=
  ζ.d*∏ i, (ζ.primes i-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical ordered comparison lists obtained from actual colliding witnesses. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionSurvivors {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) : Finset ℕ :=
  (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j)

def survivingIndex {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) :
    Fin (collisionSurvivors p q η ξ i k).card ↪o ℕ :=
  (collisionSurvivors p q η ξ i k).orderEmbOfFin rfl

def survivingPair {x : ℝ} {H : ℕ} (p q : ℕ) (η ξ : RemainderDatum (L x H)) (i k : ℕ) :
    ShiftedPair (collisionSurvivors p q η ξ i k).card where
  left := fun j => wholeWitnessPrime p η (survivingIndex p q η ξ i k j)
  right := fun j => wholeWitnessPrime q ξ (survivingIndex p q η ξ i k j)
  remainder := (suffixPreimage ξ k).totient

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCanceled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canceled product and the residual integer satisfy Ford's size bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionCanceledProduct {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j),
    (wholeWitnessPrime p η j-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingBlockSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact block values and bounds for both surviving shifted-prime lists. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def witnessBlockValue {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) (i k : ℕ) : ℕ :=
  (suffixPreimage η k).totient*∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ChosenCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical basic witnesses for distinct good tuples and their first differing prime. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def chosenRemainder (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) : RemainderDatum (L x H) :=
  if h : IsPrefixDatum x H ζ then Classical.choose ((isPrefixDatum_iff x H ζ).mp h)
  else ⟨fun _ => 1,1⟩

def goodCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  ((goodTupleFinset x H t) ×ˢ (goodTupleFinset x H t)).filter
    (fun q => q.1 ≠ q.2 ∧ tupleValue q.1=tupleValue q.2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleRecovery
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The prime-occurrence allocation bound in equations (residual-factorization)
and (tuple-recovery-cost). Repeated prime factors are counted with multiplicity.
-/

open scoped BigOperators

namespace TotientAsymptotic

def prefixDatumEncoding {n : ℕ} (t : PrefixDatum n) : Fin (n+1) → ℕ :=
  Fin.cons t.d (fun i => t.primes i-1)

end TotientAsymptotic

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting the residual tuple data forgotten by Ford's comparison map. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

abbrev RecoveredPair (b n : ℕ) := ShiftedPair b × PrefixDatum n × PrefixDatum n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualTupleRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact tuple data hidden in a comparison residual, on either side of the prefix cut. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def residualTupleData {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) (k : ℕ) :
    PrefixDatum (R x H-k) where
  primes := fun j => remainderPrime η (k+j.val+1)
  d := if k ≤ R x H then (remainderTail x H η).totient else (suffixPreimage η k).totient

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's comparison bound applied to finite families of actual tuple pairs. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def comparisonPairAt (x : ℝ) (H k : ℕ) (I : Finset ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : ShiftedPair I.card where
  left := fun j => wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail)
    (I.orderEmbOfFin rfl j)
  right := fun j => wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail)
    (I.orderEmbOfFin rfl j)
  remainder := (suffixPreimage (chosenRemainder x H q.2.tail) k).totient

def comparisonEncoding (x : ℝ) (H k : ℕ) (I : Finset ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : RecoveredPair I.card (R x H-k) :=
  (comparisonPairAt x H k I q,
    residualTupleData (chosenRemainder x H q.1.tail) k,
    residualTupleData (chosenRemainder x H q.2.tail) k)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionClassData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovering the fixed-prime data in an actual finite collision class. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def canceledIndices (i k : ℕ) (I : Finset ℕ) : Finset ℕ := Finset.Icc i k \ I

def canceledPrimesAt (x : ℝ) (H i k : ℕ) (I : Finset ℕ)
    (τ : TotientTuple (R x H)) : Fin (canceledIndices i k I).card → ℕ :=
  fun j => wholeWitnessPrime τ.head (chosenRemainder x H τ.tail)
    ((canceledIndices i k I).orderEmbOfFin rfl j)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tuple suffixes, with the common prefix removed exactly once. -/

noncomputable section

namespace TotientAsymptotic

def tupleSuffix {R : ℕ} (τ : TotientTuple R) (i : ℕ) : PrefixDatum (R+1-i) where
  primes := fun j => tuplePrimes τ ⟨i+j.val,by have := j.isLt; omega⟩
  d := τ.tail.d

def pairSuffix {R : ℕ} (q : TotientTuple R × TotientTuple R) (i : ℕ) :
    PrefixDatum (R+1-i) × PrefixDatum (R+1-i) := (tupleSuffix q.1 i,tupleSuffix q.2 i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGridScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially small normalized alignment mesh at each actual collision cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def collisionMesh (x y : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (B (normalityScale x i)*B y)/B y

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer size and large-prime-part bounds for Ford's comparison hypotheses. -/

noncomputable section

namespace TotientAsymptotic

def partBelow (n : ℕ) (Z : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)).prod

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def collisionGridIndex (δ u v : ℝ) : ℕ := ⌊min u v/δ⌋₊

def collisionGridLower (δ : ℝ) (n : ℕ) : ℝ := δ*n

def collisionGridUpper (δ : ℝ) (J n : ℕ) : ℝ := δ*(n+2*J+3 : ℕ)

def collisionGridFamilies (δ : ℝ) (b : ℕ) : Finset (Fin b → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (⌊1/δ⌋₊+1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's cutoff restrictions in the normalized coordinates of the finite grid. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def comparisonCutoffs (y : ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.exp (B y*ν j))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PairedComparisonGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual paired intervals, including the ungridded top and smooth bottom. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pairedGridUpper {b : ℕ} (δ ζ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 1 else if hj : j<b then collisionGridUpper δ j (n ⟨j,hj⟩) else ζ

def pairedGridLower {b : ℕ} (δ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 4/5 else if hj : j<b then collisionGridLower δ (n ⟨j,hj⟩) else 0

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualSurvivingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height geometry derived from the chosen actual good witnesses. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def leftFactorHeight {b : ℕ} (t : ShiftedPair b) (r : Fin b) : ℝ :=
  B (largestPrimeFactor (t.left r-1))

def rightFactorHeight {b : ℕ} (t : ShiftedPair b) (r : Fin b) : ℝ :=
  B (largestPrimeFactor (t.right r-1))

structure ComparisonHeightBounds {b : ℕ} (t : ShiftedPair b) (Y Z : ℝ) : Prop where
  positive : ∀ r, 0 < leftFactorHeight t r ∧ 0 < rightFactorHeight t r
  top : ∀ r, leftFactorHeight t r ≤ Y ∧ rightFactorHeight t r ≤ Y
  head : ∀ hb : 0<b, (9/10 : ℝ)*Y ≤ min (leftFactorHeight t ⟨0,hb⟩) (rightFactorHeight t ⟨0,hb⟩)
  tail : ∀ r, 0 < r.val → max (leftFactorHeight t r) (rightFactorHeight t r) ≤ (18/25 : ℝ)*Y
  bottom : ∀ r, (4/5 : ℝ)*Z ≤ min (leftFactorHeight t r) (rightFactorHeight t r)
  separated : ∀ r s, r < s → (1/10 : ℝ)*Z ≤
    min (leftFactorHeight t r) (rightFactorHeight t r)-max (leftFactorHeight t s) (rightFactorHeight t s)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualComparisonCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite cutoffs for the actual collision comparison. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pairGridLabel {b : ℕ} (t : ShiftedPair b) (y δ : ℝ) (r : Fin b) : ℕ :=
  collisionGridIndex δ (leftFactorHeight t r/B y) (rightFactorHeight t r/B y)

def pairUpperCoordinates {b : ℕ} (t : ShiftedPair b) (y Z δ : ℝ) : ℕ → ℝ :=
  pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ)

def pairLowerCoordinates {b : ℕ} (t : ShiftedPair b) (y δ : ℝ) : ℕ → ℝ :=
  pairedGridLower δ (pairGridLabel t y δ)


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedPrimeCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The classical prime number theorem, in precisely the epsilon form used here.
Hadamard and de la Vallée Poussin (1896); for a numbered, accessible statement
see Terence Tao, *254A, Notes 2: Complex-analytic multiplicative number theory*
(9 December 2014), Exercise 40, following Corollary 39:
https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/
Only pi(y) ~ y/log(y) is retained from the stronger published estimate.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def PrimeNumberTheoremInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop,
    |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y| ≤ ε*(y/Real.log y)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualFordData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All Ford hypotheses for a block of actual good tuple pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The arithmetic data of a good collision in a single counting block.
The positive-index block endpoints will be supplied by dyadic subdivision. -/
structure GoodCollisionBlock (x t : ℝ) (H i : ℕ) (y : ℝ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : Prop where
  left : IsGoodTuple x H t q.1
  right : IsGoodTuple x H t q.2
  value : tupleValue q.1=tupleValue q.2
  first : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i ≠
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i
  common : ∀ j < i, wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j
  minLeft : y^(9/10 : ℝ) ≤ wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i
  minRight : y^(9/10 : ℝ) ≤ wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i
  size : (witnessBlockValue q.1.head (chosenRemainder x H q.1.tail) i (collisionLastIndex x i) : ℝ) ≤ y
  zero : i=0 → y=x

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothResidualMass
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler product bounds the entire smooth residual-integer sum. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def reciprocalNatHom : ℕ →* ℝ where
  toFun := fun n => (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by intro m n; simp [mul_comm]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-difference partition and its suffix quotient. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def FirstDifferenceAt {x : ℝ} {H : ℕ} (i : ℕ)
    (q : TotientTuple (R x H) × TotientTuple (R x H)) : Prop :=
  wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) i ≠
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) i ∧
  ∀ j < i, wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
    wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j

def firstCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  (goodCollisionPairs x H t).filter (FirstDifferenceAt i)

def firstCollisionSuffixes (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) :
    Finset (PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) :=
  (firstCollisionPairs x H t i).image (fun q => pairSuffix q i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A projected prime prefix has mass bounded by its own simplex volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def projectedPrimeGrid (x : ℝ) (K : ℕ) (Q : Finset (Fin (R x K) → ℕ)) : Finset (Fin (R x K) → ℕ) :=
  (bandGrid x K).filter (fun b =>
    ∃ p ∈ Q, primePrefixCoord p ∈ unitGridCell b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection preserves the nonnegative simplex inequalities. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tupleInnerPrefix {N : ℕ} (τ : TotientTuple N) (n : ℕ) : Fin n → ℕ :=
  fun j => if hj : j.val < N then τ.tail.primes ⟨j.val,hj⟩ else 1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over the possible common prime prefixes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def projectedPrimeFactor (C D : ℝ) (K : ℕ) : ℝ :=
  (1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K)*projectedEnvelope D K

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeMassSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split a finite prime family at an arbitrary coordinate without multiplying
by the number of possible prefixes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeInitial {N : ℕ} (p : Fin N → ℕ) (n : ℕ) (hn : n ≤ N) : Fin n → ℕ :=
  fun j => p (Fin.castLE hn j)

def primeFinal {N : ℕ} (p : Fin N → ℕ) (n : ℕ) : Fin (N-n) → ℕ :=
  fun j => p ⟨n+j.val,by have := j.isLt; omega⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedWitnessCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting any specified family of full basic witnesses, with their cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessHeadSet {x : ℝ} {H : ℕ} (t : ℝ) (η : RemainderDatum (L x H)) : Finset ℕ :=
  (Finset.range (⌊t⌋₊+2)).filter (fun p => IsBasicTuple x H t (witnessTuple p η))

def witnessFamily {x : ℝ} {H : ℕ} (t : ℝ) (S : Finset (RemainderDatum (L x H))) :
    Finset (RemainderDatum (L x H) × ℕ) :=
  (S ×ˢ Finset.range (⌊t⌋₊+2)).filter (fun q => IsBasicTuple x H t (witnessTuple q.2 q.1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalRemainderLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford normality applied to each actual positive-index witness layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalRemainders (x : ℝ) (H i j : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    ¬ IsNormalPrime (normalityScale x i) (remainderPrime η j))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalInternalDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum every non-head normality failure, retaining all basic witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 0 (R x H)).biUnion (fun i =>
    (Finset.Icc (max 1 i) (L x H)).biUnion (nonNormalRemainders x H i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaReciprocal
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Euler-product moment for the remaining-factor exclusion.
The exponent three is sufficient for the application. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def omegaReciprocal : ℕ →* ℝ where
  toFun n := (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m=0
    · subst m; simp
    by_cases hn : n=0
    · subst n; simp
    have hh := (Nat.perm_primeFactorsList_mul hm hn).length_eq
    rw [List.length_append] at hh
    simp only [hh,Nat.cast_mul,pow_add]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalOmegaMoment
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicative moments for the number of prime factors in an interval. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def intervalOmegaWeight (a U T : ℝ) : ℕ →* ℝ where
  toFun n := a^(omegaIn n U T)/(n:ℝ)
  map_one' := by simp [omegaIn]
  map_mul' m n := by
    by_cases hm : m=0
    · subst m; simp
    by_cases hn : n=0
    · subst n; simp
    simp only [omegaIn_mul hm hn,Nat.cast_mul,pow_add]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeIntervalMass
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint bookkeeping for reciprocal primes in half-open intervals. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime

def primesBelow (x : ℝ) : Finset ℕ :=
  (primesUpTo x).filter (fun p => (p : ℝ)<x)

def primeReciprocalLE (x : ℝ) : ℝ := ∑ p ∈ primesUpTo x, (p : ℝ)⁻¹

def primeReciprocalLT (x : ℝ) : ℝ := ∑ p ∈ primesBelow x, (p : ℝ)⁻¹

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityTilt
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-root tilt giving the saving in the normality tail. -/
noncomputable section
namespace TotientAsymptotic

def normalityTilt (A B : ℝ) : ℝ := Real.sqrt A/(4*Real.sqrt B)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the interval deviations over the finite normality grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalityGridCell (A : ℝ) (M : ℕ) (Q : Finset ℕ) (ij : ℕ×ℕ) : Finset ℕ :=
  Q.filter (fun n => 1 ≤ ij.1 ∧ ij.1 < ij.2 ∧ ij.2 ≤ M ∧ A ≤ (ij.2:ℝ)-1 ∧
    Real.sqrt (A*((ij.2:ℝ)-1))-4 ≤
      |(omegaIn n (normalityGridPoint ij.1) (normalityGridPoint ij.2):ℝ)-((ij.2:ℝ)-ij.1)|)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityGridMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite union of the normality grid cells. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace TotientAsymptotic

def normalityGridIndices (M : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range (M+1)).product (Finset.range (M+1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AbnormalCofactorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both failures of prime normality have small reciprocal cofactor mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def AbnormalCofactor (S x : ℝ) (n : ℕ) : Prop :=
  2*B S-1 < (omegaIn n 1 S:ℝ) ∨ ∃ U T : ℝ,
    S ≤ U ∧ U < T ∧ T ≤ x ∧
    Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualSuffixMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual reciprocal mass of distinct colliding suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def suffixDyadicIndex {n : ℕ} (s : PrefixDatum n × PrefixDatum n) : ℕ :=
  Nat.clog 2 (prefixDenominator s.1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The discrete tail, in the coordinate order used by the full simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailVector {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℝ :=
  fun i => tailLog η (H-1-i.val)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBoxAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Aggregate all discrete tails in a box before measuring the continuous
prefix. No factor counting the number of tail witnesses occurs. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ)) :
    Set ((Fin R → ℝ) × (Fin T → ℝ)) :=
  ⋃ b ∈ K, U b ×ˢ unitGridCell b

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBoxCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefix-times-tail-box measure is the usual full-coordinate volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def joinCoordinates (R T : ℕ) :
    ((Fin R → ℝ) × (Fin T → ℝ)) ≃ᵐ (Fin (R+T) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin R ⊕ Fin T => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (R+T) => ℝ) finSumFinEquiv)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PerturbationCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of all prefix perturbations, uniformly in dimension and phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def exponentialShellTail (H : ℕ) : ℝ :=
  polynomialGeometricTail 1 (Real.exp (-1/40)) H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveEnclosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Banded perturbed witness regions and their unit boxes have an additive
full-dimensional enclosure with explicit coordinate errors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def boxSlackError (x : ℝ) (k : ℕ) : ℝ :=
  (xi x k-1)*((11/10 : ℝ)*bandScale x k)+4*((m x-k : ℕ) : ℝ)^2

def boxTopError (x : ℝ) : ℝ := topPerturbation x+4*(m x : ℝ)^2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the additive box errors with their exact slice coefficients. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def boxErrorTail (H : ℕ) : ℝ := exponentialShellTail H+quadraticShellTail H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveShellUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing all retained slack slices in one enlarged full-dimensional simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def additiveBoxSimplex (x : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  prefixRegion N (B x+boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))

def additiveBoxShell (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  (additiveBoxSimplex x N \
    prefixRegion N (B x-boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))) ∪
  ⋃ i : Fin R, additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x) 0
      (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
        (2*boxSlackError x (i.val+1)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandExtraction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-union and geometric-tail argument behind the manuscript's
`ford-bands` estimate.  Only Ford's explicitly stated Theorems 10 and 16
remain hypotheses; the summation and the passage to model bands are proved.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def modelBandsCondition (x : ℝ) (P n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 (m x-P),
    (9/10 : ℝ) * bandScale x i ≤ primeDoubleLog n i ∧
      primeDoubleLog n i ≤ (11/10 : ℝ) * bandScale x i

def extractedStructureCondition (x : ℝ) (P n : ℕ) : Prop :=
  modelBandsCondition x P n ∧ extractedSimplexCondition x P n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def fordCofactor (n k : ℕ) : ℕ := (n.primeFactorsList.reverse.drop k).prod

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteMap
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-map counting lemma in `collisions.tex`, Lemma `finite-map`.
The collision count records ordered distinct pairs of good tuples with the
same image.  Both the exceptional values and all tuples above them are bounded.
-/

open scoped BigOperators

namespace TotientAsymptotic.FiniteMap

variable {α β : Type*} [DecidableEq β]

def fiber (G : Finset α) (F : α → β) (w : β) : Finset α :=
  G.filter (fun t => F t = w)

def collisionCount (G : Finset α) (W : Finset β) (F : α → β) : ℕ :=
  ∑ w ∈ W, (fiber G F w).card * ((fiber G F w).card - 1)

def multipleValues (G : Finset α) (W : Finset β) (F : α → β) : Finset β :=
  W.filter (fun w => 2 ≤ (fiber G F w).card)

def badValues (G D : Finset α) (W E : Finset β) (F : α → β) : Finset β :=
  E ∪ D.image F ∪ multipleValues G W F

def badPreimages (T G D : Finset α) (W E : Finset β) (F : α → β) : Finset α :=
  T.filter (fun t => F t ∈ badValues G D W E F)

end TotientAsymptotic.FiniteMap

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalHeadDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality failures of the largest prime have vanishing relative mass. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalHeadTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ¬IsNormalPrime (normalityScale x 0) τ.head)

def normalHeadError (x : ℝ) : ℝ :=
  (1+B x)^5*Real.exp (-((B x)^(1/3 : ℝ))/6)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete normality exclusion for the actual universally good tuples. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ nonNormalInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsWitnessNormality {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H), ∃ j ∈ Finset.Icc i (collisionLastIndex x i),
    ¬IsNormalPrime (normalityScale x i) (wholeWitnessPrime p η j)

def normalityFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessNormality τ.head η)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaPrimeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete factor-count moment bounds exceptional shifted primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaExceptionalPrimes (N : ℕ) (T : ℝ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => T ≤ ((p-1).primeFactorsList.length : ℝ))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaRemainderLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional shifted-prime moment applied to actual remainder layers. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaExceptionalRemainders (x : ℝ) (H i j : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    fordBandScale x i/(2*((m x-i : ℕ) : ℝ)^9) < ((remainderPrime η j-1).primeFactorsList.length : ℝ))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaInternalDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite layer summation for the remaining-factor exclusion. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 0 (R x H)).biUnion (fun i =>
    (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete residual factor-count exclusion for universally good tuples. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ omegaInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsWitnessOmega {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    fordBandScale x i/((m x-i : ℕ) : ℝ)^8 < ((collisionResidual η i).primeFactorsList.length : ℝ)

def omegaFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessOmega η)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionHeadCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete comparison estimate for pairs with different head primes. -/

noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  (goodCollisionPairs x H t).filter (fun q => q.1.head ≠ q.2.head)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestoreCommonPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring all common prefixes after counting distinct suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionInnerPrefixes (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) : Finset (Fin (i-1) → ℕ) :=
  (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (i-1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullWitnessWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct weighted count including the head prime, used only for the
zero-index squarefree exclusion. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def fullWitnessPrimes {x : ℝ} {H : ℕ} (q : RemainderDatum (L x H) × ℕ) :
    Fin (L x H+1) → ℕ := Fin.cons q.2 q.1.primes

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftDivisorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary reciprocal mass of divisible prime shifts and square tails. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def shiftDivisiblePrimes (N d : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => d ∣ p-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareCase (x : ℝ) (H : ℕ) (t : ℝ) (q j k : ℕ) :
    Finset (RemainderDatum (L x H) × ℕ) :=
  (witnessFamily t (basicRemainderFinset x H)).filter (fun w =>
    if j=k then q^2 ∣ wholeWitnessPrime w.2 w.1 j-1
    else q ∣ wholeWitnessPrime w.2 w.1 j-1 ∧ q ∣ wholeWitnessPrime w.2 w.1 k-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareRemainderLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each single or double shifted-prime divisibility costs a square reciprocal. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareRemainderCase (x : ℝ) (H q j k : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    if j=k then q^2 ∣ remainderPrime η j-1
    else q ∣ remainderPrime η j-1 ∧ q ∣ remainderPrime η k-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareLayerSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum square divisors and both coordinate choices in each positive-index layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareLayerPrimes (x : ℝ) (i : ℕ) : Finset ℕ :=
  (Nat.primesLE (discardPrimeBound (fordBandScale x i))).filter
    (fun q => collisionSmoothCutoff x i < (q : ℝ))

def squareLayerRemainders (x : ℝ) (H i : ℕ) : Finset (RemainderDatum (L x H)) :=
  (squareLayerPrimes x i).biUnion (fun q =>
    (Finset.Icc i (L x H)).biUnion (fun j =>
      (Finset.Icc i (L x H)).biUnion (fun k => squareRemainderCase x H q j k)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareFamily (x : ℝ) (H : ℕ) (t : ℝ) : Finset (RemainderDatum (L x H) × ℕ) := by
  letI : DecidableEq (RemainderDatum (L x H) × ℕ) := Classical.decEq _
  exact (squareLayerPrimes x 0).biUnion (fun q =>
    (Finset.Icc 0 (L x H)).biUnion (fun j =>
      (Finset.Icc 0 (L x H)).biUnion (fun k => headSquareCase x H t q j k)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def headSquareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc 0 (collisionLastIndex x 0), (wholeWitnessPrime τ.head η j-1))
      (collisionSmoothCutoff x 0))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareInternalDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All positive-index squarefree failures, including alternate witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 1 (R x H)).biUnion (squareLayerRemainders x H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PositiveSquareDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-index squarefree exclusion for every basic witness. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def squareInternalTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ squareInternalRemainders x H,
    prefixOfRemainder x H η=τ.tail)

def FailsPositiveSquare {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 1 (R x H),
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (remainderPrime η j-1))
      (collisionSmoothCutoff x i)

def positiveSquareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsPositiveSquare η)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def FailsWitnessSquare {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    ¬SquarefreeAbove (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1))
      (collisionSmoothCutoff x i)

def squareFailureTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η : RemainderDatum (L x H),
    IsBasicRemainder x H η ∧ prefixOfRemainder x H η=τ.tail ∧ FailsWitnessSquare τ.head η)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additive boundary slices vanish after the smooth-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedShellLoss (K C J : ℝ) (H : ℕ) : ℝ :=
  (4*C)*Real.exp (C*boxErrorTail (P H))*projectedEnvelope J (P H)*
    (Real.exp (K*cofactorScale H)*boxErrorTail H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additional polynomial-width shell needed to discard failures of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def inverseSquareSum : ℝ := ∑' n : ℕ, 1/((n+1 : ℕ) : ℝ)^2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-dimensional thin region associated with a failure of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def strictTopWidth (x : ℝ) : ℝ := 2*boxTopError x+B x/(m x : ℝ)^4

def strictSlackWidth (x : ℝ) (i : ℕ) : ℝ :=
  2*boxSlackError x i+(11/10 : ℝ)*bandScale x i/((m x-i : ℕ) : ℝ)^4

def strictSlackShell (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  (additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x-strictTopWidth x) 0
      (fun i => -boxSlackError x (i.val+1))) ∪
  ⋃ i : Fin R, additiveBoxSimplex x N \
    prefixRegion N (B x+boxTopError x) 0
      (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
        (strictSlackWidth x (i.val+1)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedStrictSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict-slack slices remain negligible after summing the smooth cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedStrictSlackLoss (K A D J : ℝ) (H : ℕ) : ℝ :=
  Real.exp (A*boxErrorTail (P H))*projectedEnvelope J (P H)*
    (4*A*(Real.exp (K*cofactorScale H)*boxErrorTail H)+
      D*(Real.exp (K*cofactorScale H)/(H : ℝ)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedPrimeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-box summation for a specified subfamily of the actual basic tuples. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def restrictedPrimeGrid (x : ℝ) (H : ℕ) (Q : Finset (Fin (L x H) → ℕ)) :=
  (fullPrimeGrid x H).filter (fun b => ∃ p ∈ Q, primePrefixCoord p ∈ unitGridCell b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackEnclosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A failing strict-slack witness puts its entire unit prime box in a thin shell. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def strictSlackFailure (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  {u | B x-B x/(m x : ℝ)^4 < ∑ j, a (j.val+1)*u j ∨
    ∃ i : Fin R, prefixLinear N u (Fin.castLE hRN i) <
      u (Fin.castLE hRN i)/((m x-(i.val+1) : ℕ) : ℝ)^4}

def FailsStrictSlack {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    (1-1/((m x-i : ℕ) : ℝ)^4)*remainderCoord x η i <
      ∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tuple discard caused by failure of the strict-slack condition. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def strictSlackRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter FailsStrictSlack

def strictSlackTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ∃ η ∈ strictSlackRemainders x H,
    prefixOfRemainder x H η=τ.tail)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleTotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual arithmetic realization of tuples and the finite-map comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def wholePreimage {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : ℕ :=
  p * suffixPreimage η 0

def totientValues (t : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊t⌋₊).filter IsTotient

def uncoveredValues (x : ℝ) (H : ℕ) (t : ℝ) : Finset ℕ :=
  totientValues t \ (tupleFinset x H t).image tupleValue

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuredRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from Ford's canonical preimage coordinates to basic witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def fordRemainder (x : ℝ) (H n : ℕ) : RemainderDatum (L x H) :=
  ⟨fun i => fordPrime n (i.val+1),fordCofactor n (L x H+1)⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UntruncatedRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeOnly {J : ℕ} (η : RemainderDatum J) : RemainderDatum J := ⟨η.primes,1⟩

def IsUntruncatedRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  0 < η.cofactor ∧ IsBasicRemainder x H (primeOnly η) ∧
    largestPrimeFactor η.cofactor ≤ remainderPrime η (L x H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ValueOmega
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def largeOmegaValues (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => 20*B x < (n.primeFactorsList.length : ℝ))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed cofactor and the ordered tail-prime vector determine a witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailPrimeVector {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℕ :=
  fun i => tailPrime η (H-1-i.val)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-dimensional aggregation of a finite witness family with fixed cofactor. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessPrimeRegion {H R : ℕ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ)) (p : Fin (H-P H) → ℕ) : Set (Fin R → ℝ) :=
  ⋃ η ∈ W.filter (fun η => tailPrimeVector η=p), S η

def witnessBoxRegion {H R : ℕ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ)) (b : Fin (H-P H) → ℕ) : Set (Fin R → ℝ) :=
  ⋃ η ∈ W.filter (fun η => tailVector η ∈ unitGridCell b), S η

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform prime mass for the boxes occupied by discrete witness tails. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailBoxIndex {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℕ :=
  fun i => ⌊tailVector η i⌋₊+1

def witnessGrid {H : ℕ} (W : Finset (TailDatum H)) : Finset (Fin (H-P H) → ℕ) :=
  W.image tailBoxIndex

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relating our terminal coefficient to Ford's stronger terminal inequality. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def fordSimplex (N : ℕ) (B : ℝ) : Set (Fin (N+2) → ℝ) :=
  prefixRegion (N+2) B 0 0 ∩
    {u | u (Fin.last (N+1)) ≤ u ⟨N, by omega⟩}

def shrinkLast (N : ℕ) : (Fin (N+2) → ℝ) →ₗ[ℝ] (Fin (N+2) → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun i => if i = Fin.last (N+1) then a 1 else 1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The fixed-deviation consequence of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 6.1, (6.6)--(6.8), pp. 30--31.
We use deviation 1/40 only. For the lower tail take
`theta = (1/40)/(1-1/40)` in (6.6); for the upper tail take
`theta = -(1/40)/(1+1/40)` in (6.7) or (6.8), splitting at
`-i*lambda_i/L`. The uniform bounds (6.4) give positive absolute
constants in `exp (-c*(L-i))`. Letting the terminal cutoff decrease to
zero and rescaling the simplex gives precisely the input below.
The transfer from Ford's terminal coefficient 1 to our coefficient a_1
is proved here using `shrinkLast`, rather than assumed in this input.
-/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

def fordSimplexCenter (N : ℕ) (B : ℝ) (i : Fin (N+2)) : ℝ :=
  B*rho^(i.val+1)*(1-(i.val+1 : ℝ)/(N+2))

def fordCoordinateBad (N : ℕ) (B : ℝ) (i : Fin (N+2)) : Set (Fin (N+2) → ℝ) :=
  {u | (1/40 : ℝ) < |u i/fordSimplexCenter N B i-1|}

def FordCoordinateConcentrationInput : Prop :=
  ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (fordSimplex N B)).toReal

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TruncatedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration at the full-scale bands after truncating the simplex. -/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

def fullSimplexCenter (m : ℕ) (B : ℝ) (k : ℕ) : ℝ :=
  B*rho^k*((m-k : ℕ) : ℝ)/m

def coarseCoordinateBad (m : ℕ) (B : ℝ) {N : ℕ} (i : Fin N) : Set (Fin N → ℝ) :=
  {u | u i < (95/100 : ℝ)*fullSimplexCenter m B (i.val+1) ∨
    (105/100 : ℝ)*fullSimplexCenter m B (i.val+1) < u i}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PhaseBandTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase-band comparison and the actual coordinate scaling bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def fullBoxScale (x : ℝ) (H : ℕ) (i : Fin (L x H)) : ℝ :=
  enlargementScale (fun r => 1+simplexBoxError 4 (m x-r)) i


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullBoxConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration for the actual phase bands in the enlarged full simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def fullBoxSimplex (x : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  enlargedSimplex N (B x) (1+simplexBoxError 4 (m x))
    (fun i => 1+simplexBoxError 4 (m x-(i.val+1)))

def phaseCoordinateBad (x : ℝ) {N : ℕ} (i : Fin N) : Set (Fin N → ℝ) :=
  {u | u i < (91/100 : ℝ)*bandScale x (i.val+1) ∨
    (109/100 : ℝ)*bandScale x (i.val+1) < u i}

def retainedPhaseBad (x : ℝ) (H N : ℕ) (hRN : R x H ≤ N) : Set (Fin N → ℝ) :=
  ⋃ i : Fin (R x H), fullBoxSimplex x N ∩ phaseCoordinateBad x (Fin.castLE hRN i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-dimensional band loss vanishes after both normalization and
the entire discrete-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedBandLoss (K C J c : ℝ) (H : ℕ) : ℝ :=
  Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
    projectedEnvelope J (P H)*((Real.exp (-c/2))^H/(1-Real.exp (-c/2)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnionVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact union-volume coefficient and its finite-tail limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessFinset (H : ℕ) (s : ℝ) (d : ℕ) : Finset (TailDatum H) :=
  (allTailData H).filter (fun η => η ∈ witnesses H s d)

def unionVolumeCoefficient (H : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (tailValueBound H),
    if IsTotient d then f ((ell d : ℝ)/d)/d *
      (volume (⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η)).toReal /
        G x (m x)
    else 0

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessUnionLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the band-removal estimate to the actual unions at each tail value. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def activeWitnesses (H : ℕ) (s : ℝ) : Finset (TailDatum H) :=
  (allTailData H).filter (IsWitness H s)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_VolumeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The banded perturbed volume and the exact finite coefficient differ by
a vanishing normalized error. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def exactWitnessUnion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  ⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η

def perturbedWitnessUnion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  ⋃ η ∈ witnessFinset H (theta x) d,
    perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundaryGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite boundary-box error in the prime mass comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def witnessBandedRegion (x : ℝ) (H : ℕ) (η : TailDatum H) : Set (Fin (R x H) → ℝ) :=
  perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H

def witnessBoundaryGrid (x : ℝ) (H : ℕ) (η : TailDatum H) : Finset (Fin (R x H) → ℕ) :=
  gridOuter (bandGrid x H) (witnessBandedRegion x H η) \
    gridInner (bandGrid x H) (witnessBandedRegion x H η)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedPrimeCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact largest-prime fibers and the negligible lower cutoff. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def shiftedPrimeSet (x t : ℝ) (D : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊1+t/D⌋₊).filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LowerPrimeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower bound on the largest prime has negligible cost in every actual fiber. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def headCutoffLoss (x : ℝ) : ℝ :=
  (x^(9/10 : ℝ)+1)*Real.exp ((Real.log x)^(4/5 : ℝ))*Real.log x/x

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleMassApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-prime summation over the actual finite tuple set, with all weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def weightedTupleCount (x : ℝ) (H : ℕ) (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ τ ∈ tupleFinset x H t, f ((ell τ.tail.d : ℝ)/τ.tail.d)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothCofactorMoment
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Rankin moment for the smooth cofactor discarded in extraction. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def powerReciprocal (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^σ/(n : ℝ)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),mul_div_mul_comm]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def cofactorExceptionValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  (totientValues x).filter (fun v => ∃ n : ℕ, 0<n ∧ n.totient=v ∧
    extractedStructureCondition x (P H) n ∧ x^(9/10 : ℝ) ≤ fordPrime n 0 ∧
    Real.exp (2*bandScale x (L x H))<Real.log (fordCofactor n (L x H+1)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ElementaryExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def smallValues (x : ℝ) : Finset ℕ := Finset.Icc 1 ⌊x^(19/20 : ℝ)⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTStructureInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The qualitative all-preimage structural condition. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def ExtractedStructureInput : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ P : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        (δ P+ε)*tupleNormalization x

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllPreimageCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform arithmetic extraction for every preimage outside explicit exceptional values. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def basicExceptionValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  (preimageExceptionValues x (extractedStructureCondition x (P H)) ∪ smallValues x) ∪
    (largeOmegaValues x ∪ cofactorExceptionValues x H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveRoots
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local sieve densities for a prime q with b*q+1 also prime. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def shiftedSieveRoots (p b : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun r => r*((b:ZMod p)*r+1)=0)

lemma shiftedSieveRoots_of_dvd (p b : ℕ) [Fact p.Prime] (hpb : p ∣ b) :
    shiftedSieveRoots p b = {0} := by
  have hb : (b:ZMod p)=0 := by simpa only [ZMod.natCast_eq_zero_iff] using hpb
  ext r
  simp [shiftedSieveRoots,hb]

lemma shiftedSieveRoots_of_not_dvd (p b : ℕ) [Fact p.Prime] (hpb : ¬p ∣ b) :
    shiftedSieveRoots p b = {0,-(b:ZMod p)⁻¹} := by
  have hb : (b:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hpb
  have hlin (r : ZMod p) : (b:ZMod p)*r+1=0 ↔ r=-(b:ZMod p)⁻¹ := by
    constructor
    · intro hr
      apply mul_left_cancel₀ hb
      rw [mul_neg,mul_inv_cancel₀ hb]
      exact eq_neg_of_add_eq_zero_left hr
    · rintro rfl
      simp [hb]
  ext r
  simp [shiftedSieveRoots,mul_eq_zero,hlin]

lemma shiftedSieveRoots_card (p b : ℕ) [Fact p.Prime] :
    (shiftedSieveRoots p b).card = if p ∣ b then 1 else 2 := by
  by_cases hpb : p ∣ b
  · simp [shiftedSieveRoots_of_dvd p b hpb,hpb]
  · rw [shiftedSieveRoots_of_not_dvd p b hpb,ite_eq_right hpb]
    have hb : (b:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff b p).not.mpr hpb
    exact Finset.card_pair (Ne.symm (neg_ne_zero.mpr (inv_ne_zero hb)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete two-linear-form sieve used for shifted primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def shiftedSievePolynomial (b q : ℕ) : ℕ := q*(b*q+1)

def oddSievePrimes (z : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter (fun p => p ≠ 2)

lemma mem_oddSievePrimes {z p : ℕ} : p ∈ oddSievePrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddSievePrimes,Nat.mem_primesLE,and_assoc]

lemma oddSievePrimes_prod_squarefree (z : ℕ) : Squarefree (∏ p ∈ oddSievePrimes z,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    have hpp := (mem_oddSievePrimes.mp hp).2.1
    have hqp := (mem_oddSievePrimes.mp hq).2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hd))
  · intro p hp
    exact (mem_oddSievePrimes.mp hp).2.1.squarefree

lemma mem_oddSievePrimes_of_dvd {z p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ oddSievePrimes z,q) : p ∈ oddSievePrimes z := by
  obtain ⟨q,hq,hdq⟩ := hp.prime.exists_mem_finset_dvd hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (mem_oddSievePrimes.mp hq).2.1).mp hdq
  simpa only [he] using hq

def shiftedSieveDensity (b : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ))

lemma shiftedSieveDensity_prime (b p : ℕ) (hp : p.Prime) :
    shiftedSieveDensity b p = if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ) := by
  simp [shiftedSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

lemma shiftedSieveDensity_positive (b p : ℕ) (hp : p.Prime) : 0 < shiftedSieveDensity b p := by
  rw [shiftedSieveDensity_prime b p hp]
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

lemma shiftedSieveDensity_lt_one (b p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    shiftedSieveDensity b p < 1 := by
  rw [shiftedSieveDensity_prime b p hp]
  have hpR : (2:ℝ)<p := by exact_mod_cast (show 2<p by have := hp.two_le; omega)
  split_ifs
  · exact inv_lt_one_of_one_lt₀ (by linarith)
  · exact (div_lt_one (by linarith)).mpr hpR

/-- Every density and support here is concrete; only the local discrepancy and
bounding sum remain to be estimated in the subsequent counting argument. -/
def shiftedPrimeSieve (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Icc 1 X).image (shiftedSievePolynomial b)
  prodPrimes := ∏ p ∈ oddSievePrimes z,p
  prodPrimes_squarefree := oddSievePrimes_prod_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := shiftedSieveDensity b
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => shiftedSieveDensity_positive b p hp
  nu_lt_one_of_prime := fun p hp hd => shiftedSieveDensity_lt_one b p hp
    (mem_oddSievePrimes.mp (mem_oddSievePrimes_of_dvd hp hd)).2.2
  level := y
  one_le_level := hy

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def shiftedSieveWeight (b p : ℕ) : ℝ :=
  shiftedSieveDensity b p / (1-shiftedSieveDensity b p)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveRoots
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local three-linear-form sieve in Ford's collision argument. -/
noncomputable section
namespace TotientAsymptotic

def tripleSieveRoots (p a b : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun r => r*((a:ZMod p)*r+1)*((b:ZMod p)*r+1)=0)

lemma tripleSieveRoots_eq_union (p a b : ℕ) [Fact p.Prime] :
    tripleSieveRoots p a b = shiftedSieveRoots p a ∪ shiftedSieveRoots p b := by
  ext r
  simp only [tripleSieveRoots,shiftedSieveRoots,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union,mul_eq_zero]
  tauto

lemma zero_mem_tripleSieveRoots (p a b : ℕ) [NeZero p] :
    (0:ZMod p) ∈ tripleSieveRoots p a b := by simp [tripleSieveRoots]

lemma tripleSieveRoots_card_le (p a b : ℕ) [Fact p.Prime] :
    (tripleSieveRoots p a b).card ≤ 3 := by
  have hcard := Finset.card_union_add_card_inter (shiftedSieveRoots p a) (shiftedSieveRoots p b)
  have hint : 1 ≤ (shiftedSieveRoots p a ∩ shiftedSieveRoots p b).card := by
    apply Finset.card_pos.mpr
    exact ⟨0,by simp [shiftedSieveRoots]⟩
  rw [shiftedSieveRoots_card,shiftedSieveRoots_card] at hcard
  rw [tripleSieveRoots_eq_union]
  split_ifs at hcard <;> omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveCRT
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact CRT and interval discrepancies for the three-form collision sieve. -/
noncomputable section
namespace TotientAsymptotic

def tripleSievePolynomial (a b q : ℕ) : ℕ := q*(a*q+1)*(b*q+1)

def tripleRootCount (d a b : ℕ) : ℕ :=
  Nat.card {r : ZMod d // r*((a:ZMod d)*r+1)*((b:ZMod d)*r+1)=0}

lemma tripleRootCount_eq_card (d a b : ℕ) [NeZero d] :
    tripleRootCount d a b = (tripleSieveRoots d a b).card := by
  rw [tripleRootCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete Selberg sieve for q, aq+1 and bq+1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def tripleSievePrimes (z : ℕ) : Finset ℕ := (Nat.primesLE z).filter (fun p => 3 < p)

lemma mem_tripleSievePrimes {z p : ℕ} :
    p ∈ tripleSievePrimes z ↔ p ≤ z ∧ p.Prime ∧ 3 < p := by
  simp [tripleSievePrimes,Nat.mem_primesLE,and_assoc]

lemma tripleSievePrimes_squarefree (z : ℕ) : Squarefree (∏ p ∈ tripleSievePrimes z,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    have hpp := (mem_tripleSievePrimes.mp hp).2.1
    have hqp := (mem_tripleSievePrimes.mp hq).2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hd))
  · intro p hp
    exact (mem_tripleSievePrimes.mp hp).2.1.squarefree

lemma mem_tripleSievePrimes_of_dvd {z p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ tripleSievePrimes z,q) : p ∈ tripleSievePrimes z := by
  obtain ⟨q,hq,hdq⟩ := hp.prime.exists_mem_finset_dvd hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (mem_tripleSievePrimes.mp hq).2.1).mp hdq
  simpa only [he] using hq

def tripleSieveDensity (a b : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (tripleRootCount p a b:ℝ)/p)

lemma tripleSieveDensity_prime (a b p : ℕ) (hp : p.Prime) :
    tripleSieveDensity a b p = (tripleRootCount p a b:ℝ)/p := by
  simp [tripleSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

lemma tripleSieveDensity_positive (a b p : ℕ) (hp : p.Prime) :
    0 < tripleSieveDensity a b p := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleSieveDensity_prime a b p hp,tripleRootCount_eq_card]
  have hc : 0 < (tripleSieveRoots p a b).card :=
    Finset.card_pos.mpr ⟨0,zero_mem_tripleSieveRoots p a b⟩
  exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hp.pos)

lemma tripleSieveDensity_lt_one (a b p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    tripleSieveDensity a b p < 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleSieveDensity_prime a b p hp,tripleRootCount_eq_card]
  apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
  exact_mod_cast (tripleSieveRoots_card_le p a b).trans_lt hp3

def triplePrimeSieve (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Icc 1 X).image (tripleSievePolynomial a b)
  prodPrimes := ∏ p ∈ tripleSievePrimes z,p
  prodPrimes_squarefree := tripleSievePrimes_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := tripleSieveDensity a b
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => tripleSieveDensity_positive a b p hp
  nu_lt_one_of_prime := fun p hp hd => tripleSieveDensity_lt_one a b p hp
    (mem_tripleSievePrimes.mp (mem_tripleSievePrimes_of_dvd hp hd)).2.2
  level := y
  one_le_level := hy

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler-product lower bound for the concrete Selberg denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def tripleSieveWeight (a b p : ℕ) : ℝ :=
  tripleSieveDensity a b p / (1-tripleSieveDensity a b p)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleDiscriminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exactly the primes dividing ab(b-a) can merge roots of the three forms. -/
noncomputable section
namespace TotientAsymptotic

def tripleDiscriminant (a b : ℕ) : ℕ := a*b*(b-a)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TripleSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual simultaneous primes counted by the three-form sieve. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def triplePrimeTuples (a b X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime ∧
    z < q ∧ z < a*q+1 ∧ z < b*q+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllPrimeTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring small q in the three-form sieve. -/
noncomputable section
namespace TotientAsymptotic

def allPrimeTriples (a b X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveCRT
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication of the exact shifted-prime residue counts by the Chinese remainder theorem. -/
noncomputable section
namespace TotientAsymptotic

def shiftedRootCount (d b : ℕ) : ℕ :=
  Nat.card {r : ZMod d // r*((b:ZMod d)*r+1)=0}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedSieveCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact translation of simultaneous shifted primes into the Selberg sieve. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.omega
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def shiftedPrimePairs (b X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (b*q+1).Prime ∧ z<q ∧ z<b*q+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MertensEuler
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite Euler product controlled by a convergent real power series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace TotientAsymptotic

def negativePower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-s)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllShiftedPrimePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the small primes removed by the sieve cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def allShiftedPrimePairs (b X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (b*q+1).Prime)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SieveCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit small-power cutoffs for the two-linear-form sieve. -/
noncomputable section
namespace TotientAsymptotic

def shiftedPrimeCutoff (L : ℝ) : ℕ := ⌊Real.exp (L/(128*Real.log 4))⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedFactorizations
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite encodings for ordered multiplicative factorizations. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def multiplyFactor {k : ℕ} (i : Fin k) (p : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  Function.update f i (p*f i)

def factorAllocations (k : ℕ) : List ℕ → Finset (Fin k → ℕ)
  | [] => {fun _ => 1}
  | p::L => ((Finset.univ : Finset (Fin k)) ×ˢ factorAllocations k L).image
      (fun t => multiplyFactor t.1 p t.2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CommonPrimeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal mass after one common largest prime has been extracted. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

abbrev PairedFactors (k : ℕ) := (Fin k → ℕ) × (Fin k → ℕ)

def pairedProduct {k : ℕ} (f : PairedFactors k) : ℕ := ∏ j,f.1 j

structure CommonPrimeWitness {k : ℕ} (a b : ℕ) (i : Fin k) (y T : ℝ)
    (f : PairedFactors k × ℕ) : Prop where
  left_pos : 0 < a*f.1.1 i
  right_pos : 0 < b*f.1.2 i
  left_le : (a*f.1.1 i:ℕ) ≤ y
  right_le : (b*f.1.2 i:ℕ) ≤ y
  prime_lower : T ≤ f.2
  prime : f.2.Prime
  left_prime : (a*f.1.1 i*f.2+1).Prime
  right_prime : (b*f.1.2 i*f.2+1).Prime
  different : a*f.1.1 i*f.2+1 ≠ b*f.1.2 i*f.2+1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeFactorBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic of the prime-factor bands in Ford's collision argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def partBetween (n : ℕ) (U V : ℝ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)).prod

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite factor states for the successive cutoffs in Ford's iteration. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def factorProduct {b : ℕ} (t : ShiftedPair b) : ℕ := ∏ j,t.left j

def lowerState {b : ℕ} (t : ShiftedPair b) (U : ℝ) : ShiftedPair b where
  left j := partBelow (t.left j) U
  right j := partBelow (t.right j) U
  remainder := t.remainder

def stateBand {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b) (U V : ℝ) : PairedFactors k :=
  (fun j => partBetween (t.left (Fin.castLE hk j)) U V,
   fun j => partBetween (t.right (Fin.castLE hk j)) U V)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordLargePrimeCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's ordered prime coordinates give the required number of distinct large primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def distinctPrimesAbove (n : ℕ) (U : ℝ) : Finset ℕ :=
  (partBetween n U n).primeFactors

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalSieveModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete one-dimensional sieve for integers avoiding a prime interval. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def intervalSievePrimes (S z : ℕ) : Finset ℕ :=
  (oddSievePrimes z).filter (fun p => S < p)

lemma intervalSieve_prod_dvd (S z : ℕ) :
    (∏ p ∈ intervalSievePrimes S z,p) ∣ ∏ p ∈ oddSievePrimes z,p :=
  Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)

lemma intervalSieve_squarefree (S z : ℕ) :
    Squarefree (∏ p ∈ intervalSievePrimes S z,p) :=
  (oddSievePrimes_prod_squarefree z).squarefree_of_dvd (intervalSieve_prod_dvd S z)

def intervalSieveDensity : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (p:ℝ)⁻¹)

lemma intervalSieveDensity_prime {p : ℕ} (hp : p.Prime) :
    intervalSieveDensity p = (p:ℝ)⁻¹ := by
  simp [intervalSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

def intervalPrimeSieve (S X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := Finset.Icc 1 X
  prodPrimes := ∏ p ∈ intervalSievePrimes S z,p
  prodPrimes_squarefree := intervalSieve_squarefree S z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := intervalSieveDensity
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by
    rw [intervalSieveDensity_prime hp]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => by
    rw [intervalSieveDensity_prime hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  level := y
  one_le_level := hy

def intervalSifted (S X z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (∏ p ∈ intervalSievePrimes S z,p).Coprime n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntervalSieveDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval sieve has the reciprocal Euler-product denominator. -/
noncomputable section
open scoped BigOperators
open BoundingSieve SelbergSieve
namespace TotientAsymptotic

def intervalSieveWeight (p : ℕ) : ℝ := 1/((p:ℝ)-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A value count with the band restrictions supplied by actual normal preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalBandExponent (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) : ℝ :=
  ∑ j : Fin k,(((j.val+2:ℕ):ℝ)*(B (Y j.val)-B (Y (j.val+1))+D)-
    ((j.val+2:ℕ):ℝ)*(B (Y j.val)-B (Y (j.val+1))-Real.sqrt (B S*B (Y j.val)))*
      Real.log (j.val+2))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalBandExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping the upper-count exponent into Ford's renewal coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def countBandWeight (j : ℕ) : ℝ := (j:ℝ)*(1-Real.log j)

def normalBandError (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) : ℝ :=
  D*(∑ j ∈ Finset.range k,((j+2:ℕ):ℝ))+
    ∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandUnionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual normal-preimage count over a finite family of cutoff vectors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def NormalBandWitness (S X k : ℕ) (Y : ℕ → ℕ) (v : ℕ) : Prop :=
  ∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
    (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
    SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
    (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
    ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeFactorNormalityCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting actual nonnormal primes with a sufficiently large final prime factor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalityPrimeCutoff (x : ℝ) : ℝ := Real.exp (Real.log x/(100*B x))

def normalityLargeFactorPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (nonNormalPrimes S N).filter (fun p => normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))

def normalityCofactors (S : ℝ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun b => (b:ℝ)*normalityPrimeCutoff N ≤ N ∧ AbnormalCofactor S N b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary primes are counted by their smooth predecessors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalitySmallFactorPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (nonNormalPrimes S N).filter (fun p => ¬normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeExtensionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct totient values after adjoining a large prime to a residual preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def quarterPrimes (x : ℝ) (d : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊1+x/d⌋₊).filter (fun p => x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x)

def primeExtensionValues (x : ℝ) (d : ℕ) : Finset ℕ :=
  (quarterPrimes x d).biUnion (fun p => {(p-1)*d,p*d})

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TotientCountingEnvelope
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic counting envelope used to bootstrap the global upper bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def dyadicTotientEnvelope (J : ℕ) : ℝ :=
  max 1 ((Finset.range (J+1)).sup' (by simp)
    (fun k => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargeNonNormalValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct exceptional totient values, grouped by the residual value. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def abnormalExtensionPrimes (S x : ℝ) (d : ℕ) : Finset ℕ :=
  (quarterPrimes x d).filter (fun p => 4 ≤ p ∧ ¬IsNormalPrime S p)

def abnormalExtensionValues (S x : ℝ) (d : ℕ) : Finset ℕ :=
  (abnormalExtensionPrimes S x d).biUnion (fun p => {(p-1)*d,p*d})

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.Wiener
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability
attribute [-simp] _root_.SelbergSieve.selbergBoundingSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]


noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar



@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

local instance instCoeForallRealForallComplex_solutions_1_rb9581e_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDivisorValueCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact value counting by a selected prime divisor of a preimage. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def divisorExtensionValues (x : ℝ) (p : ℕ) : Finset ℕ :=
  (totientValues (x/(p-1:ℕ))).image (fun d => (p-1)*d) ∪
    (totientValues (x/(p-1:ℕ))).image (fun d => p*d)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeavyOmegaMoment
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed 15/8 moment needed for the large-Omega nice-value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def heavyOmegaReciprocal : ℕ →* ℝ where
  toFun n := (15/8:ℝ)^n.primeFactorsList.length/(n:ℝ)
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m=0
    · subst m; simp
    by_cases hn : n=0
    · subst n; simp
    have hh := (Nat.perm_primeFactorsList_mul hm hn).length_eq
    rw [List.length_append] at hh
    simp only [hh,Nat.cast_mul,pow_add]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RegularValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete regular-value exception used in the Ford counting bootstrap. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- These are exactly the regularity conditions used in the band count;
the preimage conditions hold for every preimage of the value. -/
def CountingRegular (S : ℕ) (X : ℝ) (v : ℕ) : Prop :=
  (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧ SquarefreeAbove v S ∧
    ∀ n : ℕ,0 < n → n.totient=v → SquarefreeAbove n S ∧
      ∀ p ∈ n.primeFactors,IsNormalPrime S p

def nonNormalValues (S x : ℝ) : Finset ℕ :=
  (totientValues x).filter (fun v => ∃ n p : ℕ,0 < n ∧ n.totient=v ∧
    p.Prime ∧ p ∣ n ∧ ¬IsNormalPrime S p)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TwoBandCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-coordinate upper estimate needed to start Ford's counting bootstrap. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def twoBandCutoffs (S z w : ℕ) (j : ℕ) : ℕ := if j=0 then z else if j=1 then w else S

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LoglogGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer cutoffs on the unit log-log grid used in Ford's counting argument. -/
noncomputable section
namespace TotientAsymptotic

def loglogCutoff (b : ℝ) : ℕ := ⌊Real.exp (Real.exp b)⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CappedLoglogGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cap the log-log grid at the upper sieve endpoint. -/
noncomputable section
namespace TotientAsymptotic

def cappedLoglogIndex (K : ℕ) (t : ℝ) : ℕ := min (⌊t⌋₊-1) K

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TwoCoordinateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-coordinate instance of Ford Lemma 4.2, before absorbing errors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def coordinateCutoffPairs (S K : ℕ) (T : ℝ) : Finset (ℕ×ℕ) :=
  (((Finset.Icc 2 K).product (Finset.Icc 2 K)).image
    (fun q : ℕ×ℕ => (loglogCutoff q.1,loglogCutoff q.2))).filter
      (fun q => S ≤ q.2 ∧ q.2 ≤ q.1 ∧ T ≤ a 1*B q.1+a 2*B q.2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoffs for the initial two-coordinate counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapTop (b : ℝ) : ℕ := ⌊b-Real.log (20*b)⌋₊-1

def bootstrapBottom (b : ℝ) : ℕ := ⌊b/100000000⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalTail
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail coefficients in (1-F(z))/(1-z/rho). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def renewalTail (n : ℕ) : ℝ := ∑' k : ℕ, a (n+k+1)*rho^(k+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMoment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the tail generating series at its renewal root. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def momentPair (p : ℕ×ℕ) : ℝ := a (p.1+p.2+1)*rho^(p.1+p.2+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalKernel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative transformed kernel in Ford's renewal argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def renewalIncrement (n : ℕ) : ℝ := renewalTail (n+1)-renewalTail n

def renewalKernel : ℕ → ℝ
  | 0 => 1-renewalIncrement 0
  | n+1 => renewalIncrement n-renewalIncrement (n+1)

def renewalResolvent : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ j ∈ Finset.range (n+1), renewalKernel j*renewalResolvent (n-j)
termination_by n => n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeriesAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal coefficient identities for Ford's transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def Lseries : PowerSeries ℝ := PowerSeries.mk renewalTail
def Pseries : PowerSeries ℝ := PowerSeries.mk renewalKernel
def Useries : PowerSeries ℝ := PowerSeries.mk renewalResolvent
def Aseries : PowerSeries ℝ := PowerSeries.X*PowerSeries.mk (fun n => a (n+1))
def Gseries : PowerSeries ℝ := PowerSeries.mk g
def Hseries : PowerSeries ℝ := (1-PowerSeries.X)^2*Useries

/-- The coefficients of the regular factor are uniformly bounded by four. -/
def renewalRegular (n : ℕ) : ℝ := PowerSeries.coeff n Hseries

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPowerBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary logarithmic budgets at a power-four-thirds threshold. -/
noncomputable section
namespace TotientAsymptotic

def rowMassCutoffHeight (F δ : ℝ) : ℝ :=
  1000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RowCutoffModel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The size of the explicit residual cutoff for Ford's exponential row slack. -/
noncomputable section
namespace TotientAsymptotic

def rowModelDecay (t : ℝ) : ℝ :=
  (Real.exp (-t/40)/40000)^2/(12000000*(t+2)^6)

def rowModelConstant (F : ℝ) : ℝ := Real.log 2000000000+
  (4/3:ℝ)*(Real.log (10000*(F+31)^2)+2*Real.log 40000+Real.log 12000000)+
  8*(Real.log 24000+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapGoodValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The surviving values satisfy the bootstrap inequality for every preimage. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def BootstrapGood (x : ℝ) (v : ℕ) : Prop :=
  CountingRegular (loglogCutoff (bootstrapBottom (B x))) x v ∧
    ∀ n : ℕ,0 < n → n.totient=v →
      a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TwoPrimeResidualMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual values after one prime extension and their reciprocal mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def singlePrimeExtensions (P M : Finset ℕ) : Finset ℕ :=
  M ∪ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m}))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete strictly smaller dyadic index for the counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapIndex (J : ℕ) : ℕ := ⌊(J:ℝ)^(41/50:ℝ)⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete logarithmic majorant for the counting recurrence. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapHeight (J : ℕ) : ℝ := 1+Real.log ((J:ℝ)+1)
def bootstrapMajorant (J : ℕ) : ℝ := Real.exp (9*(Real.log (bootstrapHeight J))^2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapRealCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counting bootstrap at arbitrary real endpoints. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def countingDyadicIndex (x : ℝ) : ℕ := ⌈Real.log x/Real.log 2⌉₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BootstrapExceptionalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit, rather than merely vanishing, preliminary exceptional-value bounds. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapErrorWeight (b : ℝ) : ℝ :=
  (b+4)^6*Real.exp (9*(Real.log (b+4))^2-b/600000000)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedFiber
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The published inverse-fiber input and its arithmetic consequences.

`FordFiberPropagation d` is the single-seed specialization of the construction
in Kevin Ford, *The distribution of totients*, Ramanujan Journal 2 (1998),
67--151, arXiv:1104.3264v2 (2013), Section 5, equations (5.10)--(5.19),
and the explicit full-fiber statement in Section 7.3, p. 39.

`PPTBoundedFiberPropagation d` additionally retains the bounded multiplier
ratio from Pollack--Pomerance--Treviño, *Sets of monotonicity for Euler's
totient function*, Ramanujan Journal 30 (2013), 379--398, Lemma 4.1,
specialized to the same seed in both positions and D = d, together with
Ford's Theorem 1 to replace its scale Z(x) by V(x).  The lower-bound
constant may depend on d; the absolute bound in the published lemma is
weakened here to an existential constant for this fixed seed.

These are explicit hypotheses, not axioms.  The conclusions below count
large least-preimage ratios; they do not assert the companion asymptotic.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def FullFiber (d b : ℕ) : Prop :=
  ∀ n : ℕ, (0 < n ∧ n.totient = d*b.totient) ↔
    ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m

def PPTBoundedFiberPropagation (d : ℕ) : Prop :=
  ∃ η K : ℝ, 0 < η ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
    0 < x ∧ ∃ S : Finset ℕ, η * V x ≤ (S.card : ℝ) ∧
      ∀ b ∈ S, 0 < b ∧ ((d*b.totient : ℕ) : ℝ) ≤ x ∧
        FullFiber d b ∧ (b : ℝ) / b.totient ≤ K

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundedRatioValues
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def boundedRatioValues (x a b : ℝ) : Finset ℕ :=
  (totientValues x).filter (fun v => a ≤ (ell v : ℝ)/v ∧ (ell v : ℝ)/v ≤ b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeInterval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def primeInterval (l u : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊u⌋₊).filter (fun p : ℕ => l < p)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RemovePrimeFactor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one designated prime from a factorization and reconstructing it. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  Function.update f i (f i/q)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CommonLargestPrime
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recoverable extraction of the common largest prime from an actual pair of factors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def commonLargestEncoding {k : ℕ} (i : Fin k) (f : PairedFactors k) : PairedFactors k × ℕ :=
  let q := largestPrimeFactor (f.1 i)
  ((divideFactor i q f.1,divideFactor i q f.2),q)

def commonPrimeDecode {k : ℕ} (i : Fin k) (e : PairedFactors k × ℕ) : PairedFactors k :=
  (multiplyFactor i e.2 e.1.1,multiplyFactor i e.2 e.1.2)

structure CommonLargestConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  same_prime : largestPrimeFactor (f.1 i)=largestPrimeFactor (f.2 i)
  prime_lower : T ≤ largestPrimeFactor (f.1 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  different : a*f.1 i+1 ≠ b*f.2 i+1
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DistinctPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal mass after extracting the two unequal largest primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

abbrev TwoPrimeEncoding (k : ℕ) := PairedFactors k × (ℕ × ℕ)

def twoPrimeWeight {k : ℕ} (e : TwoPrimeEncoding k) : ℝ :=
  ((pairedProduct e.1*(e.2.1*e.2.2):ℕ):ℝ)⁻¹

def distinctCoefficient {k : ℕ} (a : ℕ) (i j : Fin k) (r : PairedFactors k) (q : ℕ) : ℕ :=
  a*multiplyFactor j q r.1 i

structure DistinctPrimeWitness {k : ℕ} (a b : ℕ) (i j : Fin k) (y T : ℝ)
    (e : TwoPrimeEncoding k) : Prop where
  left_lower : T ≤ e.2.1
  left_prime : e.2.1.Prime
  left_shift_prime : (distinctCoefficient a i j e.1 e.2.2*e.2.1+1).Prime
  left_pos : 0 < distinctCoefficient a i j e.1 e.2.2
  left_le : (distinctCoefficient a i j e.1 e.2.2:ℝ) ≤ y
  right_lower : T ≤ e.2.2
  right_prime : e.2.2.Prime
  right_shift_prime : (b*e.1.2 i*e.2.2+1).Prime
  right_pos : 0 < b*e.1.2 i
  right_le : ((b*e.1.2 i:ℕ):ℝ) ≤ y

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DistinctPrimeRemoval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two cross-prime removals in the unequal-largest-prime case. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def doubleDivide {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  divideFactor j q (divideFactor i p f)

def doubleMultiply {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  multiplyFactor i p (multiplyFactor j q f)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DistinctLargestEncoding
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction and residual bounds for unequal largest primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

structure DistinctLargestConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  order : largestPrimeFactor (f.2 i) < largestPrimeFactor (f.1 i)
  left_lower : T ≤ largestPrimeFactor (f.1 i)
  right_lower : T ≤ largestPrimeFactor (f.2 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V

def CrossRemoval {k : ℕ} (i j l : Fin k) (f : PairedFactors k) : Prop :=
  l ≠ i ∧
  largestPrimeFactor (f.2 i) ∣ divideFactor i (largestPrimeFactor (f.1 i)) f.1 j ∧
  largestPrimeFactor (f.1 i) ∣ divideFactor i (largestPrimeFactor (f.2 i)) f.2 l

def distinctLargestEncoding {k : ℕ} (i j l : Fin k) (f : PairedFactors k) : TwoPrimeEncoding k :=
  let p := largestPrimeFactor (f.1 i)
  let q := largestPrimeFactor (f.2 i)
  ((doubleDivide i j p q f.1,doubleDivide i l q p f.2),(p,q))

def distinctPrimeDecode {k : ℕ} (i j l : Fin k) (e : TwoPrimeEncoding k) : PairedFactors k :=
  (doubleMultiply i j e.2.1 e.2.2 e.1.1,doubleMultiply i l e.2.2 e.2.1 e.1.2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionBandData
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single interval's collision data and its left-right symmetry. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

structure CollisionBandConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  left_lower : T ≤ largestPrimeFactor (f.1 i)
  right_lower : T ≤ largestPrimeFactor (f.2 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  different : a*f.1 i+1 ≠ b*f.2 i+1
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V
  squarefree : Squarefree (pairedProduct f)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cutoff geometry for the application of Ford's interval sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordFactorState {b : ℕ} (t : ShiftedPair b) (V : ℝ) : ShiftedPair b where
  left j := partBelow (t.left j-1) V
  right j := partBelow (t.right j-1) V
  remainder := t.remainder

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandSupports
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support, equality and squarefreeness of the actual bands of a Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBand {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b) (Y : ℕ → ℝ) : PairedFactors k :=
  (fun j => partBetween (t.left (Fin.castLE hk j)-1) (Y k) (Y (k-1)),
   fun j => partBetween (t.right (Fin.castLE hk j)-1) (Y k) (Y (k-1)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandNormality
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise normality cap for a band in Ford's iterative count. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandCap (k : ℕ) (y S : ℝ) (Y : ℕ → ℝ) : ℝ :=
  (k:ℝ)*(B (Y (k-1))-B (Y k)+Real.sqrt (B S*B y))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_InitialRoughEncoding
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extracting the largest prime in the first, large rough factor. -/
noncomputable section
namespace TotientAsymptotic

structure InitialRoughConditions (a b d : ℕ) (y U : ℝ) (n : ℕ) : Prop where
  squarefree : Squarefree n
  large : Real.sqrt y < n
  size : ((d*n:ℕ):ℝ) ≤ y
  left_prime : (a*n+1).Prime
  right_prime : (b*n+1).Prime
  different : a*n+1 ≠ b*n+1
  left_le : ((a*n:ℕ):ℝ) ≤ y
  right_le : ((b*n:ℕ):ℝ) ≤ y
  omega_le : (n.primeFactorsList.length:ℝ) ≤ 3*B y
  support : ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ y

def initialRoughEncoding (n : ℕ) : ℕ × ℕ := (n/largestPrimeFactor n,largestPrimeFactor n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordInitialFactor
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first common rough factor of an actual Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordInitialFactor {b : ℕ} (hb : 1 ≤ b) (t : ShiftedPair b) (Y : ℕ → ℝ) : ℕ :=
  partAbove (t.left ⟨0,by omega⟩-1) (Y 1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_InitialRoughData
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sieve data supplied by extraction from the initial rough factor. -/
noncomputable section
namespace TotientAsymptotic

structure InitialPrimeData (a b d : ℕ) (y L : ℝ) (e : ℕ × ℕ) : Prop where
  residual_pos : 0 < e.1
  prime : e.2.Prime
  log_lower : L ≤ Real.log e.2
  size : ((d*e.1*e.2:ℕ):ℝ) ≤ y
  left_pos : 0 < a*e.1
  right_pos : 0 < b*e.1
  left_le : ((a*e.1:ℕ):ℝ) ≤ y
  right_le : ((b*e.1:ℕ):ℝ) ≤ y
  different : a*e.1 ≠ b*e.1
  left_prime : (a*e.1*e.2+1).Prime
  right_prime : (b*e.1*e.2+1).Prime

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordInitialCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full first-band count, with the terminal reciprocal mass left explicit. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordStateMass {b : ℕ} (T : Finset (ShiftedPair b)) (Y : ℕ → ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ s ∈ T.image (fun t => fordFactorState t (Y k)),(factorProduct s:ℝ)⁻¹

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothTerminalEncoding
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small smooth terminal factors when only one prime survives. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma smooth_terminal_factorization {d s t e : ℕ} (hd : 0 < d) (heq : d*s=t*e) :
    ∃ d₁ d₂ a b : ℕ,d=d₁*d₂ ∧ t=d₁*a ∧ e=d₂*b ∧ s=a*b := by
  have hdiv : d ∣ t*e := ⟨s,heq.symm⟩
  obtain ⟨d₁,d₂,ht,he,hdd⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  obtain ⟨a,ha⟩ := ht
  obtain ⟨b,hb⟩ := he
  refine ⟨d₁,d₂,a,b,hdd,ha,hb,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [heq,ha,hb,hdd]
  ring

abbrev SmoothTerminalTriple := ℕ × ℕ × ℕ

def terminalFirst (z : SmoothTerminalTriple) : ℕ := z.1

def terminalMiddle (z : SmoothTerminalTriple) : ℕ := z.2.1

def terminalLast (z : SmoothTerminalTriple) : ℕ := z.2.2

/-- The first coordinate is `s`; the equation is `d*s=t*e`. -/
def TerminalConditions (d N : ℕ) (z : SmoothTerminalTriple) : Prop :=
  0 < terminalFirst z ∧ d*terminalFirst z=terminalMiddle z*terminalLast z ∧
  largestPrimeFactor (terminalFirst z) ≤ N

noncomputable def terminalEncoding {N : ℕ} (d : ℕ) (hd : 0 < d)
    (z : SmoothTerminalTriple) (hz : TerminalConditions d N z) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let h := smooth_terminal_factorization hd hz.2.1
  let d₁ := h.choose
  let d₂ := h.choose_spec.choose
  let a := h.choose_spec.choose_spec.choose
  let b := h.choose_spec.choose_spec.choose_spec.choose
  ((d₁,d₂),(a,b))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalStateCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicity bounds for the final smooth factor states. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def terminalRight {k : ℕ} (t : ShiftedPair k) : Fin (k+1) → ℕ :=
  Fin.cons t.remainder t.right

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordTerminalMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal mass bounds for the actual Ford state families. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def oneStateTriple (q : ShiftedPair 1) : SmoothTerminalTriple := (q.left 0,q.right 0,q.remainder)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordStateIteration
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite iteration on images of the actual Ford cutoff states. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandCost (C : ℝ) (k : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  (C*(k:ℝ)^2*(B y)^2/(Real.log (U (k-1)))^2)*
    Real.exp (fordBandCap k y S Y*(Real.log k+1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordBandExponent
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping of the band exponents into Ford's coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordBandWeight (k : ℕ) : ℝ := (k:ℝ)*Real.log k+k

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailHeadCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting distinct candidate integers by a finite sum over ordered tails. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def tailHeadPairs {n : ℕ} (x : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) :
    Finset (Σ _p : Fin n → ℕ,ℕ) :=
  Q.sigma (fun p => primeInterval
    (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
    (x/((d*(∏ i,p i).totient:ℕ):ℝ)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The head-prime extension counts actual distinct integers and their totients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def candidateIntegers {n : ℕ} (x : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) : Finset ℕ :=
  (tailHeadPairs x d Q).image (fun z => z.2*(∏ i,z.1 i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalBackground
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive ordered translate of the prefix simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def renewalBackground (N : ℕ) (t : ℝ) (i : Fin N) : ℝ := t*g (N-i.val)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexTilt
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal changes of variables bounding a linear cap of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def simplexDiagonal (N : ℕ) (w : Fin N → ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (Matrix.diagonal w)

def positiveSimplex (N : ℕ) (w : Fin N → ℝ) (T : ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, w i*v i) ≤ T}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixWeights
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded weights expressing each prefix coordinate in standard-simplex variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def prefixSimplexMap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (weightedScale N).comp (prefixLinear N)

def prefixWeight (N : ℕ) (i j : Fin N) : ℝ :=
  if i ≤ j then g (j.val-i.val)/(rho^(i.val+1)*g (j.val+1)) else 0

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentrationExponents
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical exponent saving for fixed one-fortieth deviations. -/
noncomputable section
namespace TotientAsymptotic

def concentrationTilt (M : ℝ) : ℝ := 1/(320*M)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGapWeights
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed simplex weights for an adjacent-coordinate gap. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def prefixGapWeight (N : ℕ) (i : Fin (N+1)) (j : Fin (N+2)) : ℝ :=
  prefixWeight (N+2) i.castSucc j-rho*prefixWeight (N+2) i.succ j

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedTranslateVolume
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive volume of the ordered part of a renewal translate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def orderedSlackRegion (N : ℕ) (B t : ℝ) : Set (Fin N → ℝ) :=
  {v | v ∈ prefixRegion N B 0 0 ∧ StrictAnti v ∧
    ∀ i,t*a (N-i.val) ≤ prefixLinear N v i}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictContractionCost
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube row contraction has a bounded full Jacobian. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def rowContractionError (h : ℕ) : ℝ := 1/(5*(h+1:ℝ)^3)

def rowContractionCost : ℝ := ∑' h : ℕ,(h:ℝ)*rowContractionError h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictPrefixContraction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal contraction imposes strict Ford rows while preserving prime order. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def contractedPrefix (N : ℕ) (B : ℝ) (β : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i,0 ≤ v i) ∧ StrictAnti v ∧
    (∀ i,(∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ v i/β i) ∧
    (∑ i : Fin N,a (i.val+1)*v i) ≤ B}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricContractedFamily
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-volume prime-coordinate families with strict rows and geometric minima. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

def geometricContractedFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  contractedPrefix n (B/(1+rowContractionError m))
    (fun i => 1+rowContractionError (m-(i.val+1))) ∩
    {v | (∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i) ∧
      ∀ i j,i < j → v j ≤ v i/(1+rowContractionError (m-(i.val+1)))}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricCube
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive-volume family retains half of every margin in its unit grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def relaxedGeometricFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  contractedPrefix n (B/(1+rowContractionError m/2))
    (fun i => 1+rowContractionError (m-(i.val+1))/2) ∩
    {v | (∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i) ∧
      ∀ i j,i < j → v j ≤ v i/(1+rowContractionError (m-(i.val+1))/2)}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes around a simplex prefix, without coordinate-band hypotheses. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def prefixCubeCost (N : ℕ) : ℝ :=
  (N:ℝ)^2 + ∑ i : Fin N, g (i.val+1)*((N-i.val:ℕ):ℝ)^2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime mass in arbitrary nonnegative prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def tupleUnitGrid {N : ℕ} (Q : Finset (Fin N → ℕ)) : Finset (Fin N → ℕ) :=
  Q.image (fun p i => ⌊primePrefixCoord p i⌋₊+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixBoxGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite prime grids covering concrete bounded prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def prefixBoxGrid (N : ℕ) (B : ℝ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc 1 (⌊B/a (i.val+1)⌋₊+1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive arithmetic mass for the outer grid of the strict coordinate family. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

def geometricPrimeGrid (x c : ℝ) (n : ℕ) : Finset (Fin n → ℕ) :=
  gridOuter (prefixBoxGrid n (B x/(1+rowContractionError (m x))))
    (geometricContractedFamily (m x) n (B x) c)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadLimitedFamily
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed upper cutoff for the leading tail coordinate costs vanishing volume. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

def headLimitedFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  geometricContractedFamily m n B c ∩ {u | ∀ i,u i ≤ (3/4:ℝ)*B}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadLimitedPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with the leading tail separated from the new head. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def headLimitedPrimeGrid (x c : ℝ) (n : ℕ) : Finset (Fin n → ℕ) :=
  gridOuter (prefixBoxGrid n (B x/(1+rowContractionError (m x))))
    (headLimitedFamily (m x) n (B x) c)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateAbundance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive counting-scale family of actual prime-product candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def rawCandidates (x c : ℝ) (d H : ℕ) : Finset ℕ :=
  candidateIntegers x d (gridPrimeTuples (headLimitedPrimeGrid x c (m x-H)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateNormalHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality exclusion for the head prime on each actual tail interval. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def nonNormalHeadPairs {n : ℕ} (x S : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) :
    Finset (Σ _p : Fin n → ℕ,ℕ) :=
  Q.sigma (fun p => (primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
    (x/((d*(∏ i,p i).totient:ℕ):ℝ))).filter (fun q => ¬IsNormalPrime S q))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTMaximalSuffix
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The maximal common-prefix step in Ford, Section 5, between (5.19) and
(5.20).  The ordering of the candidate primes, rather than a bound for the
whole residual product, rules out a repeated leading prime.  Choosing the
last possible common prefix then forces every nontrivial residual
preimage to have a different largest prime.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The concrete suffix of a finite ordered candidate-prime list. -/
def pptSuffixProduct (p : ℕ → ℕ) (N j : ℕ) : ℕ :=
  ∏ i ∈ Finset.Ico j N, p i

/-- A residual nontrivial preimage whose prime factors fit after the
already removed prefix.  At index zero there is no preceding bound. -/
def PPTPrefixWitness (d : ℕ) (p : ℕ → ℕ) (N j : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ n.totient = d*(pptSuffixProduct p N j).totient ∧
    ¬pptSuffixProduct p N j ∣ n ∧
    (j = 0 ∨ ∀ q : ℕ, q.Prime → q ∣ n → q < p (j-1))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidatePrimeList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counted prime tuples as finite ordered lists for prefix cancellation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def candidatePrimeAt {n : ℕ} (p : Fin n → ℕ) (q i : ℕ) : ℕ :=
  if hi : i < n+1 then (Fin.cons q p : Fin (n+1) → ℕ) ⟨i,hi⟩ else 1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentratedPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous coordinate upper envelope, with a fixed terminal buffer. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

def prefixConcentrationIndices (N L : ℕ) : Finset (Fin (N+2)) :=
  Finset.univ.filter (fun i => i.val < N ∧ L ≤ N+2-(i.val+1))

def prefixConcentrationFailure (N L : ℕ) (B : ℝ) : Set (Fin (N+2) → ℝ) :=
  ⋃ i ∈ prefixConcentrationIndices N L,
    prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateActivePrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split an ordered coordinate vector at its last coordinate above a threshold. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

 def coordinateActivePrefix (n k : ℕ) (u : ℝ) : ℕ :=
  Nat.findGreatest (fun j => u < fordPrimeCoordinate n j) k

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine correction for the unit boxes in a coordinate-deviation count. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def coordinateCubeShift (N : ℕ) : Fin N → ℝ :=
  ((prefixLinear N).equivOfDetNeZero (by rw [prefixLinear_det]; norm_num)).symm
    (fun i => ((N-i.val:ℕ):ℝ)^2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PositiveCoordinateGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous finite-grid rounding of all positive ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def coordinateGridIndex (K n k : ℕ) (j : Fin k) : ℕ :=
  cappedLoglogIndex K (B (fordPrime n (j.val+1)))

def coordinateGridCutoff (L k : ℕ) (g : Fin k → ℕ) (j : ℕ) : ℕ :=
  if hj : j < k then loglogCutoff (g ⟨j,hj⟩) else loglogCutoff L

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete integer parameters for the coordinate-deviation estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateBottom (b ω : ℝ) (k : ℕ) : ℕ :=
  ⌊ω^2*b/(1000000*((k:ℝ)+2)^6)⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateDeviationExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical decay rate used for the exceptional-value estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateDecay (ω : ℝ) (k : ℕ) : ℝ :=
  ω^2/(12000000*((k:ℝ)+2)^6)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateEnlargement
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the terminal coordinates, the diagonal enlargement is uniformly
close to one. At fixed truncation the additive budget correction vanishes. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def coordinateEnlargement (M N : ℕ) : Fin N → ℝ :=
  enlargementScale (fun r => 1+simplexBoxError 0 (M-r))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An effective threshold for the logarithmic budget in the row estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateBudgetConstant (F : ℝ) : ℝ := 10000*(F+31)^2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstFailedRow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first failed row strictly separates the retained primes from the tail. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordRowSum (N : ℕ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (j+1) N, a (r-j)*u r

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MovingSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A slowly growing smoothness cutoff for the exceptional-cofactor count. -/
noncomputable section
namespace TotientAsymptotic

def movingSmoothCutoff (x : ℝ) : ℕ :=
  ⌊Real.exp (Real.log x/(500*B x))⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime prefix before a first failed row belongs to the unbanded simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def fordPrefixPrimes (n K : ℕ) : Fin K → ℕ := fun i => fordPrime n (i.val+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeProductValueMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct residual values of a prime prefix carry no preimage multiplicity. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def primeProductValues {N : ℕ} (P : Finset (Fin N → ℕ)) (D : Finset ℕ) : Finset ℕ :=
  (P.product D).image (fun z => z.2 * (∏ i, z.1 i).totient)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowCountBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-failed-row value counts with the residual mass fully bounded. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def FailedRowMassBudget (F ω U : ℝ) (k : ℕ) : Prop :=
  0 < ω ∧ ω ≤ 1 ∧ 512 ≤ U ∧ 2*Real.exp (Real.exp 1) ≤ U ∧
  10000 ≤ B U ∧ (8000/ω)^2 ≤ B U ∧
  max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 ∧
  4 ≤ (ω/2)*B U ∧ (coordinateDecay (ω/4) k)⁻¹ ≤ Real.exp (coordinateDecay (ω/4) k*B U)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit residual cutoffs satisfying every first-failed-row mass budget. -/
noncomputable section
namespace TotientAsymptotic

def failedRowCutoff (F ω : ℝ) (k : ℕ) : ℝ :=
  Real.exp (Real.exp (rowMassCutoffHeight F (coordinateDecay (ω/4) k)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstFailedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the first-failed-row classes without losing the Gaussian exponent. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def fordRowHolds (x : ℝ) (n i : ℕ) : Prop :=
  fordRowSum (m x) (fordPrimeCoordinate n) i ≤
    xi x i*(if i=0 then B x else fordPrimeCoordinate n i)

def FirstFailedRowAt (x : ℝ) (n j : ℕ) : Prop :=
  (∀ i < j,fordRowHolds x n i) ∧ ¬fordRowHolds x n j

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixReciprocals
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def prefixReciprocalError (H : ℕ) : ℝ := polynomialGeometricTail 0 (Real.exp (-1)) H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixPreimage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-prefix factorization and minimization over a common inverse fiber. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tuplePrimeProduct {r : ℕ} (τ : TotientTuple r) : ℕ := ∏ i, tuplePrimes τ i

def tupleLeastCandidate {r : ℕ} (τ : TotientTuple r) : ℕ :=
  tuplePrimeProduct τ * ell τ.tail.d

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniquePrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def exceptionalTotients (x : ℝ) (H : ℕ) : Finset ℕ :=
  totientValues x ∩ basicExceptionValues x H

def nonuniqueValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  FiniteMap.badValues (goodTupleFinset x H x) (badTupleFinset x H x)
    (totientValues x) (exceptionalTotients x H) tupleValue

def discardedTuples (x : ℝ) (H : ℕ) : Finset (TotientTuple (R x H)) :=
  FiniteMap.badPreimages (tupleFinset x H x) (goodTupleFinset x H x)
    (badTupleFinset x H x) (totientValues x) (exceptionalTotients x H) tupleValue

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LeastPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def candidateInWindow {r : ℕ} (k : ℕ) (x : ℝ) (τ : TotientTuple r) : Prop :=
  (k : ℝ)*x < tupleLeastCandidate τ ∧ (tupleLeastCandidate τ : ℝ) ≤ (k+1 : ℝ)*x

def candidateTuples (x : ℝ) (H k : ℕ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H x).filter (candidateInWindow k x)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedFiber
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

def prefixCandidateFactor {r : ℕ} (ζ : PrefixDatum r) : ℕ :=
  ell ζ.d*∏ i, ζ.primes i

def candidatePrimeSet (x : ℝ) (H k : ℕ) (ζ : PrefixDatum (R x H)) : Finset ℕ :=
  (shiftedPrimeSet x x (prefixDenominator ζ)).filter (fun p : ℕ =>
    (k : ℝ)*x < (p*prefixCandidateFactor ζ : ℕ) ∧
      (p*prefixCandidateFactor ζ : ℕ) ≤ (k+1 : ℝ)*x)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixWeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def prefixQ {r : ℕ} (ζ : PrefixDatum r) : ℝ := ∏ i, (1-(1 : ℝ)/ζ.primes i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullPrefixRatio
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def tupleQ {r : ℕ} (τ : TotientTuple r) : ℝ :=
  prefixQ τ.tail*(1-(1 : ℝ)/τ.head)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed normality: a polynomial logarithmic cutoff beats each bounded local tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localNormalityScale (h : ℕ) : ℝ := Real.exp (Real.exp ((h:ℝ)^4))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocallyConcentratedFamily
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-volume candidate families with upper bounds at every local tail scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

def localCoordinateCap (n : ℕ) (B : ℝ) (i : Fin n) : ℝ :=
  2*B*rho^(i.val+1)*(n-i.val:ℕ)/(n:ℝ)

def locallyConcentratedFamily (m n : ℕ) (B c : ℝ) (L : ℕ) : Set (Fin n → ℝ) :=
  headLimitedFamily m n B c ∩
    {u | ∀ i,i.val+L+2 ≤ n → u i ≤ localCoordinateCap n B i}

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive prime mass with geometric upper bounds at every local index. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localPrimeGrid (x c : ℝ) (L n : ℕ) : Finset (Fin n → ℕ) :=
  gridOuter (prefixBoxGrid n (B x/(1+rowContractionError (m x))))
    (locallyConcentratedFamily (m x) n (B x) c L)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalPrimeSupport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each suffix lies in a prime interval determined only by its distance from the end. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localPrimeHeight (A : ℝ) (L h : ℕ) : ℝ :=
  A*(h+L+2:ℕ)*(rho^(h+L+2))⁻¹+2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityLayer
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-index normality exclusion in the local candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localAbnormalTuples (x c : ℝ) (L H : ℕ)
    (i j : Fin (m x-H)) : Finset (Fin (m x-H) → ℕ) :=
  (gridPrimeTuples (localPrimeGrid x c L (m x-H))).filter
    (fun p => ¬IsNormalPrime (localNormalityScale (m x-i.val)) (p j))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalityDiscard
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of all local normality failures in the actual candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localNormalityFailures (x c : ℝ) (L H : ℕ) : Finset (Fin (m x-H) → ℕ) :=
  (Finset.univ : Finset (Fin (m x-H))).biUnion (fun i =>
    (Finset.univ.filter (fun j => i ≤ j)).biUnion (localAbnormalTuples x c L H i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalRegularPrimeMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive prime mass satisfying every needed indexed normality condition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localRegularPrimeTuples (x c : ℝ) (L H : ℕ) : Finset (Fin (m x-H) → ℕ) :=
  gridPrimeTuples (localPrimeGrid x c L (m x-H)) \ localNormalityFailures x c L H

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalCandidateAbundance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-product candidates retaining all local normality conditions. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localRegularCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  candidateIntegers x d (localRegularPrimeTuples x c L H)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalNormalCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive family of actual candidates with head and indexed tail normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localNormalCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  ((tailHeadPairs x d (localRegularPrimeTuples x c L H)).filter
    (fun z => IsNormalPrime (localNormalityScale (m x)) z.2)).image
      (fun z => z.2*(∏ i,z.1 i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTBadWitness
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The injective choice of nontrivial preimages used in Ford, Section 5,
p. 25, between (5.20) and (5.21).  Candidate sets are partitioned by their
totient value.  A singleton fiber uses its given nontrivial preimage; on a
larger fiber, a cyclic permutation followed by multiplication by a fixed
seed preimage supplies distinct nontrivial preimages.  The full fiber
multiplicity is retained throughout this construction.
-/

noncomputable section

namespace TotientAsymptotic

def pptFiniteRotation (α : Type*) [Fintype α] : Equiv.Perm α :=
  (Fintype.equivFin α).trans ((finRotate (Fintype.card α)).trans (Fintype.equivFin α).symm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPrefixGrouping
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite maximal-prefix grouping in the full-fiber sieve.  The injective
choice is made on each residual family, after the maximal-prefix
argument has proved the largest-prime mismatch for every nontrivial
residual preimage.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptPrefixProduct (p : ℕ → ℕ) (j : ℕ) : ℕ := ∏ i ∈ Finset.Ico 0 j, p i

/-- The elementary residual facts supplied by maximal-prefix selection.
This is an internal grouping invariant, not a published-input assumption. -/
def PPTBadResidual (d r : ℕ) : Prop :=
  0 < r ∧
  (∀ p : ℕ, p.Prime → p ∣ r → d+1 < p) ∧
  (∃ u : ℕ, 0 < u ∧ u.totient = d*r.totient ∧ ¬r ∣ u) ∧
  ∀ u : ℕ, 0 < u → u.totient = d*r.totient → ¬r ∣ u →
    largestPrimeFactor u ≠ largestPrimeFactor r

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalBadCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual failed candidates admit normal, ordered, maximal-prefix residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localBadCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localNormalCandidates x c d L H).filter (fun b => ¬FullFiber d b)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalBadCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A failed candidate either fails at its original head or has a bad
suffix of its tail.  The latter event is independent of the original head. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localOriginalBad (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localBadCandidates x c d L H).filter (PPTBadResidual d)

def localBadSuffixTuples (x c : ℝ) (d L H : ℕ) (i : Fin (m x-H)) :
    Finset (Fin (m x-H) → ℕ) :=
  (localRegularPrimeTuples x c L H).filter
    (fun p => PPTBadResidual d (∏ j,primeFinal p i.val j))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTotientSquare
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The large-square-in-a-totient branch of the PPT pruning argument.
Euler's product formula reduces it to a square in the integer, a square
in one prime predecessor, or a common factor of two distinct prime
predecessors.  Elementary reciprocal divisor bounds suffice when the
cutoff is a sufficiently large fixed power of the logarithm.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptDivisorMultiples (N d : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun n => n ≠ 0 ∧ d ∣ n)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSquareCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete logarithmic square cutoff for arbitrary selected preimages. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localSquareCutoff (z : ℝ) : ℕ := ⌊(Real.log z)^6⌋₊

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLocalValueEnvelope
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local value and right-preimage prime bounds from the actual candidate
prime product.  A late residual is controlled by its own coordinate
envelope, rather than by the original ambient counting parameter.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptLocalValueHeight (d H : ℕ) (T : ℝ) : ℝ :=
  T+Real.log (Real.log (d : ℝ)+(H : ℝ)+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinct bad suffixes retain the local value bounds and normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def localBadSuffixValues (x c : ℝ) (d L H : ℕ) (i : Fin (m x-H)) : Finset ℕ :=
  (localBadSuffixTuples x c d L H i).image (fun p => ∏ j,primeFinal p i.val j)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalResidualExceptionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the exceptional estimates to the actual distinct suffix values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localWitnessNonnormal (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R.filter (fun r => ∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p)

def localWitnessSquare (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R.filter (fun r => ∃ p : ℕ,p.Prime ∧ localNormalityScale h<p ∧
    (p^2 ∣ F r ∨ p^2 ∣ (F r).totient))

def localWitnessRegular (R : Finset ℕ) (F : ℕ → ℕ) (h : ℕ) : Finset ℕ :=
  R \ (localWitnessNonnormal R F h ∪ localWitnessSquare R F h)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalFullCandidateCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite pruning of the actual candidate family on its original normalization.
The regular comparison estimates are kept explicit here for application to
Ford's finite labeled counts. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localFullCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localNormalCandidates x c d L H).filter (FullFiber d)

def LocalOriginalRegularBound (x c : ℝ) (d L H : ℕ) : Prop :=
  ∀ F : ℕ → ℕ,let R := localOriginalBad x c d L H
    Set.InjOn F (R : Set ℕ) →
    (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
      largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
    ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ)

def LocalSuffixRegularBound (x c : ℝ) (d L H : ℕ) : Prop :=
  ∀ (i : Fin (m x-H)) (F : ℕ → ℕ),
    let R := localBadSuffixValues x c d L H i
    Set.InjOn F (R : Set ℕ) →
    (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
      largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
    (∑ r ∈ localWitnessRegular R F (m x-i.val),(r.totient:ℝ)⁻¹) ≤ rho^(m x-i.val)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocalSuffixComparisonData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bad suffixes retain the ordered geometric prime coordinates of
their parent tuple, together with an explicit order embedding. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def primeFinalOrderEmbedding {N : ℕ} (n : ℕ) : Fin (N-n) ↪o Fin N where
  toFun j := ⟨n+j.val,by have := j.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp only at he
    omega
  map_rel_iff' := by
    intro i j
    change n+i.val ≤ n+j.val ↔ i.val ≤ j.val
    omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTCancelCoordinates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Cancel matching coordinates after the high-prime lists have been aligned.
The first mismatch is retained, so the large-head condition is preserved.
The canceled integer prime product is retained for the later reciprocal
totient summation.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def pptUnequalCoordinates {k : ℕ} (p q : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i ≠ q i)

def pptEqualCoordinates {k : ℕ} (p q : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i = q i)

def pptCoordinateEmbedding {k : ℕ} (p q : Fin k → ℕ) :
    Fin (pptUnequalCoordinates p q).card ↪o Fin k :=
  (pptUnequalCoordinates p q).orderEmbOfFin rfl

def pptCanceledPrimeProduct {k : ℕ} (p q : Fin k → ℕ) : ℕ :=
  ∏ i ∈ pptEqualCoordinates p q, p i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite summation of the fixed-common-factor, fixed-left-tail comparison
blocks in Ford's proof of (5.23).  The published comparison predicates
remain explicit.  The extra factor from fixing the left tail is bounded
by its already proved normality estimate.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The part of the comparison bound independent of the two fixed
integer factors. -/
def pptComparisonScale (C : ℝ) (b : ℕ) (z W : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  (C*B z)^(6*b) * (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1) *
    (Real.log z)^(-2 + (∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B z)) +
      comparisonError b z W Y U)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonAssembly
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Assemble the pointwise conditions in Ford's comparison estimate after
the actual matched coordinates have been removed.  The right residual
is an integer multiplier in the shifted-product equation; no additional
representation of that multiplier as a totient is required.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptCanceledPair {k : ℕ} (p q : Fin k → ℕ) (E : ℕ) :
    ShiftedPair (pptUnequalCoordinates p q).card :=
  ⟨p ∘ pptCoordinateEmbedding p q, q ∘ pptCoordinateEmbedding p q, E⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonScaleDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The literal Ford comparison prefactor in the PPT range.  The number of
high and low primes is logarithmic in `t`; the terminal cutoff has
double logarithm at most `2 t^(2/3)`.  All fixed-seed and finite-family
costs are retained before applying the proved strict-exponent decay.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptFullComparisonPrefactor (C t : ℝ) (b D h : ℕ) (u V M : ℝ) : ℝ :=
  (C*t)^(6*b)*u^(20*(b : ℝ)*Real.log b+1)*(b+1 : ℝ)^D*
    Real.exp (4*(h : ℝ)*V*Real.log (b+1))*Real.exp (M*(Real.log t)^2)

def pptPrefactorConstant (C A M : ℝ) (D : ℕ) : ℝ :=
  6*A*(|Real.log C|+1)+48*A^2+(D : ℝ)*A+2+|M|

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTComparisonGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The PPT first cutoff approaches the head coordinate.  Its lower head
edge must therefore vary with the available inverse-cube gap.  Interior
grid intervals and their finite labels are the same as in the ordinary
comparison grid.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptGridLower {b : ℕ} (δ θ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then θ else pairedGridLower δ n j

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTLocalDimension
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The geometric lower bound on a remaining prime coordinate bounds the
length of that suffix in terms of its own comparison scale.  This is a
local statement; it does not transfer normality from a larger scale.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pptLocalDimensionConstant (c : ℝ) : ℝ := (2+|Real.log c|)/lam

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFactorLabels
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual finite label universe for the common prime product and the
small left tail. Products are counted as integers. Repeated prime lists
only enlarge the reciprocal-mass majorant.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptPrimeProductFamily (N h : ℕ) : Finset ℕ :=
  (Fintype.piFinset (fun _ : Fin h => Nat.primesLE N)).image (fun p => ∏ i, p i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTTailAlignment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The right-tail smoothness argument following Ford (5.35).  If the left
tail is smooth, an additional right prime with a large predecessor factor
would force too many normal shifts across the intervening interval.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptRightLowFactor {l : ℕ} (q : Fin l → ℕ) (E J : ℕ) : ℕ :=
  E * ∏ i ∈ Finset.univ.filter (fun i : Fin l => J ≤ i.val), (q i-1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTPrefixEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Truncate the two actual prime lists to the same high-prefix length.  The
left residual multiplier is exactly the seed times the totient of the
removed prime tail; the right multiplier is the smooth factor already
estimated in `PPTTailAlignment`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def pptPrimePrefix {k J : ℕ} (p : Fin k → ℕ) (hJ : J ≤ k) : Fin J → ℕ :=
  fun i => p (i.castLE hJ)

def pptPrimeTailProduct {k : ℕ} (p : Fin k → ℕ) (J : ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => J ≤ i.val), p i

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTActualResidual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual residual data after choosing the terminal prefix and canceling
matching coordinates. This keeps the candidate integer, both finite
factor labels, and the exact shifted-product equation together.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptTailIndices (k J : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => J ≤ i.val)

def pptTailList {k : ℕ} (p : Fin k → ℕ) (J : ℕ) :
    Fin (pptTailIndices k J).card → ℕ :=
  p ∘ (pptTailIndices k J).orderEmbOfFin rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFiniteLabels
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite label type for the actual residual comparison partition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

abbrev PPTResidualLabel :=
  Σ b : ℕ, (Fin b → ℕ) × ℕ × (Σ _h : ℕ, ℕ × (Σ _s : ℕ, ℕ))

def pptResidualLabel (b h s c a j : ℕ) (g : Fin b → ℕ) : PPTResidualLabel :=
  ⟨b, (g, (j, ⟨h, (a, ⟨s, c⟩)⟩))⟩

def pptLabelB (l : PPTResidualLabel) : ℕ := l.1
def pptLabelGrid (l : PPTResidualLabel) : Fin (pptLabelB l) → ℕ := l.2.1
def pptLabelWindow (l : PPTResidualLabel) : ℕ := l.2.2.1
def pptLabelH (l : PPTResidualLabel) : ℕ := l.2.2.2.1
def pptLabelA (l : PPTResidualLabel) : ℕ := l.2.2.2.2.1
def pptLabelC (l : PPTResidualLabel) : ℕ := l.2.2.2.2.2.2

def pptLabelWeight (l : PPTResidualLabel) : ℝ :=
  ((pptLabelA l).totient : ℝ)⁻¹*((pptLabelC l).totient : ℝ)⁻¹

def pptResidualLabels (N H : ℕ) (δ : ℝ) : Finset PPTResidualLabel := by
  classical
  exact (Finset.range (H+1)).sigma (fun b =>
    (collisionGridFamilies δ b).product ((Finset.range (H+1)).product
      ((Finset.range (H+1)).sigma (fun h =>
        (pptPrimeProductFamily N h).product
          ((Finset.range (H+1)).sigma (fun s => pptPrimeProductFamily N s))))))

def pptResidualCell (R : Finset ℕ) (label : ℕ → PPTResidualLabel)
    (l : PPTResidualLabel) : Finset ℕ := by
  classical
  exact R.filter (fun n => label n=l)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTHeadEdge
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A single lower endpoint for all leading prime factors in a local PPT
comparison block.  It depends only on the comparison scale, so the
finite grid count does not require any continuously varying labels.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pptUniformHeadEdge (t : ℝ) : ℝ := 1-(2+Real.log (3*t))/t

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTHeadSelectedGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-head grid keeps only the surviving nonleading primes
inside the geometric tail. The head itself is handled by the top row. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- Delete the leading coordinate from an ordered embedding fixing zero. -/
def pptRemoveHeadEmbedding {b N : ℕ} (e : Fin b ↪o Fin N)
    (hb : 0 < b) (_hN : 0 < N) (he : (e ⟨0,hb⟩).val=0) : Fin (b-1) ↪o Fin (N-1) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(e ⟨i.val+1,by omega⟩).val-1,by
      have hh := e.strictMono (show (⟨0,hb⟩ : Fin b) < ⟨i.val+1,by omega⟩ by
        change 0 < i.val+1; omega)
      change (e ⟨0,hb⟩).val < (e ⟨i.val+1,by omega⟩).val at hh
      have hi := (e ⟨i.val+1,by omega⟩).isLt
      omega⟩)
    (by
      intro i j hij
      have hh := e.strictMono (show (⟨i.val+1,by omega⟩ : Fin b) < ⟨j.val+1,by omega⟩ by
        change i.val+1 < j.val+1
        exact Nat.add_lt_add_right hij 1)
      have hzero := e.strictMono (show (⟨0,hb⟩ : Fin b) < ⟨i.val+1,by omega⟩ by
        change 0 < i.val+1; omega)
      change (e ⟨i.val+1,by omega⟩).val-1 < (e ⟨j.val+1,by omega⟩).val-1
      change (e ⟨i.val+1,by omega⟩).val < (e ⟨j.val+1,by omega⟩).val at hh
      change (e ⟨0,hb⟩).val < (e ⟨i.val+1,by omega⟩).val at hzero
      omega)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTWitnessCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite partition of actual regular residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def pptLabelTerminalLower (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  (B z)^(2/3:ℝ)+2*(pptLabelWindow l:ℝ)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))

def pptLabelTerminalUpper (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  (B z)^(2/3:ℝ)+(2*(pptLabelWindow l:ℝ)+1)*((B z)^(2/3:ℝ)/(2*((N:ℝ)+1)))

def pptLabelTerminal (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℝ :=
  Real.exp (Real.exp ((pptLabelTerminalLower z N l+pptLabelTerminalUpper z N l)/2))

def pptLabelUpper (z : ℝ) (N : ℕ) (l : PPTResidualLabel) : ℕ → ℝ :=
  pairedGridUpper (2*((Real.log (B z))^5/Real.sqrt (B z)))
    ((pptLabelTerminalLower z N l+pptLabelTerminalUpper z N l)/(2*B z)) (pptLabelGrid l)

def pptLabelLower (z : ℝ) (l : PPTResidualLabel) : ℕ → ℝ :=
  pptGridLower (2*((Real.log (B z))^5/Real.sqrt (B z)))
    (pptUniformHeadEdge (B z)-2*((Real.log (B z))^5/Real.sqrt (B z))) (pptLabelGrid l)

/-- Arithmetic evidence retained from the actual terminal-prefix
construction for one integer. Each field is supplied by `ppt_selected_grid_data`;
the structure contains no estimate for a finite family. -/
structure PPTResidualGridWitness (d N H : ℕ) (z S A : ℝ) (r : ℕ) where
  label : PPTResidualLabel
  length_pos : 1 ≤ pptLabelB label
  length_le : pptLabelB label ≤ H
  tail_length_le : pptLabelH label ≤ H
  label_mem : label ∈ pptResidualLabels (discardPrimeBound (B z)) H
    (2*((Real.log (B z))^5/Real.sqrt (B z)))
  terminal_normality : S ≤ pptLabelTerminal z N label
  terminal_height : 0 ≤ B (pptLabelTerminal z N label) ∧
    B (pptLabelTerminal z N label) ≤ 2*(B z)^(2/3:ℝ)
  terminal_eq : comparisonCutoffs z (pptLabelUpper z N label) (pptLabelB label)=
    pptLabelTerminal z N label
  tail : Fin (pptLabelH label) → ℕ
  tail_product : pptLabelA label=∏ i,tail i
  tail_injective : Function.Injective tail
  tail_normal : ∀ i,IsNormalPrime S (tail i)
  tail_smooth : ∀ i,(largestPrimeFactor (tail i-1):ℝ) ≤ pptLabelTerminal z N label
  pair : ShiftedPair (pptLabelB label)
  recovery : r=pptLabelC label*pptLabelA label*∏ i,pair.left i
  parameters : FordComparisonParameters (pptLabelB label) z S
    (d*(pptLabelA label).totient) (pptLabelC label).totient
    (comparisonCutoffs z (pptLabelUpper z N label)) (comparisonCutoffs z (pptLabelLower z label))
  conditions : FordComparisonConditions (pptLabelB label) z S
    (d*(pptLabelA label).totient) (pptLabelC label).totient
    (comparisonCutoffs z (pptLabelUpper z N label)) (comparisonCutoffs z (pptLabelLower z label)) pair
  exponent : -2+(∑ i ∈ Finset.Icc 1 (pptLabelB label-1),
      a i*(B (comparisonCutoffs z (pptLabelUpper z N label) i)/B z))+
    comparisonError (pptLabelB label) z S (comparisonCutoffs z (pptLabelUpper z N label))
      (comparisonCutoffs z (pptLabelLower z label)) ≤ 
        -1-(1/(80*A^3))/(Real.log (B z))^3

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Scaling
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The common-endpoint argument from Proposition `mass` in the manuscript.
`CommonEndpointComparison` names an internal estimate still requiring proof;
it is not classified as a published input.  The proof below shows precisely
how that estimate and Ford's published order bounds yield regular variation,
without any phase-continuity assumption.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pairedNormalized (c x : ℝ) : ℝ :=
  V (x/c) * Real.log x / ((x/c) * G x (m x))

def CommonEndpointComparison (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∀ᶠ x : ℝ in atTop,
    |massError x H x| ≤ ε ∧ |massError x H (x/c)| ≤ ε

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalMassSeries
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth residual mass is summable against terminal-coordinate decay. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def terminalMassWeight (c : ℝ) (k : ℕ) : ℝ :=
  Real.exp (10*(Real.log ((k:ℝ)+5))^2-c*k)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedPrimeSet
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def intervalHeads (x : ℝ) (k D A : ℕ) : Finset ℕ :=
  (shiftedPrimeSet x x D).filter (fun p : ℕ =>
    (k : ℝ)*x < (p*A : ℕ) ∧ (p*A : ℕ) ≤ (k+1 : ℝ)*x)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

def candidateMass (x : ℝ) (H k : ℕ) : ℝ :=
  ∑ ζ ∈ prefixDataFinset x H,
    fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ)/(prefixDenominator ζ : ℝ)

end TotientAsymptotic

end

end OAI
end


