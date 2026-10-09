-- Prove2me | Definitions.Def_OAIErdos3B100
-- name    : OAIErdos3B100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T22:54:36.550176+00:00
-- url     : https://prove2.me/theorems/bd29efb4-4657-47c1-a6b3-63d0a27f9ada
-- title:
--   OpenAI Erdős-3 split, definitions bundle 101 of 126
-- statement:
--   Definitions bundle 101 of 126 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B099`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 101 available.
--
--   Modules: `OAI.Erdos3.CoverLatticeResidue`, `OAI.Erdos3.FiniteProgressionPartition.label_card_le_exp_of_length_lower`, `OAI.Erdos3.FiniteProgressionPartition.label_card_mul_le_of_length_lower`, `OAI.Erdos3.FiniteProgressionPartition.normalized_point_sub_point_le`, `OAI.Erdos3.FiniteProgressionPartition.normalized_point_sub_point_le_of_bound`, `OAI.Erdos3.FiniteProgressionPartition.normalized_point_sub_start_le`, `OAI.Erdos3.FiniteProgressionPartition.normalized_point_sub_start_le_of_bound`, `OAI.Erdos3.LowDensityRelativeAbsoluteRule`, `OAI.Erdos3.NativeIntegerExpansion.affinePullback`, `OAI.Erdos3.NativeIntegerExpansion.casesOn`, `OAI.Erdos3.NativeIntegerExpansion.conjugate`, `OAI.Erdos3.NativeIntegerExpansion.linearPullbackHom`, `OAI.Erdos3.NativeIntegerExpansion.mono`, `OAI.Erdos3.NativeIntegerExpansion.norm_eval_le`, `OAI.Erdos3.NativeIntegerExpansion.ofFamily`, `OAI.Erdos3.NativeIntegerExpansion.ofModelFamily`, `OAI.Erdos3.NativeIntegerExpansion.ofTest`, `OAI.Erdos3.NativeIntegerExpansion.scaleNormLeOne`, `OAI.Erdos3.NativeIntegerExpansion.select_mean_row_correlation`, `OAI.Erdos3.NativeIntegerExpansion.select_sample_correlation`, `OAI.Erdos3.NativeIntegerExpansion.substituteExpansion`, `OAI.Erdos3.NativeIntegerExpansion.substitutedValue`, `OAI.Erdos3.NativeIntegerExpansion.substitutedValue_eq`, `OAI.Erdos3.NativeIntegerExpansion.toCyclic`, `OAI.Erdos3.NativeIntegerExpansion.weightedSum`, `OAI.Erdos3.NativeIntegerModelFamily.mono`, `OAI.Erdos3.NativeIntegerModelFamily.mono_dim`, `OAI.Erdos3.NativeIntegerModelFamily.recOn`, `OAI.Erdos3.NativeIntegerVectorEquivalence`, `OAI.Erdos3.NativeIntegerVectorEquivalence.affinePullback`, `OAI.Erdos3.NativeIntegerVectorEquivalence.affinePullbackHom`, `OAI.Erdos3.NativeIntegerVectorEquivalence.conjugate`, `OAI.Erdos3.NativeIntegerVectorEquivalence.coordinatePullback`, `OAI.Erdos3.NativeIntegerVectorEquivalence.linearPullbackHom`, `OAI.Erdos3.NativeIntegerVectorEquivalence.mono`, `OAI.Erdos3.NativeIntegerVectorEquivalence.of_coordinate_maps`, `OAI.Erdos3.NativeIntegerVectorEquivalence.selectedChainedChoice_card_bound`, `OAI.Erdos3.NativeIntegerVectorEquivalence.selectedChoice_card_bound`, `OAI.Erdos3.NativeIntegerVectorEquivalence.selectedExpansion`, `OAI.Erdos3.NativeIntegerVectorEquivalence.symm`, `OAI.Erdos3.NativeIntegerVectorEquivalence.transfer_sample_correlation`, `OAI.Erdos3.NativeMeanRowCorrelation`, `OAI.Erdos3.NativeMeanRowCorrelation.exists_of_expansion`, `OAI.Erdos3.NativeMeanRowCorrelation.mono`, `OAI.Erdos3.NilpotentLieFiltration.exists_fast_coefficient_quotient_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_fast_coefficient_quotient_projection`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_polynomial_operation_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_fast_coefficient_quotient_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_reduced_projected_comparison`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_relative`, `OAI.Erdos3.NilpotentLieFiltration.nativePolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.nativePolynomialOrbit_log`, `OAI.Erdos3.NilpotentLieFiltration.nativePolynomialOrbit_surjective`, `OAI.Erdos3.NilpotentLieFiltration.nativeReducedPolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.nativeReducedPolynomialOrbit_log`, `OAI.Erdos3.NilpotentLieFiltration.nativeReducedPolynomialOrbit_symbol`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis_structure_height`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint_matrix`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientFastSubmodule_relative`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_of_gradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom_fast`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_span`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_spanning_height`, `OAI.Erdos3.PolynomialCoordinatePartitionBound`, `OAI.Erdos3.PolynomialTranslationGroupOver.action_inverse_X_inr`, `OAI.Erdos3.PolynomialTranslationLie.baseRealElement`, `OAI.Erdos3.PolynomialTranslationLie.baseRealElement_repr`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_base_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_polynomial_eval`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_pure_base_of_shape`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_pure_polynomial_of_shape`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_realification_centralRationalLine`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslation_bounds_near_one`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslation_bounds_of_shear_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslation_inverse_action_X`, `OAI.Erdos3.PolynomialTranslationLie.bchTranslationHom_centralRationalLine`, `OAI.Erdos3.PolynomialTranslationLie.centralRationalElement`, `OAI.Erdos3.PolynomialTranslationLie.centralRationalLine`, `OAI.Erdos3.PolynomialTranslationLie.continuous_bchRealTranslationHom_base`, `OAI.Erdos3.PolynomialTranslationLie.continuous_bchRealTranslationHom_polynomial_eval`, `OAI.Erdos3.PolynomialTranslationLie.degreeOf_pack_translationLogPhasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.exists_translation_coordinate_polynomialOrbit`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_base_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_degree_symbolLift_eq`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_degree_symbolLift_realEval`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_degree_symbol_representative`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_integerEval`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_realEval`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_symbol_degree_top`, `OAI.Erdos3.PolynomialTranslationLie.majorTranslationPolynomialOrbit_top_log_graded`, `OAI.Erdos3.PolynomialTranslationLie.pack_translationLogPhasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.pack_translationLogPhasePolynomial_coefficientGrid`, `OAI.Erdos3.PolynomialTranslationLie.pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous`, `OAI.Erdos3.PolynomialTranslationLie.polynomialRealElement`, `OAI.Erdos3.PolynomialTranslationLie.polynomialRealElement_repr`, `OAI.Erdos3.PolynomialTranslationLie.polynomialRealElement_shear_base`, `OAI.Erdos3.PolynomialTranslationLie.polynomialRealElement_shear_extra`, `OAI.Erdos3.PolynomialTranslationLie.realLattice_translation_integral`, `OAI.Erdos3.PolynomialTranslationLie.realPolynomialMass_pack_translationLogPhasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.realPolynomialMass_translationLogBasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.realPolynomialMass_translationLogDirectionalSeries`, `OAI.Erdos3.PolynomialTranslationLie.realPolynomialMass_translationLogMixedGroupPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.realPolynomialMass_translationLogMixedGroupPolynomial_scale`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_base_coeff`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_coordinate_abs_le`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_coordinate_row`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_extra_coeff`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_polynomial_mem`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_repr`, `OAI.Erdos3.PolynomialTranslationLie.realShearEmbedding_shape_of_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.translationBaseCoordinatePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationBaseCoordinatePolynomial_adapted`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit_eval_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit_log`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit_realEval`, `OAI.Erdos3.PolynomialTranslationLie.translationBasePolynomialOrbit_symbol_top`, `OAI.Erdos3.PolynomialTranslationLie.translationCoordinatePolynomialOrbit`, `OAI.Erdos3.PolynomialTranslationLie.translationCoordinatePolynomialOrbit_realEval`, `OAI.Erdos3.PolynomialTranslationLie.translationLogBasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationLogBasePolynomial_coefficientGrid`, `OAI.Erdos3.PolynomialTranslationLie.translationLogBasePolynomial_weightedBasis`, `OAI.Erdos3.PolynomialTranslationLie.translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous`, `OAI.Erdos3.PolynomialTranslationLie.translationLogDirectionalSeries_coefficientGrid`, `OAI.Erdos3.PolynomialTranslationLie.translationLogGroupPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationLogGroupPolynomial_specialize`, `OAI.Erdos3.PolynomialTranslationLie.translationLogMixedGroupPolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationLogMixedGroupPolynomial_coefficientGrid_of_inputs`, `OAI.Erdos3.PolynomialTranslationLie.translationLogMixedGroupPolynomial_eq_series`, `OAI.Erdos3.PolynomialTranslationLie.translationLogMixedGroupPolynomial_eval`, `OAI.Erdos3.PolynomialTranslationLie.translationLogMixedGroupPolynomial_scale`, `OAI.Erdos3.PolynomialTranslationLie.translationLogPhasePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationLogPolynomialShear`, `OAI.Erdos3.PolynomialTranslationLie.translationLogPolynomialShear_base`, `OAI.Erdos3.PolynomialTranslationLie.translationLogPolynomialShear_phase`, `OAI.Erdos3.PolynomialTranslationLie.translationLogPolynomialShear_specialize`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialCoordinatePolynomial`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialCoordinatePolynomial_adapted`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolHom`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolHom_coord`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolHom_lift`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLift`, `OAI.Erdos3.PolynomialTranslationLie.translationPolynomialSymbolLift_log`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit_coordinate`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit_eval_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit_log`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit_realEval`, `OAI.Erdos3.PolynomialTranslationLie.translationPurePolynomialOrbit_symbol_eq_of_top`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_real_log_coordinates_bound`, `OAI.Erdos3.PolynomialTranslationLie.weightedShearEmbedding_coordinate_row`, `OAI.Erdos3.PolynomialTranslationLie.weightedSubalgebra_realPolynomial_degreeOf_le`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationDisplacementConstant`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationDisplacementConstant_pos`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationPhaseQuotientMap`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationPhaseQuotientMap_mk`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationQuotientPhase`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationQuotientPhase_mk`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueLattice`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueLattice_contains_power_cover`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueLattice_inner_grid`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueLattice_le`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueLattice_outer_grid`, `OAI.Erdos3.RelativePatchAbsoluteRule`, `OAI.Erdos3.RelativePatchInductionRule`, `OAI.Erdos3.RelativePatchPowerInductionRule`, `OAI.Erdos3.RelativePatchSliceConclusion`, `OAI.Erdos3.RelativePatchSliceConclusion.comp`, `OAI.Erdos3.ResidueBoxSlice.comp`, `OAI.Erdos3.ResidueBoxSlice.comp_length_exp_lower`, `OAI.Erdos3.ResidueBoxSlice.comp_point`, `OAI.Erdos3.ResidueBoxSlice.identity`, `OAI.Erdos3.ResidueBoxSlice.integerAffine`, `OAI.Erdos3.ResidueBoxSlice.integerAffine_comp`, `OAI.Erdos3.ResidueBoxSlice.integerAffine_finPoint`, `OAI.Erdos3.ResidueBoxSlice.integerPullback`, `OAI.Erdos3.ResidueBoxSlice.integerPullback_comp`, `OAI.Erdos3.ResidueBoxSlice.polynomial`, `OAI.Erdos3.ResidueBoxSlice.polynomial_eval`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.realChartSubstitute`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_bound_of_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_reabsorption_bound`, `OAI.Erdos3.VectorPolynomial.basisPolynomialLift_reabsorption_grid`, `OAI.Erdos3.VectorPolynomial.coordinate_realChartSubstitute`, `OAI.Erdos3.character_half`, `OAI.Erdos3.compact_quotient_of_integral_basis`, `OAI.Erdos3.continuous_polynomialShearExp_eval`, `OAI.Erdos3.continuous_weightedSupportLE_eval`, `OAI.Erdos3.coverKernelBasisEquiv`, `OAI.Erdos3.coverKernelBasisEquiv_residue`, `OAI.Erdos3.coverLatticeBasisEquiv`, `OAI.Erdos3.coverLatticeBasisEquiv_mk`, `OAI.Erdos3.coverLatticePoint`, `OAI.Erdos3.coverLatticePoint_ker`, `OAI.Erdos3.coverLatticePoint_surjective`, `OAI.Erdos3.coverLatticePoint_val`, `OAI.Erdos3.coverLatticeResidueEquiv`, `OAI.Erdos3.coverLatticeResidueEquiv_mk`, `OAI.Erdos3.detectedTranslationCoordinate_denominator_le_exp`, `OAI.Erdos3.detectedTranslationCoordinate_slow_factor_le_exp`, `OAI.Erdos3.exists_controlled_polynomial_kernel_directions`, `OAI.Erdos3.exists_detectedTranslationPhase_budget`, `OAI.Erdos3.exists_large_nonnegative_weighted_term`, `OAI.Erdos3.exists_large_value_of_mean_row_correlation`, `OAI.Erdos3.exists_mean_row_weighted_term`, `OAI.Erdos3.exists_normalizedTwist_parameter_partition`, `OAI.Erdos3.exists_uniform_polynomial_kernel_directions`, `OAI.Erdos3.exponentialProgressionScale`, `OAI.Erdos3.exponentialProgressionScale_bounds`, `OAI.Erdos3.halvingPolynomial`, `OAI.Erdos3.halvingPolynomial_eval`, `OAI.Erdos3.halvingPolynomial_support`, `OAI.Erdos3.integerPolynomialTranslationResidueCover`, `OAI.Erdos3.integerTranslationResidueSubgroup`, `OAI.Erdos3.latticeBasisResidue`, `OAI.Erdos3.latticeBasisResidue_ker`, `OAI.Erdos3.latticeBasisResidue_surjective`, `OAI.Erdos3.linearQuotientAverage`, `OAI.Erdos3.linearQuotientAverage_approx`, `OAI.Erdos3.linearQuotientAverage_bound`, `OAI.Erdos3.linearQuotientAverage_character`, `OAI.Erdos3.linearQuotientAverage_cover`, `OAI.Erdos3.linearQuotientAverage_cover_eq_of_map_eq`, `OAI.Erdos3.linearQuotientAverage_invariant`, `OAI.Erdos3.linearQuotientAverage_probability`, `OAI.Erdos3.linearQuotientEndomorphism`, `OAI.Erdos3.linearQuotientEndomorphism_continuous`, `OAI.Erdos3.majorTranslationJointPolynomial_degree_slot_top`, `OAI.Erdos3.majorTranslationJointPolynomial_degree_weightedHomogeneousComponent`, `OAI.Erdos3.majorTranslationJointPolynomial_sub_degree_top_lower`, `OAI.Erdos3.mean_row_correlation_scale`, `OAI.Erdos3.mean_row_weighted_sum_norm_le`, `OAI.Erdos3.mem_integerTranslationResidueSubgroup`, `OAI.Erdos3.ofCoordinates_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.packTranslationPolynomial_baseDerivative`, `OAI.Erdos3.packTranslationPolynomial_baseDerivative_pow`, `OAI.Erdos3.packTranslationPolynomial_directional_sum`, `OAI.Erdos3.packTranslationPolynomial_map_C`, `OAI.Erdos3.packTranslationPolynomial_pderiv`, `OAI.Erdos3.polynomialKernelDirection`, `OAI.Erdos3.polynomialKernelDirection_grid`, `OAI.Erdos3.polynomialKernelDirection_lift`, `OAI.Erdos3.polynomialKernelDirection_norm`, `OAI.Erdos3.polynomialShearExpAut_neg_over`, `OAI.Erdos3.polynomialShear_neg_pow_apply`, `OAI.Erdos3.polynomial_kernel_direction_budget`, `OAI.Erdos3.probabilityAddHaar`, `OAI.Erdos3.probabilityAddHaar_invariant`, `OAI.Erdos3.probabilityAddHaar_probability`, `OAI.Erdos3.quotientIntegerCover`, `OAI.Erdos3.quotientIntegerCover_continuous`, `OAI.Erdos3.quotientIntegerCover_mk`, `OAI.Erdos3.quotientIntegerCover_surjective`, `OAI.Erdos3.quotientLinearCharacter_integrable`, `OAI.Erdos3.quotientLinearCharacter_integral`, `OAI.Erdos3.realPolynomialCoefficientGrid_mul`, `OAI.Erdos3.realPolynomialCoefficientGrid_pderiv`, `OAI.Erdos3.realPolynomialCoefficientGrid_rat_smul`, `OAI.Erdos3.realPolynomialCoefficientGrid_sum`, `OAI.Erdos3.realPolynomialCoefficientGrid_zero`, `OAI.Erdos3.realificationLieHom_repr_coordinate`, `OAI.Erdos3.realificationLieHom_repr_zero`, `OAI.Erdos3.relativePatchBoxScore`, `OAI.Erdos3.relativePatchComplexity`, `OAI.Erdos3.relativePatchComplexity_rank_le`, `OAI.Erdos3.relativePatchDistinctWeights`, `OAI.Erdos3.relativePatchSliceScore`, `OAI.Erdos3.relativePatchSliceScore_comp`, `OAI.Erdos3.scaleMvPolynomialAxes_substitution`, `OAI.Erdos3.scaled_substitution_coeff_bound`, `OAI.Erdos3.schmidtDegreeConstant`, `OAI.Erdos3.schmidtMassCeiling`, `OAI.Erdos3.schmidtMassMultiplier`, `OAI.Erdos3.schmidtMeanDenominator`, `OAI.Erdos3.schmidtRecurrenceBase`, `OAI.Erdos3.schmidtRecurrenceExponent`, `OAI.Erdos3.schmidtStepFactor`, `OAI.Erdos3.translationBaseDerivative`, `OAI.Erdos3.translationBaseDerivative_C`, `OAI.Erdos3.translationBaseDerivative_X`, `OAI.Erdos3.translationBaseDerivative_apply`, `OAI.Erdos3.translationDirectionalDerivative_coefficientGrid`, `OAI.Erdos3.translationDirectionalDerivative_pow_coefficientGrid`, `OAI.Erdos3.translationDirectionalSeries_coefficientGrid`, `OAI.Erdos3.translationShearCoordinates`, `OAI.Erdos3.translationShearCoordinates_action`, `OAI.Erdos3.translationShearCoordinates_inverse_exp`, `OAI.Erdos3.translationShearCoordinates_map_action`, `OAI.Erdos3.translationShearCoordinates_polynomial_series`, `OAI.Erdos3.translationShear_derivation_pow_extra`, `OAI.Erdos3.translationShear_derivation_rename_eq`, `OAI.Erdos3.translationShear_derivation_rename_eq_zero`, `_private.Lattices.WeightedTranslationResidueLattice.0.OAI.Erdos3.PolynomialTranslationLie.integerTranslation_base_pow`, `_private.Polynomial.TranslationLogCoordinatePolynomials.0.OAI.Erdos3.PolynomialTranslationLie.shear_sum_apply`, `_private.Polynomial.TranslationPolynomialPackingDerivative.0.OAI.Erdos3.pderiv_inr_rename_inl`, `_private.Sampling.TranslationLogCoordinateInputGrid.0.OAI.Erdos3.PolynomialTranslationLie.constant_coefficientGrid`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B104
import Definitions.Def_OAIErdos3B105
import Definitions.Def_OAIErdos3B116

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationResidueLattice
namespace OAI

section

namespace Erdos3

variable {B : Type*}

noncomputable def integerTranslationResidueSubgroup (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℤ B) where
  carrier := {γ | ∀ i, (γ.base i : ZMod M) = 0}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply, Int.cast_add,
      ha i, hb i, add_zero]
  inv_mem' := by
    intro a ha i
    simp only [PolynomialTranslationGroupOver.base_inv, Pi.neg_apply, Int.cast_neg,
      ha i, neg_zero]

@[simp] theorem mem_integerTranslationResidueSubgroup (M : ℕ)
    (γ : PolynomialTranslationGroupOver ℤ B) :
    γ ∈ integerTranslationResidueSubgroup M ↔ ∀ i, (γ.base i : ZMod M) = 0 := Iff.rfl

noncomputable def integerPolynomialTranslationResidueCover (M : ℕ) :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (integerTranslationResidueSubgroup (B := B) M).map
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℝ))

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationResidueLattice (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    Subgroup (weightedFiltration w d hwd).Group :=
  ((integerTranslationResidueSubgroup (B := σ) M).map PolynomialTranslationGroup.fromInteger).comap
    (bchTranslationHom w d hw hwd)

theorem weightedTranslationResidueLattice_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    weightedTranslationResidueLattice w d hw hwd M ≤ weightedTranslationLattice w d hwd := by
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd]
  rintro g ⟨z, _, hz⟩
  exact ⟨z, hz⟩

omit [Fintype σ] in
theorem integerTranslation_base_pow
    (γ : PolynomialTranslationGroupOver ℤ σ) (n : ℕ) (i : σ) :
    (γ ^ n).base i = (n : ℤ) * γ.base i := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, PolynomialTranslationGroupOver.base_mul, Pi.add_apply, ih,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem weightedTranslationResidueLattice_contains_power_cover
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    subgroupPowerCover (weightedTranslationLattice w d hwd) M ≤
      weightedTranslationResidueLattice w d hw hwd M := by
  apply (subgroupPowerCover_le_iff _ _ M).mpr
  intro g hg
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd] at hg
  obtain ⟨γ, hγ⟩ := hg
  refine ⟨γ ^ M, ?_, ?_⟩
  · intro i
    rw [integerTranslation_base_pow]
    simp
  · rw [map_pow, map_pow, hγ]

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationResidueLattice_inner_grid (M : ℕ) :
    scaledIntegerGrid (d.factorial * M) ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw)
        (weightedTranslationResidueLattice w d hw hwd M) := by
  have hinner := subgroupPowerCover_inner_grid (weightedOrderedBasis w d hw)
    (weightedTranslationLattice w d hwd) d.factorial M (weightedOrderedBasis_inner_grid w d hw hwd)
  intro x hx
  apply weightedTranslationResidueLattice_contains_power_cover w d hw hwd M
  apply hinner
  simpa only [Nat.mul_comm] using hx

theorem weightedTranslationResidueLattice_outer_grid (M : ℕ) :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw)
      (weightedTranslationResidueLattice w d hw hwd M) ⊆
        denominatorGrid (d.factorial * M) := by
  intro x hx
  have h0 := weightedOrderedBasis_outer_grid w d hw hwd
    (weightedTranslationResidueLattice_le w d hw hwd M hx)
  simpa only [Nat.mul_comm] using denominator_grid_subset_mul d.factorial M h0

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem weightedShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
      (weightedShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
        (weightedShearEmbedding w d x) a = (weightedBasis w d hw).repr x i := by
  classical
  rcases a with ⟨i, a, ha⟩
  cases i with
  | inl i =>
      by_cases ha0 : a = 0
      · right
        refine ⟨Sum.inl i, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = _
        rw [shearDerivation_X_inl, ha0]
        simp
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = 0
        rw [shearDerivation_X_inl]
        simp [MvPolynomial.coeff_C, Ne.symm ha0]
  | inr u =>
      by_cases hb : ∃ b : σ →₀ ℕ, b.mapDomain Sum.inl = a
      · obtain ⟨b, rfl⟩ := hb
        have hweight : Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.weight w b := by
          change Finsupp.linearCombination ℕ (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.linearCombination ℕ w b
          rw [Finsupp.linearCombination_mapDomain]
          rfl
        have hb : Finsupp.weight w b < d := by
          change Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) + 1 ≤ d at ha
          rw [hweight] at ha
          omega
        right
        refine ⟨Sum.inr ⟨b, hb⟩, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff (b.mapDomain Sum.inl) = _
        rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff a = 0
        rw [shearDerivation_X_inr]
        apply coeff_rename_eq_zero
        intro b hba
        exact (hb ⟨b, hba⟩).elim

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem realificationLieHom_repr_zero (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (k : κ) (h : ∀ x, e.repr (φ x) k = 0) (x : ℝ ⊗[ℚ] L) :
    (e.baseChange ℝ).repr (realificationLieHom φ x) k = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realificationLieHom_repr_coordinate (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι)
    (h : ∀ x, f.repr (φ x) k = e.repr x i) (x : ℝ ⊗[ℚ] L) :
    (f.baseChange ℝ).repr (realificationLieHom φ x) k = (e.baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem realShearEmbedding_repr (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (a : PolynomialShearIndex (shearWeight w d)) :
    (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a =
      ((polynomialShearBasis (R := ℚ) (shearWeight w d)).baseChange ℝ).repr
        (realificationLieHom (weightedShearEmbedding w d) x) a := by
  exact congrArg (fun c => c a) (polynomialShearRealificationEquiv_repr (shearWeight w d)
    (realificationLieHom (weightedShearEmbedding w d) x))

theorem realShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
        (realShearEmbedding w d x) a = ((weightedBasis w d hw).baseChange ℝ).repr x i := by
  rcases weightedShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · left
    intro x
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_zero (polynomialShearBasis (shearWeight w d))
      (weightedShearEmbedding w d) a hzero x
  · right
    refine ⟨i, fun x => ?_⟩
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_coordinate (weightedBasis w d hw)
      (polynomialShearBasis (shearWeight w d)) (weightedShearEmbedding w d) a i hi x

theorem realShearEmbedding_coordinate_abs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, |((weightedBasis w d hw).baseChange ℝ).repr x i| ≤ δ)
    (a : PolynomialShearIndex (shearWeight w d)) :
    |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a| ≤
      δ := by
  rcases realShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · simpa only [hzero x, abs_zero] using hδ
  · rw [hi x]
    exact hx i

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslation_inverse_action_X (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (i : σ ⊕ Unit) :
    (PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g)).symm (X i) =
      polynomialShearExp (-(realShearEmbedding w d g.coord)) (X i) := by
  calc
    _ = PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) (X i) := by
      rw [map_inv, map_inv]
      rfl
    _ = (weightedShearRealGroupHom w d hwd g⁻¹).val (X i) := by
      rw [bchRealTranslationHom_action]
    _ = _ := by
      change polynomialShearExp (realShearEmbedding w d g⁻¹.coord) (X i) = _
      rw [coord_inv, map_neg]

theorem bchRealTranslation_bounds_of_shear_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d g.coord) a| ≤ δ) :
    let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
    (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ (K : ℝ) * δ) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ (K : ℝ) * δ := by
  let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
  have hpos : ∀ i, 1 ≤ shearWeight w d i := by
    intro i; cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hgn (a) : |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (-(realShearEmbedding w d g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have hpoint (x : σ → ℝ) (hx : ∀ i, |x i| ≤ 1) (i : σ ⊕ Unit) :
      |eval (Sum.elim x (fun _ : Unit => (0 : ℝ)))
        ((PolynomialTranslationGroupOver.actionMonoidHom
          (bchRealTranslationHom w d hwd g)).symm (X i)) -
        Sum.elim x (fun _ : Unit => (0 : ℝ)) i| ≤ (K : ℝ) * δ := by
    rw [bchRealTranslation_inverse_action_X]
    have hh := polynomialShearExp_X_displacement (-(realShearEmbedding w d g.coord))
      hpos (shearWeight_le w d hwd) hδ hδone le_rfl hgn
      (Sum.elim x (fun _ : Unit => (0 : ℝ))) (by
        intro j; cases j with
        | inl j => exact hx j
        | inr _ => simp) i
    convert hh using 1
    · simp only [aeval_eq_eval]
    · simp [K, polynomialShearDisplacementBound, mul_assoc, mul_left_comm, mul_comm]
  constructor
  · intro i
    have hh := hpoint 0 (by simp) (Sum.inl i)
    rw [PolynomialTranslationGroupOver.action_inverse_X_inl_eval] at hh
    simpa [K] using hh
  · intro x hx
    have hh := hpoint x hx (Sum.inr ())
    rw [PolynomialTranslationGroupOver.action_inverse_X_inr_eval] at hh
    simpa [K] using hh

section Metric

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedBasis_real_log_coordinates_bound (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
    (C : ℝ) * dist 1 g < 1 →
      ∀ a, |((weightedBasis w d hw).baseChange ℝ).repr g.coord a| ≤ (C : ℝ) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  dsimp only
  intro hnear a
  have hlog : ‖basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hh := norm_coordinates_le_of_near_one
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
      (lieStructureConstants (weightedOrderedBasis w d hw))
      (fun i j k => (realLieBasis_structure (weightedOrderedBasis w d hw) i j k).symm)
      (weightedOrderedBasis_structure_height w d hw) 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hh
    exact hh hnear
  have hh := (norm_le_pi_norm
    (basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g)
    (weightedIndexOrder w d a)).trans hlog
  have he : (weightedOrderedBasis w d hw).baseChange ℝ =
      ((weightedBasis w d hw).baseChange ℝ).reindex (weightedIndexOrder w d) := by
    ext j
    simp only [weightedOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs,
    he, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using hh

noncomputable def weightedTranslationDisplacementConstant (d n m : ℕ) : ℝ :=
  2 * ((polynomialShearDisplacementBound d (n+1) 1 : ℝ) + 1) *
    ((bchLogMetricConstant d m (2*d+1) 1 : ℝ) + 1)

theorem weightedTranslationDisplacementConstant_pos (d n m : ℕ) :
    0 < weightedTranslationDisplacementConstant d n m := by
  unfold weightedTranslationDisplacementConstant
  positivity

theorem bchRealTranslation_bounds_near_one (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
      (Fintype.card (WeightedBasisIndex w d))
    dist 1 g ≤ 1 / C →
      (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ C * dist 1 g) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ C * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let K : ℝ := polynomialShearDisplacementBound d (Fintype.card σ + 1) 1
  let L : ℝ := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
    (Fintype.card (WeightedBasisIndex w d))
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hC : 0 < C := weightedTranslationDisplacementConstant_pos _ _ _
  have hCeq : C = 2 * (K+1) * (L+1) := rfl
  have hLC : 2 * L ≤ C := by nlinarith [mul_nonneg hK hL]
  have hKC : K * L ≤ C := by nlinarith [mul_nonneg hK hL]
  dsimp only
  intro hnear
  have hdist : 0 ≤ dist 1 g := dist_nonneg
  have hCd : C * dist 1 g ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp hnear
    simpa only [mul_comm] using hh
  have hlognear : L * dist 1 g < 1 := by
    have hh := mul_le_mul_of_nonneg_right hLC hdist
    nlinarith
  have hcoords := weightedBasis_real_log_coordinates_bound w d hw hwd g hlognear
  have hshear := realShearEmbedding_coordinate_abs_le w d hw g.coord
    (mul_nonneg hL hdist) hcoords
  have hbounds := bchRealTranslation_bounds_of_shear_coordinates w d hw hd hwd g
    (mul_nonneg hL hdist) hlognear.le hshear
  have hprod : K * (L * dist 1 g) ≤ C * dist 1 g := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKC hdist
  constructor
  · intro i
    apply le_trans ?_ hprod
    simpa [K] using hbounds.1 i
  · intro x hx
    apply le_trans ?_ hprod
    simpa [K] using hbounds.2 x hx

end Metric

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {m : ℕ}

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

def quotientIntegerCover {E : Type*} [AddCommGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    (E ⧸ Γ) →+ (E ⧸ Γ) := nsmulAddMonoidHom q

theorem quotientIntegerCover_mk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (x : E) :
    quotientIntegerCover Γ q (QuotientAddGroup.mk' Γ x) =
      QuotientAddGroup.mk' Γ ((q : ℝ) • x) := by
  change q • QuotientAddGroup.mk' Γ x = _
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]

theorem quotientIntegerCover_surjective {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (hq : 0 < q) :
    Function.Surjective (quotientIntegerCover Γ q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
  refine ⟨QuotientAddGroup.mk' Γ ((q : ℝ)⁻¹ • x), ?_⟩
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hq0, one_smul]

theorem quotientIntegerCover_continuous {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    Continuous (quotientIntegerCover Γ q) := continuous_id.nsmul q

end Erdos3

end

section

namespace Erdos3

open MeasureTheory CircleFourier
open scoped Classical

theorem character_half : character ((1 / 2 : ℝ) : CircleFourier.Circle) = -1 := by
  have h := fourier_add_half_inv_index (T := (1 : ℝ)) (n := 1)
    (by norm_num) (by norm_num) (0 : CircleFourier.Circle)
  simpa [fourier_apply, character] using h

theorem quotientLinearCharacter_integral {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) [MeasurableSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n)
    (μ : Measure (E ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, quotientLinearCharacter Γ L hint x ∂μ) = if L = 0 then 1 else 0 := by
  classical
  by_cases hL : L = 0
  · subst L
    simp only [quotientLinearCharacter_zero, ite_true, integral_const, probReal_univ, one_smul]
  · rw [if_neg hL]
    have hx : ∃ x, L x ≠ 0 := by
      by_contra hn
      apply hL
      push Not at hn
      ext x
      exact hn x
    obtain ⟨x, hx⟩ := hx
    let v := ((1 / 2) / L x) • x
    have hv : L v = 1 / 2 := by
      change L (((1 / 2) / L x) • x) = _
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    apply integral_eq_zero_of_add_left_eq_neg (g := QuotientAddGroup.mk' Γ v)
    intro y
    rw [quotientLinearCharacter_add, quotientLinearCharacter_mk, hv, character_half, neg_one_mul]

theorem quotientLinearCharacter_integrable {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (Γ : AddSubgroup E)
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L)
    (μ : Measure (E ⧸ Γ)) [IsFiniteMeasure μ] :
    Integrable (quotientLinearCharacter Γ L hint) μ := by
  apply Integrable.of_bound (quotientLinearCharacter_continuous Γ L hint hL).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => (quotientLinearCharacter_norm Γ L hint x).le)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

noncomputable def probabilityAddHaar (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.addHaarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance probabilityAddHaar_probability (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : IsProbabilityMeasure (probabilityAddHaar G) where
  measure_univ := Measure.addHaarMeasure_self

instance probabilityAddHaar_invariant (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : (probabilityAddHaar G).IsAddLeftInvariant :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddLeftInvariant

theorem compact_quotient_of_integral_basis {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (Γ : AddSubgroup E) (b : Basis ι ℝ E) (hb : ∀ i, b i ∈ Γ) : CompactSpace (E ⧸ Γ) := by
  let L := Submodule.span ℤ (Set.range b)
  have hin : L ≤ Γ.toIntSubmodule := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hb i)
  have hc := IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' Γ)
    (QuotientAddGroup.isQuotientMap_mk Γ).continuous (by
      intro x z hz
      rw [map_add]
      have hzero : QuotientAddGroup.mk' Γ z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr (hin hz)
      rw [hzero, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Γ)] at hc
  exact ⟨hc⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

noncomputable def linearQuotientEndomorphism : (V ⧸ Γ) →+ (V ⧸ Γ) :=
  QuotientAddGroup.map Γ Γ R.toAddMonoidHom hR

noncomputable def linearQuotientAverage [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (f : (V ⧸ Γ) → W) (x : V ⧸ Γ) : W :=
  ∫ y, f (x + linearQuotientEndomorphism Γ R hR y) ∂μ

theorem linearQuotientAverage_bound [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f : (V ⧸ Γ) → W)
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : V ⧸ Γ) :
    ‖linearQuotientAverage Γ R hR μ f x‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun y => hf (x + linearQuotientEndomorphism Γ R hR y)))
  simpa only [linearQuotientAverage, integral_const, probReal_univ, one_smul] using h

theorem linearQuotientAverage_character [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ (quotientLinearCharacter Γ L hL) x =
      if L.comp R = 0 then quotientLinearCharacter Γ L hL x else 0 := by
  have hr : ∀ y ∈ Γ, ∃ n : ℤ, L.comp R y = n := fun y hy => hL (R y) (hR y hy)
  have he (y : V ⧸ Γ) :
      quotientLinearCharacter Γ L hL (linearQuotientEndomorphism Γ R hR y) =
        quotientLinearCharacter Γ (L.comp R) hr y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
    rfl
  unfold linearQuotientAverage
  simp_rw [quotientLinearCharacter_add, he]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

theorem linearQuotientEndomorphism_continuous [TopologicalSpace V] (hRc : Continuous R) :
    Continuous (linearQuotientEndomorphism Γ R hR) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp hRc

theorem linearQuotientAverage_invariant [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (f : (V ⧸ Γ) → W) (x z : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ f (x + linearQuotientEndomorphism Γ R hR z) =
      linearQuotientAverage Γ R hR μ f x := by
  have h := integral_add_left_eq_self (μ := μ)
    (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) z
  simpa only [linearQuotientAverage, map_add, add_assoc] using h

theorem linearQuotientAverage_approx [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f g : (V ⧸ Γ) → W)
    {ε : ℝ} (hε : ∀ x, ‖f x - g x‖ ≤ ε) (x : V ⧸ Γ)
    (hf : Integrable (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) μ)
    (hg : Integrable (fun y => g (x + linearQuotientEndomorphism Γ R hR y)) μ) :
    ‖linearQuotientAverage Γ R hR μ f x - linearQuotientAverage Γ R hR μ g x‖ ≤ ε := by
  unfold linearQuotientAverage
  rw [← integral_sub hf hg]
  exact linearQuotientAverage_bound Γ R hR μ (fun x => f x - g x) hε x

theorem linearQuotientAverage_probability [MeasurableSpace (V ⧸ Γ)]
    [MeasurableAdd₂ (V ⧸ Γ)] [MeasurableNeg (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (hRm : Measurable (linearQuotientEndomorphism Γ R hR))
    (f : (V ⧸ Γ) → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hfmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ linearQuotientAverage Γ R hR μ f x) ∧
      Integrable (linearQuotientAverage Γ R hR μ f) μ ∧
      (∫ x, linearQuotientAverage Γ R hR μ f x ∂μ) = 1 := by
  have h := haarShiftDensity_probability μ μ hRm.neg hfm hfi hf0 hfmass
  have he : haarShiftDensity μ (-⇑(linearQuotientEndomorphism Γ R hR)) f =
      linearQuotientAverage Γ R hR μ f := by
    funext x
    simp only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage]
  rwa [he] at h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)
  [MeasurableSpace (V ⧸ Γ)]

theorem linearQuotientAverage_cover {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (q : ℕ)
    (hcover : MeasurePreserving (quotientIntegerCover Γ q) μ μ)
    (f : (V ⧸ Γ) → W) (x : V ⧸ Γ)
    (hf : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y)) μ) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ (fun z => f (quotientIntegerCover Γ q z)) x := by
  have hf' : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y))
      (μ.map (quotientIntegerCover Γ q)) := by rwa [hcover.map_eq]
  have he := integral_map hcover.measurable.aemeasurable hf'
  rw [hcover.map_eq] at he
  change (∫ y, f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y) ∂μ) = _
  rw [he]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change f (q • x + linearQuotientEndomorphism Γ R hR (q • y)) =
      f (q • (x + linearQuotientEndomorphism Γ R hR y))
    rw [map_nsmul, nsmul_add])

theorem linearQuotientAverage_cover_eq_of_map_eq [MeasurableAdd₂ (V ⧸ Γ)]
    {Y W : Type*} [AddCommGroup Y] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (q : ℕ) (E : (V ⧸ Γ) →+ Y)
    (hker : ∀ z, E z = 0 → linearQuotientEndomorphism Γ R hR z = quotientIntegerCover Γ q z)
    (f : (V ⧸ Γ) → W) (x y : V ⧸ Γ) (hxy : E x = E y) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q y) := by
  have hz : E (y - x) = 0 := by rw [map_sub, hxy, sub_self]
  have he := linearQuotientAverage_invariant Γ R hR μ f (quotientIntegerCover Γ q x) (y - x)
  rw [hker _ hz, map_sub, ← add_sub_assoc, add_sub_cancel_left] at he
  exact he.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistParameterPartition
namespace OAI

section

namespace Erdos3

noncomputable def exponentialProgressionScale (N q : ℕ) (p : ℝ) : ℕ :=
  ⌊(N : ℝ) / (8 * q * Real.exp (2 * p))⌋₊

theorem exponentialProgressionScale_bounds (N q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : Real.exp (3 * p + 16) ≤ (N : ℝ)) :
    0 < exponentialProgressionScale N q p ∧
      q * exponentialProgressionScale N q p ≤ N ∧
      (N : ℝ) * Real.exp (-(3 * p + 16)) ≤ exponentialProgressionScale N q p ∧
      2 * (q : ℝ) * exponentialProgressionScale N q p / N ≤
        Real.exp (-(2 * p)) / 4 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < Real.exp (2 * p) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hden : 0 < 8 * (q : ℝ) * Real.exp (2 * p) := by positivity
  have hexp16 : (16 : ℝ) ≤ Real.exp 16 := by
    have := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hlarge : 16 * (q : ℝ) * Real.exp (2 * p) ≤ Real.exp (3 * p + 16) := by
    calc
      16 * (q : ℝ) * Real.exp (2 * p) ≤
          Real.exp 16 * Real.exp p * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hexp16 hqexp (by positivity) (Real.exp_nonneg _)) he.le
      _ = Real.exp (3 * p + 16) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnr : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  let x : ℝ := N / (8 * q * Real.exp (2 * p))
  have hx2 : 2 ≤ x := (le_div_iff₀ hden).mpr (by nlinarith [hlarge.trans hN])
  have hfloor : (exponentialProgressionScale N q p : ℝ) ≤ x :=
    Nat.floor_le (le_trans (by norm_num) hx2)
  have hhalf : x / 2 ≤ (exponentialProgressionScale N q p : ℝ) := by
    have := Nat.lt_floor_add_one x
    change x < (exponentialProgressionScale N q p : ℝ) + 1 at this
    linarith
  have hH : 0 < exponentialProgressionScale N q p := by
    have : (0 : ℝ) < exponentialProgressionScale N q p := by linarith
    exact_mod_cast this
  have hupper : (exponentialProgressionScale N q p : ℝ) *
      (8 * q * Real.exp (2 * p)) ≤ N := (le_div_iff₀ hden).mp hfloor
  have hfit : q * exponentialProgressionScale N q p ≤ N := by
    have : (q : ℝ) * exponentialProgressionScale N q p ≤ N := by
      have hnonneg : (0 : ℝ) ≤ exponentialProgressionScale N q p := by positivity
      nlinarith
    exact_mod_cast this
  refine ⟨hH, hfit, ?_, ?_⟩
  · calc
      (N : ℝ) * Real.exp (-(3 * p + 16)) = N / Real.exp (3 * p + 16) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ N / (16 * q * Real.exp (2 * p)) :=
        div_le_div_of_nonneg_left hnr.le (by positivity) hlarge
      _ = x / 2 := by dsimp [x]; ring
      _ ≤ _ := hhalf
  · apply (div_le_iff₀ hnr).mpr
    rw [Real.exp_neg]
    have heq : (Real.exp (2 * p))⁻¹ / 4 * (N : ℝ) = N / (4 * Real.exp (2 * p)) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp (2 * p))).mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

theorem normalized_point_sub_point_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤
      2 * q * H / N := by
  have hj : (j.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : j.val ≤ 2 * H)
  have hl : (l.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : l.val ≤ 2 * H)
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ (l.val : ℝ) := Nat.cast_nonneg _
  have hdiff : |(j.val : ℝ) - l.val| ≤ 2 * H :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hfactor : 0 ≤ (q : ℝ) / N := by positivity
  calc
    _ = (q : ℝ) / N * |(j.val : ℝ) - l.val| := by
      rw [P.point_val, P.point_val, hstep]
      push_cast
      rw [← sub_div, show ((P.start k : ℝ) + q * j.val) -
        (P.start k + q * l.val) = q * ((j.val : ℝ) - l.val) by ring]
      simp only [abs_div, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
        abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      ring
    _ ≤ (q : ℝ) / N * (2 * H) := mul_le_mul_of_nonneg_left hdiff hfactor
    _ = 2 * q * H / N := by ring

theorem normalized_point_sub_point_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤ ε :=
  (normalized_point_sub_point_le P k hstep hlen hN j l).trans hbound

theorem normalized_point_sub_start_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ 2 * q * H / N := by
  let z : Fin (P.length k) := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  have hz : (P.point k z).val = P.start k := by simp [z]
  simpa only [hz] using normalized_point_sub_point_le P k hstep hlen hN j z

theorem normalized_point_sub_start_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ ε :=
  (normalized_point_sub_start_le P k hstep hlen hN j).trans hbound

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProgressionPartition

theorem label_card_mul_le_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    {H : ℝ} (hlength : ∀ a, H ≤ (P.length a : ℝ)) :
    (Fintype.card P.Label : ℝ) * H ≤ N := by
  have hsum : (∑ a, P.length a) = N := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr P.equiv
  calc
    _ = ∑ _a : P.Label, H := by simp
    _ ≤ ∑ a : P.Label, (P.length a : ℝ) := Finset.sum_le_sum (fun a _ => hlength a)
    _ = N := by exact_mod_cast hsum

theorem label_card_le_exp_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) {A : ℝ} (hlength : ∀ a, (N : ℝ) * Real.exp (-A) ≤ P.length a) :
    (Fintype.card P.Label : ℝ) ≤ Real.exp A := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply (mul_le_mul_iff_left₀ (mul_pos hNr (Real.exp_pos (-A)))).mp
  calc
    _ ≤ (N : ℝ) := P.label_card_mul_le_of_length_lower hlength
    _ = (N : ℝ) * (Real.exp A * Real.exp (-A)) := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = Real.exp A * ((N : ℝ) * Real.exp (-A)) := by ring

end FiniteProgressionPartition

theorem exists_normalizedTwist_parameter_partition {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) :
    ∃ P : ∀ i, FiniteProgressionPartition (N i),
      (∀ i a, (P i).step a = q) ∧
      (∀ i a, 0 < (P i).length a) ∧
      (∀ i a, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a) ∧
      (∀ i a (j : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - (P i).start a / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i a (j k : Fin ((P i).length a)),
        |((P i).point a j).val / (N i : ℝ) - ((P i).point a k).val / (N i : ℝ)| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i, (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16)) ∧
      (Fintype.card (∀ i, (P i).Label) : ℝ) ≤
        Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
  classical
  let H := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hN i)
  have hlower (i : I) (a : (P i).Label) :
      (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ (P i).length a :=
    (hscale i).2.2.1.trans (by exact_mod_cast (hlength i a).1)
  have hcard (i : I) : (Fintype.card (P i).Label : ℝ) ≤ Real.exp (3 * p + 16) :=
    (P i).label_card_le_exp_of_length_lower (hNpos i) (hlower i)
  refine ⟨P, hstep, fun i a => (hscale i).1.trans_le (hlength i a).1, hlower,
    ?_, ?_, hcard, ?_⟩
  · intro i a j
    exact (P i).normalized_point_sub_start_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j
  · intro i a j k
    exact (P i).normalized_point_sub_point_le_of_bound a (hstep i a)
      (hlength i a).2 (hNpos i) (hscale i).2.2.2 j k
  · calc
      _ = ∏ i, (Fintype.card (P i).Label : ℝ) := by rw [Fintype.card_pi, Nat.cast_prod]
      _ ≤ ∏ _i : I, Real.exp (3 * p + 16) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = Real.exp ((Fintype.card I : ℝ) * (3 * p + 16)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def relativePatchComplexity {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℝ :=
  (d : ℝ) + Real.log (1 + (A.kernel.lip : ℝ))

noncomputable def relativePatchDistinctWeights {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℕ :=
  (Finset.univ.image A.weight).card

noncomputable def relativePatchBoxScore {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x ∈ integerBox N, (f x - a) * A.value (fun i => (x i : ℝ))

noncomputable def relativePatchSliceScore {X : Type*} [Fintype X] {s d q : ℕ}
    {N : X → ℕ} (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x : ∀ i, Fin (S.length i),
    (f (fun i => ((S.point x i).val : ℤ)) - a) * A.value (fun i => ((x i).val : ℝ))

def RelativePatchSliceConclusion {X : Type*} [Fintype X] (s : ℕ)
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) (rankBound : ℕ) (cost : ℝ) : Prop :=
  ∃ (q : ℕ), 0 < q ∧ ∃ (S : ResidueBoxSlice N q) (d : ℕ)
    (A : PolynomialPatch X s d),
    (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
    d ≤ rankBound ∧ relativePatchComplexity A ≤ cost ∧
    Real.exp (-cost) ≤ relativePatchSliceScore S f target A

def RelativePatchAbsoluteRule (s n₀ : ℕ) (p a Λ : ℝ) (d₀ : ℕ) : Prop :=
  ∀ (N : Fin n₀ → ℕ),
    (∀ i, (N i).Prime) → Function.Injective N →
    (∀ i j, N i ≤ 2 ^ (n₀ + 1) * N j) →
    (∀ i, Real.exp p ≤ (N i : ℝ)) →
    ∀ (f : (Fin n₀ → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a ≤ (𝔼 x ∈ integerBox N, f x) →
      RelativePatchSliceConclusion s N f Λ d₀ p

def RelativePatchInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X],
      (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch X s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

def RelativePatchPowerInductionRule (s n₀ stage : ℕ) (τ : ℝ) (E : ℕ) : Prop :=
  RelativePatchInductionRule s n₀ stage τ (fun p => (p + 2) ^ E) (fun p => (p + 2) ^ E)

theorem relativePatchComplexity_rank_le {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : (d : ℝ) ≤ relativePatchComplexity A := by
  have hlog : 0 ≤ Real.log (1 + (A.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [A.kernel.lip.coe_nonneg])
  exact le_add_of_nonneg_right hlog

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def identity (N : I → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside _ _ hj := by simpa using hj

def comp (S : ResidueBoxSlice N q) {r : ℕ} (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice N (q * r) where
  start i := S.start i + q * T.start i
  length := T.length
  inside i j hj := by
    have h := S.inside i (T.start i + r * j) (T.inside i j hj)
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h

@[simp] theorem comp_point (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : ∀ i, Fin (T.length i)) :
    (S.comp T).point x = S.point (T.point x) := by
  ext i
  simp [comp, point, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

noncomputable def polynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℝ :=
  MvPolynomial.C (S.start i : ℝ) + MvPolynomial.C (q : ℝ) * MvPolynomial.X i

@[simp] theorem polynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℝ) (fun i => ((x i).val : ℝ)) (S.polynomial i) =
      ((S.point x i).val : ℝ) := by
  simp [polynomial, point, Nat.cast_add, Nat.cast_mul]

end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem comp_length_exp_lower
    (A : ResidueBoxSlice N q) (B : ResidueBoxSlice A.length r) {u v : ℝ}
    (hA : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ A.length i)
    (hB : ∀ i, Real.exp (-v) * (A.length i : ℝ) ≤ B.length i) :
    ∀ i, Real.exp (-(u + v)) * (N i : ℝ) ≤ (A.comp B).length i := by
  intro i
  change Real.exp (-(u + v)) * (N i : ℝ) ≤ (B.length i : ℝ)
  calc
    Real.exp (-(u + v)) * (N i : ℝ) =
        Real.exp (-v) * (Real.exp (-u) * (N i : ℝ)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ Real.exp (-v) * (A.length i : ℝ) :=
      mul_le_mul_of_nonneg_left (hA i) (Real.exp_pos _).le
    _ ≤ (B.length i : ℝ) := hB i

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

def integerAffine (S : ResidueBoxSlice N q) (x : X → ℤ) : X → ℤ :=
  fun i => (S.start i : ℤ) + (q : ℤ) * x i

def integerPullback (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) :
    (X → ℤ) → ℝ := fun x => f (S.integerAffine x)

@[simp] theorem integerAffine_finPoint (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) :
    S.integerAffine (fun i => ((x i).val : ℤ)) =
      fun i => ((S.point x i).val : ℤ) := by
  funext i
  simp [integerAffine, point, Nat.cast_add, Nat.cast_mul]

@[simp] theorem integerAffine_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : X → ℤ) :
    (S.comp T).integerAffine x = S.integerAffine (T.integerAffine x) := by
  funext i
  simp only [integerAffine, comp, Nat.cast_add, Nat.cast_mul]
  ring

@[simp] theorem integerPullback_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ) :
    (S.comp T).integerPullback f = T.integerPullback (S.integerPullback f) := by
  funext x
  simp only [integerPullback, integerAffine_comp]

end ResidueBoxSlice

theorem relativePatchSliceScore_comp {X : Type*} [Fintype X]
    {s d q r : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ)
    (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore T (S.integerPullback f) a A =
      relativePatchSliceScore (S.comp T) f a A := by
  unfold relativePatchSliceScore
  apply Finset.expect_congr rfl
  intro x _
  simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
    ResidueBoxSlice.comp_point]

theorem RelativePatchSliceConclusion.comp {X : Type*} [Fintype X]
    {s q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q) (hq : 0 < q)
    {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound : ℕ} {u v : ℝ}
    (hu : 0 ≤ u)
    (hlength : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ S.length i)
    (h : RelativePatchSliceConclusion s S.length (S.integerPullback f)
      target rankBound v) :
    RelativePatchSliceConclusion s N f target rankBound (u + v) := by
  obtain ⟨r, hr, T, d, A, hT, hd, hcomplexity, hscore⟩ := h
  refine ⟨q * r, Nat.mul_pos hq hr, S.comp T, d, A,
    S.comp_length_exp_lower T hlength hT, hd, ?_, ?_⟩
  · exact hcomplexity.trans (by linarith)
  · rw [← relativePatchSliceScore_comp]
    exact (Real.exp_le_exp.mpr (by linarith : -(u + v) ≤ -v)).trans hscore

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def LowDensityRelativeAbsoluteRule (s n₀ : ℕ) (p H : ℝ) (D : ℕ) (x : ℝ) : Prop :=
  ∀ a : ℝ, Real.exp (-p) ≤ a → LowDensityThreshold H a →
    RelativePatchAbsoluteRule s n₀ x a (H * a) D

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoverBasisResidues
namespace OAI

section

namespace Erdos3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (Γ : AddSubgroup E)

noncomputable def coverLatticePoint (d : ℕ) (hd : 0 < d) :
    Γ →+ (quotientIntegerCover Γ d).ker where
  toFun x := ⟨QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val), by
    change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ _) = 0
    rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr x.property⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [smul_add]

theorem coverLatticePoint_val (d : ℕ) (hd : 0 < d) (x : Γ) :
    (coverLatticePoint Γ d hd x).val =
      QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) := rfl

theorem coverLatticePoint_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (coverLatticePoint Γ d hd) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective Γ y.val
  have hxΓ : (d : ℝ) • x ∈ Γ := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change QuotientAddGroup.mk' Γ ((d : ℝ) • x) = 0
    rw [← quotientIntegerCover_mk, hx]
    exact y.property
  refine ⟨⟨(d : ℝ) • x, hxΓ⟩, ?_⟩
  apply Subtype.ext
  rw [coverLatticePoint_val, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  exact hx

theorem coverLatticePoint_ker (d : ℕ) (hd : 0 < d) :
    (coverLatticePoint Γ d hd).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have he : QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) = 0 :=
      congrArg Subtype.val hx
    have hΓ := (QuotientAddGroup.eq_zero_iff _).mp he
    refine ⟨⟨(d : ℝ)⁻¹ • x.val, hΓ⟩, ?_⟩
    apply Subtype.ext
    change d • ((d : ℝ)⁻¹ • x.val) = x.val
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  · rintro ⟨y, rfl⟩
    change coverLatticePoint Γ d hd (d • y) = 0
    apply Subtype.ext
    rw [coverLatticePoint_val]
    change QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • (d • y.val)) = 0
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr y.property

abbrev CoverLatticeResidue (d : ℕ) := Γ ⧸ (nsmulAddMonoidHom (α := Γ) d).range

noncomputable def coverLatticeResidueEquiv (d : ℕ) (hd : 0 < d) :
    CoverLatticeResidue Γ d ≃+ (quotientIntegerCover Γ d).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (coverLatticePoint_ker Γ d hd)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (coverLatticePoint Γ d hd)
      (coverLatticePoint_surjective Γ d hd))

theorem coverLatticeResidueEquiv_mk (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverLatticeResidueEquiv Γ d hd (QuotientAddGroup.mk' _ x) =
      coverLatticePoint Γ d hd x := rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Γ : AddSubgroup E) (b : Basis I ℤ Γ)

noncomputable def latticeBasisResidue (d : ℕ) : Γ →+ (I → ZMod d) :=
  (integerResidueMap I d).toAddMonoidHom.comp b.equivFun.toAddMonoidHom

omit [Module ℝ E] in
theorem latticeBasisResidue_surjective (d : ℕ) :
    Function.Surjective (latticeBasisResidue Γ b d) :=
  (integerResidueMap_surjective I d).comp b.equivFun.surjective

omit [Module ℝ E] in
theorem latticeBasisResidue_ker (d : ℕ) :
    (latticeBasisResidue Γ b d).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have hz : b.equivFun x ∈ integerScalarLattice I (d : ℤ) := by
      rw [← integerResidueMap_ker]
      exact hx
    obtain ⟨z, hz⟩ := (integerScalarLattice_mem _ _).mp hz
    refine ⟨b.equivFun.symm z, ?_⟩
    apply b.equivFun.injective
    change b.equivFun (d • b.equivFun.symm z) = b.equivFun x
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    simpa only [natCast_zsmul] using hz
  · rintro ⟨y, rfl⟩
    change integerResidueMap I d (b.equivFun (d • y)) = 0
    have hz : b.equivFun (d • y) ∈ integerScalarLattice I (d : ℤ) := by
      apply (integerScalarLattice_mem _ _).mpr
      exact ⟨b.equivFun y, by simp only [map_nsmul, natCast_zsmul]⟩
    rw [← integerResidueMap_ker] at hz
    exact hz

noncomputable def coverLatticeBasisEquiv (d : ℕ) :
    CoverLatticeResidue Γ d ≃+ (I → ZMod d) :=
  (QuotientAddGroup.quotientAddEquivOfEq (latticeBasisResidue_ker Γ b d)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (latticeBasisResidue Γ b d)
      (latticeBasisResidue_surjective Γ b d))

omit [Module ℝ E] in
theorem coverLatticeBasisEquiv_mk (d : ℕ) (x : Γ) :
    coverLatticeBasisEquiv Γ b d (QuotientAddGroup.mk' _ x) =
      latticeBasisResidue Γ b d x := rfl

noncomputable def coverKernelBasisEquiv (d : ℕ) (hd : 0 < d) :
    (I → ZMod d) ≃+ (quotientIntegerCover Γ d).ker :=
  (coverLatticeBasisEquiv Γ b d).symm.trans (coverLatticeResidueEquiv Γ d hd)

theorem coverKernelBasisEquiv_residue (d : ℕ) (hd : 0 < d) (x : Γ) :
    coverKernelBasisEquiv Γ b d hd (latticeBasisResidue Γ b d x) =
      coverLatticePoint Γ d hd x := by
  rw [← coverLatticeBasisEquiv_mk]
  simp only [coverKernelBasisEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact coverLatticeResidueEquiv_mk Γ d hd x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationPureFactorValues
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

theorem translationShear_derivation_rename_eq_zero
    {σ : Type*} {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w ℝ)
    (hD : ∀ i, D.val (X (Sum.inl i)) = 0) (P : MvPolynomial σ ℝ) :
    D.val (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, D.val.leibniz, hD, hP, smul_zero, add_zero]

namespace PolynomialTranslationLie

variable {B : Type*} [Fintype B]

theorem bchRealTranslationHom_pure_base_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (b : B → ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = C (b i))
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = 0) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨b, 0⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val b 0
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)) ?_
  · simpa only [PolynomialTranslationGroupOver.actionElement, map_zero] using h.symm
  · change polynomialShearExp (realShearEmbedding w d v) (X (Sum.inr ())) = _
    simpa only [map_zero] using polynomialShearExp_X_of_derivation_eq_C
      (realShearEmbedding w d v) (Sum.inr ()) 0 (by simpa only [map_zero] using hP)

theorem bchRealTranslationHom_pure_polynomial_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial B ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = 0)
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = rename Sum.inl P) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨0, P⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have hsq : ((realShearEmbedding w d v).val.toLinearMap ^ 2) (X (Sum.inr ())) = 0 := by
    change (realShearEmbedding w d v).val ((realShearEmbedding w d v).val (X (Sum.inr ()))) = 0
    rw [hP]
    exact translationShear_derivation_rename_eq_zero _ hb P
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val 0 P
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _
      (by simpa only [Pi.zero_apply, map_zero] using hb i))
    (by change polynomialShearExp _ _ = _
        rw [polynomialShearExp_eq_add_of_sq_eq_zero _ hsq, hP])
  simpa only [PolynomialTranslationGroupOver.actionElement, neg_zero,
    polynomialTranslate_zero_ring] using h.symm

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationRealPureFactors
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def baseRealElement (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) : ℝ ⊗[ℚ] weightedSubalgebra w d := by
  letI := weightedBasisIndex_finite w d hw
  exact ((weightedBasis w d hw).baseChange ℝ).equivFun.symm (Sum.elim b (fun _ => 0))

noncomputable def polynomialRealElement (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) : ℝ ⊗[ℚ] weightedSubalgebra w d := by
  letI := weightedBasisIndex_finite w d hw
  exact ((weightedBasis w d hw).baseChange ℝ).equivFun.symm
    (Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val))

@[simp] theorem baseRealElement_repr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) (a : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr (baseRealElement w d hw b) a =
      Sum.elim b (fun _ => 0) a := by
  let := weightedBasisIndex_finite w d hw
  exact congrFun (((weightedBasis w d hw).baseChange ℝ).equivFun.apply_symm_apply _) a

@[simp] theorem polynomialRealElement_repr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (a : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr (polynomialRealElement w d hw P) a =
      Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val) a := by
  let := weightedBasisIndex_finite w d hw
  exact congrFun (((weightedBasis w d hw).baseChange ℝ).equivFun.apply_symm_apply _) a

theorem realShearEmbedding_base_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (i : σ) :
    ((realShearEmbedding w d x).val (X (Sum.inl i))).coeff 0 =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) := by
  let a : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inl i, 0, by
    change Finsupp.weight (shearWeight w d) 0 + 1 ≤ w i
    simpa using Nat.succ_le_of_lt (hw i)⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ a (Sum.inl i) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
  change (shearDerivation y.val (X (Sum.inl i))).coeff 0 = _
  rw [shearDerivation_X_inl]
  simp

theorem realShearEmbedding_extra_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) := by
  have hweight : Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) =
      Finsupp.weight w a.val := by
    change Finsupp.linearCombination ℕ (shearWeight w d) (a.val.mapDomain Sum.inl) = _
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  let j : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inr (), a.val.mapDomain Sum.inl, by
    change Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) + 1 ≤ d
    rw [hweight]
    exact a.property⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) j = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ j (Sum.inr a) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
  change (shearDerivation y.val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) = _
  rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]

theorem realShearEmbedding_polynomial_mem (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial σ ℝ)
    (hP : (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P) :
    P ∈ weightedSupportLT w d := by
  intro a ha
  have hcoeff : ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff
      (a.mapDomain Sum.inl) ≠ 0 := by
    rw [hP, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
    exact MvPolynomial.mem_support_iff.mp ha
  have h := (realShearEmbedding w d x).property (Sum.inr ())
    (MvPolynomial.mem_support_iff.mpr hcoeff)
  change Finsupp.weight (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  change Finsupp.weight w a < d
  change Finsupp.linearCombination ℕ (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  rw [Finsupp.linearCombination_mapDomain] at h
  exact h

theorem realShearEmbedding_shape_of_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (b : σ → ℝ) (P : weightedSupportLT (R := ℝ) w d)
    (hb : ∀ i, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) = b i)
    (hP : ∀ a, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) = P.val.coeff a.val) :
    (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P.val := by
  classical
  obtain ⟨b', P', hb', hP'⟩ := realShearEmbedding_shape w d x
  have hbq (i : σ) : b' i = b i := by
    have h := realShearEmbedding_base_coeff w d hw x i
    rw [hb', hb] at h
    simpa using h
  have hPq : P' = P.val := by
    have hmem := realShearEmbedding_polynomial_mem w d x P' hP'
    apply MvPolynomial.ext
    intro a
    by_cases ha : Finsupp.weight w a < d
    · have h := realShearEmbedding_extra_coeff w d hw x ⟨a, ha⟩
      rw [hP', coeff_rename_mapDomain Sum.inl Sum.inl_injective, hP] at h
      exact h
    · have hz (Q : MvPolynomial σ ℝ) (hQ : Q ∈ weightedSupportLT w d) : Q.coeff a = 0 := by
        by_contra hc
        exact ha (hQ (MvPolynomial.mem_support_iff.mpr hc))
      rw [hz P' hmem, hz P.val P.property]
  exact ⟨fun i => (hb' i).trans (congrArg C (hbq i)), hP'.trans (congrArg (rename Sum.inl) hPq)⟩

theorem polynomialRealElement_shear_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (i : σ) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inl i)) = 0 := by
  simpa using (realShearEmbedding_shape_of_coordinates w d hw
    (polynomialRealElement w d hw P) 0 P (by simp) (by simp)).1 i

theorem polynomialRealElement_shear_extra (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inr ())) =
      rename Sum.inl P.val :=
  (realShearEmbedding_shape_of_coordinates w d hw _ 0 P (by simp) (by simp)).2

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_sub_degree_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [← majorTranslationJointPolynomial_sub]
  exact majorTranslationJointPolynomial_lower w
    (weightedTopPart_remainder_lt (Sum.elim (fun _ : U => 1) w) hD) A hA

theorem majorTranslationJointPolynomial_degree_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (majorTranslationTopCoordinates w A) := by
  have hlower := majorTranslationJointPolynomial_sub_degree_top_lower w hD A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) A) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero]
  exact majorTranslationJointPolynomial_weightedHomogeneousComponent w
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A hA

theorem majorTranslationJointPolynomial_degree_slot_top (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (α : B →₀ ℕ) :
    weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α (majorTranslationJointPolynomial D A)) =
      polynomialSlotCoefficient α
        (majorTranslationJointPolynomial
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
          (majorTranslationTopCoordinates w A)) := by
  rw [polynomialSlotCoefficient_weightedHomogeneousComponent (fun _ : U => 1) w
    (majorTranslationJointPolynomial_degree w hD A hA),
    majorTranslationJointPolynomial_degree_weightedHomogeneousComponent w hD A hA]

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem ofCoordinates_mem_gradedPolynomialSubmodule
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)
    (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous v (ω i)) :
    ofCoordinates (R := ℚ) b P ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (ofCoordinates (R := ℚ) b P) α) = _
  apply b.repr.injective
  ext i
  have hc : b.repr (coefficients (ofCoordinates (R := ℚ) b P) α) i =
      (P i).coeff α := by
    change (b.coord i).toAddMonoidHom (coefficients (ofCoordinates (R := ℚ) b P) α) = _
    rw [← coeff_coordinate, coordinate_ofCoordinates]
  rw [basisGradeProjection_repr, hc]
  by_cases hi : ω i = Finsupp.weight v α
  · rw [if_pos hi]
  · rw [if_neg hi, (hP i).coeff_eq_zero α (Ne.symm hi)]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_of_gradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    F.realSymbolRepresentative b ω hlayers v (F.realSymbolOfPolynomial b ω hlayers v P) = P := by
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · rw [F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v P) ⟨(α, i), h⟩]
    exact F.realSymbolOfPolynomial_coordinate b ω hlayers v P ⟨(α, i), h⟩
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h]
    have hi := congrArg (fun x => (b.baseChange ℝ).repr x i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, if_neg (Ne.symm h)] at hi
    exact hi

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem exists_translation_coordinate_polynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d) :
    ∃ p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1),
      ∀ u : U → ℝ,
        bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
            (fun _ : U => 1) u p) =
          ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let F := weightedFiltration w d hwd
  let b := weightedBasis w d hw
  let ω := weightedBasisGrade w d
  have hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) :=
    weightedFiltration_layer_eq_span w d hw hwd
  let Acoord : WeightedBasisIndex w d → MvPolynomial U ℝ := Sum.elim A (fun _ => 0)
  let Pcoord : WeightedBasisIndex w d → MvPolynomial U ℝ :=
    Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)
  have hAcoord : ∀ i, Acoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
    | inr α => exact Submodule.zero_mem _
  have hPcoord : ∀ i, Pcoord i ∈ weightedSupportLE (fun _ : U => 1) (ω i) := by
    intro i
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val
  let a := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Acoord hAcoord
  let q := F.realCoordinatePolynomialOrbit b ω hlayers (fun _ : U => 1) Pcoord hPcoord
  have ha (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a) =
        ⟨fun i => eval u (A i), 0⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u a
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
      (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
    · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
        (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
    · intro i
      exact F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inl i)
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Acoord hAcoord u (Sum.inr α)
      simpa only [Acoord, Sum.elim_inr, map_zero, ZeroMemClass.coe_zero,
        MvPolynomial.coeff_zero] using h
  have hq (u : U → ℝ) : bchRealTranslationHom w d hwd
      (F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q) =
        ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
    let g := F.realification.polynomialOrbitRealEval (fun _ : U => 1) u q
    let Pu : weightedSupportLT (R := ℝ) w d :=
      ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
    have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
    · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
        (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
    · intro i
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inl i)
      simpa only [Pcoord, Sum.elim_inl, map_zero, Pi.zero_apply] using h
    · intro α
      have h := F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers _ Pcoord hPcoord u (Sum.inr α)
      change (b.baseChange ℝ).repr g.coord (Sum.inr α) = eval u (polynomialSlotCoefficient α.val P) at h
      rw [h]
      simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
        RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
        Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
        polynomialSlotCoefficient_eval u α.val P
  refine ⟨a * q, fun u => ?_⟩
  rw [map_mul, map_mul, ha, hq]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def translationBaseCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim A (fun _ => 0)

noncomputable def translationPolynomialCoordinatePolynomial
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ) :
    WeightedBasisIndex w d → MvPolynomial U ℝ :=
  Sum.elim (fun _ => 0) (fun α => polynomialSlotCoefficient α.val P)

theorem translationBaseCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ i, (A i).totalDegree ≤ w i) (i : WeightedBasisIndex w d) :
    translationBaseCoordinatePolynomial w d A i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact (mem_weightedSupportLE_one_iff _ _).mpr (hA i)
  | inr α => exact Submodule.zero_mem _

theorem translationPolynomialCoordinatePolynomial_adapted
    (w : B → ℕ) (d : ℕ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    translationPolynomialCoordinatePolynomial w d P i ∈
      weightedSupportLE (fun _ : U => 1) (weightedBasisGrade w d i) := by
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr α => exact polynomialSlotCoefficient_degree (fun _ : U => 1) w hP α.val

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationBasePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA)

noncomputable def translationPurePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) := by
  letI := weightedBasisIndex_finite w d hw
  letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP)

noncomputable def translationCoordinatePolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationBasePolynomialOrbit w d hw hwd A hA *
    translationPurePolynomialOrbit w d hw hwd P hP

@[simp] theorem translationBasePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationBasePolynomialOrbit w d hw hwd A hA).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationBaseCoordinatePolynomial w d A) := rfl

@[simp] theorem translationPurePolynomialOrbit_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    letI := weightedBasisIndex_finite w d hw
    letI : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
    (translationPurePolynomialOrbit w d hw hwd P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis w d hw).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial w d P) := rfl

@[simp] theorem translationBasePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationBasePolynomialOrbit w d hw hwd A hA).log =
        translationBaseCoordinatePolynomial w d A i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) i

@[simp] theorem translationPurePolynomialOrbit_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (i : WeightedBasisIndex w d) :
    VectorPolynomial.coordinate (((weightedBasis w d hw).baseChange ℝ).coord i).toAddMonoidHom
      (translationPurePolynomialOrbit w d hw hwd P hP).log =
        translationPolynomialCoordinatePolynomial w d P i := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_coordinate
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) i

theorem translationBasePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)).coord i =
      eval u (translationBaseCoordinatePolynomial w d A i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)
    (translationBaseCoordinatePolynomial_adapted w d A hA) u i

theorem translationPurePolynomialOrbit_eval_coordinates
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (u : U → ℝ) (i : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)).coord i =
      eval u (translationPolynomialCoordinatePolynomial w d P i) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  exact (weightedFiltration w d hwd).realCoordinatePolynomialOrbit_eval_coordinates
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)
    (translationPolynomialCoordinatePolynomial_adapted w d P hP) u i

theorem translationBasePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)) =
      ⟨fun i => eval u (A i), 0⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationBasePolynomialOrbit w d hw hwd A hA)
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord
    (fun i => eval u (A i)) (0 : weightedSupportLT (R := ℝ) w d) ?_ ?_
  · exact bchRealTranslationHom_pure_base_of_shape w d hwd g.coord _ hs.1
      (by simpa only [ZeroMemClass.coe_zero, map_zero] using hs.2)
  · intro i
    exact translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inl i)
  · intro α
    simpa only [translationBaseCoordinatePolynomial, Sum.elim_inr, map_zero,
      ZeroMemClass.coe_zero, MvPolynomial.coeff_zero] using
      translationBasePolynomialOrbit_eval_coordinates w d hw hwd A hA u (Sum.inr α)

theorem translationPurePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)) =
      ⟨0, specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  let g := (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
    (fun _ : U => 1) u (translationPurePolynomialOrbit w d hw hwd P hP)
  let Pu : weightedSupportLT (R := ℝ) w d :=
    ⟨specializeMajorParameters (RingHom.id ℝ) P u, hPslot u⟩
  have hs := realShearEmbedding_shape_of_coordinates w d hw g.coord 0 Pu ?_ ?_
  · exact bchRealTranslationHom_pure_polynomial_of_shape w d hwd g.coord Pu.val
      (fun i => by simpa only [Pi.zero_apply, map_zero] using hs.1 i) hs.2
  · intro i
    simpa only [translationPolynomialCoordinatePolynomial, Sum.elim_inl, map_zero,
      Pi.zero_apply] using
      translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inl i)
  · intro α
    have h := translationPurePolynomialOrbit_eval_coordinates w d hw hwd P hP u (Sum.inr α)
    change ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inr α) =
      eval u (polynomialSlotCoefficient α.val P) at h
    rw [h]
    simpa only [MvPolynomial.aeval_eq_eval, Pu, specializeMajorParameters,
      RingHom.comp_id, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.coe_eval₂Hom] using
      polynomialSlotCoefficient_eval u α.val P

theorem translationCoordinatePolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hPslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (translationCoordinatePolynomialOrbit w d hw hwd A hA P hP)) =
      ⟨fun i => eval u (A i), specializeMajorParameters (RingHom.id ℝ) P u⟩ := by
  rw [translationCoordinatePolynomialOrbit, map_mul, map_mul,
    translationBasePolynomialOrbit_realEval, translationPurePolynomialOrbit_realEval
      w d hw hwd P hP hPslot]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module VectorPolynomial
open NilpotentLieFiltration
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def translationPolynomialSymbolHom
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realPolynomialSymbolHom
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)).comp
      ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
        (fun _ : U => 1)).toMonoidHom

@[simp] theorem translationPolynomialSymbolHom_coord
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1)) :
    (translationPolynomialSymbolHom w d hw hwd p).coord =
      (weightedFiltration w d hwd).realSymbolOfPolynomial
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log := rfl

noncomputable def translationPolynomialSymbolLift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm
      ((weightedFiltration w d hwd).realPolynomialSymbolLift
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x)

@[simp] theorem translationPolynomialSymbolLift_log
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (translationPolynomialSymbolLift w d hw hwd x).log =
      (weightedFiltration w d hwd).realSymbolRepresentative
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) x.coord := rfl

@[simp] theorem translationPolynomialSymbolHom_lift
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPolynomialSymbolLift w d hw hwd x) = x := by
  simp only [translationPolynomialSymbolHom, translationPolynomialSymbolLift,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    realPolynomialSymbolHom_lift]

theorem translationBasePolynomialOrbit_symbol_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (translationBasePolynomialOrbit w d hw hwd (majorTranslationTopCoordinates w A)
        (majorTranslationTopCoordinates_degree w A)) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationBaseCoordinatePolynomial w d A i)) =
      translationBaseCoordinatePolynomial w d (majorTranslationTopCoordinates w A) := by
    funext i
    cases i with
    | inl i => rfl
    | inr α => exact map_zero _
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationBasePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationBaseCoordinatePolynomial w d A)]
  rw [hcoords]

theorem translationPurePolynomialOrbit_symbol_eq_of_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (P Q : MvPolynomial (U ⊕ B) ℝ)
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hQ : Q ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (htop : ∀ α : B →₀ ℕ,
      weightedHomogeneousComponent (fun _ : U => 1) (d - Finsupp.weight w α)
        (polynomialSlotCoefficient α P) = polynomialSlotCoefficient α Q) :
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd P hP) =
    translationPolynomialSymbolHom w d hw hwd
      (translationPurePolynomialOrbit w d hw hwd Q hQ) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  have hcoords : (fun i : WeightedBasisIndex w d =>
      weightedHomogeneousComponent (fun _ : U => 1) (weightedBasisGrade w d i)
        (translationPolynomialCoordinatePolynomial w d P i)) =
      translationPolynomialCoordinatePolynomial w d Q := by
    funext i
    cases i with
    | inl i => exact map_zero _
    | inr α => exact htop α.val
  apply NilpotentLieBCHGroup.ext
  simp only [translationPolynomialSymbolHom_coord, translationPurePolynomialOrbit_log]
  rw [(weightedFiltration w d hwd).realSymbolOfPolynomial_ofCoordinates_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
    (translationPolynomialCoordinatePolynomial w d P)]
  rw [hcoords]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

noncomputable def majorTranslationPolynomialOrbit
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit w d hw hwd A hA
    (majorTranslationJointPolynomial D A) (majorTranslationJointPolynomial_degree w hD A hA)

theorem majorTranslationPolynomialOrbit_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
      algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) A u := by
  rw [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit_realEval
    w d hw hwd A hA _ _ (majorTranslationJointPolynomial_specialize_lower w hw hD A),
    majorTranslationJointPolynomial_specialize]
  rfl

theorem majorTranslationPolynomialOrbit_top_log_graded
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationPolynomialOrbit w d hw hwd D
      (fun _ hα => (hD (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log ∈
      gradedPolynomialSubmodule ((weightedBasis w d hw).baseChange ℝ)
        (weightedBasisGrade w d) (fun _ : U => 1) := by
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  apply (weightedFiltration w d hwd).realPolynomialOrbit_log_mul_mem_graded
    (weightedBasis w d hw) (weightedBasisGrade w d) (fun _ : U => 1)
    (weightedBasis_homogeneous_brackets w d hw)
  · rw [translationBasePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact majorTranslationTopCoordinates_homogeneous w A i
    | inr α => exact isWeightedHomogeneous_zero ℝ _ _
  · rw [translationPurePolynomialOrbit_log]
    apply ofCoordinates_mem_gradedPolynomialSubmodule
    intro i
    cases i with
    | inl i => exact isWeightedHomogeneous_zero ℝ _ _
    | inr α =>
      change (polynomialSlotCoefficient α.val
        (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A))).IsWeightedHomogeneous
          (fun _ : U => 1) (d - Finsupp.weight w α.val)
      have htop := majorTranslationJointPolynomial_top_homogeneous w hD A
      have hle : majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
          weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
        fun _ hβ => (htop (mem_support_iff.mp hβ)).le
      have he := polynomialSlotCoefficient_weightedHomogeneousComponent
        (fun _ : U => 1) w hle α.val
      rw [htop.weightedHomogeneousComponent_same] at he
      rw [← he]
      exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

 theorem majorTranslationPolynomialOrbit_symbol_degree_top
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA) =
    translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
          (mem_support_iff.mp hα)).le)
        (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)) := by
  simp only [majorTranslationPolynomialOrbit, translationCoordinatePolynomialOrbit, map_mul]
  rw [translationBasePolynomialOrbit_symbol_top w d hw hwd A hA]
  rw [translationPurePolynomialOrbit_symbol_eq_of_top w d hw hwd
    (majorTranslationJointPolynomial D A)
    (majorTranslationJointPolynomial
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (majorTranslationTopCoordinates w A))
    (majorTranslationJointPolynomial_degree w hD A hA)
    (majorTranslationJointPolynomial_degree w
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A))
    (majorTranslationJointPolynomial_degree_slot_top w hD A hA)]

 theorem majorTranslationPolynomialOrbit_degree_symbol_representative
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    (weightedFiltration w d hwd).realSymbolRepresentative
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord =
    (majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A)).log := by
  rw [majorTranslationPolynomialOrbit_symbol_degree_top w d hw hwd D hD A hA,
    translationPolynomialSymbolHom_coord]
  exact (weightedFiltration w d hwd).realSymbolRepresentative_of_gradedPolynomial
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) _
    (majorTranslationPolynomialOrbit_top_log_graded w d hw hwd _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) A)

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_eq
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) :
    translationPolynomialSymbolLift w d hw hwd
      (translationPolynomialSymbolHom w d hw hwd
        (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)) =
    majorTranslationPolynomialOrbit w d hw hwd
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
      (fun _ hα => ((weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (mem_support_iff.mp hα)).le)
      (majorTranslationTopCoordinates w A) (majorTranslationTopCoordinates_degree w A) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationPolynomialSymbolLift w d hw hwd
    (translationPolynomialSymbolHom w d hw hwd
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA))).log = _
  rw [translationPolynomialSymbolLift_log,
    majorTranslationPolynomialOrbit_degree_symbol_representative w d hw hwd D hD A hA]
  rfl

 theorem majorTranslationPolynomialOrbit_degree_symbolLift_realEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (u : U → ℝ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u
        (translationPolynomialSymbolLift w d hw hwd
          (translationPolynomialSymbolHom w d hw hwd
            (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)))) =
      algebraicMajorSymbol
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D)
        (specializeMajorParameters (RingHom.id ℝ)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) 0)
        (majorTranslationTopCoordinates w A) u := by
  rw [majorTranslationPolynomialOrbit_degree_symbolLift_eq w d hw hwd D hD A hA]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd _ _ _ _ u

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedTranslationLatticePhase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem realLattice_translation_integral
    {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationNilmanifold w d hw hwd).realLattice) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationSubgroup := by
  change g ∈ (weightedTranslationLattice w d hwd).map NilpotentLieBCHGroup.realificationHom at hg
  obtain ⟨r,hr,rfl⟩ := hg
  have hi : bchTranslationHom w d hw hwd r ∈ PolynomialTranslationGroup.integralGroup :=
    (bchTranslationHom_mem_integralGroup_iff w d hw hwd r).mpr hr
  obtain ⟨z,hz⟩ := hi
  refine ⟨z,?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← hz]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

noncomputable def weightedTranslationPhaseQuotientMap :
    (weightedTranslationNilmanifold w d hw hwd).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationSubgroup) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realLattice_translation_integral w d hw hwd (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul,map_inv] using h)

@[simp] theorem weightedTranslationPhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationPhaseQuotientMap w d hw hwd (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

noncomputable def weightedTranslationQuotientPhase (D₀ : MvPolynomial σ ℝ) :
    (weightedTranslationNilmanifold w d hw hwd).Space → ℂ :=
  translationQuotientPhase D₀ ∘ weightedTranslationPhaseQuotientMap w d hw hwd

@[simp] theorem weightedTranslationQuotientPhase_mk (D₀ : MvPolynomial σ ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationQuotientPhase w d hw hwd D₀ (QuotientGroup.mk g) =
      translationPhaseFunction D₀ (bchRealTranslationHom w d hwd g) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FastCoefficientRelativeKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem firstCoefficientFastSubmodule_relative :
    F.firstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.firstCoefficientFastSubmodule w hw U.toSubmodule := by
  rw [F.firstCoefficientFastSubmodule_eq_image, F.firstCoefficientFastSubmodule_eq_image]
  simp only [reducedSquareFastRelativeSubmodule, inf_assoc, inf_idem]

theorem realFirstCoefficientFastSubmodule_relative :
    F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.realFirstCoefficientFastSubmodule w hw U.toSubmodule := by
  unfold realFirstCoefficientFastSubmodule
  rw [F.firstCoefficientFastSubmodule_relative]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFastCoefficientMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

namespace NilpotentLieFiltration

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_matrix
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap =
      D.map (Rat.castHom ℝ) *
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
          (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
        S.map (Rat.castHom ℝ) := by
  have hsection : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ *
      S.map (Rat.castHom ℝ) = 1 := by
    rw [hD]
    exact real_matrix_right_inverse D S hDS
  have h := quotient_action_matrix (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (F.realFirstCoefficientAdjoint w g).toLinearMap
    (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap
    (fun x => (F.realFastCoefficientAdjoint_mk w hw U g hg x).symm)
    (S.map (Rat.castHom ℝ)) hsection
  exact h.trans (congrArg (fun P : Matrix κ (FirstCoefficientIndex w ω) ℝ =>
    P * LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
      (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
      S.map (Rat.castHom ℝ)) hD)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFastCoefficientQuotientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fast_coefficient_quotient_projection
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
    ∃ Q : Matrix (FirstCoefficientIndex w ω) (FirstCoefficientIndex w ω) ℚ,
      Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
        (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap ∧
      (∀ i j, i.val.1 ≠ j.val.1 → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) H' := by
  have hg := F.exists_fast_coefficient_generators_exp e ω hF w hw U v hspan hH hv hp hn hm hq hHp
  obtain ⟨K, hK, hKp, z, hz, hzK⟩ := hg
  have hblocks := F.firstCoefficientFastSubmodule_monomial_blocks e ω hF w hw U hU
  have he := exists_submodule_block_quotient_projection (F.firstCoefficientBasis e ω hF w)
    (fun i => i.val.1) (F.firstCoefficientFastSubmodule w hw U) z hz hblocks hK hzK
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  have hcost : (imageDefiningHeight
      (Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ)
      (Fintype.card (FirstCoefficientIndex w ω)) K : ℝ) ≤ Real.exp ((p + 2) ^ 420) := by
    have h := imageDefiningHeight_le_exp _ _ K (by positivity : 0 ≤ (p + 2) ^ 40)
      (hdm.trans (le_power_budget hp (by decide : 1 ≤ 40)))
      (hd.trans (le_power_budget hp (by decide : 1 ≤ 40))) hKp
    exact exponential_budget_comp hp (by positivity) 40 10 le_rfl h
  exact ⟨_, imageDefiningHeight_pos _ _ _ hK, hcost, Q, hQQ, hker, hblock, hQ⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℚ (F.FirstCoefficientModule w ⧸ F.firstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.firstCoefficientBasis e ω hF w) b
          (F.firstCoefficientFastSubmodule w hw U).mkQ = D ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℚ, b.equivFun.symm y =
          (F.firstCoefficientFastSubmodule w hw U).mkQ
            ((F.firstCoefficientBasis e ω hF w).equivFun.symm (S *ᵥ y)) := by
  classical
  have he := F.exists_fast_coefficient_quotient_projection e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨K, hK, hKp, Q, _, hkerQ, hQb, hQ⟩ := he
  have hr := exists_block_quotient_rows (fun i : FirstCoefficientIndex w ω => i.val.1) Q hQb hK hQ
  obtain ⟨d, hd', rows, hinj, hsurj, hker, S, hDS, hSb, hS⟩ := hr
  let D := Q.submatrix rows id
  have hkerD : LinearMap.ker D.mulVecLin = (F.firstCoefficientFastSubmodule w hw U).map
      (F.firstCoefficientBasis e ω hF w).equivFun.toLinearMap := hker.trans hkerQ
  let b := submoduleQuotientCoordinateBasis (F.firstCoefficientBasis e ω hF w)
    (F.firstCoefficientFastSubmodule w hw U) D hkerD hsurj
  have hSbudget : (rationalKernelHeight d K : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have h := rationalKernelHeight_le_budget d K (by positivity : 0 ≤ (p + 2) ^ 420)
      (((Nat.cast_le.mpr hd').trans hd).trans (le_power_budget hp (by decide : 1 ≤ 420))) hKp
    exact exponential_budget_comp hp (by positivity) 420 7 le_rfl h
  refine ⟨d, hd', rows, hinj, b, D, S,
    submoduleQuotientCoordinateBasis_matrix _ _ _ _ _, hDS,
    (fun i j h => hQb (rows i) j h), hSb, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hQ (rows i) j).1).trans hKp,
      (Nat.cast_le.mpr (hQ (rows i) j).2).trans hKp⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hSbudget,
      (Nat.cast_le.mpr (hS i j).2).trans hSbudget⟩
  · intro y
    exact submoduleQuotientCoordinateEquiv_symm _ _ _ _ _ S hDS y

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_quotient_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw U),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        ∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw U).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y)) := by
  have h := F.exists_fast_coefficient_quotient_basis e ω hF w hw U hU v hspan hH hv
    hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _⟩ := h
  refine ⟨d, hdim, rows, hinj, F.realFastCoefficientBasis w hw U b, D, S,
    ?_, hDS, hDb, hSb, hDh, hSh, ?_⟩
  · rw [F.realFastCoefficientBasis_matrix, hD]
  · exact F.realFastCoefficientBasis_symm w hw U e ω hF b D S hD hDS

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalLinearLiftReabsorption
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

theorem basisPolynomialLift_bound_of_coordinate_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k)) (x : K)
    (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * A / τ)
      (basisPolynomialLift b S x) := by
  apply (basisPolynomialLift_coefficientBound b S e T M hS x).mono e T hT
  calc
    (Fintype.card κ : ℝ) * M * ‖b.equivFun x‖ ≤
        (Fintype.card κ : ℝ) * M * (A / τ) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (Nat.cast_nonneg _) hM)
    _ = _ := by ring

theorem basisPolynomialLift_reabsorption_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M N A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k))
    (small : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : CoefficientBound e T (N / τ) small)
    (x : K) (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((N + (Fintype.card κ : ℝ) * M * A) / τ)
      (small + basisPolynomialLift b S x) := by
  have h := basisPolynomialLift_bound_of_coordinate_bound b S e T hT M A τ hM hS x hx
  have hsum := hsmall.sub e T (h.neg e T)
  rw [sub_neg_eq_add] at hsum
  convert hsum using 1
  ring

theorem basisPolynomialLift_reabsorption_grid (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m n : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : CoefficientGrid e n rational)
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (n * (m * l)) (rational + basisPolynomialLift b R x) := by
  have h := basisPolynomialLift_coefficientGrid b R e l m hR x hx
  intro α
  have hsum := realDenominatorGrid_sub_product n (m * l)
    (fun i => e.repr (coefficients rational α) i)
    (-(fun i => e.repr (coefficients (basisPolynomialLift b R x) α) i))
    (hrational α) (realDenominatorGrid_neg (m * l) (h α))
  simp only [sub_neg_eq_add] at hsum
  simp only [map_add, Finsupp.add_apply]
  exact hsum

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

end NilpotentLieBCHGroup

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

structure NativeIntegerModelFamily {σ I : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (f : I → (σ → ℤ) → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : I → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  normalized : ∀ i, model.filtration.realification.polynomialOrbitEval w 0 (test i).orbit = 1
  eval : ∀ i x, (test i).eval x = f i x

attribute [local instance] NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerModelFamily

variable {σ I : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : I → (σ → ℤ) → ℂ}

noncomputable def mono (R : NativeIntegerModelFamily w s p f) (hpq : p ≤ q) :
    NativeIntegerModelFamily w s q f :=
  { R with complexity := fun i => (R.complexity i).mono hpq }

@[simp] theorem mono_dim (R : NativeIntegerModelFamily w s p f) (hpq : p ≤ q) :
    (R.mono hpq).dim = R.dim := rfl

end NativeIntegerModelFamily

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeIntegerExpansion {σ : Type*} (w : σ → ℕ)
    (s : ℕ) (p : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Fin count → Type
  [lie : ∀ i, LieRing (L i)]
  [algebra : ∀ i, LieAlgebra ℚ (L i)]
  dim : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [topologicalAdd : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [hausdorff : ∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  model : ∀ i, RationalFilteredNilmanifold (L i) s (dim i)
  test : ∀ i, (model i).Niltest w
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).eval x

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerExpansion

variable {σ : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : (σ → ℤ) → ℂ}

noncomputable def mono (E : NativeIntegerExpansion w s p f) (hpq : p ≤ q) :
    NativeIntegerExpansion w s q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

noncomputable def conjugate (E : NativeIntegerExpansion w s p f) :
    NativeIntegerExpansion w s p (fun x => star (f x)) :=
  { E with
    test := fun i => (E.test i).conjugate
    complexity := E.complexity
    coefficient := fun i => star (E.coefficient i)
    cost := by simpa only [norm_star] using E.cost
    eval := by
      intro x
      have h := congrArg star (E.eval x)
      simpa only [star_sum, star_mul, mul_comm,
        RationalFilteredNilmanifold.Niltest.eval_conjugate] using h }

noncomputable def ofTest {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest w) (hT : T.ComplexityLE p) (hf : ∀ x, f x = T.eval x) :
    NativeIntegerExpansion w s p f := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  exact {
    count := 1
    count_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
    L := fun _ => L
    dim := fun _ => d
    model := fun _ => D
    test := fun _ => T
    complexity := fun _ => hT
    coefficient := fun _ => 1
    cost := by simpa using Real.one_le_exp hp
    eval := fun x => by simpa using hf x }

noncomputable def ofModelFamily {I : Type*} {g : I → (σ → ℤ) → ℂ}
    (R : NativeIntegerModelFamily w s p g) (i : I) :
    NativeIntegerExpansion w s p (g i) :=
  ofTest (R.test i) (R.complexity i) (fun x => (R.eval i x).symm)

end NativeIntegerExpansion

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (eta (sample u))‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))‖ := by
  have hpoint (u : X) : f u * star (eta (sample u)) =
      ∑ i, star (E.coefficient i) * (f u * star ((E.test i).eval (sample u))) := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [star_mul]
    ring
  have hmean : (𝔼 u ∈ S, f u * star (eta (sample u))) =
      ∑ i, star (E.coefficient i) * (𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, star (E.coefficient i) *
          (f u * star ((E.test i).eval (sample u))) := Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun i => star (E.coefficient i))
    (fun i => 𝔼 u ∈ S, f u * star ((E.test i).eval (sample u)))
    (Real.exp_pos (-q)) (Real.exp_pos p) (by simpa only [norm_star] using E.cost)
    (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem norm_eval_le {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (x : σ → ℤ) : ‖f x‖ ≤ Real.exp (2 * p) := by
  rw [E.eval x]
  calc
    ‖∑ i, E.coefficient i * (E.test i).eval x‖ ≤
        ∑ i, ‖E.coefficient i * (E.test i).eval x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖E.coefficient i‖ * Real.exp p := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((E.test i).eval_budget (E.complexity i) x) (norm_nonneg _)
    _ = (∑ i, ‖E.coefficient i‖) * Real.exp p := (Finset.sum_mul _ _ _).symm
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.cost (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {σ : Type*} {w : σ → ℕ} {s : ℕ} {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest w) (c : I → ℂ)
    {p : ℝ} {f : (σ → ℤ) → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).eval x) :
    NativeIntegerExpansion w s p f := by
  let e := (Fintype.equivFin I).symm
  exact {
    count := Fintype.card I
    count_bound := hcard
    L := fun i => L (e i)
    dim := fun i => d (e i)
    model := fun i => D (e i)
    test := fun i => T (e i)
    complexity := fun i => hT (e i)
    coefficient := fun i => c (e i)
    cost := (e.sum_comp (fun i => ‖c i‖)).le.trans hc
    eval := fun x => (hf x).trans (e.sum_comp
      (fun i => c i * (T i).eval x)).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {σ : Type*} {w : σ → ℕ} {s : ℕ}
    {p q : ℝ} {f : I → (σ → ℤ) → ℂ} (E : ∀ i, NativeIntegerExpansion w s p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeIntegerExpansion w s (p + q) (fun x => ∑ i, c i * f i x) := by
  classical
  let A := Σ i, Fin (E i).count
  refine ofFamily (I := A) (fun a => (E a.1).model a.2)
    (fun a => (E a.1).test a.2) (fun a => c a.1 * (E a.1).coefficient a.2) ?_
    (fun a => ((E a.1).complexity a.2).mono (by linarith)) ?_ ?_
  · change (Fintype.card (Σ i, Fin (E i).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _ : I, Real.exp p := Finset.sum_le_sum (fun i _ => by
        simpa only [Fintype.card_fin] using (E i).count_bound)
      _ = (Fintype.card I : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp q * Real.exp p := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p + q) := by rw [← Real.exp_add, add_comm]
  · exact (sum_pair_coefficient_norms_le c (fun i => (E i).coefficient)
      (Real.exp_nonneg p) hc (fun i => (E i).cost)).trans_eq
      (by rw [← Real.exp_add, add_comm])
  · intro x
    change (∑ i, c i * f i x) = ∑ a : Sigma (fun i => Fin (E i).count), _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [(E i).eval x, Finset.mul_sum]
    simp only [mul_assoc]

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def affinePullback {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (integerAffineMap A b x)) :=
  { E with
    test := fun i => (E.test i).affinePullback A b
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_affinePullback] using
        E.eval (integerAffineMap A b x) }

noncomputable def toCyclic {s : ℕ} {p : ℝ} {f : (Unit → ℤ) → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p f) (N : ℕ) [NeZero N] :
    NativeNilsequenceExpansion s N p (fun x => f (fun _ => (x.val : ℤ))) where
  count := E.count
  count_bound := E.count_bound
  L := E.L
  dim := E.dim
  model := E.model
  test := E.test
  complexity := E.complexity
  coefficient := E.coefficient
  cost := E.cost
  eval x := E.eval (fun _ => (x.val : ℤ))

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def scaleNormLeOne {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeIntegerExpansion w s p (fun x => c * f x) :=
  { E with
    coefficient := fun i => c * E.coefficient i
    cost := by
      simp only [norm_mul, ← Finset.mul_sum]
      exact (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hc).trans E.cost
    eval := by
      intro x
      rw [E.eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc _ _ _).symm }

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ τ : Type*} {w : σ → ℕ} {v : τ → ℕ} {s : ℕ} {p : ℝ}
  {f : (σ → ℤ) → ℂ}

noncomputable def substitutedValue (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) : ℂ :=
  ∑ i, E.coefficient i * ((E.test i).substitute P hP).eval x

noncomputable def substituteExpansion (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i)) :
    NativeIntegerExpansion v s p (E.substitutedValue P hP) :=
  { E with
    test := fun i => (E.test i).substitute P hP
    complexity := E.complexity
    eval := fun _ => rfl }

theorem substitutedValue_eq (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (P i) = (y i : ℚ)) :
    E.substitutedValue P hP x = f y := by
  rw [E.eval y]
  unfold substitutedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [RationalFilteredNilmanifold.Niltest.eval_substitute _ _ _ x y hxy]

end Erdos3.NativeIntegerExpansion

namespace Erdos3

noncomputable def halvingPolynomial {σ : Type*} (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem halvingPolynomial_support {σ : Type*} (r : σ → ℤ) (i : σ) :
    halvingPolynomial r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [halvingPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (1 / 2 : ℚ))
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

theorem halvingPolynomial_eval {σ : Type*} (r x : σ → ℤ)
    (hr : ∀ i, x i % 2 = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (halvingPolynomial r i) =
      ((x i / 2 : ℤ) : ℚ) := by
  have hi : x i = 2 * (x i / 2) + r i := by
    have h := hr i
    omega
  have hiq : (x i : ℚ) = 2 * ((x i / 2 : ℤ) : ℚ) + (r i : ℚ) := by exact_mod_cast hi
  simp only [halvingPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (1 / 2 : ℚ) * ((x i : ℚ) - (r i : ℚ)) = ((x i / 2 : ℤ) : ℚ)
  linarith

end Erdos3

end

section

namespace Erdos3

structure NativeIntegerVectorEquivalence {σ J K : Type*} [Fintype J] [Fintype K]
    (s : ℕ) (p : ℝ) (chi : J → (σ → ℤ) → ℂ) (eta : K → (σ → ℤ) → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
    (fun x => chi j x * star (eta k x)))

namespace NativeIntegerVectorEquivalence

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p q : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}

theorem mono (E : NativeIntegerVectorEquivalence s p chi eta) (hpq : p ≤ q) :
    NativeIntegerVectorEquivalence s q chi eta where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

theorem symm (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p eta chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem conjugate (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p (fun j x => star (chi j x))
      (fun k x => star (eta k x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem affinePullback {τ : Type*} [Fintype τ]
    (E : NativeIntegerVectorEquivalence s p chi eta) (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => chi j (integerAffineMap A b x)) (fun k x => eta k (integerAffineMap A b x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.affinePullback A b⟩

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

noncomputable def selectedExpansion (j : J) (k : K) :
    NativeIntegerExpansion (fun _ : σ => 1) s p
      (fun x => chi j x * star (eta k x)) :=
  Classical.choice (E.expansion j k)

theorem transfer_sample_correlation {X : Type*} (S : Finset X) (x : X → σ → ℤ)
    (j : J) (f : X → ℂ) {q : ℝ}
    (hunit : ∀ u ∈ S, ∑ k, ‖eta k (x u)‖ ^ 2 = 1)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (chi j (x u))‖) :
    ∃ (k : K) (a : Fin (E.selectedExpansion j k).count),
      Real.exp (-(q + 2 * p)) ≤
        ‖𝔼 u ∈ S, f u * star (eta k (x u)) *
          star (((E.selectedExpansion j k).test a).eval (x u))‖ := by
  classical
  let R (k : K) := E.selectedExpansion j k
  have hexp (k : K) (u : X) (_hu : u ∈ S) :
      star (chi j (x u)) * star (star (eta k (x u))) =
        ∑ a, star ((R k).coefficient a) * star (((R k).test a).eval (x u)) := by
    have h := congrArg star ((R k).eval (x u))
    simpa only [star_sum, star_mul, star_star, mul_comm] using h
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation S f
    (fun u => star (chi j (x u))) (fun k u => star (eta k (x u)))
    (fun k a => star ((R k).coefficient a))
    (fun k a u => star (((R k).test a).eval (x u)))
    (fun u hu => by simpa only [norm_star] using hunit u hu) hexp
    (Real.exp_pos (-q)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hcorr
  have hfrac : Real.exp (-q) / (Real.exp p * Real.exp p) =
      Real.exp (-(q + 2 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  exact ⟨k, a, hka⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def linearPullbackHom {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (fun i => A i x)) :=
  { E with
    test := fun i => (E.test i).linearPullbackHom A
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
        using E.eval (fun i => A i x) }

end NativeIntegerExpansion

namespace NativeIntegerVectorEquivalence

theorem linearPullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => A i x)) (fun k x => g k (fun i => A i x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.linearPullbackHom A⟩

theorem coordinatePullback {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (a : σ → τ) :
    NativeIntegerVectorEquivalence s p (fun j x => f j (fun i => x (a i)))
      (fun k x => g k (fun i => x (a i))) :=
  E.linearPullbackHom (fun i => ⟨⟨fun x => x (a i), rfl⟩, fun _ _ => rfl⟩)

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem selectedChoice_card_bound {σ I J : Type*} [Fintype I] [Fintype J]
    {s : ℕ} {p : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count) : ℝ) ≤ Real.exp (2 * p) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p := Finset.sum_le_sum (fun j _ => by
      simpa only [Fintype.card_fin] using (E.selectedExpansion i j).count_bound)
    _ = (Fintype.card J : ℝ) * Real.exp p := by simp
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, two_mul]

theorem selectedChainedChoice_card_bound {σ I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {s : ℕ} {p q : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    {h : K → (σ → ℤ) → ℂ} (E : NativeIntegerVectorEquivalence s p f g)
    (F : NativeIntegerVectorEquivalence s q g h) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count ×
      (Σ k : K, Fin (F.selectedExpansion j k).count)) : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p * Real.exp (2 * q) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      exact mul_le_mul (E.selectedExpansion i j).count_bound (F.selectedChoice_card_bound j)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card J : ℝ) * (Real.exp p * Real.exp (2 * q)) := by simp
    _ ≤ Real.exp p * (Real.exp p * Real.exp (2 * q)) :=
      mul_le_mul_of_nonneg_right E.right_dimension (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem affinePullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => b i + A i x))
      (fun k x => g k (fun i => b i + A i x)) := by
  classical
  have hinput (x : τ → ℤ) :
      integerAffineMap (fun i j => A i (Pi.single j 1)) b x = fun i => b i + A i x := by
    funext i
    rw [integerAffineMap, ← integerLinearForm_eq_sum]
  simpa only [hinput] using E.affinePullback (fun i j => A i (Pi.single j 1)) b

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_large_nonnegative_weighted_term {I : Type*} [Fintype I]
    (w z : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, 0 ≤ z i)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, w i ≤ M) (hmass : ρ ≤ ∑ i, w i * z i) :
    ∃ i, ρ / M ≤ z i := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ z hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    ρ ≤ ∑ j, w j * z j := hmass
    _ ≤ ∑ j, w j * z i := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hw j))
    _ = (∑ j, w j) * z i := (Finset.sum_mul _ _ _).symm
    _ ≤ M * z i := mul_le_mul_of_nonneg_right hcost (hz i)
    _ = z i * M := mul_comm _ _

theorem mean_row_weighted_sum_norm_le {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) :
    (𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) ≤ ∑ i, ‖c i‖ * (𝔼 h, ‖𝔼 x, F i h x‖) := by
  have hp (h : H) : ‖𝔼 x, ∑ i, c i * F i h x‖ ≤ ∑ i, ‖c i‖ * ‖𝔼 x, F i h x‖ := by
    simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simpa only [Finset.expect_sum_comm, ← Finset.mul_expect] using hm

theorem exists_mean_row_weighted_term {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, ‖c i‖ ≤ M) (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) :
    ∃ i, ρ / M ≤ 𝔼 h, ‖𝔼 x, F i h x‖ :=
  exists_large_nonnegative_weighted_term (fun i => ‖c i‖) (fun i => 𝔼 h, ‖𝔼 x, F i h x‖)
    (fun _ => norm_nonneg _) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hρ hM hcost (hmass.trans (mean_row_weighted_sum_norm_le c F))

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_mean_row_correlation {σ H X : Type*} [Fintype H] [Fintype X]
    {w : σ → ℕ} {s : ℕ} {p : ℝ} {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (sample : H → X → σ → ℤ) (f : H → X → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    ∃ i : Fin E.count, ρ / Real.exp p ≤
      𝔼 h, ‖𝔼 x, f h x * star ((E.test i).eval (sample h x))‖ := by
  let F (i : Fin E.count) (h : H) (x : X) := f h x * star ((E.test i).eval (sample h x))
  have heq (h : H) (x : X) : f h x * star (g (sample h x)) =
      ∑ i, star (E.coefficient i) * F i h x := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [F, star_mul]
    ring
  simp only [heq] at hmass
  exact exists_mean_row_weighted_term (fun i => star (E.coefficient i)) F hρ (Real.exp_pos _)
    (by simpa only [norm_star] using E.cost) hmass

end NativeIntegerExpansion
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_scale {H X : Type*} [Fintype H] [Fintype X]
    (f g : H → X → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (𝔼 h, ‖𝔼 x, f h x * star ((a : ℂ) * g h x)‖) =
      a * (𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) := by
  have heq (h : H) : (𝔼 x, f h x * star ((a : ℂ) * g h x)) =
      (a : ℂ) * (𝔼 x, f h x * star (g h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp only [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    ← Finset.mul_expect]

theorem exists_large_value_of_mean_row_correlation {H X : Type*}
    [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
    (f g : H → X → ℂ) (hf : ∀ h x, ‖f h x‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) :
    ∃ h x, ρ ≤ ‖g h x‖ := by
  have hb : ρ ≤ 𝔼 h, 𝔼 x, ‖g h x‖ := by
    apply hcorr.trans
    apply Finset.expect_le_expect
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf h x)
  obtain ⟨h, _, hh⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hb
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hh
  exact ⟨h, x, hx⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMeanRowCorrelation {σ H X : Type*} [Fintype H] [Fintype X]
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : H → X → σ → ℤ) (f : H → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ 𝔼 h, ‖𝔼 x, f h x * star (test.eval (sample h x))‖

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeMeanRowCorrelation

variable {σ H X : Type*} [Fintype H] [Fintype X] {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {sample : H → X → σ → ℤ} {f : H → X → ℂ}

noncomputable def mono (V : NativeMeanRowCorrelation w s p sample f) (hpq : p ≤ q) :
    NativeMeanRowCorrelation w s q sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    Nonempty (NativeMeanRowCorrelation w s (q + p) sample f) := by
  obtain ⟨i, hi⟩ := E.select_mean_row_correlation sample f (Real.exp_pos _) hcorr
  refine ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := ?_ }⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end NativeMeanRowCorrelation
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealTranslationEvaluationContinuity
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

theorem continuous_weightedSupportLE_eval {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    let := moduleTopology ℝ (weightedSupportLE (R := ℝ) w n)
    Continuous fun z : weightedSupportLE (R := ℝ) w n × (σ → ℝ) =>
      eval z.2 z.1.val := by
  classical
  let W := weightedSupportLE (R := ℝ) w n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let b := Module.finBasis ℝ W
  have hb : Continuous fun z : W × (σ → ℝ) =>
      ∑ i, b.repr z.1 i * eval z.2 (b i).val := by
    apply continuous_finsetSum
    intro i _
    exact ((IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
      ((MvPolynomial.continuous_eval (b i).val).comp continuous_snd)
  convert hb using 1
  ext z
  have h := congrArg (fun Q : W => eval z.2 Q.val) (b.sum_repr z.1)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval,
    smul_eq_mul] using h.symm

theorem continuous_polynomialShearExp_eval {σ X : Type*} [Fintype σ]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (D : X →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ) (P : MvPolynomial σ ℝ) :
    Continuous fun z : X × (σ → ℝ) => eval z.2 (polynomialShearExp (D z.1) P) := by
  classical
  let n := P.weightedTotalDegree w
  let W := weightedSupportLE (R := ℝ) w n
  let instFiniteW : Module.Finite ℝ W := weightedSupportLE_moduleFinite w hw n
  let instTopoW : TopologicalSpace W := moduleTopology ℝ W
  let instTopAddW : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℝ W
  let p : W := ⟨P, (mem_weightedSupportLE_iff w n P).mpr le_rfl⟩
  let L : X →ₗ[ℝ] Module.End ℝ W :=
    { toFun := fun x => polynomialShearEnd (D x) n
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (x + y)).val Q.val = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro Q
        apply Subtype.ext
        change (D (c • x)).val Q.val = _
        rw [map_smul]
        rfl }
  let instModuleTopoX : IsModuleTopology ℝ X := isModuleTopologyOfFiniteDimensional
  have hL : Continuous (fun z : X × W => L z.1 z.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left L
  have hpower (k : ℕ) : Continuous fun x : X => (L x ^ k) p := by
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply] using
        (continuous_const : Continuous fun _ : X => p)
    | succ k ih =>
      simpa only [pow_succ', Module.End.mul_apply, Function.comp_def, id_eq] using
        hL.comp (continuous_id.prodMk ih)
  have hexp : Continuous fun x : X =>
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) • (L x ^ k) p := by
    apply continuous_finsetSum
    intro k _
    exact (hpower k).const_smul ((k.factorial : ℝ)⁻¹)
  have heval := (continuous_weightedSupportLE_eval w hw n).comp
    ((hexp.comp continuous_fst).prodMk continuous_snd)
  convert heval using 1
  ext z
  rw [polynomialShearExp_eq_sum (D z.1) p.property]
  simp only [Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ((L z.1 ^ k) p : MvPolynomial σ ℝ) =
    ((D z.1).val.toLinearMap ^ k) P from polynomialShearEnd_pow_coe _ _ _ _]
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [smul_eval, Rat.cast_inv, Rat.cast_natCast]
  rfl

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_polynomial_eval (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (a : σ → ℝ) :
    eval a (bchRealTranslationHom w d hwd g).polynomial =
      -eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
        (polynomialShearExp (-realShearEmbedding w d g.coord) (X (Sum.inr ()))) := by
  have h := PolynomialTranslationGroupOver.action_inverse_X_inr_eval
    (bchRealTranslationHom w d hwd g) a 0
  have hi : (PolynomialTranslationGroupOver.actionMonoidHom
      (bchRealTranslationHom w d hwd g)).symm =
      PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) := by
    rw [map_inv]
    exact (map_inv PolynomialTranslationGroupOver.actionMonoidHom _).symm
  rw [hi, bchRealTranslationHom_action] at h
  change eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
    (polynomialShearExp (realShearEmbedding w d (-g.coord)) (X (Sum.inr ()))) =
    0 - eval a (bchRealTranslationHom w d hwd g).polynomial at h
  rw [map_neg] at h
  linarith

theorem continuous_bchRealTranslationHom_polynomial_eval
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      eval z.2 (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (-(realShearEmbedding w d).toLinearMap) (X (Sum.inr ()))
  have he : Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      (z.1, Sum.elim z.2 (fun _ : Unit => (0 : ℝ))) := by
    apply continuous_fst.prodMk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_snd
    | inr _ => exact continuous_const
  convert (hc.comp he).neg using 1
  ext z
  exact bchRealTranslationHom_polynomial_eval w d hwd ⟨z.1⟩ z.2

theorem continuous_bchRealTranslationHom_base
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun x : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (bchRealTranslationHom w d hwd ⟨x⟩).base := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  apply continuous_pi
  intro i
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (realShearEmbedding w d).toLinearMap (X (Sum.inl i))
  have he := hc.comp (continuous_id.prodMk
    (continuous_const : Continuous fun _ : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (0 : σ ⊕ Unit → ℝ)))
  convert he using 1
  ext x
  have ha := bchRealTranslationHom_action w d hwd ⟨x⟩
  have hx := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℝ ≃ₐ[ℝ]
    MvPolynomial (σ ⊕ Unit) ℝ => eval 0 (f (X (Sum.inl i)))) ha
  change eval 0 (PolynomialTranslationGroupOver.actionHom
    (bchRealTranslationHom w d hwd ⟨x⟩) (X (Sum.inl i))) =
    eval 0 (polynomialShearExp (realShearEmbedding w d x) (X (Sum.inl i))) at hx
  simpa only [PolynomialTranslationGroupOver.actionHom_X_inl, map_add, eval_X,
    Pi.zero_apply, eval_C, zero_add, Function.comp_apply, id_eq, LieHom.coe_toLinearMap] using hx

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedProjectedComparison
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem quotientTopBasis_structure_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : QuotientTopBasisIndex s ω) :
    RationalHeightLE (lieStructureConstants (F.quotientTopBasis e ω hF) a b k) H := by
  have hspan : (F.layerIdeal (s + 1)).toSubmodule =
      Submodule.span ℚ (e '' {i | s + 1 ≤ ω i}) := hF (s + 1)
  have he : lieStructureConstants (F.quotientTopBasis e ω hF) a b k =
      lieStructureConstants e a.val b.val k.val :=
    supportedQuotientBasis_lieStructure e (F.layerIdeal (s + 1))
      {i | s + 1 ≤ ω i} hspan a b k
  rw [he]
  exact hc a.val b.val k.val

theorem reducedSquareSndSymbolMap_span (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareSndSymbolMap w (v i))) =
      (U.map (F.reducedSquareSndSymbolMap w)).toSubmodule := by
  change _ = U.toSubmodule.map (F.reducedSquareSndSymbolMap w).toLinearMap
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem reducedSquareSndSymbolMap_spanning_height (w : σ → ℕ)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w) {H : ℕ}
    (hv : ∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H)
    (i : κ) (z : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (v i)) z) H := by
  rw [F.reducedSquareSndSymbolMap_repr e ω hF]
  exact hv i _

theorem reducedSquareRealSymbolHom_fast (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra U) :
    (F.reducedSquareRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) := by
  rw [realificationLieSubalgebra_map]
  exact ⟨g.coord, hg, rfl⟩

theorem exists_reduced_projected_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
        (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
          P.coord ∈ realificationLieSubalgebra U →
          B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) E →
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) A →
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
          (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) ∧
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w m
            (F.reducedSquareRealSymbolHom w R * D⁻¹) := by
  have hcomparisonExists := exists_bounded_symbol_comparison s a
  obtain ⟨C, hC, hcomparison⟩ := hcomparisonExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  have hdim : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hdata := hcomparison F.quotientTop (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w hw
    (U.map (F.reducedSquareSndSymbolMap w)) (fun i => F.reducedSquareSndSymbolMap w (v i))
    (F.reducedSquareSndSymbolMap_span w U v hspan) H l p hH hl hp hdim hσ hκ hHp hlp
    (F.quotientTopBasis_structure_height e ω hF hc)
    (F.reducedSquareSndSymbolMap_spanning_height e ω hF w v hv)
  obtain ⟨m, hm, hmp, hlm, hcompare⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hA hR hD
  exact hcompare T hT A B D (F.reducedSquareRealSymbolHom w E)
    (F.reducedSquareRealSymbolHom w P) (F.reducedSquareRealSymbolHom w R)
    hB (F.reducedSquareRealSymbolHom_fast w U P hP)
    (by simpa only [map_mul] using heq) hA (F.reducedSquareRealSymbolHom_slow e ω hF w T _ E hE)
    hD (F.reducedSquareRealSymbolHom_grid e ω hF w l R hR)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_substitution {I J : Type*}
    (T : J → ℝ) (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes T (eval₂Hom C f p) =
      eval₂Hom C (fun i => scaleMvPolynomialAxes T (f i)) p := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  simp only [coe_eval₂Hom, ← eval_assoc, Function.comp_def, scaleMvPolynomialAxes_eval]

theorem scaled_substitution_coeff_bound {I J : Type*}
    (T : J → ℝ) (hT : ∀ j, 0 < T j)
    (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ)
    {A B : ℝ} {s : ℕ} (hB : 1 ≤ B)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B)
    (hp : ∀ α, |p.coeff α| ≤ A) (hdegree : p.totalDegree ≤ s)
    (α : J →₀ ℕ) :
    |(eval₂Hom C f p).coeff α| ≤
      ((p.support.card : ℝ) * A * B ^ s) / monomialScale T α := by
  have hmass : realPolynomialMass p ≤ p.support.card * A := by
    unfold realPolynomialMass
    exact (Finset.sum_le_sum (fun β _ => hp β)).trans_eq (by simp)
  have hsub : realPolynomialMass (scaleMvPolynomialAxes T (eval₂Hom C f p)) ≤
      p.support.card * A * B ^ s := by
    rw [scaleMvPolynomialAxes_substitution]
    exact (realPolynomialMass_substitution_le p _ hB hf hdegree).trans
      (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by linarith) _))
  have h := (realPolynomialMass_coeff_le
    (scaleMvPolynomialAxes T (eval₂Hom C f p)) α).trans hsub
  rw [scaleMvPolynomialAxes_coeff, abs_mul,
    abs_of_pos (monomialScale_pos T hT α)] at h
  exact (le_div_iff₀ (monomialScale_pos T hT α)).mpr h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module

variable {σ τ ι V : Type*}

theorem coordinate_realChartSubstitute
    [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (l : V →ₗ[ℝ] ℝ) (f : σ → MvPolynomial τ ℝ) (P : VectorPolynomial σ ℚ V) :
    coordinate l.toAddMonoidHom (Erdos3.VectorPolynomial.realChartSubstitute f P) =
      MvPolynomial.eval₂Hom MvPolynomial.C f (coordinate l.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro x
  rw [← coordinate_eval₂ l x, eval₂_realChartSubstitute, coordinate_eval₂]
  simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_assoc, Function.comp_def]

theorem CoefficientBound.realChartSubstitute [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s := (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationCoordinateBudget
namespace OAI

section

namespace Erdos3

theorem detectedTranslationCoordinate_denominator_le_exp (n k m q : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p)
    (hq : q ≤ ⌈Real.exp p⌉₊ ^ (n * k) * m) :
    (q : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hnk : (n : ℝ) * k ≤ p * p :=
    mul_le_mul hn hk (Nat.cast_nonneg _) hp
  have hnk' := mul_le_mul_of_nonneg_right hnk (show 0 ≤ p + 1 by positivity)
  have hlog : ((n * k : ℕ) : ℝ) * (p + 1) + p ≤ (p + 3) ^ 3 := by
    rw [Nat.cast_mul]
    nlinarith [sq_nonneg p]
  calc
    (q : ℝ) ≤ ((⌈Real.exp p⌉₊ ^ (n * k) * m : ℕ) : ℝ) := Nat.cast_le.mpr hq
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * (p + 1)) * Real.exp p := by
      rw [Nat.cast_mul]
      exact mul_le_mul (ceil_exp_power_le_exp hp (n * k)) hm
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * (p + 1) + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem detectedTranslationCoordinate_slow_factor_le_exp (k : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) :
    (k : ℝ) * (⌈Real.exp p⌉₊ : ℝ) * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hkexp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p, pow_nonneg hp 3])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MajorTranslationBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {U B : Type*} [Fintype B]

theorem bchRealTranslationHom_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) (i : B) :
    (bchRealTranslationHom w d hwd g).base i =
      ((weightedBasis w d hw).baseChange ℝ).repr g.coord (Sum.inl i) := by
  obtain ⟨b, P, hb, _⟩ := realShearEmbedding_shape w d g.coord
  have hact := congrArg (fun f : MvPolynomial (B ⊕ Unit) ℝ ≃ₐ[ℝ]
      MvPolynomial (B ⊕ Unit) ℝ => f (X (Sum.inl i)))
    (bchRealTranslationHom_action w d hwd g)
  change PolynomialTranslationGroupOver.actionHom (bchRealTranslationHom w d hwd g)
    (X (Sum.inl i)) = polynomialShearExp (realShearEmbedding w d g.coord)
      (X (Sum.inl i)) at hact
  rw [PolynomialTranslationGroupOver.actionHom_X_inl,
    polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)] at hact
  have hbase : (bchRealTranslationHom w d hwd g).base i = b i := by
    simpa using congrArg (fun polynomial : MvPolynomial (B ⊕ Unit) ℝ => polynomial.coeff 0) hact
  have hcoord := realShearEmbedding_base_coeff w d hw g.coord i
  rw [hb i] at hcoord
  exact hbase.trans (by simpa using hcoord)

theorem majorTranslationPolynomialOrbit_base_coordinate
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i) (i : B) :
    VectorPolynomial.coordinate
      (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (majorTranslationPolynomialOrbit w d hw hwd D hD A hA).log = A i := by
  apply MvPolynomial.funext
  intro u
  rw [← VectorPolynomial.coordinate_eval₂]
  change ((weightedBasis w d hw).baseChange ℝ).repr
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (majorTranslationPolynomialOrbit w d hw hwd D hD A hA)).coord
        (Sum.inl i) = eval u (A i)
  rw [← bchRealTranslationHom_base_coordinate w d hw hwd,
    majorTranslationPolynomialOrbit_realEval]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeEquivalenceCoordinateMaps
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_coordinate_maps {σ I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    {s : ℕ} {p r : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g)
    (f' : K → (σ → ℤ) → ℂ) (g' : L → (σ → ℤ) → ℂ)
    (a : K → I) (b : L → J)
    (hf : ∀ k x, f' k x = f (a k) x) (hg : ∀ l x, g' l x = g (b l) x)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp r) (hL : (Fintype.card L : ℝ) ≤ Real.exp r)
    (hpr : p ≤ r) : NativeIntegerVectorEquivalence s r f' g' := by
  refine ⟨hK, hL, fun k l => ?_⟩
  obtain ⟨R⟩ := E.expansion (a k) (b l)
  have heq : (fun x => f (a k) x * star (g (b l) x)) =
      (fun x => f' k x * star (g' l x)) := by
    funext x
    rw [hf, hg]
  exact ⟨heq ▸ R.mono hpr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]
  [Algebra ℚ R] [Algebra ℚ S] {w : σ ⊕ Unit → ℕ}

noncomputable def translationShearCoordinates
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver R σ :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose

theorem translationShearCoordinates_action
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom (translationShearCoordinates D b P hb hP) =
      (polynomialShearExpAut D).val :=
  (existsUnique_translation_of_shear_exp D b P hb hP).exists.choose_spec

theorem translationShearCoordinates_map_action
    (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    PolynomialTranslationGroupOver.actionMonoidHom
        (PolynomialTranslationGroupOver.map f (translationShearCoordinates D b P hb hP)) =
      (polynomialShearExpAut (polynomialShearMap f D)).val := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have he := congrArg
    (fun a : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R => a (X i))
    (translationShearCoordinates_action D b P hb hP)
  change PolynomialTranslationGroupOver.actionHom _ (X i) = polynomialShearExp D (X i) at he
  have hm := PolynomialTranslationGroupOver.map_actionHom f
    (translationShearCoordinates D b P hb hP) (X i)
  rw [he, polynomialShearExp_map, map_X] at hm
  exact hm.symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem PolynomialTranslationGroupOver.action_inverse_X_inr
    (g : PolynomialTranslationGroupOver R σ) :
    (actionMonoidHom g).symm (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ :=
    (map_inv actionMonoidHom g).symm
  rw [he]
  change actionHom g⁻¹ (X (Sum.inr ())) = _
  rw [actionHom_X_inr]
  simp only [base_inv, polynomial_inv, map_neg, polynomialTranslate_comp_ring,
    neg_add_cancel, polynomialTranslate_zero_ring, sub_eq_add_neg]

theorem polynomialShearExpAut_neg_over {ι : Type*}
    (w : ι → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (-D) = (polynomialShearExpAut D)⁻¹ := by
  exact (polynomialShearBCHEquivOver w d hw).map_inv
    (⟨D⟩ : (polynomialShearRatFiltration (R := R) w d hw).Group)

theorem translationShearCoordinates_inverse_exp
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    polynomialShearExp (-D) (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl (translationShearCoordinates D b P hb hP).polynomial := by
  rw [← polynomialShearExpAut_apply, polynomialShearExpAut_neg_over w d hw]
  have he := translationShearCoordinates_action D b P hb hP
  change ((polynomialShearExpAut D).val).symm (X (Sum.inr ())) = _
  rw [← he]
  exact PolynomialTranslationGroupOver.action_inverse_X_inr _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def translationBaseDerivative (b : σ → R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (fun i => C (b i))

@[simp] theorem translationBaseDerivative_C (b : σ → R) (r : R) :
    translationBaseDerivative b (C r) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem translationBaseDerivative_X (b : σ → R) (i : σ) :
    translationBaseDerivative b (X i) = C (b i) := mkDerivation_X _ _ _

theorem translationBaseDerivative_apply [Fintype σ] (b : σ → R)
    (P : MvPolynomial σ R) :
    translationBaseDerivative b P = ∑ i, b i • pderiv i P := by
  classical
  have h : translationBaseDerivative b = ∑ i, b i • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [translationBaseDerivative_X]
    change _ = (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) (X j)
    rw [map_sum]
    simp [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.C_eq_smul_one]
  rw [h]
  change (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) P = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

theorem translationShear_derivation_rename_eq {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    D.val (rename Sum.inl P) = rename Sum.inl (translationBaseDerivative b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
      hb, translationBaseDerivative_X, map_add, rename_C, hP]

theorem translationShear_derivation_pow_extra {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) (k : ℕ) :
    (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) =
      rename Sum.inl (((translationBaseDerivative b).toLinearMap ^ k) P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact translationShear_derivation_rename_eq D b hb _

variable [Algebra ℚ R]

theorem polynomialShear_neg_pow_apply {ι : Type*} {w : ι → ℕ}
    (D : PolynomialShearLieAlgebra w R) (k : ℕ) (Q : MvPolynomial ι R) :
    ((-D).val.toLinearMap ^ k) Q =
      (-1 : ℚ) ^ k • (D.val.toLinearMap ^ k) Q := by
  have h : (-D).val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap := by
    change -D.val.toLinearMap = (-1 : ℚ) • D.val.toLinearMap
    exact (neg_one_smul ℚ D.val.toLinearMap).symm
  rw [h, smul_pow, LinearMap.smul_apply]

theorem translationShearCoordinates_polynomial_series
    (w : σ ⊕ Unit → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d)
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    (translationShearCoordinates D b P hb hP).polynomial =
      ∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P := by
  have he := translationShearCoordinates_inverse_exp w d hw D b P hb hP
  rw [polynomialShearExp_eq_sum (-D) (weightedSupportLE_X w (Sum.inr ())),
    Finset.sum_range_succ'] at he
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul] at he
  have hs : (∑ k ∈ Finset.range (w (Sum.inr ())),
      (((k + 1).factorial : ℚ)⁻¹) •
        ((-D).val.toLinearMap ^ (k + 1)) (X (Sum.inr ()))) =
      -rename Sum.inl (∑ k ∈ Finset.range (w (Sum.inr ())),
        ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)) •
          ((translationBaseDerivative b).toLinearMap ^ k) P) := by
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [polynomialShear_neg_pow_apply, translationShear_derivation_pow_extra D b P hb hP]
    rw [AlgHom.map_smul_of_tower, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  rw [hs] at he
  apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
  apply neg_injective
  apply add_left_cancel (a := X (Sum.inr ()))
  simpa only [sub_eq_add_neg] using he.symm.trans (add_comm _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationLogCoordinatePolynomials
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem shear_sum_apply {S I : Type*} [CommRing S] {w : I → ℕ}
    (D : κ → PolynomialShearLieAlgebra w S) (P : MvPolynomial I S) :
    (∑ k, D k).val P = ∑ k, (D k).val P := by
  classical
  have h (t : Finset κ) : (∑ k ∈ t, D k).val P = ∑ k ∈ t, (D k).val P := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert k t hk ih =>
      simp only [Finset.sum_insert hk]
      change (D k).val P + (∑ k ∈ t, D k).val P = _
      rw [ih]
  exact h Finset.univ

noncomputable def translationLogPolynomialShear (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialShearLieAlgebra (shearWeight w d) (MvPolynomial U ℝ) :=
  ∑ k, f k • polynomialShearMap (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))

noncomputable def translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    MvPolynomial U ℝ := ∑ k, f k * C ((x k).val.base i : ℝ)

noncomputable def translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial B (MvPolynomial U ℝ) :=
  ∑ k, C (f k) * MvPolynomial.map (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (x k).val.polynomial

theorem translationLogPolynomialShear_base (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inl i)) =
      C (translationLogBasePolynomial w d x f i) := by
  classical
  simp only [translationLogPolynomialShear, translationLogBasePolynomial,
    shear_sum_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inl i)) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inl i))) = _
  rw [shearDerivation_X_inl, map_C]
  rw [← MvPolynomial.C_mul']
  rfl

theorem translationLogPolynomialShear_phase (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inr ())) =
      rename Sum.inl (translationLogPhasePolynomial w d x f) := by
  classical
  simp only [translationLogPolynomialShear, translationLogPhasePolynomial,
    shear_sum_apply, map_sum, map_mul, rename_C]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inr ())) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inr ()))) = _
  rw [shearDerivation_X_inr, MvPolynomial.map_rename]
  exact MvPolynomial.C_mul'.symm

theorem translationLogPolynomialShear_specialize (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    polynomialShearMap (MvPolynomial.eval u) (translationLogPolynomialShear w d x f) =
      realShearEmbedding w d (∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k) := by
  classical
  have hc : (MvPolynomial.eval u).comp (C.comp (algebraMap ℚ ℝ)) = algebraMap ℚ ℝ := by
    ext r
    simp
  simp only [translationLogPolynomialShear, polynomialShearMap_sum, polynomialShearMap_smul,
    polynomialShearMap_comp, hc, map_sum, realShearEmbedding_tmul]

noncomputable def translationLogGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationShearCoordinates (translationLogPolynomialShear w d x f)
    (translationLogBasePolynomial w d x f) (translationLogPhasePolynomial w d x f)
    (translationLogPolynomialShear_base w d x f) (translationLogPolynomialShear_phase w d x f)

theorem translationLogGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (MvPolynomial.eval u) (translationLogGroupPolynomial w d x f) =
      bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [translationLogGroupPolynomial, translationShearCoordinates_map_action,
    bchRealTranslationHom_action, weightedShearRealGroupHom_apply]
  rw [translationLogPolynomialShear_specialize]
  rfl

noncomputable def translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial (translationLogGroupPolynomial w d x f).polynomial

theorem translationLogMixedGroupPolynomial_eval (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (translationLogMixedGroupPolynomial w d x f) =
      eval a (bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩).polynomial := by
  rw [translationLogMixedGroupPolynomial, packTranslationPolynomial_eval]
  congr 1
  exact congrArg PolynomialTranslationGroupOver.polynomial
    (translationLogGroupPolynomial_specialize w d hwd x f u)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateInputBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem packTranslationPolynomial_map_C {U B R : Type*} [CommSemiring R]
    (P : MvPolynomial B R) :
    packTranslationPolynomial (U := U) (MvPolynomial.map C P) = rename Sum.inr P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, map_X, packTranslationPolynomial_X, rename_X, hP]

namespace PolynomialTranslationLie

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    packTranslationPolynomial (translationLogPhasePolynomial w d x f) =
      ∑ k, rename Sum.inl (f k) *
        rename Sum.inr (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) := by
  classical
  unfold translationLogPhasePolynomial
  simp only [map_sum, map_mul, packTranslationPolynomial_C]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← MvPolynomial.map_map, packTranslationPolynomial_map_C]

theorem realPolynomialMass_translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀) (i : B) :
    realPolynomialMass (translationLogBasePolynomial w d x f i) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  unfold translationLogBasePolynomial
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      apply (realPolynomialMass_mul_le _ _).trans
      rw [realPolynomialMass_C]
      exact mul_le_mul (hf k) (hx k i) (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem realPolynomialMass_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hf k))
          ((realPolynomialMass_rename_le _ _).trans (hx k)) (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem weightedSubalgebra_realPolynomial_degreeOf_le (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : B) :
    (MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial).degreeOf i ≤ d := by
  classical
  rw [degreeOf_eq_sup]
  apply Finset.sup_le
  intro α hα
  have hs := MvPolynomial.support_map_subset (algebraMap ℚ ℝ) x.val.polynomial hα
  have hx := x.property.2 hs
  change Finsupp.weight w α + 1 ≤ d at hx
  have hαi := Finsupp.le_weight w (hw i).ne' α
  exact hαi.trans (by omega)

theorem degreeOf_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (i : B) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d x f)).degreeOf
      (Sum.inr i) ≤ d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add,
    degreeOf_rename_of_injective Sum.inr_injective i]
  exact weightedSubalgebra_realPolynomial_degreeOf_le w d hw (x k) i

theorem realPolynomialMass_translationLogDirectionalSeries (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  exact realPolynomialMass_translationDirectionalSeries d _ _
    (degreeOf_pack_translationLogPhasePolynomial w d hw x f) (by positivity)
    (realPolynomialMass_translationLogBasePolynomial w d x f hM hf hbase)
    (realPolynomialMass_pack_translationLogPhasePolynomial w d x f hM hf hphase)

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationLogCoordinateWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*}

namespace PolynomialTranslationLie

variable [Fintype B] (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]

theorem translationLogBasePolynomial_weightedBasis
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ) (i : B) :
    translationLogBasePolynomial w d (weightedBasis w d hw) f i = f (Sum.inl i) := by
  classical
  unfold translationLogBasePolynomial
  rw [Finset.sum_eq_single (Sum.inl i)]
  · simp
  · intro k _ hki
    cases k with
    | inl j =>
      have hji : j ≠ i := fun h => hki (congrArg Sum.inl h)
      simp [Ne.symm hji]
    | inr α => simp
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateHomogeneous
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

theorem translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) (i : B) :
    (translationLogBasePolynomial w d (weightedBasis w d hw) f i).IsWeightedHomogeneous
      v (w i) := by
  rw [translationLogBasePolynomial_weightedBasis]
  exact hf (Sum.inl i)

theorem pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d (weightedBasis w d hw) f)).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro k _
  cases k with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero, mul_zero]
    exact isWeightedHomogeneous_zero ℝ _ _
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    have hleft : (rename Sum.inl (f (Sum.inr a))).IsWeightedHomogeneous (Sum.elim v w)
        (d - Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous v (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl i)) (hf (Sum.inr a))
    have hright : (rename Sum.inr (monomial a.val (1 : ℝ))).IsWeightedHomogeneous
        (Sum.elim v w) (Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous w (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inr i))
        (isWeightedHomogeneous_monomial w a.val 1 rfl)
    simpa only [mem_weightedHomogeneousSubmodule, Nat.sub_add_cancel a.property.le]
      using hleft.mul hright

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialPackingDerivative
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*}

theorem pderiv_inr_rename_inl (i : B) (P : MvPolynomial U ℝ) :
    pderiv (Sum.inr i) (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem packTranslationPolynomial_pderiv (Q : MvPolynomial B (MvPolynomial U ℝ)) (i : B) :
    packTranslationPolynomial (pderiv i Q) =
      pderiv (Sum.inr i) (packTranslationPolynomial Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C P => simp [pderiv_inr_rename_inl]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      packTranslationPolynomial_X, hP, pderiv_X, Pi.single_apply]
    by_cases h : j = i <;> simp [h]

theorem packTranslationPolynomial_directional_sum [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (∑ i, b i • pderiv i Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  classical
  rw [translationDirectionalDerivative_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPolynomial.C_mul', map_mul, packTranslationPolynomial_C,
    packTranslationPolynomial_pderiv]

theorem packTranslationPolynomial_baseDerivative [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (translationBaseDerivative b Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  rw [translationBaseDerivative_apply, packTranslationPolynomial_directional_sum]

theorem packTranslationPolynomial_baseDerivative_pow [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) (k : ℕ) :
    packTranslationPolynomial (((translationBaseDerivative b).toLinearMap ^ k) Q) =
      ((translationDirectionalDerivative b) ^ k) (packTranslationPolynomial Q) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change packTranslationPolynomial (translationBaseDerivative b
      (((translationBaseDerivative b).toLinearMap ^ k) Q)) = _
    rw [packTranslationPolynomial_baseDerivative, ih]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.TranslationLogCoordinateInputGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ U B : Type*}

theorem realPolynomialCoefficientGrid_zero (q : ℕ) :
    realPolynomialCoefficientGrid q (0 : MvPolynomial σ ℝ) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simp

theorem realPolynomialCoefficientGrid_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) {q : ℕ}
    (hP : ∀ i ∈ s, realPolynomialCoefficientGrid q (P i)) :
    realPolynomialCoefficientGrid q (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realPolynomialCoefficientGrid_zero q
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact realPolynomialCoefficientGrid_add (hP i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem realPolynomialCoefficientGrid_mul {q r : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid r Q) :
    realPolynomialCoefficientGrid (q * r) (P * Q) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
    ((realPolynomialCoefficientGrid_iff _ _).mp hQ)
  simpa only [Nat.cast_mul, map_mul, mul_mul_mul_comm] using h

theorem realPolynomialCoefficientGrid_pderiv (i : σ) {q : ℕ}
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (pderiv i P) := by
  obtain ⟨I, hI⟩ := (realPolynomialCoefficientGrid_iff _ _).mp hP
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨pderiv i I, ?_⟩
  rw [← pderiv_map, hI, pderiv_C_mul]

theorem realPolynomialCoefficientGrid_rat_smul (z : ℤ) {t r : ℕ} (ht : 0 < t)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (t * r) (((z : ℝ) / (t : ℝ)) • P) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    (C_int_mem_integralRealPolynomialSubring z)
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
  have heq : C ((t * r : ℕ) : ℝ) * (((z : ℝ) / (t : ℝ)) • P) =
      C (z : ℝ) * (C (r : ℝ) * P) := by
    rw [← C_mul', ← mul_assoc, ← map_mul]
    have hs : ((t * r : ℕ) : ℝ) * ((z : ℝ) / (t : ℝ)) = (z : ℝ) * (r : ℝ) := by
      push_cast
      field_simp
    rw [hs, map_mul, mul_assoc]
  rw [heq]
  exact h

variable [Fintype B]

theorem translationDirectionalDerivative_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q r : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (q * r) (translationDirectionalDerivative b P) := by
  rw [translationDirectionalDerivative_apply]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun i _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hb i))
      (realPolynomialCoefficientGrid_pderiv (Sum.inr i) hP)

theorem translationDirectionalDerivative_pow_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) (i : ℕ) :
    realPolynomialCoefficientGrid (q ^ (i + 1)) (((translationDirectionalDerivative b) ^ i) P) := by
  induction i with
  | zero => simpa using hP
  | succ i ih =>
      simpa only [pow_succ', Module.End.mul_apply] using
        translationDirectionalDerivative_coefficientGrid b _ hb ih

theorem translationDirectionalSeries_coefficientGrid (d : ℕ)
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (translationDirectionalSeries d b P) := by
  unfold translationDirectionalSeries
  apply realPolynomialCoefficientGrid_sum
  intro i hi
  have hid : i + 1 ≤ d := Finset.mem_range.mp hi
  have hterm := realPolynomialCoefficientGrid_rat_smul ((-1 : ℤ) ^ i)
    (Nat.factorial_pos (i + 1))
    (translationDirectionalDerivative_pow_coefficientGrid b P hb hP i)
  have hdiv : (i + 1).factorial * q ^ (i + 1) ∣ d.factorial * q ^ (d + 1) :=
    Nat.mul_dvd_mul (Nat.factorial_dvd_factorial hid) (pow_dvd_pow q (by omega))
  apply realPolynomialCoefficientGrid_mono hdiv
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hterm

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem constant_coefficientGrid {l : ℕ} {a : ℝ}
    (ha : ∃ z : ℤ, (z : ℝ) = (l : ℝ) * a) :
    realPolynomialCoefficientGrid l (C a : MvPolynomial U ℝ) := by
  obtain ⟨z, hz⟩ := ha
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  rw [← map_mul, ← hz]
  exact C_int_mem_integralRealPolynomialSubring z

theorem translationLogBasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (i : B) :
    realPolynomialCoefficientGrid (q * l) (translationLogBasePolynomial w d x f i) := by
  unfold translationLogBasePolynomial
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (hf k) (constant_coefficientGrid (hbase k i))

theorem pack_translationLogPhasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (q * l)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  rw [pack_translationLogPhasePolynomial]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hf k))
      (realPolynomialCoefficientGrid_rename Sum.inr (hphase k))

theorem translationLogDirectionalSeries_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) :=
  translationDirectionalSeries_coefficientGrid d _ _
    (translationLogBasePolynomial_coefficientGrid w d x f hf hbase)
    (pack_translationLogPhasePolynomial_coefficientGrid w d x f hf hphase)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateScaling
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogMixedGroupPolynomial_eq_series (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) :
    translationLogMixedGroupPolynomial w d x f =
      translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  have hweights : ∀ i, shearWeight w d i ≤ d := by
    intro i
    cases i with
    | inl i => exact hwd i
    | inr i => exact le_rfl
  unfold translationLogMixedGroupPolynomial translationLogGroupPolynomial
  rw [translationShearCoordinates_polynomial_series (shearWeight w d) d hweights]
  simp only [shearWeight, translationDirectionalSeries, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_rat_smul, packTranslationPolynomial_baseDerivative_pow]
  rw [← algebraMap_smul ℝ ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ))]
  congr 1
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]

theorem realPolynomialMass_translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationLogMixedGroupPolynomial w d x f) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact realPolynomialMass_translationLogDirectionalSeries w d hw x f hM hB₀ hf hbase hphase

theorem translationLogMixedGroupPolynomial_coefficientGrid_of_inputs
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationLogMixedGroupPolynomial w d x f) := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact translationLogDirectionalSeries_coefficientGrid w d x f hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogMixedGroupPolynomial_scale (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f) =
    translationLogMixedGroupPolynomial w d x (fun k => scaleMvPolynomialAxes H (f k)) := by
  apply MvPolynomial.funext
  intro z
  let u : U → ℝ := fun i => z (Sum.inl i)
  let a : B → ℝ := fun i => z (Sum.inr i)
  have hz : z = Sum.elim u a := by funext i; cases i <;> rfl
  rw [hz, scaleMvPolynomialAxes_eval]
  have he : (fun i => Sum.elim H (fun _ : B => (1 : ℝ)) i * Sum.elim u a i) =
      Sum.elim (fun i => H i * u i) a := by
    funext i
    cases i <;> simp
  rw [he, translationLogMixedGroupPolynomial_eval w d hwd,
    translationLogMixedGroupPolynomial_eval w d hwd]
  simp only [scaleMvPolynomialAxes_eval]

theorem realPolynomialMass_translationLogMixedGroupPolynomial_scale
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    (H : U → ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H (f k)) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f)) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_scale w d hwd]
  exact realPolynomialMass_translationLogMixedGroupPolynomial w d hw hwd x _
    hM hB₀ hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MajorTranslationIntegerEvaluation
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {U B : Type*} [Fintype B]

theorem majorTranslationPolynomialOrbit_integerEval
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (x : U → ℤ) :
    bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitEval
        (fun _ : U => 1) x (majorTranslationPolynomialOrbit w d hw hwd F hF A hA)) =
      algebraicMajorSymbol F (specializeMajorParameters (RingHom.id ℝ) F 0) A
        (fun i => (x i : ℝ)) := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact majorTranslationPolynomialOrbit_realEval w d hw hwd F hF A hA _

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationCentralLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def centralRationalElement (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (q : ℚ) : weightedSubalgebra w d :=
  ⟨⟨0, C q⟩, ⟨by simp, (monomial_mem_restrictSupport ℚ).mpr
    (Or.inl (by simpa using hd))⟩⟩

noncomputable def centralRationalLine (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) : (weightedFiltration w d hwd).Group :=
  ⟨centralRationalElement w d hd q⟩

@[simp] theorem bchTranslationHom_centralRationalLine (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    bchTranslationHom w d hw hwd (centralRationalLine w d hd hwd q) = ⟨0, C q⟩ := by
  change PolynomialTranslationGroup.exponentialElement 0 (C q) = _
  apply PolynomialTranslationGroup.ext
  · rfl
  · exact polynomialExponentialCoordinate_C 0 q

@[simp] theorem bchRealTranslationHom_realification_centralRationalLine
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom
      (centralRationalLine w d hd hwd q)) = ⟨0, C (q : ℝ)⟩ := by
  rw [bchRealTranslationHom_rational w d hw hwd, bchTranslationHom_centralRationalLine]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change algebraMap ℚ ℝ 0 = 0
    exact map_zero _
  · change MvPolynomial.map (algebraMap ℚ ℝ) (C q) = C (q : ℝ)
    simp

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseBudget
namespace OAI

section

namespace Erdos3

theorem exists_detectedTranslationPhase_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t k b m q : ℕ) (p H A : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ p → (k : ℝ) ≤ p →
      (b : ℝ) ≤ p → 0 ≤ H → H ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      q ≤ ⌈Real.exp p⌉₊ ^ (t * k) * m →
      let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
      Z ≤ Real.exp ((p + C) ^ C) ∧
      ((d : ℝ) + 1) * ((t : ℝ) * Z) *
          (1 + (b : ℝ) * d * t * Z) ^ d ≤ Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hcoordinate⟩ := exists_translationCoordinate_budget d
  let S : Polynomial ℕ :=
    Polynomial.C (d + 3) * (Polynomial.X + 1) + (Polynomial.X + 3) ^ 3
  let Q : Polynomial ℕ := S + (S + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t k b m q p H A hp hn ht hk hb hH hHp hA hAp hm hq
  let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
  let s : ℝ := ((d : ℝ) + 3) * (p + 1) + (p + 3) ^ 3
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsbudget : s + (s + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, S, s, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hsp : p ≤ s := by
    dsimp [s]
    have hdp := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hp
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsZ : ((d : ℝ) + 3) * p + d ≤ s := by
    dsimp [s]
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsq : (p + 3) ^ 3 ≤ s := by
    exact le_add_of_nonneg_left (by positivity)
  have hnp : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hkp : (k : ℝ) ≤ Real.exp p := hk.trans (by linarith [Real.add_one_le_exp p])
  have hZ : Z ≤ Real.exp s := by
    apply le_trans _ (Real.exp_le_exp.mpr hsZ)
    calc
      Z ≤ Real.exp (p + 1) ^ d * Real.exp p * Real.exp p * Real.exp p := by
        dsimp [Z]
        gcongr
      _ = Real.exp (((d : ℝ) + 3) * p + d) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hqexp : (q : ℝ) ≤ Real.exp s :=
    (detectedTranslationCoordinate_denominator_le_exp t k m q hp ht hk hm hq).trans
      (Real.exp_le_exp.mpr hsq)
  have hts : (t : ℝ) ≤ Real.exp s :=
    (ht.trans hsp).trans (by linarith [Real.add_one_le_exp s])
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  obtain ⟨hmass, hdenom⟩ := hcoordinate b t q s Z 1 hs (hb.trans hsp) hts
    hZ0 hZ zero_le_one (Real.one_le_exp_iff.mpr hs) hqexp
  have hpow : (s + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans hsbudget
  have hsle : s ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) a)).trans hsbudget
  refine ⟨hZ.trans (Real.exp_le_exp.mpr hsle), ?_, hdenom.trans (Real.exp_le_exp.mpr hpow)⟩
  have hmass' := hmass.trans (Real.exp_le_exp.mpr hpow)
  simpa only [Z, mul_one, mul_assoc] using hmass'

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialOperationBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ M : ℝ, 0 ≤ M → ∀ Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L),
        Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T M Q →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) * M) (dualAdjoint A Q)) ∧
      (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
        A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
        ∀ i : σ, CoefficientBound (b.baseChange ℝ) T
          (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
          (formalLogDerivative i A)) := by
  obtain ⟨C, hC, hoperations⟩ := exists_scaled_polynomial_dual_bound s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT
  classical
  have hN : (1 : ℝ) ≤ Real.exp ((p + 2) ^ a) := Real.one_le_exp (by positivity)
  have hops := hoperations F b ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hc T hT
  constructor
  · intro A hA hAbound M hM Q hQ hQbound
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    have hybound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T M y := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT hM y).mpr
      rwa [hy]
    have hunit : ∀ z, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 z →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (dualAdjoint G z) := by
      intro z hz
      exact hops.2 G z hxbound (F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN z hz)
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * M) (dualAdjoint G y) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        (dualAdjointRealLinearEquiv G).toLinearMap _ hunit hM y hybound
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hM) _).mp hout
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hf
    exact hf
  · intro A hA hAbound i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxbound : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ a)) x := by
      apply (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT (Real.exp_nonneg _) x).mpr
      rwa [hx]
    let Φ := dualRealLogarithmicDifferential
      (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot) x
    have hunit : ∀ y, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 y →
        F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C)) (Φ y) := by
      intro y hy
      have hy' := F.realAdaptedCoefficientBound_mono b ω hF _ T hT hN y hy
      change F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T (Real.exp ((p + C) ^ C))
        (dualLogDerivative ⟨dualConstantLie x + dualInfinitesimal y⟩)
      apply hops.1
      · simpa only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero] using hxbound
      · simpa only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add] using hy'
    have hderivative := F.realAdaptedDirectionalDerivative_single_bound b ω hF T hT
      (Real.exp_nonneg _) x hxbound i
    have hfactor : 0 ≤ (s : ℝ) * Real.exp ((p + 2) ^ a) / T i :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) (hT i).le
    have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
        (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
        (F.realAdaptedLogDerivative (Pi.single i 1) x) :=
      weighted_linear_bound_of_unit
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
        (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
        Φ _ hunit hfactor _ hderivative
    have hf := (F.realAdaptedCoefficientBound_iff_formal b ω hF _ T hT
      (mul_nonneg (Real.exp_nonneg _) hfactor) _).mp hout
    rw [F.realAdaptedLogDerivative_eq_formal, hx] at hf
    exact hf

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def nativePolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (F.realAdaptedPolynomialMap w g.coord)
    (F.realAdaptedPolynomialMap_adapted w g.coord)

@[simp] theorem nativePolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativePolynomialOrbit w g).log = F.realAdaptedPolynomialMap w g.coord := rfl

theorem nativePolynomialOrbit_surjective (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    Function.Surjective (F.nativePolynomialOrbit w) := by
  intro q
  obtain ⟨g, hg⟩ := F.realAdaptedPolynomialGroupHom_surjective w b ω hF ⟨⟨q.log, q.property⟩⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun z : (F.realification.adaptedPolynomialFiltration w).Group => z.coord.val) hg

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def nativeReducedPolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realification.PolynomialOrbit w :=
  F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl (F.nativePolynomialOrbit w g)

theorem nativeReducedPolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativeReducedPolynomialOrbit w g).log =
      F.quotientTop.realAdaptedPolynomialMap w
        ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) := by
  exact (F.realFilteredPolynomialMap_polynomial F.quotientTop
    (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w g.coord).symm

theorem nativeReducedPolynomialOrbit_symbol
    (b : Basis ι ℚ (L ⧸ F.layerIdeal (s + 1))) (ω : ι → ℕ)
    (hF : ∀ j, F.quotientTop.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realPolynomialSymbolHom b ω hF w
      ⟨⟨(F.nativeReducedPolynomialOrbit w g).log,
        (F.nativeReducedPolynomialOrbit w g).property⟩⟩ =
      F.adaptedReducedRealSymbolHom w g := by
  apply NilpotentLieBCHGroup.ext
  change F.quotientTop.realSymbolOfPolynomial b ω hF w
    (F.nativeReducedPolynomialOrbit w g).log = _
  rw [F.nativeReducedPolynomialOrbit_log,
    F.quotientTop.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  have hmap : (F.quotientTop.polynomialSymbolMap w).toLinearMap.comp
      (F.quotientTopPolynomialMap w).toLinearMap = (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    rfl
  change (F.quotientTop.polynomialSymbolMap w).toLinearMap.baseChange ℝ
    ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hmap]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

noncomputable def schmidtStepFactor (C e d : ℕ) (A : ℝ) : ℝ :=
  1 + (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) *
    (schmidtRadiusFactor d A + (d : ℝ) + 1)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMassMultiplier (d : ℕ) (A : ℝ) : ℝ :=
  Real.exp 10 * ((d : ℝ) + Real.log A + 1) ^ 2

noncomputable def schmidtMassCeiling (d : ℕ) (A : ℝ) : ℝ :=
  A * (schmidtMassMultiplier d A) ^ d

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtDegreeConstant (C e : ℕ) : ℝ :=
  (10 + 8 * Real.exp (4 * Real.pi + 1)) *
    (1 + 2 * Real.exp Real.pi * (C : ℝ) * (8 : ℝ) ^ e)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMeanDenominator (C e d : ℕ) (A : ℝ) : ℝ :=
  (schmidtDegreeConstant C e * A ^ (e + 1) *
    (schmidtMassMultiplier d A) ^ (d * (e + 1) + 2)) ^ (d + 1)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

def schmidtRecurrenceExponent (e : ℕ) : ℕ := 15 * (e + 1) + 23

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtRecurrenceBase (C e : ℕ) : ℝ :=
  2 + 121 * Real.exp 10 + schmidtDegreeConstant C e + schmidtRecurrenceExponent e

end Erdos3

end

section

namespace Erdos3

open Polynomial

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

universe u

open Polynomial

def PolynomialCoordinatePartitionBound (k : ℕ) (K : ℝ) (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
    (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
    K * ((Fintype.card ι : ℝ) + 1) ≤ H →
    H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
    ∃ (Q : FiniteProgressionPartition N) (z : Q.Label → ι → ℝ) (m : Q.Label → ℕ → ι → ℤ),
      Fintype.card Q.Label * H ≤ 2 ^ k * N ∧
      ∀ i n, n < Q.length i → ∀ j,
        |(P j).eval ((Q.start i + Q.step i * n : ℕ) : ℝ) - m i n j - z i j| ≤ (k : ℝ) / H

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelDirectionBudget
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

noncomputable def polynomialKernelDirection (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : σ) : κ → ℝ :=
  realSubspaceCoordinateMap b Q (coefficients P (Finsupp.single i 1))

theorem polynomialKernelDirection_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (i : σ) :
    bracketSystemLift e (polynomialKernelDirection b Q P i) = coefficients P (Finsupp.single i 1) :=
  lift_realSubspaceCoordinateMap b e Q hQ _ (hP _)

theorem polynomialKernelDirection_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (hP : CoefficientBound (b.baseChange ℝ) T M P) (i : σ) :
    ‖polynomialKernelDirection b Q P i‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / T i := by
  have hp := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP (Finsupp.single i 1)
  have hs : monomialScale T (Finsupp.single i 1) = T i := by
    simp only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one]
  rw [hs] at hp
  apply (realSubspaceCoordinateMap_norm b Q hQ _).trans
  calc
    (((Fintype.card μ : ℝ) + 1) * (H + 1)) * ‖(b.baseChange ℝ).equivFun
        (coefficients P (Finsupp.single i 1))‖ ≤
        (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (M / T i) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem polynomialKernelDirection_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (l : ℕ)
    (hP : CoefficientGrid (b.baseChange ℝ) l P) (i : σ) :
    polynomialKernelDirection b Q P i ∈ realDenominatorGrid (matrixDenominator Q * l) :=
  realSubspaceCoordinateMap_grid b Q l _ (hP _)

theorem exists_controlled_polynomial_kernel_directions
    (b : Basis μ ℚ L) (e : Basis κ ℚ E) {H l : ℕ}
    (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    (hl : 0 < l) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ d ≤ rationalSolveHeight (Fintype.card κ) H ^
        (Fintype.card κ * Fintype.card μ) * l ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ (((Fintype.card μ : ℝ) + 1) *
          ((rationalSolveHeight (Fintype.card κ) H : ℝ) + 1)) * M / T i ∧
        c i ∈ realDenominatorGrid d := by
  classical
  obtain ⟨Q, hQ, hQheight⟩ := exists_bracketLiftMatrix_leftInverse b e hH he
  refine ⟨polynomialKernelDirection b Q A, polynomialKernelDirection b Q B,
    matrixDenominator Q * l, Nat.mul_pos (matrixDenominator_pos Q) hl,
    Nat.mul_le_mul_right l (matrixDenominator_le Q hQheight), fun i => ?_⟩
  exact ⟨polynomialKernelDirection_lift b e Q hQ A hA i,
    polynomialKernelDirection_lift b e Q hQ B hB i,
    polynomialKernelDirection_norm b Q hQheight A T hT M hM hAbound i,
    polynomialKernelDirection_grid b Q B l hBgrid i⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  {E : Submodule ℚ L}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem polynomial_kernel_direction_budget (n k H l : ℕ) {p M : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((rationalSolveHeight k H : ℝ) + 1) * M ≤ Real.exp ((p + 2) ^ 8) ∧
      ((rationalSolveHeight k H ^ (k * n) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  let B := (p + 2) ^ 5
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith : (1 : ℝ) ≤ p + 2)
  have hpB : p ≤ B := le_power_budget hp (by decide : 1 ≤ 5)
  have hq : 0 ≤ p + B := add_nonneg hp hB
  have hheight : (rationalSolveHeight k H : ℝ) ≤ Real.exp (p + B) :=
    (rationalSolveHeight_le_budget k H hp hk hHp).trans
      (Real.exp_le_exp.mpr (by dsimp [B]; linarith))
  have hfactor := current_layer_coordinate_factor_bound hq n (rationalSolveHeight k H)
    (hn.trans (le_add_of_nonneg_right hB)) hheight
  have h8 : (8 : ℝ) ≤ (p + 2) ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (p + 2) ^ 3 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
  have hlog : 2 * (p + B) + 1 + p ≤ (p + 2) ^ 8 := by
    calc
      _ ≤ 6 * B := by linarith
      _ ≤ (p + 2) ^ 3 * B := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = _ := by dsimp [B]; ring
  constructor
  · calc
      _ ≤ Real.exp (2 * (p + B) + 1) * Real.exp p :=
        mul_le_mul hfactor hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + B) + 1 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  · have hHpow : (1 : ℕ) ≤ H ^ (n * k) := one_le_pow₀ hH
    have hnat := Nat.mul_le_mul_right (rationalSolveHeight k H ^ (k * n)) hHpow
    simp only [one_mul] at hnat
    have hK : ((rationalSolveHeight k H ^ (k * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) :=
      (Nat.cast_le.mpr hnat).trans (rational_grid_height_le_exp n k H hp hn hk hHp)
    have hd := grid_allowance_mul_le_exp hp hl hK
    simpa only [Nat.mul_comm] using hd

theorem exists_uniform_polynomial_kernel_directions
    {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype μ] [Fintype κ]
    {E : Submodule ℚ L} (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hambient : (Fintype.card μ : ℝ) ≤ p) (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p)
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hAbound : CoefficientBound (b.baseChange ℝ) T M A)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) l B) :
    ∃ (a c : σ → κ → ℝ) (d : ℕ),
      0 < d ∧ (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      ∀ i,
        bracketSystemLift e (a i) = coefficients A (Finsupp.single i 1) ∧
        bracketSystemLift e (c i) = coefficients B (Finsupp.single i 1) ∧
        ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
  obtain ⟨a, c, d, hd, hdbound, hdirs⟩ := exists_controlled_polynomial_kernel_directions
    b e hH he hl A B hA hB T hT M hM hAbound hBgrid
  have hbudget := polynomial_kernel_direction_budget (Fintype.card μ) (Fintype.card κ) H l
    hp hM hH hambient hkernel hHp hlp hMp
  refine ⟨a, c, d, hd, (Nat.cast_le.mpr hdbound).trans hbudget.2, fun i => ?_⟩
  exact ⟨(hdirs i).1, (hdirs i).2.1,
    (hdirs i).2.2.1.trans (div_le_div_of_nonneg_right hbudget.1 (hT i).le), (hdirs i).2.2.2⟩

end Erdos3

end

end OAI

end


