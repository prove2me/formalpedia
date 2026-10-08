-- Prove2me | Definitions.Def_OAIErdos3B016
-- name    : OAIErdos3B016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T11:29:51.479018+00:00
-- url     : https://prove2.me/theorems/20adb980-b064-455f-9528-eae07a26a032
-- title:
--   OpenAI Erdős-3 split, definitions bundle 17 of 88
-- statement:
--   Definitions bundle 17 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B015`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 17 available.
--
--   Modules: `OAI.Erdos3.ColumnResiduePattern`, `OAI.Erdos3.FiniteProbabilityWeights.abs_mean_sub_const_le`, `OAI.Erdos3.FiniteProbabilityWeights.exists_code_fiber_mass`, `OAI.Erdos3.FiniteProbabilityWeights.fiberLaw_complexMean`, `OAI.Erdos3.FiniteProbabilityWeights.fiberLaw_mean`, `OAI.Erdos3.FiniteProbabilityWeights.integral_normalizedDensityTest_compare`, `OAI.Erdos3.FiniteProbabilityWeights.joint_normalization_compare`, `OAI.Erdos3.FiniteProbabilityWeights.mean_comm`, `OAI.Erdos3.FiniteProbabilityWeights.mean_mem_Icc`, `OAI.Erdos3.FiniteProbabilityWeights.mean_mul_le_of_capped_comparison`, `OAI.Erdos3.FiniteProbabilityWeights.mean_prod`, `OAI.Erdos3.FiniteProbabilityWeights.mean_sub`, `OAI.Erdos3.FiniteProbabilityWeights.mean_sum`, `OAI.Erdos3.FiniteProbabilityWeights.norm_density_weighted_complexMean_le`, `OAI.Erdos3.FiniteProbabilityWeights.normalizedDensityTest`, `OAI.Erdos3.FiniteProbabilityWeights.normalizedDensityTest_integrable`, `OAI.Erdos3.FiniteProbabilityWeights.normalizedDensityTest_measurable`, `OAI.Erdos3.FiniteProbabilityWeights.normalizedDensityTest_norm_le_one`, `OAI.Erdos3.FiniteProbabilityWeights.normalizedDensityTest_remove_normalization`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_complexMean`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_complexMean_eq_normalizedDensityTest`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_mean`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_test_le`, `OAI.Erdos3.FiniteProbabilityWeights.reweightPositive_weight`, `OAI.Erdos3.FiniteProbabilityWeights.siteLaw`, `OAI.Erdos3.FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound`, `OAI.Erdos3.FiniteProbabilityWeights.siteLaw_mean`, `OAI.Erdos3.FiniteProbabilityWeights.uniformFinset`, `OAI.Erdos3.FiniteProbabilityWeights.uniformFinset_complexMean`, `OAI.Erdos3.FiniteProbabilityWeights.uniformFinset_mean`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_base_reweight_test_le`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_injective_mean_le`, `OAI.Erdos3.MultidegreeLieFiltration.SquarefreeAlgebra`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairDegreeLayer`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairDegreeLayer_eq`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairDegreeLayer_le_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairDegree_diagonal`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairDegree_higher`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_le_degree`, `OAI.Erdos3.MultidegreeLieFiltration.mem_squarefreeCoefficientLayer`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAdaptedSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAdapted_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAlgebraEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAlgebraEquiv_apply`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAlgebraFiniteDimensional`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAlgebra_finrank`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAlgebra_finrank_le`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeCoefficientLayer`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstant_mem_shiftedPolynomialIdeal`, `OAI.Erdos3.NilpotentLieFiltration.mem_shiftedPolynomialIdeal`, `OAI.Erdos3.NilpotentLieFiltration.shiftedAdaptedSubmodule_antitone`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomialIdeal`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomialIdeal_antitone`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomialIdeal_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomialIdeal_one`, `OAI.Erdos3.PolynomialRationalApproximation`, `OAI.Erdos3.PolynomialRationalApproximation.mono`, `OAI.Erdos3.PolynomialRationalApproximation.nat_smul`, `OAI.Erdos3.PolynomialSlots.exists_coefficient_normalized`, `OAI.Erdos3.PolynomialSlots.exists_coefficient_normalized_prefix`, `OAI.Erdos3.PolynomialSlots.shear`, `OAI.Erdos3.PolynomialSlots.shear_center_before`, `OAI.Erdos3.PolynomialSlots.shear_center_eval`, `OAI.Erdos3.PolynomialSlots.shear_center_self`, `OAI.Erdos3.PolynomialSlots.shear_integer_residual`, `OAI.Erdos3.PolynomialSlots.specializeCenter`, `OAI.Erdos3.PolynomialSlots.specializeCenter_degree`, `OAI.Erdos3.PolynomialSlots.specializeCenter_full_degree`, `OAI.Erdos3.PolynomialSlots.sub_topPart_lower`, `OAI.Erdos3.PolynomialSlots.topPart`, `OAI.Erdos3.PolynomialSlots.topPart_aeval_independent`, `OAI.Erdos3.PolynomialSlots.topPart_lift_specialize`, `OAI.Erdos3.PolynomialSlots.topPart_parameter_exponent_zero`, `OAI.Erdos3.SquarefreeIndex.blockDegree_ofFinset`, `OAI.Erdos3.SquarefreeIndex.blockDegree_support`, `OAI.Erdos3.SquarefreeIndex.ofFinset`, `OAI.Erdos3.SquarefreeIndex.ofFinset_add_complement`, `OAI.Erdos3.SquarefreeIndex.ofFinset_apply`, `OAI.Erdos3.SquarefreeIndex.ofFinset_support`, `OAI.Erdos3.SquarefreeIndex.permute`, `OAI.Erdos3.SquarefreeIndex.permute_apply`, `OAI.Erdos3.SquarefreeIndex.permute_blockDegree`, `OAI.Erdos3.SquarefreeIndex.permute_disjoint`, `OAI.Erdos3.SquarefreeIndex.permute_disjointAdd`, `OAI.Erdos3.SquarefreeIndex.permute_weight`, `OAI.Erdos3.SquarefreeIndex.permute_zero_iff`, `OAI.Erdos3.SquarefreeIndex.support_ofFinset`, `OAI.Erdos3.SquarefreeIndex.support_subset_of_add`, `OAI.Erdos3.SquarefreeSplit`, `OAI.Erdos3.VectorPolynomial.dehomogenize_degreeLE`, `OAI.Erdos3.VectorPolynomial.exists_absorbed_polynomial_site_tests`, `OAI.Erdos3.VectorPolynomial.factored_polynomial_mode_character`, `OAI.Erdos3.VectorPolynomial.homogeneous_degreeLE`, `OAI.Erdos3.VectorPolynomial.homogeneous_site_factorization_iff`, `OAI.Erdos3.VectorPolynomial.homogeneously_factored_polynomial_character`, `OAI.Erdos3.VectorPolynomial.preparedComparisonGridPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedComparisonSourcePolynomial`, `OAI.Erdos3.VectorPolynomial.siteEvaluation_dehomogenize`, `OAI.Erdos3.VectorPolynomial.siteEvaluation_homogenize`, `OAI.Erdos3.affineShiftCoordinate`, `OAI.Erdos3.affineShiftCoordinate_degree`, `OAI.Erdos3.affineShiftPullback`, `OAI.Erdos3.affineShiftPullback_degree`, `OAI.Erdos3.affineShiftPullback_eval`, `OAI.Erdos3.affineShiftPullback_translate`, `OAI.Erdos3.affineShift_difference_eq_topSymbol`, `OAI.Erdos3.affineShift_full_coefficient_base`, `OAI.Erdos3.affineShift_full_coefficient_top`, `OAI.Erdos3.affineShift_full_difference`, `OAI.Erdos3.bchIntegralDenominatorBound`, `OAI.Erdos3.bchSubgroupCoordinates_repr`, `OAI.Erdos3.blockExponent`, `OAI.Erdos3.blockExponent_apply`, `OAI.Erdos3.blockExponent_permute`, `OAI.Erdos3.blockExponent_weight`, `OAI.Erdos3.blockExponent_zero`, `OAI.Erdos3.blockMonomial`, `OAI.Erdos3.blockMonomial_coefficient`, `OAI.Erdos3.blockSplitMultiplicity`, `OAI.Erdos3.boundedColumnResidueRepresentative`, `OAI.Erdos3.boundedColumnResidueRepresentative_bounds`, `OAI.Erdos3.boundedColumnResidueRepresentative_congr`, `OAI.Erdos3.card_squarefreeSplit`, `OAI.Erdos3.centeredFiniteMarginal`, `OAI.Erdos3.centeredFiniteMarginal_excessMass_le`, `OAI.Erdos3.centeredFiniteMarginal_excessMass_le_of_ae`, `OAI.Erdos3.centeredFiniteMarginal_excessMass_le_of_uniform`, `OAI.Erdos3.centeredFiniteMarginal_mean`, `OAI.Erdos3.centeredFiniteMarginal_siteLaw`, `OAI.Erdos3.centeredFiniteSliceResidualEnvelope`, `OAI.Erdos3.centeredFiniteSliceResidualEnvelope_dominates`, `OAI.Erdos3.centeredFiniteSliceResidualEnvelope_nonneg`, `OAI.Erdos3.centeredFinite_excessMass_integrable`, `OAI.Erdos3.centeredFinite_siteLaw_weight_measurable`, `OAI.Erdos3.columnResiduePattern`, `OAI.Erdos3.columnResiduePattern_eq_iff`, `OAI.Erdos3.columnResidueReduction`, `OAI.Erdos3.columnResidueReduction_pattern`, `OAI.Erdos3.columnResidueRepresentative`, `OAI.Erdos3.columnResidueRepresentative_cast`, `OAI.Erdos3.complex_remove_normalization`, `OAI.Erdos3.conditionPolynomial`, `OAI.Erdos3.coordinateGridBCHSubgroup`, `OAI.Erdos3.coordinateGridBCHSubgroup_coordinates`, `OAI.Erdos3.coordinateShearEquiv`, `OAI.Erdos3.coordinateShearEquiv_inverse_mass`, `OAI.Erdos3.coordinateShearHom`, `OAI.Erdos3.coordinateShearHom_X`, `OAI.Erdos3.coordinateShearHom_comp_neg`, `OAI.Erdos3.coordinateShearHom_degree`, `OAI.Erdos3.coordinateShearHom_mass`, `OAI.Erdos3.coordinateShearHom_rename`, `OAI.Erdos3.crtInputAddEquiv`, `OAI.Erdos3.crtInputModulusNeZero`, `OAI.Erdos3.crtPolynomialCharge`, `OAI.Erdos3.crtPolynomialInputLaw`, `OAI.Erdos3.crtPrimePowerIntegerPolynomialOutput`, `OAI.Erdos3.crtPrimePowerPolynomialLaw`, `OAI.Erdos3.crtPrimePowerPolynomialMap`, `OAI.Erdos3.degree_le_one_eq_constant_add_row`, `OAI.Erdos3.denominator_grid_smul_mem_scaled`, `OAI.Erdos3.denominator_grid_subset_mul`, `OAI.Erdos3.diagonalMultiaffineScaling`, `OAI.Erdos3.diagonalMultiaffineScaling_degree`, `OAI.Erdos3.diagonalMultiaffineScaling_eval`, `OAI.Erdos3.diagonalMultiaffineScaling_top`, `OAI.Erdos3.dynkinWord_mem_multiple`, `OAI.Erdos3.earlierSlot_ne_self`, `OAI.Erdos3.exists_bchSubgroup_outer_grid_change_basis`, `OAI.Erdos3.exists_bch_stable_integral_grid`, `OAI.Erdos3.exists_integral_grid_subgroup`, `OAI.Erdos3.exists_jointExceptional_polynomial_budget`, `OAI.Erdos3.exists_linear_model_partner`, `OAI.Erdos3.exists_nearly_maximizing_sampled_slice_tests`, `OAI.Erdos3.exists_sampled_slice_model`, `OAI.Erdos3.exists_spatialMatrixBlock_polynomial_budget`, `OAI.Erdos3.exists_triangularPolynomialEquiv`, `OAI.Erdos3.exists_triangularPolynomialEquiv_prefix`, `OAI.Erdos3.exists_triangularPolynomialEquiv_prefix_mass`, `OAI.Erdos3.exists_weighted_exponential_constant_fiber`, `OAI.Erdos3.exponent_eq_full_or_missing`, `OAI.Erdos3.exponent_total_eq_zero_iff`, `OAI.Erdos3.factorialBlockMonomial`, `OAI.Erdos3.factorialBlockMonomial_coefficient`, `OAI.Erdos3.fin_multiaffine_polynomial_bias`, `OAI.Erdos3.fin_multiaffine_strided_bias`, `OAI.Erdos3.finsupp_weight_add_function`, `OAI.Erdos3.freezePolynomial`, `OAI.Erdos3.freezePolynomial_eval`, `OAI.Erdos3.freezePolynomial_map`, `OAI.Erdos3.freezePolynomial_monomial_coeff_eq_zero_of_no_keep`, `OAI.Erdos3.freezePolynomial_monomial_eq_C_of_no_keep`, `OAI.Erdos3.freezePolynomial_sub_lower`, `OAI.Erdos3.freezePolynomial_support`, `OAI.Erdos3.freezePolynomial_top`, `OAI.Erdos3.freezePolynomial_top_independent`, `OAI.Erdos3.frozenCoordinate`, `OAI.Erdos3.frozenCoordinate_support`, `OAI.Erdos3.frozenCoordinate_zero_homogeneous`, `OAI.Erdos3.frozenPolynomialFamily_coeff_mem`, `OAI.Erdos3.fullShiftExponent`, `OAI.Erdos3.fullShiftExponent_apply`, `OAI.Erdos3.fullShiftExponent_sum`, `OAI.Erdos3.fullShiftExponent_weight`, `OAI.Erdos3.fullSquarefreeExponent_map_equiv`, `OAI.Erdos3.full_coefficient_zero_of_lower_support`, `OAI.Erdos3.full_mixed_difference_of_totalDegree`, `OAI.Erdos3.intModuleBCHSubgroup`, `OAI.Erdos3.integerBoxUniformWeights`, `OAI.Erdos3.integerPolynomialQuotient_coeff`, `OAI.Erdos3.integerPolynomialRankProbability`, `OAI.Erdos3.integerRowShift`, `OAI.Erdos3.integerRowShift_bound`, `OAI.Erdos3.integerRowShift_normalized_bound`, `OAI.Erdos3.integerSiteValue`, `OAI.Erdos3.intervalUniformWeights`, `OAI.Erdos3.lieBCH_mem_of_divisible_brackets`, `OAI.Erdos3.lieBCH_mem_of_divisible_brackets_nilpotent`, `OAI.Erdos3.localPrimePowerIntegerPolynomialOutput`, `OAI.Erdos3.localPrimePowerIntegerPolynomialOutput_reduce`, `OAI.Erdos3.longChart_freezePolynomial_zero_eq_killCompl`, `OAI.Erdos3.longChart_frozen_top_eval_mem`, `OAI.Erdos3.longChart_top_eval_mem`, `OAI.Erdos3.markedLieSpan`, `OAI.Erdos3.markedLieSpan_antitone`, `OAI.Erdos3.markedLieSpan_le_layer`, `OAI.Erdos3.markedLieSpan_leaf`, `OAI.Erdos3.markedLieSpan_lie_mem`, `OAI.Erdos3.markedLieSpan_marked_terminal`, `OAI.Erdos3.markedLieSpan_top_le_ker`, `OAI.Erdos3.markedLieSpan_zero_marked`, `OAI.Erdos3.mem_selectedResidueRefinement`, `OAI.Erdos3.mem_weightedSupportLE_one_iff`, `OAI.Erdos3.modularRankChargeFactor`, `OAI.Erdos3.modularRankDecayExponent`, `OAI.Erdos3.multiaffineExpansion_affine`, `OAI.Erdos3.multiaffineOption_eval`, `OAI.Erdos3.multiaffinePolynomial_eval`, `OAI.Erdos3.multiaffine_polynomial_bias`, `OAI.Erdos3.multidegreeFactorial`, `OAI.Erdos3.multidegreeFactorial_pos`, `OAI.Erdos3.multidegreeFactorial_split`, `OAI.Erdos3.multilinearSlicePolynomial`, `OAI.Erdos3.multilinearSlicePolynomial_degree`, `OAI.Erdos3.multilinearSlicePolynomial_eval`, `OAI.Erdos3.multilinearSlicePolynomial_top`, `OAI.Erdos3.multilinear_box_biased_slice`, `OAI.Erdos3.multilinear_box_coordinate_approximation`, `OAI.Erdos3.multilinear_slice_bias_approximation`, `OAI.Erdos3.norm_real_phase_double_mean_le_one`, `OAI.Erdos3.normalizedMass_freezePolynomial_le`, `OAI.Erdos3.normalizedSliceTest`, `OAI.Erdos3.normalizedSliceTest_mean`, `OAI.Erdos3.normalizedSliceTest_norm_le`, `OAI.Erdos3.optionLinearCoefficient_squarefree`, `OAI.Erdos3.optionSquarefree_full_exponent`, `OAI.Erdos3.paired_multilinear_box_coordinate_approximation`, `OAI.Erdos3.paired_multilinear_common_approximation`, `OAI.Erdos3.paired_multilinear_polynomial_approximation`, `OAI.Erdos3.patchParameterWeight`, `OAI.Erdos3.patchSlotWeight`, `OAI.Erdos3.patchVariableWeight_split`, `OAI.Erdos3.polynomialAffineClass`, `OAI.Erdos3.polynomialCommonScale`, `OAI.Erdos3.polynomialDifference`, `OAI.Erdos3.polynomialDifference_C`, `OAI.Erdos3.polynomialDifference_affine`, `OAI.Erdos3.polynomialDifference_apply`, `OAI.Erdos3.polynomialDifference_commute`, `OAI.Erdos3.polynomialDifference_degree`, `OAI.Erdos3.polynomialDifference_direction_add`, `OAI.Erdos3.polynomialDifference_direction_smul`, `OAI.Erdos3.polynomialDifference_eval`, `OAI.Erdos3.polynomialDifference_row`, `OAI.Erdos3.polynomialFamily_eval_mem`, `OAI.Erdos3.polynomialFamily_eval_sub_zero_mem`, `OAI.Erdos3.polynomialFamily_freeze_coeff_mem`, `OAI.Erdos3.polynomialHom_preserves_weightedDegree`, `OAI.Erdos3.polynomialIterDifference`, `OAI.Erdos3.polynomialIterDifferenceMultilinear`, `OAI.Erdos3.polynomialIterDifference_commute`, `OAI.Erdos3.polynomialIterDifference_degree`, `OAI.Erdos3.polynomialIterDifference_eval`, `OAI.Erdos3.polynomialIterDifference_topSymbol`, `OAI.Erdos3.polynomialIterDifference_update_add`, `OAI.Erdos3.polynomialIterDifference_update_smul`, `OAI.Erdos3.polynomialRationalApproximation_of_decomposition`, `OAI.Erdos3.polynomialSlotShear`, `OAI.Erdos3.polynomialSlotShear_apply`, `OAI.Erdos3.polynomialSlotShear_cast`, `OAI.Erdos3.polynomialTopSymbol`, `OAI.Erdos3.polynomialTopSymbolMultilinear`, `OAI.Erdos3.polynomialTopSymbolMultilinear_apply`, `OAI.Erdos3.polynomialTranslate_add_apply`, `OAI.Erdos3.polynomialTranslate_sub_mem_weightedSupportLT`, `OAI.Erdos3.prescribedCRTPolynomialInput`, `OAI.Erdos3.primePowerHomogeneousRankProbability`, `OAI.Erdos3.primePower_crt_coprime`, `OAI.Erdos3.productive_mass_mul_le_sampledSliceSeminorm`, `OAI.Erdos3.rational_nat_smul_mem`, `OAI.Erdos3.realBlockPolynomialEval`, `OAI.Erdos3.realBlockPolynomialEval_coefficient`, `OAI.Erdos3.realFactorialBlockMonomial_coefficient`, `OAI.Erdos3.realPolynomialMass_freezePolynomial_le`, `OAI.Erdos3.refinedColumnExtraResidue`, `OAI.Erdos3.residueLatticeArray`, `OAI.Erdos3.residueLatticeArray_injective`, `OAI.Erdos3.residueLatticeArray_range`, `OAI.Erdos3.residueLatticeArray_rowShift`, `OAI.Erdos3.residueProfileCenter`, `OAI.Erdos3.residueProfileWidth`, `OAI.Erdos3.residueProfileWidth_pos`, `OAI.Erdos3.residueProfile_point`, `OAI.Erdos3.residueRowShift_normalized_bound`, `OAI.Erdos3.residueSmoothIndexPMF`, `OAI.Erdos3.residueSmoothIndexPMF_toReal`, `OAI.Erdos3.residueSmoothMass_congr`, `OAI.Erdos3.residueSmoothPMF`, `OAI.Erdos3.residueSmoothPMF_at`, `OAI.Erdos3.residueSmoothPMF_conditional_weight`, `OAI.Erdos3.residueSmoothPMF_congr`, `OAI.Erdos3.residueSmoothPMF_expectation`, `OAI.Erdos3.residueSmoothPMF_zero_off`, `OAI.Erdos3.residueSmoothScalarPMFs`, `OAI.Erdos3.residueSmoothWeight`, `OAI.Erdos3.residueSmoothWeight_at`, `OAI.Erdos3.residueSmoothWeight_congr`, `OAI.Erdos3.residueSmoothWeight_eq_pattern`, `OAI.Erdos3.residueSmoothWeight_mass`, `OAI.Erdos3.residueSmoothWeight_zero_off`, `OAI.Erdos3.residue_smooth_row_shift_transfer`, `OAI.Erdos3.residue_smooth_row_shift_transfer_lipschitz_amplitude`, `OAI.Erdos3.rightBracketList_mem_intModule`, `OAI.Erdos3.roundedIntegerPolynomial`, `OAI.Erdos3.roundedIntegerPolynomial_coeff`, `OAI.Erdos3.roundedIntegerPolynomial_real_degree`, `OAI.Erdos3.roundedIntegerPolynomial_remainder_bound`, `OAI.Erdos3.rowDirectionLinear`, `OAI.Erdos3.rowShiftedSite_eq`, `OAI.Erdos3.rowShiftedTuple`, `OAI.Erdos3.rowTopSymbolMultilinear`, `OAI.Erdos3.rowTopSymbolMultilinear_apply`, `OAI.Erdos3.row_shift_difference_eq_topSymbol`, `OAI.Erdos3.row_shifted_site_phase_cauchySchwarz`, `OAI.Erdos3.sampledSingleTestSeminorm`, `OAI.Erdos3.sampledSingleTestSeminorm_bddAbove`, `OAI.Erdos3.sampledSingleTestSeminorm_le`, `OAI.Erdos3.sampledSliceSeminorm`, `OAI.Erdos3.sampledSliceSeminorm_apply`, `OAI.Erdos3.sampledSliceSeminorm_congr_values`, `OAI.Erdos3.sampledSliceSeminorm_le_siteLaw`, `OAI.Erdos3.sampledTestLinearMap`, `OAI.Erdos3.sampledTestSeminorm`, `OAI.Erdos3.sampledTestSeminorm_apply`, `OAI.Erdos3.sampledTestSeminorm_le_siteLaw`, `OAI.Erdos3.scalarCoefficientBad`, `OAI.Erdos3.scalarCoefficientTupleEquiv`, `OAI.Erdos3.scaleMvPolynomialAxes_freezePolynomial`, `OAI.Erdos3.selectedResidueCellWeight`, `OAI.Erdos3.selectedResidueCellWeight_nonneg`, `OAI.Erdos3.selectedResidueCellWeight_sum`, `OAI.Erdos3.selectedResidueDensityMass`, `OAI.Erdos3.selectedResidueDensityMass_bound_of_constant_test`, `OAI.Erdos3.selectedResidueDensityMass_complex`, `OAI.Erdos3.selectedResidueDensityMass_integral`, `OAI.Erdos3.selectedResidueDensityMass_l1_surrogate`, `OAI.Erdos3.selectedResidueDensityMass_singleton_window_bound`, `OAI.Erdos3.selectedResidueDensityMass_window_bound`, `OAI.Erdos3.selectedResidueDensityPMF`, `OAI.Erdos3.selectedResidueDensityPMF_complexMean`, `OAI.Erdos3.selectedResidueDensityPMF_error`, `OAI.Erdos3.selectedResidueDensityPMF_error_of_bounded_test`, `OAI.Erdos3.selectedResidueDensityPMF_mean`, `OAI.Erdos3.selectedResidueDensityPMF_normalizedDensityTest`, `OAI.Erdos3.selectedResidueDensityPMF_remove_normalization`, `OAI.Erdos3.selectedResidueDensityPMF_toReal`, `OAI.Erdos3.selectedResidueDensityPMF_zero_of_density_zero`, `OAI.Erdos3.selectedResidueFiniteLaw`, `OAI.Erdos3.selectedResidueFiniteLaw_complexMean`, `OAI.Erdos3.selectedResidueFiniteLaw_densityMass`, `OAI.Erdos3.selectedResidueFiniteLaw_mean`, `OAI.Erdos3.selectedResidueRefinement`, `OAI.Erdos3.selectedResidueSmoothPMF`, `OAI.Erdos3.selectedResidueSmoothPMF_approximation`, `OAI.Erdos3.selectedResidueSmoothPMF_bind_le_of_cells`, `OAI.Erdos3.selectedResidueSmoothPMF_bind_toReal_mixture`, `OAI.Erdos3.selectedResidueSmoothPMF_bound_of_cells`, `OAI.Erdos3.selectedResidueSmoothPMF_bounded_mixture`, `OAI.Erdos3.selectedResidueSmoothPMF_const`, `OAI.Erdos3.selectedResidueSmoothPMF_discard_error`, `OAI.Erdos3.selectedResidueSmoothPMF_mixture`, `OAI.Erdos3.selectedResidueSmoothPMF_projection_approximation`, `OAI.Erdos3.selectedResidueSmoothPMF_toReal`, `OAI.Erdos3.selectedResidueSmoothWeight`, `OAI.Erdos3.selectedResidueSmoothWeight_eq_sum`, `OAI.Erdos3.selectedResidueSmoothWeight_mass`, `OAI.Erdos3.selectedResidueSmoothWeight_mass_pos`, `OAI.Erdos3.selectedResidueSmoothWeight_nonneg`, `OAI.Erdos3.selectedResidueSmoothWeight_plateau`, `OAI.Erdos3.selectedResidueSmoothWeight_singleton_mass_upper`, `OAI.Erdos3.selectedResidueSmoothWeight_summable`, `OAI.Erdos3.selectedResidueSmoothWeight_zero_off`, `OAI.Erdos3.selectedResidue_center_mixture_compare`, `OAI.Erdos3.slotAddShearEquiv`, `OAI.Erdos3.slotPolynomialInput`, `OAI.Erdos3.slotPolynomialInput_update`, `OAI.Erdos3.slotPolynomialLift`, `OAI.Erdos3.slotPolynomialLift_degree`, `OAI.Erdos3.slotPolynomialLift_eval`, `OAI.Erdos3.slotPolynomialLift_lower`, `OAI.Erdos3.slotPrefixLift`, `OAI.Erdos3.slotPrefixLift_degree`, `OAI.Erdos3.slotPrefixLift_eval`, `OAI.Erdos3.slotPrefixLift_self`, `OAI.Erdos3.slotShearSubstitution`, `OAI.Erdos3.slotShearSubstitution_before`, `OAI.Erdos3.slotShearSubstitution_degree`, `OAI.Erdos3.slotShearSubstitution_eval`, `OAI.Erdos3.smoothProbabilityProfile_plateau`, `OAI.Erdos3.squarefreeDisjointAdd_total`, `OAI.Erdos3.squarefreeExponent_total_le`, `OAI.Erdos3.squarefreePermute`, `OAI.Erdos3.squarefreePermute_coefficient`, `OAI.Erdos3.squarefreePermute_monomial`, `OAI.Erdos3.squarefreePermute_symm_apply`, `OAI.Erdos3.squarefreeSplitSubsetEquiv`, `OAI.Erdos3.squarefreeSplit_degree`, `OAI.Erdos3.squarefreeSplit_ext`, `OAI.Erdos3.squarefreeSupportModule_lie_mem`, `OAI.Erdos3.squarefree_polynomial_eval`, `OAI.Erdos3.squarefree_polynomial_expansion`, `OAI.Erdos3.stridedMatrixPoint`, `OAI.Erdos3.stridedMatrixPoint_update`, `OAI.Erdos3.stridedMatrixSliceBase`, `OAI.Erdos3.sub_topComponent_mem_lowerSupport`, `OAI.Erdos3.subgroupPowerCover_grid`, `OAI.Erdos3.subgroupPowerCover_inner_grid`, `OAI.Erdos3.subgroupPowerCover_le_of_grid`, `OAI.Erdos3.subsetPolynomial`, `OAI.Erdos3.subsetPolynomial_coefficient`, `OAI.Erdos3.subsetPolynomial_degree`, `OAI.Erdos3.subsetPolynomial_eval`, `OAI.Erdos3.taggedPolynomialOutputCurry`, `OAI.Erdos3.tensorDenominatorBound_le`, `OAI.Erdos3.tensorDiagonalPolynomial_approximation`, `OAI.Erdos3.tensorDiagonalPolynomial_coeff_bound`, `OAI.Erdos3.tensorDiagonalPolynomial_rational_split`, `OAI.Erdos3.tensor_entry_bound_rescale`, `OAI.Erdos3.tensor_product_scale_le`, `OAI.Erdos3.top_coeff_polynomialTranslate`, `OAI.Erdos3.totalDegree_le_of_positive_weightedSupport`, `OAI.Erdos3.totalDegree_map_le`, `OAI.Erdos3.totalDegree_sub_top_component_le`, `OAI.Erdos3.triangularPolynomialEquiv`, `OAI.Erdos3.triangularPolynomialEquiv_X`, `OAI.Erdos3.triangularPolynomialEquiv_degree`, `OAI.Erdos3.triangularPolynomialEquiv_inverse_degree`, `OAI.Erdos3.triangularPolynomialEquiv_inverse_mass`, `OAI.Erdos3.vectorDesignatedRankFailureProbability`, `OAI.Erdos3.vector_shift_difference_eq_topSymbol`, `OAI.Erdos3.weightedComparison_difference`, `OAI.Erdos3.weightedComparison_monomial`, `OAI.Erdos3.weightedComparison_monomial_one`, `OAI.Erdos3.weightedComparison_mul`, `OAI.Erdos3.weightedSupportLE_lt_succ`, `OAI.Erdos3.weightedSupportLE_of_map_injective`, `OAI.Erdos3.weightedSupportLE_of_weight_le`, `OAI.Erdos3.weightedSupportLE_totalDegree_le_of_pos`, `OAI.Erdos3.weightedSupportLT_aeval`, `OAI.Erdos3.weightedSupportLT_map`, `OAI.Erdos3.weightedTopPart_preserves_degree`, `OAI.Erdos3.weightedTopPart_remainder_lt`, `OAI.Erdos3.weightedTop_aeval`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B015

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

noncomputable def SquarefreeIndex.ofFinset (S : Finset ι) : SquarefreeIndex ι := by
  classical
  exact ⟨Finsupp.equivFunOnFinite.symm (fun i => if i ∈ S then 1 else 0),
    fun i => by
      change (if i ∈ S then 1 else 0) ≤ 1
      split_ifs <;> omega⟩

theorem SquarefreeIndex.ofFinset_apply [DecidableEq ι] (S : Finset ι) (i : ι) :
    (ofFinset S).val i = if i ∈ S then 1 else 0 := by
  classical
  simp [ofFinset]

theorem SquarefreeIndex.support_ofFinset (S : Finset ι) : (ofFinset S).val.support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, ofFinset_apply]
  split_ifs <;> simp_all

theorem SquarefreeIndex.ofFinset_support (a : SquarefreeIndex ι) : ofFinset a.val.support = a := by
  classical
  apply Subtype.ext
  ext i
  rw [ofFinset_apply]
  have hi := a.property i
  split_ifs with h
  · have := Finsupp.mem_support_iff.mp h
    omega
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem SquarefreeIndex.ofFinset_add_complement [DecidableEq ι] (S T : Finset ι) (hST : S ⊆ T) :
    (ofFinset S).val + (ofFinset (T \ S)).val = (ofFinset T).val := by
  classical
  ext i
  simp only [Finsupp.add_apply, ofFinset_apply, Finset.mem_sdiff]
  by_cases hi : i ∈ S
  · simp only [hi, hST hi, not_true_eq_false, and_false, ite_true, ite_false, add_zero]
  · by_cases hj : i ∈ T <;> simp [hi, hj]

theorem SquarefreeIndex.blockDegree_ofFinset [DecidableEq σ] (π : ι → σ)
    (S : Finset ι) (i : σ) :
    blockDegree π (ofFinset S).val i = (S.filter fun j => π j = i).card := by
  classical
  rw [blockDegree_apply]
  simp only [ofFinset_apply]
  have h : (fun j => if π j = i then (if j ∈ S then 1 else 0) else 0) =
      (fun j => if j ∈ S ∧ π j = i then 1 else 0) := by
    funext j
    split_ifs <;> simp_all
  rw [h]
  have hs : (Finset.univ.filter fun j => j ∈ S ∧ π j = i) =
      S.filter (fun j => π j = i) := by ext j; simp
  simpa only [Finset.sum_boole, Nat.cast_id] using congrArg Finset.card hs

theorem SquarefreeIndex.blockDegree_support [DecidableEq σ] (π : ι → σ)
    (a : SquarefreeIndex ι) (i : σ) :
    blockDegree π a.val i = (a.val.support.filter fun j => π j = i).card := by
  rw [← blockDegree_ofFinset π a.val.support i, ofFinset_support]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def fullShiftExponent (n : ℕ) : Fin n →₀ ℕ :=
  (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val

theorem fullShiftExponent_apply (n : ℕ) (i : Fin n) : fullShiftExponent n i = 1 := by
  simp only [fullShiftExponent, SquarefreeIndex.ofFinset_apply, Finset.mem_univ, ite_true]

theorem fullShiftExponent_sum (n : ℕ) : (fullShiftExponent n).sum (fun _ e => e) = n := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem exponent_eq_full_or_missing {n : ℕ} (d : Fin n →₀ ℕ)
    (hd : d.sum (fun _ e => e) ≤ n) : d = fullShiftExponent n ∨ ∃ i, d i = 0 := by
  by_cases hz : ∃ i, d i = 0
  · exact Or.inr hz
  left
  have hpos (i : Fin n) : 1 ≤ d i := by
    have hn : d i ≠ 0 := fun hi => hz ⟨i, hi⟩
    omega
  have hsum : (∑ i, d i) ≤ n := by
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
  ext i
  rw [fullShiftExponent_apply]
  by_contra hi
  have hstrict : (1 : ℕ) < d i := by have := hpos i; omega
  have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hpos j)
    ⟨i, Finset.mem_univ i, hstrict⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
  omega

end Erdos3

end

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

omit [Fintype ι] in
theorem SquarefreeIndex.support_subset_of_add (a b c : SquarefreeIndex ι)
    (h : a.val + b.val = c.val) : a.val.support ⊆ c.val.support := by
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  have ha := Finsupp.mem_support_iff.mp hi
  have hs := congrArg (fun u : ι →₀ ℕ => u i) h
  simp only [Finsupp.add_apply] at hs
  omega

abbrev SquarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ) :=
  {p : SquarefreeIndex ι × SquarefreeIndex ι //
    p.1.val + p.2.val = c.val ∧ blockDegree π p.1.val = a ∧ blockDegree π p.2.val = b}

theorem squarefreeSplit_ext (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p q : SquarefreeSplit π c a b) (h : p.val.1 = q.val.1) : p = q := by
  apply Subtype.ext
  apply Prod.ext h
  apply Subtype.ext
  have hs := p.property.1.trans q.property.1.symm
  rw [h] at hs
  exact add_left_cancel hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ σ : Type*}

def SquarefreeIndex.permute (e : ι ≃ κ) : SquarefreeIndex ι ≃ SquarefreeIndex κ where
  toFun a := ⟨Finsupp.equivMapDomain e a.val, fun j => a.property (e.symm j)⟩
  invFun b := ⟨Finsupp.equivMapDomain e.symm b.val, fun i => b.property (e i)⟩
  left_inv a := Subtype.ext ((Finsupp.equivCongrLeft e).left_inv a.val)
  right_inv b := Subtype.ext ((Finsupp.equivCongrLeft e).right_inv b.val)

@[simp] theorem SquarefreeIndex.permute_apply (e : ι ≃ κ) (a : SquarefreeIndex ι) (j : κ) :
    (permute e a).val j = a.val (e.symm j) := rfl

theorem SquarefreeIndex.permute_disjoint (e : ι ≃ κ) (a b : SquarefreeIndex ι) :
    Disjoint (permute e a).val.support (permute e b).val.support ↔
      Disjoint a.val.support b.val.support := Finset.disjoint_map e.toEmbedding

theorem SquarefreeIndex.permute_disjointAdd (e : ι ≃ κ) (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    permute e (a.disjointAdd b hab) =
      (permute e a).disjointAdd (permute e b) ((permute_disjoint e a b).mpr hab) := by
  apply Subtype.ext
  ext j
  rfl

theorem SquarefreeIndex.permute_zero_iff (e : ι ≃ κ) (a : SquarefreeIndex ι) :
    (permute e a).val = 0 ↔ a.val = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun c : κ →₀ ℕ => c (e i)) h
    simpa only [permute_apply, Equiv.symm_apply_apply, Finsupp.zero_apply] using hi
  · intro h
    ext j
    simp only [permute_apply, h, Finsupp.zero_apply]

theorem SquarefreeIndex.permute_blockDegree [Fintype ι] (π : ι → σ)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockDegree π (permute e a).val = blockDegree π a.val := by
  classical
  ext i
  simp only [blockDegree_apply, permute_apply]
  calc
    (∑ j, if π j = i then a.val (e.symm j) else 0) =
        ∑ j, if π (e j) = i then a.val j else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp e (fun j => if π j = i then a.val (e.symm j) else 0)).symm
    _ = _ := by simp only [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

noncomputable def blockExponent (π : ι → σ) (a : ι →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (blockDegree π a)

@[simp] theorem blockExponent_apply (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockExponent π a i = blockDegree π a i := rfl

@[simp] theorem blockExponent_zero (π : ι → σ) : blockExponent π 0 = 0 := by
  ext i
  simp only [blockExponent_apply, blockDegree_zero, Pi.zero_apply, Finsupp.zero_apply]

theorem blockExponent_permute (π : ι → σ) (e : Equiv.Perm ι)
    (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockExponent π (SquarefreeIndex.permute e a).val = blockExponent π a.val := by
  ext i
  simp only [blockExponent_apply, SquarefreeIndex.permute_blockDegree π e he a]

def multidegreeFactorial (a : σ → ℕ) : ℕ := ∏ i, (a i).factorial

theorem multidegreeFactorial_pos (a : σ → ℕ) : 0 < multidegreeFactorial a :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (a i)

end Erdos3

end

section

namespace Erdos3

theorem SquarefreeIndex.permute_weight {ι κ : Type*} (e : ι ≃ κ)
    (a : SquarefreeIndex ι) (x : ι → ℚ) :
    ((permute e a).val.prod fun j n => x (e.symm j) ^ n) =
      a.val.prod (fun i n => x i ^ n) := by
  change (Finsupp.equivMapDomain e a.val).prod _ = _
  rw [Finsupp.prod_equivMapDomain]
  simp only [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def blockSplitMultiplicity (a b : σ → ℕ) : ℕ := ∏ i, (a i + b i).choose (a i)

theorem multidegreeFactorial_split (a b : σ → ℕ) :
    multidegreeFactorial a * multidegreeFactorial b * blockSplitMultiplicity a b =
      multidegreeFactorial (a + b) := by
  simp only [multidegreeFactorial, blockSplitMultiplicity, ← Finset.prod_mul_distrib, Pi.add_apply]
  apply Finset.prod_congr rfl
  intro i _
  have h := Nat.add_choose_mul_factorial_mul_factorial (b i) (a i)
  rw [Nat.add_comm (b i) (a i)] at h
  calc
    (a i).factorial * (b i).factorial * (a i + b i).choose (a i) =
        (a i + b i).choose (a i) * (b i).factorial * (a i).factorial := by ac_rfl
    _ = _ := h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def squarefreeSplitSubsetEquiv (π : ι → σ) (c : SquarefreeIndex ι)
    (a b : σ → ℕ) (hc : blockDegree π c.val = a + b) :
    SquarefreeSplit π c a b ≃
      {T : Finset ι // T ⊆ c.val.support ∧ ∀ i, (T.filter fun j => π j = i).card = a i} where
  toFun p := ⟨p.val.1.val.support, by
    refine ⟨SquarefreeIndex.support_subset_of_add _ _ _ p.property.1, ?_⟩
    intro i
    rw [← SquarefreeIndex.blockDegree_support π p.val.1 i, p.property.2.1]⟩
  invFun T := by
    let u := SquarefreeIndex.ofFinset T.val
    let v := SquarefreeIndex.ofFinset (c.val.support \ T.val)
    have huv : u.val + v.val = c.val := by
      have h := SquarefreeIndex.ofFinset_add_complement T.val c.val.support T.property.1
      simpa only [SquarefreeIndex.ofFinset_support] using h
    have hu : blockDegree π u.val = a := by
      ext i
      exact (SquarefreeIndex.blockDegree_ofFinset π T.val i).trans (T.property.2 i)
    have hv : blockDegree π v.val = b := by
      have h := congrArg (blockDegree π) huv
      rw [blockDegree_add, hu, hc] at h
      exact add_left_cancel h
    exact ⟨(u, v), huv, hu, hv⟩
  left_inv p := squarefreeSplit_ext π c a b _ _ (SquarefreeIndex.ofFinset_support p.val.1)
  right_inv T := Subtype.ext (SquarefreeIndex.support_ofFinset T.val)

theorem card_squarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (hc : blockDegree π c.val = a + b) :
    Fintype.card (SquarefreeSplit π c a b) = blockSplitMultiplicity a b := by
  classical
  rw [Fintype.card_congr (squarefreeSplitSubsetEquiv π c a b hc), card_blockSubsets]
  unfold blockSplitMultiplicity
  apply Finset.prod_congr rfl
  intro i _
  rw [← SquarefreeIndex.blockDegree_support π c i, hc, Pi.add_apply]

omit [Fintype σ] [DecidableEq ι] [DecidableEq σ] in
theorem squarefreeSplit_degree (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p : SquarefreeSplit π c a b) : blockDegree π c.val = a + b := by
  rw [← p.property.1, blockDegree_add, p.property.2.1, p.property.2.2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultilinearSlicePolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem squarefree_polynomial_expansion {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) :
    P = ∑ S : Finset ι, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val
      (P.coeff (SquarefreeIndex.ofFinset S).val) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : SquarefreeExponent d
  · have he : (SquarefreeIndex.ofFinset d.support).val = d :=
      congrArg Subtype.val (SquarefreeIndex.ofFinset_support ⟨d,hd⟩)
    rw [Finset.sum_eq_single d.support]
    · simp [he]
    · intro S _ hS
      have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
        intro h
        apply hS
        have hs := congrArg Finsupp.support h
        rwa [SquarefreeIndex.support_ofFinset] at hs
      simp [hne]
    · simp
  · have hz : P.coeff d = 0 := by
      by_contra h
      exact hd (hP d (MvPolynomial.mem_support_iff.mpr h))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro S _
    have hne : (SquarefreeIndex.ofFinset S).val ≠ d := by
      intro h
      exact hd (h ▸ (SquarefreeIndex.ofFinset S).property)
    simp [hne]

theorem squarefree_polynomial_eval {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : MvPolynomial ι R)
    (hP : ∀ d ∈ P.support, SquarefreeExponent d) (x : ι → R) :
    MvPolynomial.eval x P = ∑ S : Finset ι, P.coeff (SquarefreeIndex.ofFinset S).val *
      ∏ i, if i ∈ S then x i else 1 := by
  conv_lhs => rw [squarefree_polynomial_expansion P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [SquarefreeIndex.ofFinset_apply]
  split_ifs <;> simp

theorem multiaffinePolynomial_eval {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → R) :
    MvPolynomial.eval x P =
      multiaffineExpansion (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x := by
  exact squarefree_polynomial_eval P
    (fun d hd i => (MvPolynomial.le_degreeOf_of_mem_support i hd).trans (hP i)) x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def subsetPolynomial {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) : MvPolynomial I R :=
  ∑ S, MvPolynomial.monomial (SquarefreeIndex.ofFinset S).val (c S)

theorem subsetPolynomial_coefficient {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (S : Finset I) :
    (subsetPolynomial c).coeff (SquarefreeIndex.ofFinset S).val = c S := by
  simp only [subsetPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    have hne : (SquarefreeIndex.ofFinset T).val ≠ (SquarefreeIndex.ofFinset S).val := by
      intro h
      apply hT
      simpa only [SquarefreeIndex.support_ofFinset] using congrArg Finsupp.support h
    simp [hne]
  · simp

theorem subsetPolynomial_degree {I R : Type*} [Fintype I] [CommRing R]
    (c : Finset I → R) (i : I) : (subsetPolynomial c).degreeOf i ≤ 1 := by
  unfold subsetPolynomial
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro S _
  by_cases hc : c S = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc]
    exact (SquarefreeIndex.ofFinset S).property i

theorem subsetPolynomial_eval {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (c : Finset I → R) (x : I → R) :
    MvPolynomial.eval x (subsetPolynomial c) = ∑ S, c S * ∏ i ∈ S, x i := by
  rw [subsetPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_pow]
  have he : (fun i => x i ^ (SquarefreeIndex.ofFinset S).val i) =
      (fun i => if i ∈ S then x i else 1) := by
    funext i
    rw [SquarefreeIndex.ofFinset_apply]
    split_ifs <;> simp
  rw [he, Finset.prod_ite_mem_eq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def multilinearSlicePolynomial {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    MvPolynomial (Fin n) R := subsetPolynomial (fun S => F (S.piecewise w b))

theorem multilinearSlicePolynomial_eval {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (x : Fin n → R) :
    MvPolynomial.eval x (multilinearSlicePolynomial F b w) =
      F (fun i => b i + x i • w i) := by
  rw [multilinearSlicePolynomial, subsetPolynomial_eval]
  exact (multilinear_affine_expansion F b w x).symm

theorem multilinearSlicePolynomial_degree {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) (i : Fin n) :
    (multilinearSlicePolynomial F b w).degreeOf i ≤ 1 := subsetPolynomial_degree _ _

theorem multilinearSlicePolynomial_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) R) (b w : Fin n → M) :
    (multilinearSlicePolynomial F b w).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = F w := by
  rw [multilinearSlicePolynomial, subsetPolynomial_coefficient, Finset.piecewise_univ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineOptionExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multiaffineExpansion_affine {n : ℕ} (a b : Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    multiaffineExpansion (fun S => a S*t+b S) x =
      multiaffineExpansion a x*t + multiaffineExpansion b x := by
  unfold multiaffineExpansion
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem optionLinearCoefficient_squarefree {n : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℝ) (hP : ∀ i, P.degreeOf i ≤ 1) (j : ℕ) :
    ∀ d ∈ ((MvPolynomial.optionEquivLeft ℝ (Fin n) P).coeff j).support,
      SquarefreeExponent d := by
  intro d hd i
  have hd' : d.optionElim j ∈ P.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft ℝ).mp hd
  have h := (MvPolynomial.le_degreeOf_of_mem_support (some i) hd').trans (hP (some i))
  simpa using h

theorem multiaffineOption_eval {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun i => Option.elim i t x) P =
      multiaffineExpansion
        (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)*t +
          P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)) x := by
  let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) P
  have hQ : Q.natDegree ≤ 1 := by
    rw [MvPolynomial.natDegree_optionEquivLeft]
    exact hP none
  have he (j : ℕ) : MvPolynomial.eval x (Q.coeff j) =
      multiaffineExpansion (fun S => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim j)) x := by
    rw [squarefree_polynomial_eval (Q.coeff j) (optionLinearCoefficient_squarefree P hP j)]
    simp only [multiaffineExpansion, Q, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [MvPolynomial.optionEquivLeft_elim_eval, multiaffineExpansion_affine]
  change Polynomial.eval t (Polynomial.map (MvPolynomial.eval x) Q) = _
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hQ]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [he 1, he 0]

theorem optionSquarefree_full_exponent {n : ℕ} :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val.optionElim 1 =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val := by
  ext i
  cases i <;> simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePolynomialBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_real_phase_double_mean_le_one {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X → Y → ℝ) :
    ‖𝔼 x, 𝔼 y, character (F x y : CircleFourier.Circle)‖ ≤ 1 := by
  calc
    _ ≤ 𝔼 x, ‖𝔼 y, character (F x y : CircleFourier.Circle)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 𝔼 x, 𝔼 y, ‖character (F x y : CircleFourier.Circle)‖ :=
      Finset.expect_le_expect (fun x _ => RCLike.norm_expect_le (K := ℂ))
    _ = 1 := by simp

theorem multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin n → ℕ) (M : ℕ)
    (u : Fin n → ℝ) (w : ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : (∀ i, Fin (N i)), 𝔼 t : Fin M,
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hMp⟩⟩
  have hζ1 : ζ ≤ 1 := hbias.trans (norm_real_phase_double_mean_le_one _)
  let a := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 1)
  let b := fun S : Finset (Fin n) => P.coeff ((SquarefreeIndex.ofFinset S).val.optionElim 0)
  have hphase (x : ∀ i, Fin (N i)) (t : Fin M) :
      character ((MvPolynomial.eval
        (fun i => Option.elim i (w+(t.val : ℝ)) (fun j => u j+((x j).val : ℝ))) P : ℝ) :
        CircleFourier.Circle) = multiaffineIntervalPhase a b u w x t := by
    rw [multiaffineOption_eval P hP]
    rfl
  simp_rw [hphase] at hbias
  have h := multiaffine_bias_approximation N M a b u w hζ hζ1 hN hM hbias
  simpa only [a, optionSquarefree_full_exponent] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrideProductBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem full_mixed_difference_of_totalDegree {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : P.totalDegree ≤ n) (u v : Fin n → R) :
    additiveBoxDifference n (fun x (_ : Unit) => eval x P) u v () =
      P.coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  have he : (fun x (_ : Unit) => eval x P) =
      (fun x (_ : Unit) => ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i) := by
    funext x _
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, eval_monomial, Finsupp.prod_pow]
  rw [he, additiveBoxDifference_sum]
  have hm (d : Fin n →₀ ℕ) :
      additiveBoxDifference n (fun x (_ : Unit) => P.coeff d * ∏ i, x i ^ d i) u v () =
        P.coeff d * ∏ i, (u i ^ d i - v i ^ d i) :=
    additiveBoxDifference_product n (fun _ : Unit => P.coeff d) (fun i x => x ^ d i) u v ()
  simp_rw [hm]
  rw [Finset.sum_eq_single (fullShiftExponent n)]
  · simp only [fullShiftExponent_apply, pow_one]
  · intro d hd hne
    obtain ⟨i, hi⟩ := (exponent_eq_full_or_missing d ((le_totalDegree hd).trans hP)).resolve_left hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, pow_zero, sub_self]), mul_zero]
  · intro hnot
    rw [notMem_support_iff.mp hnot, zero_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def diagonalMultiaffineScaling {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  subsetPolynomial (fun S => P.coeff (SquarefreeIndex.ofFinset S).val * ∏ i ∈ S, s i)

theorem diagonalMultiaffineScaling_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) (i : Fin n) : (diagonalMultiaffineScaling P s).degreeOf i ≤ 1 :=
  subsetPolynomial_degree _ _

theorem diagonalMultiaffineScaling_top {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) :
    (diagonalMultiaffineScaling P s).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val * ∏ i, s i := by
  exact subsetPolynomial_coefficient _ _

theorem diagonalMultiaffineScaling_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (s x : Fin n → ℝ) :
    MvPolynomial.eval x (diagonalMultiaffineScaling P s) =
      MvPolynomial.eval (fun i => s i*x i) P := by
  rw [diagonalMultiaffineScaling, subsetPolynomial_eval, multiaffinePolynomial_eval P hP]
  unfold multiaffineExpansion
  simp only [Finset.prod_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fullSquarefreeExponent_map_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset ι)).val.mapDomain e =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset κ)).val := by
  ext j
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [Finsupp.mapDomain_apply e.injective]
  simp [SquarefreeIndex.ofFinset_apply]

theorem fin_multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+((x i).val : ℝ)) P : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
  let e := _root_.finSuccEquiv n
  let Q := MvPolynomial.rename e P
  have hQ : ∀ j, Q.degreeOf j ≤ 1 := by
    intro j
    obtain ⟨i,rfl⟩ := e.surjective j
    rw [MvPolynomial.degreeOf_rename_of_injective e.injective]
    exact hP i
  have heval (x : ∀ i : Fin n, Fin (N i.succ)) (t : Fin (N 0)) :
      MvPolynomial.eval
        (fun j => Option.elim j (u 0+(t.val : ℝ)) (fun i => u i.succ+((x i).val : ℝ))) Q =
      MvPolynomial.eval
        (fun i => u i+(((Fin.cons t x : ∀ j : Fin (n+1), Fin (N j)) i).val : ℝ)) P := by
    rw [MvPolynomial.eval_rename]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  rw [expect_dependent_fin_cons, Finset.expect_comm] at hbias
  simp_rw [← heval] at hbias
  have h := multiaffine_polynomial_bias Q hQ (fun i => N i.succ) (N 0)
    (fun i => u i.succ) (u 0) hζ (fun i => hN i.succ) (hN 0) hbias
  have hcoeff : Q.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val := by
    rw [← fullSquarefreeExponent_map_equiv e, MvPolynomial.coeff_rename_mapDomain e e.injective]
  simpa only [hcoeff, Fin.prod_univ_succ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fin_multiaffine_strided_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N s : Fin (n+1) → ℕ) (hs : ∀ i, 0 < s i)
    (u : Fin (n+1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/D| ≤ multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ)*(N i : ℝ)) := by
  let A := diagonalMultiaffineScaling P (fun i => (s i : ℝ))
  have hsr : ∀ i, (0 : ℝ) < s i := fun i => by exact_mod_cast hs i
  have heval (x : ∀ i, Fin (N i)) :
      MvPolynomial.eval (fun i => u i/(s i : ℝ)+((x i).val : ℝ)) A =
      MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P := by
    rw [diagonalMultiaffineScaling_eval P hP]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    rw [mul_add, mul_div_cancel₀ _ (hsr i).ne']
  obtain ⟨q,hq,hqQ,m,hm⟩ := fin_multiaffine_polynomial_bias A
    (diagonalMultiaffineScaling_degree P _) N (fun i => u i/(s i : ℝ)) hζ hN
    (by simpa only [heval] using hbias)
  let S := ∏ i, s i
  have hSp : 0 < S := Finset.prod_pos (fun i _ => hs i)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hSp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have happrox : |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
      (S : ℝ)-(m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
    simpa only [A, diagonalMultiaffineScaling_top, S, Nat.cast_prod] using hm
  refine ⟨q*S,Nat.mul_pos hq hSp,?_,m,?_⟩
  · simpa only [Nat.cast_mul, S, Nat.cast_prod] using mul_le_mul_of_nonneg_right hqQ hSr.le
  · have he : P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/(q*S : ℕ) =
        (P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
          (S : ℝ)-(m : ℝ)/q)/S := by
      push_cast
      field_simp
    rw [he, abs_div, abs_of_pos hSr]
    apply (div_le_div_of_nonneg_right happrox hSr.le).trans_eq
    rw [div_div, Finset.prod_mul_distrib]
    simp only [S, Nat.cast_prod]
    congr 1
    ring

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_slice_bias_approximation {M : Type*} [AddCommGroup M] [Module ℝ M]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => M) ℝ)
    (b w : Fin (n + 1) → M) (N s : Fin (n + 1) → ℕ)
    (hs : ∀ i, 0 < s i) (u : Fin (n + 1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((F (fun i => b i + (u i + (s i : ℝ) * ((x i).val : ℝ)) • w i) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |F w - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ) * (N i : ℝ)) := by
  have hb : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i + (s i : ℝ) * ((x i).val : ℝ))
        (multilinearSlicePolynomial F b w) : ℝ) : CircleFourier.Circle)‖ := by
    simpa only [multilinearSlicePolynomial_eval] using hbias
  have h := fin_multiaffine_strided_bias (multilinearSlicePolynomial F b w)
    (multilinearSlicePolynomial_degree F b w) N s hs u hζ hN hb
  simpa only [multilinearSlicePolynomial_top] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultilinearBoxInverse
namespace OAI

section

namespace Erdos3

open scoped Classical

def stridedMatrixPoint {H I : Type*} {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) : H → I → ℝ :=
  fun i k => b i k + (s k : ℝ) * ((x i k).val : ℝ)

noncomputable def stridedMatrixSliceBase {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) (j : H → I) : H → I → ℝ :=
  fun i => Function.update (stridedMatrixPoint b s x i) (j i) (b i (j i))

theorem stridedMatrixPoint_update {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (y : H → ∀ k, Fin (N k)) (j : H → I)
    (x : ∀ i, Fin (N (j i))) :
    stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i)) =
      fun i => stridedMatrixSliceBase b s y j i +
        ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [stridedMatrixPoint, stridedMatrixSliceBase]
  · simp [stridedMatrixPoint, stridedMatrixSliceBase, hk]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_box_biased_slice {I : Type*} [Fintype I] [DecidableEq I] {h : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin h => I → ℝ) ℝ)
    (N s : I → ℕ) (hN : ∀ k, 0 < N k) (b : Fin h → I → ℝ)
    (j : Fin h → I) {ζ : ℝ}
    (hbias : ζ ≤ ‖𝔼 x : Fin h → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖) :
    ∃ c : Fin h → I → ℝ, ζ ≤ ‖𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (fun i => c i + ((s (j i) : ℝ) * ((x i).val : ℝ)) •
        Pi.single (j i) (1 : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hN k⟩⟩
  obtain ⟨y, hy⟩ := exists_biased_matrix_coordinate_slice (H := Fin h) (I := I)
    (fun k => Fin (N k)) j
    (fun x : Fin h → ∀ k, Fin (N k) =>
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle))
    (δ := ζ) hbias
  refine ⟨stridedMatrixSliceBase b s y j, ?_⟩
  have he : (𝔼 x : ∀ i, Fin (N (j i)),
      character ((F (stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i))) : ℝ) :
        CircleFourier.Circle)) =
      𝔼 x : ∀ i, Fin (N (j i)),
        character ((F (fun i => stridedMatrixSliceBase b s y j i +
          ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ)) : ℝ) :
            CircleFourier.Circle) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg (fun v : Fin h → I → ℝ => character ((F v : ℝ) : CircleFourier.Circle))
      (stridedMatrixPoint_update b s y j x)
  exact hy.trans_eq (congrArg norm he)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) (b : Fin (n + 1) → I → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      character ((F (stridedMatrixPoint b s x) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  obtain ⟨c, hc⟩ := multilinear_box_biased_slice F N s hNp b j hbias
  apply multilinear_slice_bias_approximation F c
    (fun i => Pi.single (j i) (1 : ℝ)) (fun i => N (j i)) (fun i => s (j i))
    (fun i => hs (j i)) (fun _ => 0) hζ (fun i => hN (j i))
  simpa only [zero_add] using hc

theorem paired_multilinear_box_coordinate_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖)
    (j : Fin (n + 1) → I) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ) ∧
      ∃ m : ℤ, |F (fun i => Pi.single (j i) (1 : ℝ)) - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hNp k⟩⟩
  rw [Finset.expect_comm] at hbias
  obtain ⟨y, hy⟩ := exists_biased_finite_slice
    (fun y x : Fin (n + 1) → ∀ k, Fin (N k) =>
      character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)) hbias
  let b : Fin (n + 1) → I → ℝ := fun i k => -((s k : ℝ) * ((y i k).val : ℝ))
  have he (x : Fin (n + 1) → ∀ k, Fin (N k)) :
      stridedMatrixPoint b s x = fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
        (s k : ℝ) * ((y i k).val : ℝ) := by
    funext i k
    dsimp [stridedMatrixPoint, b]
    ring
  apply multilinear_box_coordinate_approximation F N s hs b hζ hN _ j
  simpa only [he] using hy

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TopSupportSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem mem_weightedSupportLE_one_iff {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (d : ℕ) :
    P ∈ weightedSupportLE (1 : σ → ℕ) d ↔ P.totalDegree ≤ d := by
  simpa only [weightedTotalDegree_one] using mem_weightedSupportLE_iff (1 : σ → ℕ) d P

theorem weightedSupportLT_aeval {σ τ R : Type*} [CommRing R]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLT w d) :
    aeval f P ∈ weightedSupportLT v d := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT v d).sum_mem
  intro a ha b hb
  have hap : Finsupp.weight w a < d := hP ha
  exact (weightedSupportLE_aeval_monomial w v f hf a _ hb).trans_lt hap

theorem polynomialTranslate_sub_mem_weightedSupportLT {σ R : Type*} [CommRing R]
    (base : σ → R) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {P : MvPolynomial σ R} {d : ℕ} (hP : P ∈ weightedSupportLE w d) :
    polynomialTranslate base P - P ∈ weightedSupportLT w d := by
  have hexp : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : R) := by
    simpa only [smul_monomial, smul_eq_mul, mul_one] using P.as_sum
  have he := congrArg (fun Q => polynomialTranslate base Q - Q) hexp
  simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub] at he
  rw [he]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  apply (weightedSupportLT w d).smul_mem
  intro b hb
  have hap : Finsupp.weight w a ≤ d := hP ha
  exact ((polynomialTranslate_monomial_bounds base w hw a).2 hb).trans_le hap

theorem fullShiftExponent_weight (n : ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) = n := by
  simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
    fullShiftExponent_sum n

theorem full_coefficient_zero_of_lower_support {R : Type*} [CommRing R] {n : ℕ}
    {P : MvPolynomial (Fin n) R} (hP : P ∈ weightedSupportLT (1 : Fin n → ℕ) n) :
    P.coeff (fullShiftExponent n) = 0 := by
  by_contra hn
  have hlt : Finsupp.weight (1 : Fin n → ℕ) (fullShiftExponent n) < n :=
    hP (mem_support_iff.mpr hn)
  rw [fullShiftExponent_weight] at hlt
  exact (lt_irrefl n) hlt

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineShiftPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def affineShiftCoordinate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) : MvPolynomial (Fin n) ℝ :=
  C (base i) + ∑ j, C (direction j i) * X j

noncomputable def affineShiftPullback {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (affineShiftCoordinate base direction)

theorem affineShiftPullback_eval {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (t : Fin n → ℝ) :
    eval t (affineShiftPullback base direction P) =
      eval (fun i => base i + ∑ j, direction j i * t j) P := by
  change (aeval t) ((aeval (affineShiftCoordinate base direction)) P) =
    (aeval (fun i => base i + ∑ j, direction j i * t j)) P
  rw [comp_aeval_apply]
  simp only [affineShiftCoordinate, map_add, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self_apply]

theorem affineShiftCoordinate_degree {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) :
    (affineShiftCoordinate base direction i).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp only [totalDegree_C, zero_le]
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)

theorem affineShiftPullback_degree {I : Type*} {n d : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ d) :
    (affineShiftPullback base direction P).totalDegree ≤ d := by
  simpa only [affineShiftPullback, aeval_eq_eval₂Hom, algebraMap_eq, Nat.mul_one] using polynomial_substitution_totalDegree_le P
    (affineShiftCoordinate base direction) (affineShiftCoordinate_degree base direction) hP

theorem affineShift_full_difference {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      (affineShiftPullback base direction P).coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  simpa only [affineShiftPullback_eval] using full_mixed_difference_of_totalDegree
    (affineShiftPullback base direction P) (affineShiftPullback_degree base direction P hP) u v

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineTopCoefficient
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem affineShiftPullback_translate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (P : MvPolynomial I ℝ) :
    affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P) =
      affineShiftPullback base direction P := by
  have he : (affineShiftPullback (fun _ => 0) direction).comp (polynomialTranslate base) =
      affineShiftPullback base direction := by
    apply algHom_ext
    intro i
    simp [AlgHom.comp_apply, polynomialTranslate_X, affineShiftPullback,
      affineShiftCoordinate, add_comm]
  exact AlgHom.congr_fun he P

theorem affineShift_full_coefficient_base {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback (fun _ => 0) direction P).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate (fun _ => 0) direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hp := (mem_weightedSupportLE_one_iff P n).mpr hP
  have ht := polynomialTranslate_sub_mem_weightedSupportLT base (1 : I → ℕ)
    (fun _ => by simp) hp
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate (fun _ => 0) direction) hc ht
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback (fun _ => 0) direction (polynomialTranslate base P - P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub, affineShiftPullback_translate] at hz
  exact sub_eq_zero.mp hz

theorem sub_topComponent_mem_lowerSupport {I R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    P - homogeneousComponent n P ∈ weightedSupportLT (1 : I → ℕ) n := by
  intro a ha
  change Finsupp.weight (1 : I → ℕ) a < n
  have hne : (P - homogeneousComponent n P).coeff a ≠ 0 := mem_support_iff.mp ha
  simp only [coeff_sub, coeff_homogeneousComponent] at hne
  by_cases hd : a.degree = n
  · simp only [hd, ite_true, sub_self, ne_eq, not_true_eq_false] at hne
  · have haP : P.coeff a ≠ 0 := by
      intro hz
      simp only [hz, hd, ite_false, sub_self, ne_eq, not_true_eq_false] at hne
    have hle : Finsupp.weight (1 : I → ℕ) a ≤ n :=
      (mem_weightedSupportLE_one_iff P n).mpr hP (mem_support_iff.mpr haP)
    have hn : Finsupp.weight (1 : I → ℕ) a ≠ n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
    omega

theorem affineShift_full_coefficient_top {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    (affineShiftPullback base direction P).coeff (fullShiftExponent n) =
      (affineShiftPullback base direction (homogeneousComponent n P)).coeff (fullShiftExponent n) := by
  have hc (i : I) : affineShiftCoordinate base direction i ∈
      weightedSupportLE (1 : Fin n → ℕ) ((1 : I → ℕ) i) :=
    (mem_weightedSupportLE_one_iff _ 1).mpr (affineShiftCoordinate_degree _ _ _)
  have hl := weightedSupportLT_aeval (1 : I → ℕ) (1 : Fin n → ℕ)
    (affineShiftCoordinate base direction) hc (sub_topComponent_mem_lowerSupport P hP)
  have hz := full_coefficient_zero_of_lower_support hl
  change (affineShiftPullback base direction (P - homogeneousComponent n P)).coeff
    (fullShiftExponent n) = 0 at hz
  rw [map_sub, coeff_sub] at hz
  exact sub_eq_zero.mp hz

noncomputable def polynomialTopSymbol {I : Type*} (n : ℕ) (P : MvPolynomial I ℝ)
    (direction : Fin n → I → ℝ) : ℝ :=
  (affineShiftPullback (fun _ => 0) direction (homogeneousComponent n P)).coeff (fullShiftExponent n)

theorem affineShift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      polynomialTopSymbol n P direction * ∏ i, (u i - v i) := by
  rw [affineShift_full_difference base direction P hP,
    affineShift_full_coefficient_base base direction P hP,
    affineShift_full_coefficient_top (fun _ => 0) direction P hP]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

noncomputable def integerSiteValue {K V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (tuple : K → V) : V := ∑ k, site k • tuple k

noncomputable def rowShiftedTuple {h : ℕ} {K X V : Type*} [AddCommGroup V]
    (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) (k : K) : V := base k + ∑ i, rows i k • shift (x i)

theorem rowShiftedSite_eq {h : ℕ} {K X V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) :
    integerSiteValue site (rowShiftedTuple base rows shift x) =
      shiftedBoxSite (integerSiteValue site base) (fun i => ∑ k, rows i k * site k) shift x := by
  unfold integerSiteValue rowShiftedTuple shiftedBoxSite
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_smul, mul_comm]

theorem row_shifted_site_phase_cauchySchwarz {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (site : S → K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (phase : (K → V) → ℝ) (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖ := by
  simpa only [rowShiftedSite_eq] using shifted_site_phase_cauchySchwarz hh
    (fun s => integerSiteValue (site s) base) (fun s i => ∑ k, rows i k * site s k)
    shift hzero (fun x => phase (rowShiftedTuple base rows shift x)) test htest

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem vector_shift_difference_eq_topSymbol {I : Type*} {n : ℕ}
    (base : I → ℝ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u v : Fin n → I → ℝ) :
    additiveBoxDifference n
      (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P) u v () =
      polynomialTopSymbol n P (fun i k => u i k - v i k) := by
  let f : Fin n → ℝ → I → ℝ := fun i t k => v i k + (u i k - v i k) * t
  have hu : (fun i => f i 1) = u := by
    funext i k
    dsimp [f]
    ring
  have hv : (fun i => f i 0) = v := by
    funext i k
    dsimp [f]
    ring
  have he := additiveBoxDifference_map n f
    (fun (w : Fin n → I → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, w i k) P)
    (fun _ => 1) (fun _ => 0) ()
  rw [hu, hv] at he
  rw [← he]
  have hfun :
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => base k + ∑ i, f i (t i) k) P) =
      (fun (t : Fin n → ℝ) (_ : Unit) => eval (fun k => (base k + ∑ i, v i k) +
        ∑ i, (u i k - v i k) * t i) P) := by
    funext t z
    apply congrArg (fun point : I → ℝ => eval point P)
    funext k
    simp only [f, Finset.sum_add_distrib]
    ring
  rw [hfun]
  simpa only [sub_zero, Finset.prod_const_one, mul_one] using
    affineShift_difference_eq_topSymbol (fun k => base k + ∑ i, v i k)
      (fun i k => u i k - v i k) P hP (fun _ => 1) (fun _ => 0)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem row_shift_difference_eq_topSymbol {K J X : Type*} {h : ℕ}
    (base : K → J → ℝ) (rows : Fin h → K → ℤ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h) (u v : Fin h → X) :
    additiveBoxDifference h
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) u v () =
      polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) := by
  let f : Fin h → X → (K × J) → ℝ := fun i x z => (rows i z.1 : ℝ) * shift x z.2
  have he :
      (fun x (_ : Unit) => eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P) =
      (fun x (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, f i (x i) z) P) := by
    funext x t
    apply congrArg (fun point : (K × J) → ℝ => eval point P)
    funext z
    simp only [rowShiftedTuple, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, f]
    simp only [zsmul_eq_mul]
  rw [he]
  have hm := additiveBoxDifference_map h f
    (fun (w : Fin h → (K × J) → ℝ) (_ : Unit) => eval (fun z => base z.1 z.2 + ∑ i, w i z) P)
    u v ()
  exact hm.trans (by simpa only [f, mul_sub] using
    (vector_shift_difference_eq_topSymbol
      (fun z => base z.1 z.2) P hP (fun i => f i (u i)) (fun i => f i (v i))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialTranslate_add_apply {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialTranslate u (polynomialTranslate v P) = polynomialTranslate (u + v) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

noncomputable def polynomialDifference {I R : Type*} [CommRing R] (u : I → R) :
    MvPolynomial I R →ₗ[R] MvPolynomial I R :=
  (polynomialTranslate u).toLinearMap - LinearMap.id

theorem polynomialDifference_apply {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) :
    polynomialDifference u P = polynomialTranslate u P - P := rfl

theorem polynomialDifference_commute {I R : Type*} [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) :
    polynomialDifference u (polynomialDifference v P) =
      polynomialDifference v (polynomialDifference u P) := by
  simp only [polynomialDifference_apply, map_sub, polynomialTranslate_add_apply]
  rw [add_comm u v]
  abel

theorem polynomialDifference_degree {I R : Type*} [CommRing R]
    (u : I → R) (P : MvPolynomial I R) {d : ℕ} (hP : P.totalDegree ≤ d + 1) :
    (polynomialDifference u P).totalDegree ≤ d := by
  have hd := polynomialTranslate_sub_mem_weightedSupportLT u (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P (d + 1)).mpr hP)
  apply (mem_weightedSupportLE_one_iff _ d).mp
  intro a ha
  have hlt : Finsupp.weight (1 : I → ℕ) a < d + 1 := hd ha
  change Finsupp.weight (1 : I → ℕ) a ≤ d
  omega

theorem polynomialDifference_eval {I R : Type*} [CommRing R]
    (u x : I → R) (P : MvPolynomial I R) :
    eval x (polynomialDifference u P) = eval (x + u) P - eval x P := by
  rw [polynomialDifference_apply, map_sub]
  change aeval x (polynomialTranslate u P) - eval x P = _
  rw [polynomialTranslate, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C, Algebra.algebraMap_self_apply]
  rfl

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem degree_le_one_eq_constant_add_row {I R : Type*} [Fintype I] [CommRing R]
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + rowPolynomial (polynomialLinearRow P) := by
  have he : P = C (P.coeff 0) + homogeneousComponent 1 P := by
    have hd : P.totalDegree = 0 ∨ P.totalDegree = 1 := by omega
    rcases hd with hd | hd
    · rw [homogeneousComponent_eq_zero 1 P (by omega), add_zero]
      exact totalDegree_eq_zero_iff_eq_C.mp hd
    · simpa [hd, Finset.sum_range_succ] using (sum_homogeneousComponent P).symm
  have hr : polynomialLinearRow (homogeneousComponent 1 P) = polynomialLinearRow P := by
    funext i
    simp only [polynomialLinearRow, coeff_homogeneousComponent, Finsupp.degree_single, ite_true]
  exact he.trans (congrArg (fun Q => C (P.coeff 0) + Q)
    ((homogeneous_eq_rowPolynomial _ (homogeneousComponent_isHomogeneous 1 P)).trans
      (congrArg rowPolynomial hr)))

theorem polynomialDifference_C {I R : Type*} [CommRing R] (u : I → R) (c : R) :
    polynomialDifference u (C c) = 0 := by
  rw [polynomialDifference_apply, polynomialTranslate_C, sub_self]

theorem polynomialDifference_row {I R : Type*} [Fintype I] [CommRing R]
    (u a : I → R) :
    polynomialDifference u (rowPolynomial a) = C (∑ i, a i * u i) := by
  simp only [polynomialDifference_apply, rowPolynomial, map_sum, map_mul,
    polynomialTranslate_C, polynomialTranslate_X, mul_add,
    add_sub_cancel_left]

theorem polynomialDifference_affine {I R : Type*} [Fintype I] [CommRing R]
    (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference u P = C (∑ i, polynomialLinearRow P i * u i) := by
  conv_lhs => rw [degree_le_one_eq_constant_add_row P hP]
  rw [map_add, polynomialDifference_C, zero_add, polynomialDifference_row]

theorem polynomialDifference_direction_add {I R : Type*} [Fintype I] [CommRing R]
    (u v : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (u + v) P = polynomialDifference u P + polynomialDifference v P := by
  simp only [polynomialDifference_affine _ P hP, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, map_add]

theorem polynomialDifference_direction_smul {I R : Type*} [Fintype I] [CommRing R]
    (c : R) (u : I → R) (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    polynomialDifference (c • u) P = c • polynomialDifference u P := by
  rw [polynomialDifference_affine _ P hP, polynomialDifference_affine _ P hP,
    smul_eq_C_mul, ← map_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Erdos3

namespace Erdos3

noncomputable def polynomialIterDifference {I R : Type*} [CommRing R] :
    (n : ℕ) → MvPolynomial I R → (Fin n → I → R) → MvPolynomial I R
  | 0, P, _ => P
  | n + 1, P, u => polynomialIterDifference n (polynomialDifference (u 0) P) (Fin.tail u)

theorem polynomialIterDifference_commute {I R : Type*} [CommRing R] (n : ℕ)
    (v : I → R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (polynomialDifference v P) u =
      polynomialDifference v (polynomialIterDifference n P u) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference]
    rw [polynomialDifference_commute, ih]

theorem polynomialIterDifference_degree {I R : Type*} [CommRing R] (n d : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + d) (u : Fin n → I → R) :
    (polynomialIterDifference n P u).totalDegree ≤ d := by
  induction n generalizing P d with
  | zero => simpa only [polynomialIterDifference, zero_add] using hP
  | succ n ih =>
    exact ih d _ (polynomialDifference_degree (u 0) P (by omega)) (Fin.tail u)

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [Fintype I] [CommRing R] [Fintype R]

omit [Fintype I] [Fintype R] in

theorem totalDegree_sub_top_component_le (n : ℕ) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ n + 1) :
    (P - homogeneousComponent (n + 1) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ n).mp
  intro a ha
  have hcoeff : (P - homogeneousComponent (n + 1) P).coeff a ≠ 0 :=
    Finsupp.mem_support_iff.mp ha
  rw [coeff_sub, coeff_homogeneousComponent] at hcoeff
  have hne : a.degree ≠ n + 1 := by
    intro h
    exact hcoeff (by simp [h])
  have haP : a ∈ P.support := by
    apply mem_support_iff.mpr
    simpa only [if_neg hne, sub_zero] using hcoeff
  have hbound := (mem_weightedSupportLE_one_iff P (n + 1)).mpr hP haP
  change Finsupp.weight (fun _ : I => 1) a ≤ n + 1 at hbound
  change Finsupp.weight (fun _ : I => 1) a ≤ n
  rw [← Finsupp.degree_eq_weight_one] at hbound ⊢
  omega

end Erdos3

namespace Erdos3

open scoped Classical

theorem polynomialIterDifference_update_add {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (a b : I → R),
        polynomialIterDifference n P (Function.update u j (a + b)) =
          polynomialIterDifference n P (Function.update u j a) +
            polynomialIterDifference n P (Function.update u j b) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j a b
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_add a b _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j a b

theorem polynomialIterDifference_update_smul {I R : Type*} [Fintype I] [CommRing R] (n : ℕ) :
    ∀ (P : MvPolynomial I R), P.totalDegree ≤ n →
      ∀ (u : Fin n → I → R) (j : Fin n) (c : R) (a : I → R),
        polynomialIterDifference n P (Function.update u j (c • a)) =
          c • polynomialIterDifference n P (Function.update u j a) := by
  induction n with
  | zero => intro P hP u j; exact Fin.elim0 j
  | succ n ih =>
    intro P hP u j c a
    cases j using Fin.cases with
    | zero =>
      simp only [polynomialIterDifference, Function.update_self, Fin.tail_update_zero,
        polynomialIterDifference_commute]
      exact polynomialDifference_direction_smul c a _
        (polynomialIterDifference_degree n 1 P hP (Fin.tail u))
    | succ j =>
      simp only [polynomialIterDifference, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      exact ih _ (polynomialDifference_degree (u 0) P hP) (Fin.tail u) j c a

noncomputable def polynomialIterDifferenceMultilinear {I R : Type*} [Fintype I] [CommRing R]
    (n : ℕ) (P : MvPolynomial I R) (hP : P.totalDegree ≤ n) :
    MultilinearMap R (fun _ : Fin n => I → R) (MvPolynomial I R) :=
  MultilinearMap.mk' (polynomialIterDifference n P)
    (polynomialIterDifference_update_add n P hP) (polynomialIterDifference_update_smul n P hP)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

noncomputable def polynomialCommonScale (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  aeval (fun i => C c * X i)

noncomputable def polynomialAffineClass (r : I → R) (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  (polynomialCommonScale c).comp (polynomialTranslate r)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem polynomialIterDifference_eval {I R : Type*} [CommRing R] (n : ℕ)
    (P : MvPolynomial I R) (u : Fin n → I → R) (base : I → R) :
    eval base (polynomialIterDifference n P u) =
      additiveBoxDifference n
        (fun (w : Fin n → I → R) (_ : Unit) => eval (fun j => base j + ∑ i, w i j) P)
        u (fun _ => 0) () := by
  induction n generalizing P with
  | zero => simp [polynomialIterDifference, additiveBoxDifference]
  | succ n ih =>
    simp only [polynomialIterDifference, additiveBoxDifference]
    rw [ih]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_add]
    apply congrArg (fun F : (Fin n → I → R) → Unit → R =>
      additiveBoxDifference n F (Fin.tail u) (fun _ => 0) ())
    funext w t
    rw [polynomialDifference_eval]
    apply congrArg (fun value : R => value - eval (fun j => base j + ∑ i, w i j) P)
    apply congrArg (fun point : I → R => eval point P)
    funext j
    simp only [Pi.add_apply]
    ring

theorem polynomialIterDifference_topSymbol {I : Type*} (n : ℕ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n)
    (u : Fin n → I → ℝ) (base : I → ℝ) :
    eval base (polynomialIterDifference n P u) = polynomialTopSymbol n P u := by
  rw [polynomialIterDifference_eval]
  simpa only [Pi.zero_apply, sub_zero] using
    vector_shift_difference_eq_topSymbol base P hP u (fun _ => 0)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def modularRankDecayExponent (s : ℕ) (C : ℝ) : ℝ :=
  C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)

def modularRankChargeFactor (s : ℕ) : ℕ := 4 * s * (2 ^ s * s.factorial)

noncomputable def primePowerHomogeneousRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V (ZMod (p ^ A))) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem totalDegree_map_le {V R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (F : MvPolynomial V R) : (map φ F).totalDegree ≤ F.totalDegree := by
  unfold totalDegree
  apply Finset.sup_le
  intro m hm
  exact le_totalDegree (support_map_subset φ F hm)

noncomputable def integerPolynomialRankProbability
    {V J : Type*} [Fintype V] [Fintype J]
    (p B n : ℕ) [NeZero p]
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) : ℝ :=
  𝔼 u : Fin n → V → ZMod (p ^ B),
    if polynomialLinearRow (polynomialIterDifference n
      (polynomialCharacterRow row (fun i =>
        map (Int.castRingHom (ZMod (p ^ B)))
          (homogeneousComponent (n + 1) (F i)))) u) = 0 then 1 else 0

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem primePower_crt_coprime {L : Type*} (p A : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) :
    Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)) := by
  intro l k hlk
  exact Nat.coprime_pow_primes (A l) (A k) (hp l) (hp k) (hinj.ne hlk)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerPolynomialLaw (p A : L → ℕ) [∀ l, NeZero (p l)] :
    FiniteProbabilityWeights (∀ l, V → ZMod (p l ^ A l)) :=
  FiniteProbabilityWeights.pi (fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))

noncomputable def crtPrimePowerPolynomialMap {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Fin s) (i : J j) : ZMod (∏ l, p l ^ A l) :=
  eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
    (crtInput (fun l => p l ^ A l) hq
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)

noncomputable def crtPolynomialCharge (p b e : L → ℕ) (s : ℕ) (C : ℝ) : ℝ :=
  (∏ l, ((p l ^ (b l + e l) : ℕ) : ℝ)) ^
    (modularRankDecayExponent s C * modularRankChargeFactor s)

end Erdos3

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

noncomputable def polynomialTopSymbolMultilinear {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (MvPolynomial.aeval (fun _ : I => (0 : ℝ))).toLinearMap.compMultilinearMap
    (polynomialIterDifferenceMultilinear n P hP)

theorem polynomialTopSymbolMultilinear_apply {I : Type*} [Fintype I]
    (n : ℕ) (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u : Fin n → I → ℝ) :
    polynomialTopSymbolMultilinear n P hP u = polynomialTopSymbol n P u := by
  change MvPolynomial.eval (fun _ => 0) (polynomialIterDifference n P u) = _
  exact polynomialIterDifference_topSymbol n P hP u _

end Erdos3

end

section

namespace Erdos3

noncomputable def rowDirectionLinear {K I : Type*} (a : K → ℝ) :
    (I → ℝ) →ₗ[ℝ] ((K × I) → ℝ) :=
  LinearMap.pi (fun z => a z.1 • LinearMap.proj z.2)

noncomputable def rowTopSymbolMultilinear {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n) (a : Fin n → K → ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => I → ℝ) ℝ :=
  (polynomialTopSymbolMultilinear n P hP).compLinearMap (fun i => rowDirectionLinear (a i))

theorem rowTopSymbolMultilinear_apply {K I : Type*} [Fintype K] [Fintype I]
    (n : ℕ) (P : MvPolynomial (K × I) ℝ) (hP : P.totalDegree ≤ n)
    (a : Fin n → K → ℝ) (u : Fin n → I → ℝ) :
    rowTopSymbolMultilinear n P hP a u =
      polynomialTopSymbol n P (fun i z => a i z.1 * u i z.2) := by
  change polynomialTopSymbolMultilinear n P hP (fun i => rowDirectionLinear (a i) (u i)) = _
  rw [polynomialTopSymbolMultilinear_apply]
  rfl

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_common_approximation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ a : (Fin (n + 1) → I) → ℤ, ∀ j,
        |F (fun i => Pi.single (j i) (1 : ℝ)) - (a j : ℝ) / D| ≤
          multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)) := by
  exact exists_common_rational_approximations_varying (I := Fin (n + 1) → I)
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)))
    (fun j : Fin (n + 1) → I => multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))
    (fun j : Fin (n + 1) → I =>
      multiaffineBiasBudget n ζ / ∏ i, ((s (j i) : ℝ) * (N (j i) : ℝ)))
    (fun j : Fin (n + 1) → I =>
      paired_multilinear_box_coordinate_approximation F N s hs hζ hN hbias j)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem tensorDenominatorBound_le {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I]
    {B S : ℝ} (hB : 0 ≤ B) (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (hS : ∀ i, s i ≤ S) :
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ (B * S ^ Fintype.card H) ^ (Fintype.card I ^ Fintype.card H) := by
  have hj (j : H → I) : (∏ i, s (j i)) ≤ S ^ Fintype.card H := by
    calc
      (∏ i, s (j i)) ≤ ∏ _i : H, S := Finset.prod_le_prod (fun i _ => hs (j i)) (fun i _ => hS (j i))
      _ = S ^ Fintype.card H := by simp
  calc
    (∏ j : H → I, (B * ∏ i, s (j i))) ≤ ∏ _j : H → I, (B * S ^ Fintype.card H) :=
      Finset.prod_le_prod (fun j _ => mul_nonneg hB (Finset.prod_nonneg (fun i _ => hs (j i))))
        (fun j _ => mul_le_mul_of_nonneg_left (hj j) hB)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_coeff_bound {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    {B : ℝ} (hB : 0 ≤ B) (hθ : ∀ j, |θ j| ≤ B / ∏ i, T (j i))
    (α : I →₀ ℕ) :
    |(tensorDiagonalPolynomial θ).coeff α| ≤
      (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  rw [tensorDiagonalPolynomial_eq_sum_monomial]
  simp only [MvPolynomial.coeff_sum]
  have hj (j : Fin h → I) :
      |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        B / monomialScale T α := by
    by_cases he : productBlockExponent j = α
    · simpa [he, ← monomialScale_productBlockExponent j T] using hθ j
    · simp only [MvPolynomial.coeff_monomial, he, ite_false, abs_zero]
      exact div_nonneg hB (monomialScale_pos T hT α).le
  calc
    |∑ j : Fin h → I, (MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| ≤
        ∑ j : Fin h → I, |(MvPolynomial.monomial (productBlockExponent j) (θ j)).coeff α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin h → I, B / monomialScale T α := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [mul_div_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_rational_split {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ) :
    tensorDiagonalPolynomial θ = tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D) +
      MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) (tensorDiagonalPolynomial m) := by
  rw [tensorDiagonalPolynomial_map, ← tensorDiagonalPolynomial_mul, ← tensorDiagonalPolynomial_add]
  congr 1
  funext j
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem tensorDiagonalPolynomial_approximation {I : Type*} [Fintype I] {h : ℕ}
    (θ : (Fin h → I) → ℝ) (m : (Fin h → I) → ℤ) (D : ℕ)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 0 ≤ B)
    (hθ : ∀ j, |θ j - (m j : ℝ) / D| ≤ B / ∏ i, T (j i)) :
    ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
      tensorDiagonalPolynomial θ = E + MvPolynomial.C (1 / (D : ℝ)) *
        MvPolynomial.map (Int.castRingHom ℝ) Q ∧
      ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ h * B / monomialScale T α := by
  exact ⟨tensorDiagonalPolynomial (fun j => θ j - (m j : ℝ) / D),
    tensorDiagonalPolynomial m, tensorDiagonalPolynomial_rational_split θ m D,
    tensorDiagonalPolynomial_coeff_bound _ T hT hB hθ⟩

theorem integerPolynomialQuotient_coeff {I : Type*} (D : ℕ) (Q : MvPolynomial I ℤ)
    (α : I →₀ ℕ) :
    (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q).coeff α =
      ((Q.coeff α : ℤ) : ℝ) / D := by
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensor_product_scale_le {I : Type*} {h : ℕ} (T H : I → ℝ)
    (hH : ∀ i, 0 ≤ H i) {A : ℝ} (hscale : ∀ i, H i ≤ A * T i)
    (j : Fin h → I) :
    (∏ i, H (j i)) ≤ A ^ h * ∏ i, T (j i) := by
  calc
    (∏ i, H (j i)) ≤ ∏ i, (A * T (j i)) :=
      Finset.prod_le_prod (fun i _ => hH (j i)) (fun i _ => hscale (j i))
    _ = _ := by simp [Finset.prod_mul_distrib]

theorem tensor_entry_bound_rescale {I : Type*} {h : ℕ}
    (f : (Fin h → I) → ℝ) (T H : I → ℝ)
    (hT : ∀ i, 0 < T i) (hH : ∀ i, 0 < H i) {A B : ℝ}
    (hscale : ∀ i, H i ≤ A * T i) (hB : 0 ≤ B)
    (hf : ∀ j, |f j| ≤ B / ∏ i, T (j i)) :
    ∀ j, |f j| ≤ (A ^ h * B) / ∏ i, H (j i) := by
  intro j
  apply (hf j).trans
  apply (div_le_div_iff₀ (Finset.prod_pos (fun i _ => hT (j i)))
    (Finset.prod_pos (fun i _ => hH (j i)))).mpr
  calc
    B * ∏ i, H (j i) ≤ B * (A ^ h * ∏ i, T (j i)) :=
      mul_le_mul_of_nonneg_left (tensor_product_scale_le T H (fun i => (hH i).le) hscale j) hB
    _ = (A ^ h * B) * ∏ i, T (j i) := by ring

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem paired_multilinear_polynomial_approximation {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => I → ℝ) ℝ)
    (P : MvPolynomial I ℝ) (hP : ∀ w, MvPolynomial.eval w P = F (fun _ => w))
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((F (fun i k => (s k : ℝ) * ((x i k).val : ℝ) -
          (s k : ℝ) * ((y i k).val : ℝ)) : ℝ) : CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ (n + 1) *
          (A ^ (n + 1) * multiaffineBiasBudget n ζ) / monomialScale H α := by
  obtain ⟨D, hD, hDb, m, hm⟩ := paired_multilinear_common_approximation F N s hs hζ hN hbias
  have hT (k : I) : 0 < (s k : ℝ) * (N k : ℝ) := by
    exact mul_pos (Nat.cast_pos.mpr (hs k)) ((multiaffineBiasBudget_pos n hζ).trans_le (hN k))
  have hmH := tensor_entry_bound_rescale
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ)) - (m j : ℝ) / D)
    (fun k => (s k : ℝ) * (N k : ℝ)) H hT hH hscale (multiaffineBiasBudget_pos n hζ).le hm
  obtain ⟨E, Q, hE, hcoeff⟩ := tensorDiagonalPolynomial_approximation
    (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) m D
    H hH (mul_nonneg (pow_nonneg hA _) (multiaffineBiasBudget_pos n hζ).le) hmH
  have he : P = tensorDiagonalPolynomial
      (fun j : Fin (n + 1) → I => F (fun i => Pi.single (j i) (1 : ℝ))) := by
    apply MvPolynomial.funext
    intro w
    rw [hP, tensorDiagonalPolynomial_multilinear_eval]
  exact ⟨D, hD, hDb, E, Q, he.trans hE, hcoeff⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialRationalApproximationMono
namespace OAI

section

namespace Erdos3

def PolynomialRationalApproximation {I : Type*} (T : I → ℝ) (R : ℝ)
    (P : MvPolynomial I ℝ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧ ∃ Q : MvPolynomial I ℤ,
    ∀ α, |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| ≤ R / monomialScale T α

theorem polynomialRationalApproximation_of_decomposition {I : Type*}
    (T : I → ℝ) (R : ℝ) (P E : MvPolynomial I ℝ) (Q : MvPolynomial I ℤ)
    (D : ℕ) (hD : 0 < D) (hDR : (D : ℝ) ≤ R)
    (hP : P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q)
    (hE : ∀ α, |E.coeff α| ≤ R / monomialScale T α) :
    PolynomialRationalApproximation T R P := by
  refine ⟨D, hD, hDR, Q, ?_⟩
  intro α
  rw [hP, MvPolynomial.coeff_add,
    integerPolynomialQuotient_coeff, add_sub_cancel_right]
  exact hE α

end Erdos3

end

section

namespace Erdos3

theorem PolynomialRationalApproximation.mono {I : Type*}
    {T : I → ℝ} {R S : ℝ} {P : MvPolynomial I ℝ}
    (h : PolynomialRationalApproximation T R P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : PolynomialRationalApproximation T S P := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  exact ⟨D, hD, hDR.trans hRS, Q, fun α =>
    (hQ α).trans (div_le_div_of_nonneg_right hRS (monomialScale_pos T hT α).le)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalApproximationScaling
namespace OAI

section

namespace Erdos3

theorem PolynomialRationalApproximation.nat_smul {I : Type*} {T : I → ℝ} {R : ℝ}
    {P : MvPolynomial I ℝ} (h : PolynomialRationalApproximation T R P)
    (q : ℕ) (hq : 0 < q) :
    PolynomialRationalApproximation T ((q : ℝ) * R) ((q : ℝ) • P) := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨D, hD, hDR.trans (by nlinarith), (q : ℤ) • Q, ?_⟩
  intro α
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    |(q : ℝ) * P.coeff α - ((q : ℝ) * ((Q.coeff α : ℤ) : ℝ)) / D| =
        (q : ℝ) * |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| := by
      rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ (q : ℝ) * (R / monomialScale T α) :=
      mul_le_mul_of_nonneg_left (hQ α) (Nat.cast_nonneg q)
    _ = ((q : ℝ) * R) / monomialScale T α := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ ι R : Type*} [CommRing R]

theorem polynomialHom_preserves_weightedDegree (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p ∈ weightedSupportLE w n := by
  rw [MvPolynomial.aeval_unique F]
  exact weightedSupportLE_aeval v w _ hF hp

noncomputable def coordinateShearHom (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) :
    MvPolynomial τ R →ₐ[R] MvPolynomial τ R := by
  classical
  exact aeval (Function.update X i (X i + rename f Q))

theorem coordinateShearHom_X [DecidableEq τ] (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) (j : τ) :
    coordinateShearHom i f Q (X j) =
      Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q) j := by
  classical
  by_cases h : j = i
  · subst j
    simp only [coordinateShearHom, MvPolynomial.aeval_X, Function.update_self]
  · simp [coordinateShearHom, Function.update, h]

theorem coordinateShearHom_rename (i : τ) (f : σ → τ) (Q : MvPolynomial σ R)
    (g : ι → τ) (hg : ∀ j, g j ≠ i) (P : MvPolynomial ι R) :
    coordinateShearHom i f Q (rename g P) = rename g P := by
  classical
  rw [coordinateShearHom, MvPolynomial.aeval_rename]
  have he : (Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q)) ∘ g = X ∘ g := by
    funext j
    exact Function.update_of_ne (hg j) _ _
  rw [he, ← MvPolynomial.rename_eq_aeval]

theorem coordinateShearHom_comp_neg (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) :
    (coordinateShearHom i f Q).comp (coordinateShearHom i f (-Q)) = AlgHom.id R _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  change coordinateShearHom i f Q (coordinateShearHom i f (-Q) (X j)) = X j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self, map_add, coordinateShearHom_X, Function.update_self,
      coordinateShearHom_rename i f Q f hf, map_neg]
    exact add_neg_cancel_right (X i) (rename f Q)
  · rw [Function.update_of_ne h, coordinateShearHom_X, Function.update_of_ne h]

noncomputable def coordinateShearEquiv (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) : MvPolynomial τ R ≃ₐ[R] MvPolynomial τ R :=
  AlgEquiv.ofAlgHom (coordinateShearHom i f Q) (coordinateShearHom i f (-Q))
    (coordinateShearHom_comp_neg i f hf Q)
    (by simpa only [neg_neg] using coordinateShearHom_comp_neg i f hf (-Q))

theorem coordinateShearHom_degree (w : τ → ℕ) (i : τ) (f : σ → τ)
    (Q : MvPolynomial σ R) (hQ : rename f Q ∈ weightedSupportLE w (w i))
    {P : MvPolynomial τ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    coordinateShearHom i f Q P ∈ weightedSupportLE w n := by
  classical
  apply polynomialHom_preserves_weightedDegree w w _ _ hP
  intro j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self]
    exact (weightedSupportLE w (w i)).add_mem (weightedSupportLE_X w i) hQ
  · rw [Function.update_of_ne h]
    exact weightedSupportLE_X w j

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

theorem earlierSlot_ne_self (i : Fin d) (j : Fin i.val) : earlierSlot i j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  change j.val = i.val at hv
  omega

theorem exists_triangularPolynomialEquiv_prefix (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_⟩
      · intro i
        rw [if_neg (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [if_neg (by change ¬ n < n; omega),
            if_pos (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [if_pos hi, if_pos (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [if_neg hi, if_neg (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)

theorem exists_triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = X i + rename (earlierSlot i) (Q i)) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  obtain ⟨E, hE, hd, hi⟩ := exists_triangularPolynomialEquiv_prefix w Q hQ d le_rfl
  refine ⟨E, ?_, hd, hi⟩
  intro i
  simpa only [if_pos i.isLt] using hE i

noncomputable def triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R :=
  Classical.choose (exists_triangularPolynomialEquiv w Q hQ)

theorem triangularPolynomialEquiv_X (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (i : Fin d) :
    triangularPolynomialEquiv w Q hQ (X i) = X i + rename (earlierSlot i) (Q i) :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).1 i

theorem triangularPolynomialEquiv_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    triangularPolynomialEquiv w Q hQ p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.1 m p hp

theorem triangularPolynomialEquiv_inverse_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    (triangularPolynomialEquiv w Q hQ).symm p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.2 m p hp

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_lt_succ {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLT w (d + 1) :=
  fun _ ha => Nat.lt_succ_iff.mpr (hp ha)

theorem weightedSupportLT_map (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLT v n) :
    F p ∈ weightedSupportLT w n := by
  cases n with
  | zero =>
      rw [weightedSupportLT_zero_eq hp, map_zero]
      exact Submodule.zero_mem _
  | succ n =>
      exact weightedSupportLE_lt_succ (polynomialHom_preserves_weightedDegree v w F hF
        (weightedSupportLT_succ_le hp))

theorem weightedComparison_mul (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hGp : G p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - G p ∈ weightedSupportLT w d)
    (hdq : F q - G q ∈ weightedSupportLT w e) :
    F (p * q) - G (p * q) ∈ weightedSupportLT w (d + e) := by
  rw [map_mul, map_mul,
    show F p * F q - G p * G q = (F p - G p) * F q + G p * (F q - G q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hGp hdq)

theorem weightedComparison_monomial_one (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - G (monomial a 1) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - G (monomial (Finsupp.single i n) 1) ∈
        weightedSupportLT w (n * v i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - G 1 ∈ _
        rw [map_one, map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
          (X i) (n * v i) (v i) (polynomialHom_preserves_weightedDegree v w G hG hp)
          (hF i) ih (hD i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - G 1 ∈ weightedSupportLT w 0
      rw [map_one, map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial v a (1 : R)
      have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight v (Finsupp.single i n)) (Finsupp.weight v a)
        (polynomialHom_preserves_weightedDegree v w G hG hp)
        (polynomialHom_preserves_weightedDegree v w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

theorem weightedComparison_monomial (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - G (monomial a r) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  have hFc : F (C r) = C r := F.commutes r
  have hGc : G (C r) = C r := G.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, map_mul, map_mul, hFc, hGc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedComparison_monomial_one v w F G hF hG hD a)

theorem weightedComparison_difference (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p - G p ∈ weightedSupportLT w n := by
  classical
  change (F.toLinearMap - G.toLinearMap : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) p ∈
    weightedSupportLT w n
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w n).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha)
    (weightedComparison_monomial v w F G hF hG hD a (p.coeff a))

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem totalDegree_le_of_positive_weightedSupport (w : σ → ℕ) (hw : ∀ i, 1 ≤ w i)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) : P.totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff P n).mp
  intro α hα
  have hweight : Finsupp.weight (1 : σ → ℕ) α ≤ Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Pi.one_apply]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (α i) (hw i))
  exact hweight.trans (hP hα)

theorem coordinateShearHom_mass (i : τ) (f : σ → τ) (Q : MvPolynomial σ ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass (coordinateShearHom i f Q P) ≤ realPolynomialMass P * (1 + M) ^ n := by
  classical
  apply realPolynomialMass_substitution_le P _ (by linarith) _ hP
  intro j
  by_cases hj : j = i
  · subst j
    rw [Function.update_self]
    exact (realPolynomialMass_add_le _ _).trans (by simpa only [realPolynomialMass_X] using add_le_add (le_refl (1 : ℝ)) hQ)
  · rw [Function.update_of_ne hj, realPolynomialMass_X]
    linarith

theorem coordinateShearEquiv_inverse_mass (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass ((coordinateShearEquiv i f hf Q).symm P) ≤
      realPolynomialMass P * (1 + M) ^ n := by
  exact coordinateShearHom_mass i f (-Q) hM (by simpa only [map_neg, realPolynomialMass_neg] using hQ) hP

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {d : ℕ}

theorem exists_triangularPolynomialEquiv_prefix_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m →
        realPolynomialMass (E.symm p) ≤ realPolynomialMass p * (1 + M) ^ (m * n)) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [if_neg (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
      · intro m p hp
        change realPolynomialMass p ≤ realPolynomialMass p * (1 + M) ^ (m * 0)
        simp only [Nat.mul_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv, hEmass⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [if_neg (by change ¬ n < n; omega),
            if_pos (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [if_pos hi, if_pos (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [if_neg hi, if_neg (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
      · intro m p hp
        have hHp : H.symm p ∈ weightedSupportLE w m := by
          change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
          apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
          simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)
        have hHm : realPolynomialMass (H.symm p) ≤ realPolynomialMass p * (1 + M) ^ m :=
          coordinateShearEquiv_inverse_mass k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
            hM (hQM k) (totalDegree_le_of_positive_weightedSupport w hw hp)
        change realPolynomialMass (E.symm (H.symm p)) ≤ realPolynomialMass p * (1 + M) ^ (m * (n + 1))
        calc
          _ ≤ realPolynomialMass (H.symm p) * (1 + M) ^ (m * n) := hEmass m (H.symm p) hHp
          _ ≤ (realPolynomialMass p * (1 + M) ^ m) * (1 + M) ^ (m * n) :=
            mul_le_mul_of_nonneg_right hHm (pow_nonneg (by linarith) _)
          _ = realPolynomialMass p * (1 + M) ^ (m * (n + 1)) := by
            rw [mul_assoc, ← pow_add, show m + m * n = m * (n + 1) by ring]

theorem triangularPolynomialEquiv_inverse_mass (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) ℝ)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {M : ℝ} (hM : 0 ≤ M) (hQM : ∀ i, realPolynomialMass (rename (earlierSlot i) (Q i)) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass ((triangularPolynomialEquiv w Q hQ).symm P) ≤
      realPolynomialMass P * (1 + M) ^ (n * d) := by
  obtain ⟨E, hE, _, _, hmass⟩ :=
    exists_triangularPolynomialEquiv_prefix_mass w hw Q hQ hM hQM d le_rfl
  have he : E.toAlgHom = (triangularPolynomialEquiv w Q hQ).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change E (X i) = triangularPolynomialEquiv w Q hQ (X i)
    rw [hE, triangularPolynomialEquiv_X, if_pos i.isLt]
  have heq : E = triangularPolynomialEquiv w Q hQ :=
    AlgEquiv.ext (fun P => DFunLike.congr_fun he P)
  rw [← heq]
  exact hmass n P hP

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem weightedSupportLE_totalDegree_le_of_pos {w : σ → ℕ}
    (hw : ∀ i, 0 < w i) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P ∈ weightedSupportLE w d) : P.totalDegree ≤ d := by
  exact totalDegree_le_of_positive_weightedSupport w hw hP

theorem weightedSupportLE_of_map_injective (φ : R →+* S)
    (hφ : Function.Injective φ) {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : map φ P ∈ weightedSupportLE w d) :
    P ∈ weightedSupportLE w d := by
  intro α hα
  apply hP
  change α ∈ (map φ P).support
  change α ∈ P.support at hα
  rwa [support_map_of_injective P hφ]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def roundedIntegerPolynomial (P : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff P).mapRange round round_zero)

@[simp] theorem roundedIntegerPolynomial_coeff (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (roundedIntegerPolynomial P).coeff a = round (P.coeff a) := rfl

theorem roundedIntegerPolynomial_real_degree (P : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P) ∈ weightedSupportLE w d := by
  intro a ha
  apply hP
  change a ∈ (MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).support at ha
  change a ∈ P.support
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hp
  apply ha
  change (round (P.coeff a) : ℝ) = 0
  rw [hp, round_zero, Int.cast_zero]

theorem roundedIntegerPolynomial_remainder_bound (P : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    |(P - MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).coeff a| ≤ 1 / 2 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, roundedIntegerPolynomial_coeff]
  exact abs_sub_round (P.coeff a)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} {d : ℕ}

def slotPolynomialInput (t : σ → R) (b : Fin d → R) (i : Fin d) : σ ⊕ Fin i.val → R :=
  Sum.elim t (fun j => b (earlierSlot i j))

theorem slotPolynomialInput_update (t : σ → R) (b : Fin d → R) (i : Fin d) (c : R) :
    slotPolynomialInput t (Function.update b i c) i = slotPolynomialInput t b i := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [earlierSlot] at hv
      omega

noncomputable def slotAddShearEquiv [AddCommGroup R] (i : Fin d)
    (f : (Fin d → R) → R) (hf : ∀ b c, f (Function.update b i c) = f b) :
    (Fin d → R) ≃ (Fin d → R) where
  toFun b := Function.update b i (b i + f b)
  invFun b := Function.update b i (b i - f b)
  left_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, add_sub_cancel_right]
    · simp only [Function.update_of_ne h]
  right_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, sub_add_cancel]
    · simp only [Function.update_of_ne h]

noncomputable def polynomialSlotShear [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) : (Fin d → R) ≃ (Fin d → R) :=
  slotAddShearEquiv i (fun b => MvPolynomial.eval (slotPolynomialInput t b i) Q)
    (fun b c => by rw [slotPolynomialInput_update])

theorem polynomialSlotShear_apply [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) (b : Fin d → R) :
    polynomialSlotShear t i Q b =
      Function.update b i (b i + MvPolynomial.eval (slotPolynomialInput t b i) Q) := rfl

theorem polynomialSlotShear_cast (t : σ → ℤ) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) ℤ) (b : Fin d → ℤ) :
    (fun j => (polynomialSlotShear t i Q b j : ℝ)) =
      polynomialSlotShear (fun a => (t a : ℝ)) i (MvPolynomial.map (Int.castRingHom ℝ) Q)
        (fun j => (b j : ℝ)) := by
  have hi : (fun a => ((slotPolynomialInput t b i a : ℤ) : ℝ)) =
      slotPolynomialInput (fun a => (t a : ℝ)) (fun j => (b j : ℝ)) i := by
    funext a
    cases a <;> rfl
  have heval := MvPolynomial.map_eval (Int.castRingHom ℝ) (slotPolynomialInput t b i) Q
  change ((MvPolynomial.eval (slotPolynomialInput t b i) Q : ℤ) : ℝ) = _ at heval
  simp only [Function.comp_def, Int.coe_castRingHom] at heval
  rw [hi] at heval
  funext j
  rw [polynomialSlotShear_apply, polynomialSlotShear_apply]
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, Int.cast_add]
    rw [heval]
  · simp only [Function.update_of_ne h]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem finsupp_weight_add_function (v w : σ → ℕ) (a : σ →₀ ℕ) :
    Finsupp.weight (v + w) a = Finsupp.weight v a + Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.add_apply, smul_add,
    Finset.sum_add_distrib]

theorem weightedSupportLE_of_weight_le {v w : σ → ℕ} (hvw : ∀ i, v i ≤ w i)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p ∈ weightedSupportLE v d := by
  intro a ha
  change Finsupp.weight v a ≤ d
  apply le_trans _ (hp ha)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (a i) (hvw i))

theorem weightedTopPart_preserves_degree (v w : σ → ℕ) (n : ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    weightedHomogeneousComponent v n p ∈ weightedSupportLE w d := by
  intro a ha
  change a ∈ (weightedHomogeneousComponent v n p).support at ha
  rw [support_weightedHomogeneousComponent] at ha
  exact hp (Finset.mem_filter.mp ha).1

theorem weightedTopPart_remainder_lt (w : σ → ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p - weightedHomogeneousComponent w d p ∈ weightedSupportLT w d := by
  intro a ha
  change a ∈ (p - weightedHomogeneousComponent w d p).support at ha
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_sub, coeff_weightedHomogeneousComponent] at hc
  by_cases he : Finsupp.weight w a = d
  · exact (hc (by rw [if_pos he, sub_self])).elim
  · have hpa : p.coeff a ≠ 0 := by simpa only [if_neg he, sub_zero] using hc
    have hle : Finsupp.weight w a ≤ d := hp (MvPolynomial.mem_support_iff.mpr hpa)
    change Finsupp.weight w a < d
    omega

def patchSlotWeight {d : ℕ} (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 0) (fun j => w (earlierSlot i j))

def patchParameterWeight {d : ℕ} (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

theorem patchVariableWeight_split {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    patchVariableWeight (σ := σ) w i = patchSlotWeight w i + patchParameterWeight i := by
  funext a
  cases a <;> simp [patchVariableWeight, patchSlotWeight, patchParameterWeight]

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

noncomputable def topPart (A : PolynomialSlots σ d w) : PolynomialSlots σ d w where
  center i := weightedHomogeneousComponent (patchSlotWeight w i) (w i) (A.center i)
  degree i := weightedTopPart_preserves_degree _ _ _ (A.degree i)

theorem sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.center i - A.topPart.center i ∈ weightedSupportLT (patchSlotWeight w i) (w i) := by
  apply weightedTopPart_remainder_lt
  apply weightedSupportLE_of_weight_le _ (A.degree i)
  intro a
  cases a <;> simp [patchSlotWeight, patchVariableWeight]

theorem topPart_parameter_exponent_zero (A : PolynomialSlots σ d w) (i : Fin d)
    (a : (σ ⊕ Fin i.val) →₀ ℕ) (ha : (A.topPart.center i).coeff a ≠ 0) (j : σ) :
    a (Sum.inl j) = 0 := by
  have hs : a ∈ (weightedHomogeneousComponent (patchSlotWeight w i) (w i)
      (A.center i)).support := MvPolynomial.mem_support_iff.mpr ha
  rw [support_weightedHomogeneousComponent] at hs
  obtain ⟨hA, htop⟩ := Finset.mem_filter.mp hs
  have hdegree : Finsupp.weight (patchVariableWeight w i) a ≤ w i := A.degree i hA
  rw [patchVariableWeight_split, finsupp_weight_add_function, htop] at hdegree
  have hzero : Finsupp.weight (patchParameterWeight i) a = 0 := by omega
  have hle := Finsupp.le_weight (patchParameterWeight (σ := σ) i)
    (s := Sum.inl j) (by decide : (1 : ℕ) ≠ 0) a
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

end PolynomialSlots

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def slotPrefixLift (k i : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  aeval (PolynomialSlots.placementSubstitution id i k) R

theorem slotPrefixLift_degree (w : Fin d → ℕ) (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    slotPrefixLift k i R ∈ weightedSupportLE (patchVariableWeight w i) (w k) :=
  weightedSupportLE_aeval _ _ _
    (PolynomialSlots.placementSubstitution_degree id (fun _ => rfl) i k) hR

theorem slotPrefixLift_eval (k i : Fin d) (hki : k.val ≤ i.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ) :
    aeval (slotPolynomialInput t b i) (slotPrefixLift k i R) =
      aeval (slotPolynomialInput t b k) R := by
  rw [slotPrefixLift, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f R)
  funext v
  cases v with
  | inl a => simp only [PolynomialSlots.placementSubstitution, Sum.elim_inl,
      aeval_X, slotPolynomialInput]
  | inr j =>
      have hj : (id (earlierSlot k j)).val < i.val := lt_of_lt_of_le j.isLt hki
      simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dif_pos hj,
        aeval_X, slotPolynomialInput]
      rfl

theorem slotPrefixLift_self (k : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    slotPrefixLift k k R = R := by
  have hsub : PolynomialSlots.placementSubstitution (σ := σ) id k k = X := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
        have hj : (id (earlierSlot k j)).val < k.val := j.isLt
        simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dif_pos hj]
        rfl
  rw [slotPrefixLift, hsub, MvPolynomial.aeval_X_left_apply]

noncomputable def slotShearSubstitution (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0)

theorem slotShearSubstitution_degree (w : Fin d → ℕ) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (i : Fin d) (v : σ ⊕ Fin i.val) :
    slotShearSubstitution k R i v ∈
      weightedSupportLE (patchVariableWeight w i) (patchVariableWeight w i v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      change X (Sum.inr j) + (if earlierSlot i j = k then slotPrefixLift k i R else 0) ∈
        weightedSupportLE (patchVariableWeight w i) (w (earlierSlot i j))
      apply (weightedSupportLE _ _).add_mem (weightedSupportLE_X _ (Sum.inr j))
      by_cases h : earlierSlot i j = k
      · rw [if_pos h]
        simpa only [patchVariableWeight, Sum.elim_inr, h] using slotPrefixLift_degree w k i R hR
      · rw [if_neg h]
        exact Submodule.zero_mem _

theorem slotShearSubstitution_before (k i : Fin d) (hik : i.val ≤ k.val)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) : slotShearSubstitution k R i = X := by
  funext v
  cases v with
  | inl a => rfl
  | inr j =>
      have h : earlierSlot i j ≠ k := by
        intro h
        have hv := congrArg Fin.val h
        have hj := j.isLt
        simp only [earlierSlot] at hv
        omega
      simp only [slotShearSubstitution, Sum.elim_inr, if_neg h, add_zero]

theorem slotShearSubstitution_eval (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ)
    (v : σ ⊕ Fin i.val) :
    aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i v := by
  cases v with
  | inl a => simp only [slotShearSubstitution, Sum.elim_inl, aeval_X, slotPolynomialInput]
  | inr j =>
      by_cases h : earlierSlot i j = k
      · have hki : k.val ≤ i.val := by
          have hj : (earlierSlot i j).val < i.val := j.isLt
          rw [h] at hj
          exact hj.le
        change aeval (slotPolynomialInput t b i)
          (X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0) = _
        rw [if_pos h, map_add, aeval_X, slotPrefixLift_eval k i hki]
        simp only [slotPolynomialInput, Sum.elim_inr, polynomialSlotShear_apply,
          h, Function.update_self, MvPolynomial.aeval_eq_eval]
      · simp only [slotShearSubstitution, Sum.elim_inr, if_neg h, add_zero,
          aeval_X, slotPolynomialInput, polynomialSlotShear_apply, Function.update_of_ne h]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shear (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    PolynomialSlots σ d w where
  center i := aeval (slotShearSubstitution k R i) (A.center i) -
    if i = k then slotPrefixLift k i R else 0
  degree i := by
    apply (weightedSupportLE _ _).sub_mem
    · exact weightedSupportLE_aeval _ _ _ (slotShearSubstitution_degree w k R hR i)
        (A.degree i)
    · by_cases h : i = k
      · subst i
        rw [if_pos rfl]
        exact slotPrefixLift_degree w k k R hR
      · rw [if_neg h]
        exact Submodule.zero_mem _

theorem shear_center_before (A : PolynomialSlots σ d w) (k i : Fin d)
    (hik : i.val < k.val) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center i = A.center i := by
  have hne : i ≠ k := by intro h; subst i; exact (lt_irrefl _ hik)
  change aeval (slotShearSubstitution k R i) (A.center i) -
    (if i = k then slotPrefixLift k i R else 0) = _
  rw [slotShearSubstitution_before k i hik.le, MvPolynomial.aeval_X_left_apply,
    if_neg hne, sub_zero]

theorem shear_center_self (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center k = A.center k - R := by
  change aeval (slotShearSubstitution k R k) (A.center k) -
    (if k = k then slotPrefixLift k k R else 0) = _
  rw [slotShearSubstitution_before k k le_rfl, MvPolynomial.aeval_X_left_apply,
    if_pos rfl, slotPrefixLift_self]

theorem shear_center_eval (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    ((A.shear k R hR).slots t).center b i =
      (A.slots t).center (polynomialSlotShear t k R b) i -
        if i = k then MvPolynomial.eval (slotPolynomialInput t b k) R else 0 := by
  change aeval (slotPolynomialInput t b i)
      (aeval (slotShearSubstitution k R i) (A.center i) -
        if i = k then slotPrefixLift k i R else 0) = _
  rw [map_sub, MvPolynomial.comp_aeval_apply]
  have he : (fun v => aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v)) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i :=
    funext (slotShearSubstitution_eval k i R t b)
  rw [he]
  congr 1
  by_cases h : i = k
  · subst i
    rw [if_pos rfl, if_pos rfl, slotPrefixLift_self, MvPolynomial.aeval_eq_eval]
  · rw [if_neg h, if_neg h, map_zero]

theorem shear_integer_residual (A : PolynomialSlots σ d w) (k : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin k.val) ℤ)
    (hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
      weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℤ) (b : Fin d → ℤ) :
    ((A.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ).slots
      (fun a => (t a : ℝ))).residual b =
    (A.slots (fun a => (t a : ℝ))).residual (polynomialSlotShear t k Q b) := by
  funext i
  change (b i : ℝ) - _ = (polynomialSlotShear t k Q b i : ℝ) - _
  rw [shear_center_eval]
  have he := polynomialSlotShear_cast t k Q b
  rw [← he]
  have hi := congrFun he i
  rw [polynomialSlotShear_apply (R := ℝ)] at hi
  by_cases h : i = k
  · subst i
    simp only [Function.update_self, ite_true] at hi ⊢
    linarith
  · simp only [Function.update_of_ne h, if_neg h, sub_zero] at hi ⊢
    rw [hi]

end PolynomialSlots

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

noncomputable def slotPolynomialLift (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R) :
    MvPolynomial (σ ⊕ Fin d) R := rename (Sum.map id (earlierSlot i)) P

theorem slotPolynomialLift_degree (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLE (Sum.elim v w) n := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

theorem slotPolynomialLift_lower (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLT (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLT (Sum.elim v w) n := by
  apply weightedSupportLT_map _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

theorem slotPolynomialLift_eval (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R)
    (t : σ → R) (b : Fin d → R) :
    aeval (Sum.elim t b) (slotPolynomialLift i P) = aeval (slotPolynomialInput t b i) P := by
  rw [slotPolynomialLift, MvPolynomial.aeval_rename]
  apply congrArg (fun f => aeval f P)
  funext a
  cases a <;> rfl

namespace PolynomialSlots

variable {w : Fin d → ℕ}

noncomputable def specializeCenter (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    MvPolynomial (Fin i.val) ℝ := aeval (Sum.elim (fun a => C (t a)) X) (A.center i)

theorem specializeCenter_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.specializeCenter t i ∈ weightedSupportLE (fun j => w (earlierSlot i j)) (w i) := by
  apply weightedSupportLE_aeval _ _ _ _ (A.degree i)
  intro a
  cases a with
  | inl j => exact weightedSupportLE_C _ 1 (t j)
  | inr j => exact weightedSupportLE_X _ j

theorem specializeCenter_full_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    rename (earlierSlot i) (A.specializeCenter t i) ∈ weightedSupportLE w (w i) := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (earlierSlot i)) _
    (A.specializeCenter_degree t i)
  intro j
  rw [rename_X]
  exact weightedSupportLE_X w (earlierSlot i j)

theorem topPart_aeval_independent {S : Type*} [CommRing S] [Algebra ℝ S]
    (A : PolynomialSlots σ d w) (i : Fin d) (t u : σ → S) (b : Fin i.val → S) :
    aeval (Sum.elim t b) (A.topPart.center i) =
      aeval (Sum.elim u b) (A.topPart.center i) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro v a hv ha
  cases v with
  | inl j => exact ((Finsupp.mem_support_iff.mp hv)
      (A.topPart_parameter_exponent_zero i a ha j)).elim
  | inr j => rfl

theorem topPart_lift_specialize (A : PolynomialSlots σ d w) (i : Fin d) :
    slotPolynomialLift i (A.topPart.center i) =
      rename Sum.inr (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
  let b : Fin i.val → MvPolynomial (σ ⊕ Fin d) ℝ := fun j => X (Sum.inr (earlierSlot i j))
  have hcomp : (rename (R := ℝ) (Sum.inr : Fin d → σ ⊕ Fin d)).comp
      ((rename (earlierSlot i)).comp (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X))) =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (σ ⊕ Fin d) ℝ)) b) := by
    apply MvPolynomial.algHom_ext
    intro a
    cases a <;> simp [b]
  have he := congrArg (fun F : MvPolynomial (σ ⊕ Fin i.val) ℝ →ₐ[ℝ]
      MvPolynomial (σ ⊕ Fin d) ℝ => F (A.topPart.center i)) hcomp
  simp only [AlgHom.comp_apply] at he
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs, he, slotPolynomialLift, MvPolynomial.rename_eq_aeval]
  have hinput : (X : σ ⊕ Fin d → MvPolynomial (σ ⊕ Fin d) ℝ) ∘
      Sum.map id (earlierSlot i) = Sum.elim (fun a => X (Sum.inl a)) b := by
    funext a
    cases a <;> rfl
  rw [hinput]
  exact A.topPart_aeval_independent i _ _ b

end PolynomialSlots

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem exists_coefficient_normalized_prefix (A : PolynomialSlots σ d w) (n : ℕ) :
    n ≤ d → ∃ B : PolynomialSlots σ d w,
      (∀ i : Fin d, i.val < n → ∀ a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  induction n with
  | zero =>
      intro _
      refine ⟨A, ?_, ?_⟩
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
      · intro t
        exact ⟨Equiv.refl _, fun _ => rfl⟩
  | succ n ih =>
      intro hn
      obtain ⟨B, hB, hBA⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let Q := roundedIntegerPolynomial (B.center k)
      have hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
          weightedSupportLE (patchVariableWeight w k) (w k) :=
        roundedIntegerPolynomial_real_degree (B.center k) _ _ (B.degree k)
      refine ⟨B.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ, ?_, ?_⟩
      · intro i hi a
        by_cases hik : i = k
        · subst i
          rw [shear_center_self]
          exact roundedIntegerPolynomial_remainder_bound (B.center k) a
        · have hine : i.val ≠ n := by
            intro he
            apply hik
            exact Fin.ext he
          have hil : i.val < n := by omega
          rw [shear_center_before B k i hil]
          exact hB i hil a
      · intro t
        obtain ⟨e, he⟩ := hBA t
        refine ⟨(polynomialSlotShear t k Q).trans e, ?_⟩
        intro b
        rw [shear_integer_residual]
        exact he _

theorem exists_coefficient_normalized (A : PolynomialSlots σ d w) :
    ∃ B : PolynomialSlots σ d w,
      (∀ i a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  obtain ⟨B, hB, hBA⟩ := A.exists_coefficient_normalized_prefix d le_rfl
  exact ⟨B, fun i => hB i i.isLt, hBA⟩

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rational_nat_smul_mem (M : Submodule ℤ L) {z : L} (hz : z ∈ M) (D : ℕ) :
    (D : ℚ) • z ∈ M := by
  rw [Nat.cast_smul_eq_nsmul ℚ]
  exact M.nsmul_mem hz D

theorem rightBracketList_mem_intModule (M : Submodule ℤ L)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M)
    (f : X → L) (hf : ∀ x, f x ∈ M) (xs : List X) {z : L} (hz : z ∈ M) :
    rightBracketList f xs z ∈ M := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih => exact ih (hbr z hz (f x) (hf x))

theorem dynkinWord_mem_multiple (M : Submodule ℤ L) (D : ℕ)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (f : X → L) (hf : ∀ x, f x ∈ M) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    ∃ z ∈ M, dynkinWord f w = (D : ℚ) • z := by
  have hclosed : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M := by
    intro a ha b hb
    obtain ⟨z, hz, heq⟩ := hbr a ha b hb
    rw [heq]
    exact rational_nat_smul_mem M hz D
  cases htail : w.tail with
  | nil => exact False.elim (hw htail)
  | cons x xs =>
      obtain ⟨z, hz, heq⟩ := hbr (f w.head) (hf _) (f x) (hf _)
      refine ⟨rightBracketList f xs z, rightBracketList_mem_intModule M hclosed f hf xs hz, ?_⟩
      simp only [dynkinWord, htail, rightBracketList_cons, Module.End.mul_apply,
        rightBracket_apply, heq, map_smul]

theorem lieBCH_mem_of_divisible_brackets (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hs : 1 ≤ s)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs]
  apply M.add_mem (M.add_mem ha hb)
  apply M.sum_mem
  intro w hw
  obtain ⟨hw, htail⟩ := Finset.mem_filter.mp hw
  have hf : ∀ i : Fin 2, ![a, b] i ∈ M := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨z, hz, heq⟩ := dynkinWord_mem_multiple M D hbr ![a, b] hf w htail
  obtain ⟨n, hn⟩ := hc w hw
  rw [heq, smul_smul, mul_comm _ (D : ℚ), hn, Int.cast_smul_eq_zsmul ℚ]
  exact M.smul_mem n hz

theorem lieBCH_mem_of_divisible_brackets_nilpotent (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_mem_of_divisible_brackets M D hs hbr hc ha hb
  · have hs0 : s = 0 := by omega
    subst s
    have hz : a = 0 := by
      have h : a ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using h
    rw [hz, lieBCH_zero_left hnil]
    exact hb

def intModuleBCHSubgroup (M : Submodule ℤ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ M, ∀ b ∈ M, lieBCH s a b ∈ M) :
    Subgroup (NilpotentLieBCHGroup L s hnil) where
  carrier := {g | g.coord ∈ M}
  one_mem' := M.zero_mem
  mul_mem' := by intro a b ha hb; exact hstable a.coord ha b.coord hb
  inv_mem' := by intro a ha; exact M.neg_mem ha

end Erdos3

end

section

namespace Erdos3

open Module

theorem denominator_grid_smul_mem_scaled {ι : Type*} (l m₀ m : ℕ)
    (hm : l * m₀ ∣ m) {x : ι → ℚ} (hx : x ∈ denominatorGrid l) :
    (m : ℚ) • x ∈ scaledIntegerGrid m₀ := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (k : ℤ) * z i, ?_⟩
  ext i
  have hi := hz i
  change (l : ℚ) * x i = (z i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (m₀ : ℚ) * k * ((l : ℚ) * x i) := by ring
    _ = _ := by rw [hi]; ring

theorem denominator_grid_subset_mul {ι : Type*} (l m : ℕ) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid (m * l) := by
  intro x hx
  have h := hx.nat_smul m
  simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem bchSubgroupCoordinates_repr (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (g : NilpotentLieBCHGroup L s hnil) :
    e.equivFun g.coord ∈ bchSubgroupCoordinates e Γ ↔ g ∈ Γ := by
  change (⟨e.equivFun.symm (e.equivFun g.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ ↔ _
  rw [LinearEquiv.symm_apply_apply]

theorem subgroupPowerCover_inner_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) := by
  rintro x ⟨z, rfl⟩
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))⟩
  have hg : g ∈ Γ := hinner ⟨z, rfl⟩
  have heq : e.equivFun (g ^ m).coord = ((m * l : ℕ) : ℚ) • fun i => (z i : ℚ) := by
    rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
    change (m : ℚ) • e.equivFun (e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))) = _
    rw [LinearEquiv.apply_symm_apply, smul_smul, Nat.cast_mul]
  rw [← heq]
  exact (bchSubgroupCoordinates_repr e _ _).mpr (pow_mem_subgroupPowerCover Γ hg m)

theorem subgroupPowerCover_le_of_grid (e : Basis ι ℚ L)
    (Γ Λ₀ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m₀ m : ℕ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hinner : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    (hm : l * m₀ ∣ m) : subgroupPowerCover Γ m ≤ Λ₀ := by
  apply (subgroupPowerCover_le_iff Γ Λ₀ m).mpr
  intro g hg
  apply (bchSubgroupCoordinates_repr e Λ₀ (g ^ m)).mp
  rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
  exact hinner (denominator_grid_smul_mem_scaled l m₀ m hm
    (houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)))

theorem subgroupPowerCover_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) ∧
      bchSubgroupCoordinates e (subgroupPowerCover Γ m) ⊆ denominatorGrid (m * l) := by
  refine ⟨subgroupPowerCover_inner_grid e Γ l m hinner, ?_⟩
  intro x hx
  exact denominator_grid_subset_mul l m (houter (subgroupPowerCover_le Γ m hx))

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def bchIntegralDenominatorBound (s : ℕ) : ℕ :=
  bchCoefficientHeight s ^ (bchBracketSupport s).card

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bch_stable_integral_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
        lieBCH s a b ∈ coordinateGridModule e B := by
  classical
  obtain ⟨D, hD, hDb, u, hu, _⟩ := exists_bch_integer_coefficients s
  obtain ⟨E, hE, hEb, c, hEcoeff, _⟩ := exists_bounded_integer_array
    (fun ijk : ι × (ι × ι) => lieStructureConstants e ijk.1 ijk.2.1 ijk.2.2)
    (fun ijk => hc ijk.1 ijk.2.1 ijk.2.2)
  have hEb' : E ≤ H ^ (Fintype.card ι ^ 3) := by
    simpa only [Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using hEb
  let B := (D * E) * l
  have hscaled (i j k : ι) :
      ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n := by
    refine ⟨(l : ℤ) * c (i, j, k), ?_⟩
    simp only [B, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, hEcoeff]
    ring
  refine ⟨B, Nat.mul_pos (Nat.mul_pos hD hE) hl, dvd_mul_left l (D * E),
    Nat.mul_le_mul_right l (Nat.mul_le_mul hDb hEb'), ?_⟩
  intro a ha b hb
  exact lieBCH_mem_of_divisible_brackets_nilpotent (coordinateGridModule e B) D hnil
    (fun x hx y hy => coordinateGrid_bracket_divisible e B D hscaled hx hy)
    (fun w hw => ⟨u w hw, (hu w hw).symm⟩) ha hb

def coordinateGridBCHSubgroup (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    Subgroup (NilpotentLieBCHGroup L s hnil) :=
  intModuleBCHSubgroup (coordinateGridModule e B) hnil hstable

theorem coordinateGridBCHSubgroup_coordinates (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    bchSubgroupCoordinates e (coordinateGridBCHSubgroup e B hnil hstable) = scaledIntegerGrid B := by
  ext x
  change e.equivFun (e.equivFun.symm x) ∈ scaledIntegerGrid B ↔ x ∈ scaledIntegerGrid B
  rw [LinearEquiv.apply_symm_apply]

theorem exists_integral_grid_subgroup (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
      0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl hc
  let Λ := coordinateGridBCHSubgroup e B hnil hstable
  have hcoords := coordinateGridBCHSubgroup_coordinates e B hnil hstable
  refine ⟨B, Λ, hB, hdiv, hbound, ?_, hcoords⟩
  intro g hg
  apply (bchSubgroupCoordinates_repr e Γ g).mp
  apply hinner
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← hcoords]
  exact (bchSubgroupCoordinates_repr e Λ g).mpr hg

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bchSubgroup_outer_grid_change_basis
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ N : ℕ, 0 < N ∧ bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  let A := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, ?_⟩
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨b.equivFun.symm x⟩
  have hg : g ∈ Γ := hx
  have hgrid := houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)
  have hint := integralVector_denominator_mulVec A ((l : ℚ) • e.equivFun g.coord) hgrid
  have hA : A *ᵥ e.equivFun g.coord = x := by
    dsimp only [A]
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
    exact b.equivFun.apply_symm_apply x
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Matrix.mulVec_smul, hA,
    smul_smul, Nat.cast_mul] using hint

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeAdaptedLieAlgebra
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeAdapted_lie_mem (x y : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (hy : y ∈ F.squarefreeAdaptedModule π) :
    ⁅x, y⁆ ∈ F.squarefreeAdaptedModule π := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero, zero_lie]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hb : b.val = 0
  · rw [(hy b).2 hb, map_zero, lie_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    apply F.squarefreeMonomial_mem_adapted π
    · change a.val + b.val ≠ 0
      intro he
      apply ha
      ext i
      have hi := congrArg (fun c : ι →₀ ℕ => c i) he
      simp only [Finsupp.add_apply, Finsupp.zero_apply] at hi ⊢
      omega
    · change ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ ∈
        F.layer (blockDegree π (a.val + b.val))
      rw [blockDegree_add]
      exact F.lie_mem (hx a).1 (hy b).1
  · rw [squarefreeMonomial_lie_overlap a b hab]
    exact (F.squarefreeAdaptedModule π).zero_mem

noncomputable def squarefreeAdaptedSubalgebra : LieSubalgebra ℚ (SquarefreePolynomial ι L) :=
  { F.squarefreeAdaptedModule π with
    lie_mem' := fun hx hy => F.squarefreeAdapted_lie_mem π _ _ hx hy }

abbrev SquarefreeAlgebra := ↥(F.squarefreeAdaptedSubalgebra π)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeAlgebraCoordinates
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeCoefficientLayer (a : SquarefreeIndex ι) : Submodule ℚ L := by
  classical
  exact if a.val = 0 then ⊥ else F.layer (blockDegree π a.val)

theorem mem_squarefreeCoefficientLayer (a : SquarefreeIndex ι) (v : L) :
    v ∈ F.squarefreeCoefficientLayer π a ↔
      v ∈ F.layer (blockDegree π a.val) ∧ (a.val = 0 → v = 0) := by
  classical
  by_cases ha : a.val = 0 <;> simp [squarefreeCoefficientLayer, ha, F.zero_eq_top]

noncomputable def squarefreeAlgebraEquiv :
    F.SquarefreeAlgebra π ≃ₗ[ℚ] ((a : SquarefreeIndex ι) → F.squarefreeCoefficientLayer π a) where
  toFun x a := ⟨squarefreePolynomialEquiv x.val a,
    (F.mem_squarefreeCoefficientLayer π a _).mpr (x.property a)⟩
  invFun f := ⟨squarefreePolynomialEquiv.symm (fun a => (f a).val), by
    intro a
    simpa only [LinearEquiv.apply_symm_apply] using
      (F.mem_squarefreeCoefficientLayer π a _).mp (f a).property⟩
  left_inv x := by
    apply Subtype.ext
    exact squarefreePolynomialEquiv.symm_apply_apply x.val
  right_inv f := by
    ext a
    exact congrFun (squarefreePolynomialEquiv.apply_symm_apply (fun b => (f b).val)) a
  map_add' x y := by
    ext a
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) a
  map_smul' r x := by
    ext a
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) a

theorem squarefreeAlgebraEquiv_apply (x : F.SquarefreeAlgebra π) (a : SquarefreeIndex ι) :
    (F.squarefreeAlgebraEquiv π x a).val = squarefreePolynomialEquiv x.val a := rfl

instance squarefreeAlgebraFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ (F.SquarefreeAlgebra π) :=
  FiniteDimensional.of_injective (F.squarefreeAlgebraEquiv π).toLinearMap
    (F.squarefreeAlgebraEquiv π).injective

theorem squarefreeAlgebra_finrank [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) =
      ∑ a : SquarefreeIndex ι, Module.finrank ℚ (F.squarefreeCoefficientLayer π a) := by
  rw [(F.squarefreeAlgebraEquiv π).finrank_eq, Module.finrank_pi_fintype]

theorem squarefreeAlgebra_finrank_le [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) ≤
      2 ^ Fintype.card ι * Module.finrank ℚ L := by
  rw [F.squarefreeAlgebra_finrank π]
  calc
    _ ≤ ∑ _a : SquarefreeIndex ι, Module.finrank ℚ L :=
      Finset.sum_le_sum fun a _ => (F.squarefreeCoefficientLayer π a).finrank_le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeIndex, Nat.cast_id]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreePolynomialPermutation
namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreePermute (e : ι ≃ κ) :
    SquarefreePolynomial ι L ≃ₗ[ℚ] SquarefreePolynomial κ L :=
  squarefreePolynomialEquiv.trans
    ((LinearEquiv.funCongrLeft ℚ L (SquarefreeIndex.permute e).symm).trans
      squarefreePolynomialEquiv.symm)

theorem squarefreePermute_coefficient (e : ι ≃ κ) (x : SquarefreePolynomial ι L)
    (a : SquarefreeIndex κ) :
    squarefreePolynomialEquiv (squarefreePermute e x) a =
      squarefreePolynomialEquiv x ((SquarefreeIndex.permute e).symm a) := by
  change squarefreePolynomialEquiv (squarefreePolynomialEquiv.symm _) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem squarefreePermute_monomial (e : ι ≃ κ) (a : SquarefreeIndex ι) (v : L) :
    squarefreePermute e (squarefreeMonomial a v) =
      squarefreeMonomial (SquarefreeIndex.permute e a) v := by
  apply squarefreePolynomialEquiv.injective
  ext b
  obtain ⟨b, rfl⟩ := (SquarefreeIndex.permute e).surjective b
  rw [squarefreePermute_coefficient, Equiv.symm_apply_apply]
  by_cases h : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self, squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne a b h,
      squarefreePolynomialEquiv_monomial_ne _ _
        (fun he => h ((SquarefreeIndex.permute e).injective he))]

theorem squarefreePermute_symm_apply (e : ι ≃ κ) (x : SquarefreePolynomial ι L) :
    squarefreePermute e.symm (squarefreePermute e x) = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient]
  change squarefreePolynomialEquiv x
    ((SquarefreeIndex.permute e).symm (SquarefreeIndex.permute e a)) = _
  rw [Equiv.symm_apply_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeSupportBracket
namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeSupportModule_lie_mem {P Q R : SquarefreeIndex ι → Prop}
    (h : ∀ a b (hab : Disjoint a.val.support b.val.support),
      P a → Q b → R (a.disjointAdd b hab))
    {x y : SquarefreePolynomial ι L}
    (hx : x ∈ squarefreeSupportModule P) (hy : y ∈ squarefreeSupportModule Q) :
    ⁅x, y⁆ ∈ squarefreeSupportModule R := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : P a
  · by_cases hb : Q b
    · by_cases hab : Disjoint a.val.support b.val.support
      · rw [squarefreeMonomial_lie_disjoint a b hab]
        exact squarefreeMonomial_mem_support _ (h a b hab ha hb) _
      · rw [squarefreeMonomial_lie_overlap a b hab]
        exact (squarefreeSupportModule R).zero_mem
    · rw [hy b hb, map_zero, lie_zero]
      exact (squarefreeSupportModule R).zero_mem
  · rw [hx a ha, map_zero, zero_lie]
    exact (squarefreeSupportModule R).zero_mem

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealBlockPolynomialEval
namespace OAI

section

namespace Erdos3

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def blockMonomial (π : ι → σ) (a : σ → ℕ) : L →ₗ[ℚ] SquarefreePolynomial ι L := by
  classical
  exact squarefreePolynomialEquiv.symm.toLinearMap.comp
    (LinearMap.pi fun c : SquarefreeIndex ι => if blockDegree π c.val = a then LinearMap.id else 0)

theorem blockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (blockMonomial π a x) c =
      if blockDegree π c.val = a then x else 0 := by
  classical
  simp only [blockMonomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

noncomputable def factorialBlockMonomial (π : ι → σ) (a : σ → ℕ) :
    L →ₗ[ℚ] SquarefreePolynomial ι L :=
  (multidegreeFactorial a : ℚ) • blockMonomial π a

theorem factorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (factorialBlockMonomial π a x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, map_smul, Pi.smul_apply,
    blockMonomial_coefficient, smul_ite, smul_zero]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realFactorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] L) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv ((factorialBlockMonomial π a).baseChange ℝ x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      factorialBlockMonomial_coefficient]
    by_cases h : blockDegree π c.val = a
    · simp only [h, ite_true, TensorProduct.tmul_smul]
    · simp only [h, ite_false, TensorProduct.tmul_zero]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy]
    split_ifs <;> simp only [smul_add, add_zero]

noncomputable def realBlockPolynomialEval (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) : ℝ ⊗[ℚ] SquarefreePolynomial ι L :=
  ∑ a ∈ (coefficients p).support,
    (a.prod fun i n => x i ^ n) • (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p a)

theorem realBlockPolynomialEval_coefficient (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (realBlockPolynomialEval π p x) c =
      ((blockExponent π c.val).prod fun i n => x i ^ n) •
        ((multidegreeFactorial (blockDegree π c.val) : ℚ) •
          coefficients p (blockExponent π c.val)) := by
  classical
  simp only [realBlockPolynomialEval, map_sum, Finset.sum_apply, map_rat_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (blockExponent π c.val)]
  · simp only [realFactorialBlockMonomial_coefficient, blockExponent_apply, ite_true]
  · intro a _ ha
    rw [realFactorialBlockMonomial_coefficient]
    have hca : blockDegree π c.val ≠ (fun i => a i) := by
      intro h
      apply ha
      ext i
      exact (congrFun h i).symm
    rw [if_neg hca, smul_zero]
  · intro hc
    rw [Finsupp.notMem_support_iff.mp hc, map_zero, map_zero, Pi.zero_apply, smul_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTotalDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exponent_total_eq_zero_iff (a : ι →₀ ℕ) :
    (∑ i, a i) = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hi
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    simp only [Finsupp.zero_apply, Finset.sum_const_zero]

theorem squarefreeExponent_total_le (a : SquarefreeIndex ι) :
    (∑ i, a.val i) ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => a.property i
    _ = _ := by simp

theorem squarefreeDisjointAdd_total (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    (∑ i, (a.disjointAdd b hab).val i) = (∑ i, a.val i) + ∑ i, b.val i := by
  change (∑ i, (a.val + b.val) i) = _
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogenizedModeFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem homogeneous_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial I R W} (hp : Homogeneous h p) : DegreeLE (1 : I → ℕ) h p := by
  apply (degreeLE_iff _ _ _).mpr
  intro d hd
  have he := homogeneous_support_degree hp hd
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he.le

theorem dehomogenize_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial (Option I) R W} (hp : Homogeneous h p) :
    DegreeLE (1 : I → ℕ) h (substitute dehomogenizingSubstitution p) := by
  classical
  apply degreeLE_substitute_affine _ _ p (homogeneous_degreeLE hp)
  intro i
  cases i with
  | none => simp [dehomogenizingSubstitution]
  | some i =>
    change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
    simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R)

theorem siteEvaluation_homogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (h : ℕ) (p : VectorPolynomial I R W) :
    siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) (homogenize h p) = siteEvaluation site p := by
  funext s
  exact eval_homogenize h p (site s)

theorem siteEvaluation_dehomogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (p : VectorPolynomial (Option I) R W) :
    siteEvaluation site (substitute dehomogenizingSubstitution p) =
      siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p := by
  funext s
  change eval (site s) (substitute dehomogenizingSubstitution p) = _
  rw [eval_substitute]
  apply congrArg (fun x => eval x p)
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

theorem homogeneous_site_factorization_iff {I S R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (site : S → I → R) (Λ : VectorPolynomial I R W →ₗ[R] R)
    (M : (S → W) →ₗ[R] R) :
    (∀ p, Homogeneous h p → Λ (substitute dehomogenizingSubstitution p) =
      M (siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p)) ↔
    (∀ p, DegreeLE (1 : I → ℕ) h p → Λ p = M (siteEvaluation site p)) := by
  constructor
  · intro hf p hp
    have he := hf (homogenize h p) (homogenize_homogeneous h p hp)
    rwa [dehomogenize_homogenize, siteEvaluation_homogenize] at he
  · intro hf p hp
    have he := hf (substitute dehomogenizingSubstitution p) (dehomogenize_degreeLE hp)
    rwa [siteEvaluation_dehomogenize] at he

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FactoredPolynomialCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem factored_polynomial_mode_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, DegreeLE (1 : K → ℕ) h q → Λ q = M (siteEvaluation site q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) := by
  rw [hfactor _ (degreeLE_substitute_affine f hf p hp), character_linear_site_sum]
  apply Finset.prod_congr rfl
  intro s _
  change siteFunctionalCharacter M s (eval (site s) (substitute f p)) = _
  rw [eval_substitute]

theorem homogeneously_factored_polynomial_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, Homogeneous h q → Λ (substitute dehomogenizingSubstitution q) =
      M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) :=
  factored_polynomial_mode_character h site Λ M
    ((homogeneous_site_factorization_iff h site Λ M).mp hfactor) p hp f hf

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSiteAbsorption
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_absorbed_polynomial_site_tests {A I K S G : Type*} {W : A → Type*}
    [Fintype A] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℝ)
    (Λ : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → Λ a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (f : G → I → MvPolynomial K ℝ) (hf : ∀ g i, (f g i).totalDegree ≤ 1)
    (low : G → ℝ) (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ g,
      character ((low g + ∑ a, Λ a (substitute (f g) (p a)) : ℝ) : CircleFourier.Circle) *
        (∏ s, test s (fun i => MvPolynomial.aeval (site s) (f g i))) =
      character (low g : CircleFourier.Circle) *
        (∏ s, test' s (fun i => MvPolynomial.aeval (site s) (f g i))) := by
  classical
  choose M hM using hfactor
  let χ : A → S → (I → ℝ) → ℂ := fun a s x => siteFunctionalCharacter (M a) s (eval x (p a))
  refine ⟨absorbedSiteTests χ test, ?_, ?_⟩
  · intro s x
    rw [absorbedSiteTests_norm χ (fun a s x => siteFunctionalCharacter_norm _ _ _) test]
    exact htest s x
  · intro g
    apply absorb_factored_phases χ test
      (fun g s i => MvPolynomial.aeval (site s) (f g i))
      (fun a g => Λ a (substitute (f g) (p a))) _ low g
    intro a g
    exact homogeneously_factored_polynomial_character (h a) site (Λ a) (M a) (hM a) (p a) (hp a) (f g) (hf g)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerRowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j)) : K × I → ℤ :=
  fun z => ∑ i, rows i z.1 * ((s z.2 : ℤ) * (x i z.2).val)

theorem integerRowShift_bound {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j))
    {C : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (z : K × I) :
    |(integerRowShift rows s x z : ℝ)| ≤ (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
  simp only [integerRowShift, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  calc
    |∑ i, (rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| ≤
        ∑ i, |(rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin h, C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg (s z.2))
        (Nat.cast_nonneg (x i z.2).val) : (0 : ℝ) ≤ (s z.2 : ℝ) * ((x i z.2).val : ℝ))]
      have hx : ((x i z.2).val : ℝ) ≤ (N z.2 : ℝ) := by exact_mod_cast (x i z.2).isLt.le
      exact mul_le_mul (hrows i z.1)
        (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)) (by positivity) hC
    _ = _ := by simp; ring

theorem integerRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (s : I → ℕ)
    (x : Fin h → ∀ j, Fin (N j)) (S : K × I → ℝ) (hS : ∀ z, 0 < S z)
    {C ε : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hε : 0 ≤ ε)
    (hscale : ∀ z, (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) ≤ ε * S z) :
    ‖rectangularLatticePoint 0 S (integerRowShift rows s x)‖ ≤ ε := by
  rw [rectangularLatticePoint_zero_origin]
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro z
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hS z)]
  apply (div_le_iff₀ (hS z)).mpr
  exact (integerRowShift_bound rows s x hC hrows z).trans (hscale z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def residueLatticeArray {K I : Type*} (residue : K × I → ℤ) (modulus : I → ℕ)
    (x : K × I → ℤ) : K × I → ℤ :=
  fun z => residue z + (modulus z.2 : ℤ) * x z

noncomputable def residueProfileCenter {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) : K × I → ℝ :=
  fun z => -(residue z : ℝ) / modulus z.2

noncomputable def residueProfileWidth {K I : Type*}
    (modulus : I → ℕ) (V : K × I → ℝ) : K × I → ℝ := fun z => V z / modulus z.2

theorem residueProfileWidth_pos {K I : Type*} (modulus : I → ℕ) (V : K × I → ℝ)
    (hmodulus : ∀ j, 0 < modulus j) (hV : ∀ z, 0 < V z) (z : K × I) :
    0 < residueProfileWidth modulus V z :=
  div_pos (hV z) (by exact_mod_cast hmodulus z.2)

theorem residueLatticeArray_rowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (residue : K × I → ℤ) (modulus : I → ℕ) (rows : Fin h → K → ℤ)
    (u : Fin h → ∀ j, Fin (N j)) (x : K × I → ℤ) (k : K) (j : I) :
    ((residueLatticeArray residue modulus (x + integerRowShift rows (fun _ => 1) u) (k, j) : ℤ) : ℝ) =
      rowShiftedTuple (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)) rows
        (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) u k j := by
  simp only [residueLatticeArray, integerRowShift, rowShiftedTuple, Pi.add_apply,
    Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast, Nat.cast_one, one_mul,
    Finset.sum_apply, zsmul_eq_mul]
  rw [mul_add, Finset.mul_sum, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, Pi.intCast_apply]
  ring

theorem residueRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (modulus : I → ℕ)
    (hmodulus : ∀ j, 0 < modulus j) (u : Fin h → ∀ j, Fin (N j))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    {C r : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z) :
    ‖rectangularLatticePoint 0 (residueProfileWidth modulus V)
      (integerRowShift rows (fun _ => 1) u)‖ ≤ r := by
  apply integerRowShift_normalized_bound rows (fun _ => 1) u _
    (residueProfileWidth_pos modulus V hmodulus hV) hC hrows hr
  intro z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [Nat.cast_one, one_mul, residueProfileWidth]
  rw [← mul_div_assoc, le_div_iff₀ hm]
  calc
    (h : ℝ) * C * (N z.2 : ℝ) * (modulus z.2 : ℝ) =
      (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) := by ring
    _ ≤ r * V z := hmove z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_point {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (x : K × I → ℤ) :
    rectangularLatticePoint (residueProfileCenter residue modulus) (residueProfileWidth modulus V) x =
      fun z => (residueLatticeArray residue modulus x z : ℝ) / V z := by
  funext z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [rectangularLatticePoint, residueProfileCenter, residueProfileWidth,
    residueLatticeArray, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp [hm.ne', (hV z).ne']
  ring

noncomputable def residueSmoothIndexPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  shiftedSmoothProductPMF (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
    (residueProfileWidth_pos modulus V hmodulus hV) hZ

theorem residueSmoothIndexPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  simp only [residueSmoothIndexPMF, shiftedSmoothProductPMF_toReal, shiftedSmoothProductMass,
    rectangularWeight, residueProfile_point residue modulus hmodulus V hV]

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeArray_injective {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) :
    Function.Injective (residueLatticeArray residue modulus) := by
  intro x y he
  funext z
  have hm : (modulus z.2 : ℤ) ≠ 0 := by exact_mod_cast (hmodulus z.2).ne'
  exact mul_left_cancel₀ hm (add_left_cancel (congrFun he z))

theorem residueLatticeArray_range {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (y : K × I → ℤ) :
    y ∈ Set.range (residueLatticeArray residue modulus) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z := by
  constructor
  · rintro ⟨x, rfl⟩ z
    exact ⟨x z, by simp only [residueLatticeArray, add_sub_cancel_left]⟩
  · intro h
    classical
    refine ⟨fun z => (h z).choose, ?_⟩
    funext z
    have hz := (h z).choose_spec
    change residue z + (modulus z.2 : ℤ) * (h z).choose = y z
    omega

noncomputable def residueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (K × I → ℤ) :=
  (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
    (residueLatticeArray residue modulus)

theorem residueSmoothPMF_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ
        (residueLatticeArray residue modulus x)).toReal =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) /
        ∑' y, smoothProductProfile (K × I)
          (fun z => (residueLatticeArray residue modulus y z : ℝ) / V z) := by
  rw [residueSmoothPMF, pmf_map_injective_at _ _ (residueLatticeArray_injective residue modulus hmodulus)]
  exact residueSmoothIndexPMF_toReal residue modulus hmodulus V hV hZ x

theorem residueSmoothPMF_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ)
    (hy : ¬∀ z, (modulus z.2 : ℤ) ∣ y z - residue z) :
    residueSmoothPMF residue modulus hmodulus V hV hZ y = 0 := by
  exact pmf_map_zero_off_range _ _ y (by rwa [residueLatticeArray_range])

theorem residueSmoothPMF_expectation {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (φ : (K × I → ℤ) → ℂ) :
    (∑' y, ((residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal : ℂ) * φ y) =
      ∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
        φ (residueLatticeArray residue modulus x) :=
  pmf_map_injective_expectation _ _ (residueLatticeArray_injective residue modulus hmodulus) φ

end Erdos3

end

section

namespace Erdos3

noncomputable def residueSmoothScalarPMFs {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : K × I → PMF ℤ :=
  fun z => shiftedSmoothCoefficientPMF
    (residueProfileCenter residue modulus z) (residueProfileWidth modulus V z)
    (residueProfileWidth_pos modulus V hmodulus hV z)
    (shiftedSmoothProductMass_coordinate_pos
      (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
      (residueProfileWidth_pos modulus V hmodulus hV) hZ z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_smooth_row_shift_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  apply shiftedSmoothProductPMF_shift_transfer (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) (fun _ => hΦ _)
  intro x
  simpa only [residueLatticeArray_rowShift] using
    hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem residue_smooth_row_shift_transfer_lipschitz_amplitude {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B)
    (F : (K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      (F (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) *
        Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  have ht := shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude
    (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))
    (fun _ => hΦ _) (fun x => by
      simpa only [residueLatticeArray_rowShift] using
        hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) F hF hLip
  simpa only [residueSmoothIndexPMF, residueProfile_point residue modulus hmodulus V hV]
    using ht

end Erdos3

end

section

namespace Erdos3

noncomputable def residueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (y : K × I → ℤ) : ℝ := by
  classical
  exact if ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z then
    smoothProductProfile (K × I) (fun z => (y z : ℝ) / V z) else 0

theorem residueSmoothWeight_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight residue modulus V (residueLatticeArray residue modulus x) =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) := by
  have hc := (residueLatticeArray_range residue modulus _).mp ⟨x, rfl⟩
  simp [residueSmoothWeight, hc]

theorem residueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus V) =
      ∑' y, residueSmoothWeight residue modulus V y := by
  have hs : Function.support (residueSmoothWeight residue modulus V) ⊆
      Set.range (residueLatticeArray residue modulus) := by
    intro y hy
    apply (residueLatticeArray_range residue modulus y).mpr
    by_contra hn
    exact hy (by simp only [residueSmoothWeight, hn, ite_false])
  have he := (residueLatticeArray_injective residue modulus hmodulus).tsum_eq hs
  simpa only [shiftedSmoothProductMass, rectangularWeight,
    residueProfile_point residue modulus hmodulus V hV, residueSmoothWeight_at] using he

theorem residueSmoothPMF_conditional_weight {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (y : K × I → ℤ) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ y).toReal =
      residueSmoothWeight residue modulus V y / ∑' z, residueSmoothWeight residue modulus V z := by
  classical
  by_cases hc : ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z
  · obtain ⟨x, rfl⟩ := (residueLatticeArray_range residue modulus y).mpr hc
    rw [residueSmoothWeight_at, ← residueSmoothWeight_mass residue modulus hmodulus V hV]
    have he := residueSmoothPMF_at residue modulus hmodulus V hV hZ x
    simpa only [shiftedSmoothProductMass, rectangularWeight,
      residueProfile_point residue modulus hmodulus V hV] using he
  · simp only [residueSmoothPMF_zero_off residue modulus hmodulus V hV hZ y hc,
      ENNReal.toReal_zero, residueSmoothWeight, hc, ite_false, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

abbrev ColumnResiduePattern (K I : Type*) (modulus : I → ℕ) :=
  ∀ z : K × I, ZMod (modulus z.2)

def columnResiduePattern {K I : Type*} (modulus : I → ℕ) (x : K × I → ℤ) :
    ColumnResiduePattern K I modulus := fun z => x z

noncomputable def columnResidueRepresentative {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) : K × I → ℤ :=
  fun z => (ZMod.intCast_surjective (r z)).choose

theorem columnResidueRepresentative_cast {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (z : K × I) :
    (columnResidueRepresentative modulus r z : ZMod (modulus z.2)) = r z :=
  (ZMod.intCast_surjective (r z)).choose_spec

theorem columnResiduePattern_eq_iff {K I : Type*} (modulus : I → ℕ)
    (r : ColumnResiduePattern K I modulus) (x : K × I → ℤ) :
    columnResiduePattern modulus x = r ↔
      ∀ z, (modulus z.2 : ℤ) ∣ x z - columnResidueRepresentative modulus r z := by
  constructor
  · intro he z
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, columnResidueRepresentative_cast]
    exact sub_eq_zero.mpr (congrFun he z)
  · intro h
    funext z
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h z)
    rw [Int.cast_sub, columnResidueRepresentative_cast, sub_eq_zero] at hz
    exact hz

theorem residueSmoothWeight_eq_pattern {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (r : ColumnResiduePattern K I modulus)
    (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x =
      if columnResiduePattern modulus x = r then
        smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0 := by
  classical
  simp only [residueSmoothWeight, ← columnResiduePattern_eq_iff]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem residueSmoothWeight_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (V : K × X → ℝ)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    residueSmoothWeight r modulus V = residueSmoothWeight s modulus V := by
  funext y
  have he : (∀ z, (modulus z.2 : ℤ) ∣ y z - r z) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - s z := by
    constructor
    · intro h z
      have hid : y z - s z = (y z - r z) - (s z - r z) := by ring
      rw [hid]
      exact dvd_sub (h z) (hrs z)
    · intro h z
      have hid : y z - r z = (y z - s z) + (s z - r z) := by ring
      rw [hid]
      exact dvd_add (h z) (hrs z)
  simp only [residueSmoothWeight, he]

theorem residueSmoothMass_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z) :
    shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V) =
      shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V) := by
  rw [residueSmoothWeight_mass r modulus hmodulus V hV,
    residueSmoothWeight_mass s modulus hmodulus V hV, residueSmoothWeight_congr r s modulus V hrs]

theorem residueSmoothPMF_congr {K X : Type*} [Fintype K] [Fintype X]
    (r s : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hrs : ∀ z, (modulus z.2 : ℤ) ∣ s z - r z)
    (hr : 0 < shiftedSmoothProductMass (residueProfileCenter r modulus) (residueProfileWidth modulus V))
    (hs : 0 < shiftedSmoothProductMass (residueProfileCenter s modulus) (residueProfileWidth modulus V)) :
    residueSmoothPMF r modulus hmodulus V hV hr = residueSmoothPMF s modulus hmodulus V hV hs := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [residueSmoothPMF_conditional_weight, residueSmoothWeight_congr r s modulus V hrs]

noncomputable def boundedColumnResidueRepresentative {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) : K × X → ℤ :=
  fun z => columnResidueRepresentative modulus r z % (modulus z.2 : ℤ)

theorem boundedColumnResidueRepresentative_congr {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) (z : K × X) :
    (modulus z.2 : ℤ) ∣ boundedColumnResidueRepresentative modulus r z - columnResidueRepresentative modulus r z := by
  refine ⟨-(columnResidueRepresentative modulus r z / (modulus z.2 : ℤ)), ?_⟩
  have h := Int.emod_add_mul_ediv (columnResidueRepresentative modulus r z) (modulus z.2 : ℤ)
  unfold boundedColumnResidueRepresentative
  nlinarith

theorem boundedColumnResidueRepresentative_bounds {K X : Type*} (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (r : ColumnResiduePattern K X modulus) (z : K × X) :
    0 ≤ boundedColumnResidueRepresentative modulus r z ∧
      boundedColumnResidueRepresentative modulus r z < (modulus z.2 : ℤ) := by
  have hq : (0 : ℤ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def selectedResidueSmoothWeight {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : ℝ :=
  if columnResiduePattern modulus x ∈ G then
    smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0

theorem selectedResidueSmoothWeight_eq_sum {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) :
    selectedResidueSmoothWeight modulus G V x =
      ∑ r : G, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  symm
  calc
    _ = ∑ r ∈ G, residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x :=
      Finset.sum_coe_sort G (fun r => residueSmoothWeight (columnResidueRepresentative modulus r) modulus V x)
    _ = _ := by
      simp only [residueSmoothWeight_eq_pattern, Finset.sum_ite_eq, selectedResidueSmoothWeight]

theorem residueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    residueSmoothWeight residue modulus V x = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile (K × I)) 0 V hV
    (smoothProductProfile_zero_outside (K × I)) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [residueSmoothWeight, hz, ite_self]

theorem selectedResidueSmoothWeight_nonneg {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (x : K × I → ℤ) : 0 ≤ selectedResidueSmoothWeight modulus G V x := by
  unfold selectedResidueSmoothWeight
  split
  · exact (smoothProductProfile_range (K × I) _).1
  · exact le_rfl

theorem selectedResidueSmoothWeight_zero_off {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (x : K × I → ℤ) (hx : x ∉ rectangularWeightIndices 0 V 1) :
    selectedResidueSmoothWeight modulus G V x = 0 := by
  rw [selectedResidueSmoothWeight_eq_sum]
  simp only [residueSmoothWeight_zero_off _ _ V hV x hx, Finset.sum_const_zero]

theorem selectedResidueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    (∑' x, selectedResidueSmoothWeight modulus G V x) =
      ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  simp_rw [selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_weight_sum_tsum _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_summable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) : Summable (selectedResidueSmoothWeight modulus G V) :=
  (hasSum_sum_of_ne_finset_zero (selectedResidueSmoothWeight_zero_off modulus G V hV)).summable

theorem selectedResidueSmoothWeight_mass_pos {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  obtain ⟨r, hr⟩ := hG
  rw [selectedResidueSmoothWeight_mass modulus G V hV]
  exact (hc ⟨r, hr⟩).trans_le
    (Finset.single_le_sum (fun s _ => (hc s).le) (Finset.mem_univ (⟨r, hr⟩ : G)))

noncomputable def selectedResidueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) : PMF (K × I → ℤ) :=
  realWeightPMF (selectedResidueSmoothWeight modulus G V)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_summable modulus G V hV) hZ

theorem selectedResidueSmoothPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (x : K × I → ℤ) :
    (selectedResidueSmoothPMF modulus G V hV hZ x).toReal =
      selectedResidueSmoothWeight modulus G V x / ∑' y, selectedResidueSmoothWeight modulus G V y :=
  realWeightPMF_apply _ _ _ _ x

theorem selectedResidueSmoothPMF_mixture {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x) =
      ∑ r : G, (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus G V y) : ℝ) : ℂ) *
        (∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x) := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  simp_rw [selectedResidueSmoothPMF_toReal, residueSmoothPMF_conditional_weight, ht,
    selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_normalized_mixture _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ

theorem selectedResidueSmoothPMF_bound_of_cells {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus V))
    (φ : (K × I → ℤ) → ℂ) {ε : ℝ}
    (hφ : ∀ r : G,
      ‖∑' x, ((residueSmoothPMF (columnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r) x).toReal : ℂ) * φ x‖ ≤ ε) :
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x,
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * φ x‖ ≤ ε := by
  have hcell (r : G) : 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rw [← residueSmoothWeight_mass _ modulus hmodulus V hV]
    exact hc r
  have hZ := selectedResidueSmoothWeight_mass_pos modulus G hG V hV hcell
  have ht := selectedResidueSmoothWeight_mass modulus G V hV
  have htotal : 0 < ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
    rwa [← ht]
  refine ⟨hZ, ?_⟩
  simp_rw [selectedResidueSmoothPMF_toReal, ht, selectedResidueSmoothWeight_eq_sum]
  apply finite_supported_normalized_mixture_bound _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV) hcell htotal φ
  intro r
  simpa only [residueSmoothPMF_conditional_weight] using hφ r

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f g : (K × I → ℤ) → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (he : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ η := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  exact normalized_finite_weight_approximation _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w f g hη hw he

theorem selectedResidueSmoothPMF_projection_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f f₀ g₀ g : (K × I → ℤ) → ℂ) {η ε : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (hf : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - f₀ x‖ ≤ η)
    (hg : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖g₀ x - g x‖ ≤ η)
    (hproject : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f₀ x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g₀ x)‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ 2 * η + ε := by
  have hfirst := selectedResidueSmoothPMF_approximation modulus G V hV hZ w f f₀ hη hw hf
  have hlast := selectedResidueSmoothPMF_approximation modulus G V hV hZ w g₀ g hη hw hg
  let E (a : (K × I → ℤ) → ℂ) :=
    ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * a x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E f₀) (E g)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E f₀) (E g₀) (E g)
  change ‖E f - E f₀‖ ≤ η at hfirst
  change ‖E g₀ - E g‖ ≤ η at hlast
  change ‖E f₀ - E g₀‖ ≤ ε at hproject
  change ‖E f - E g‖ ≤ 2 * η + ε
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

noncomputable def selectedResidueDensityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (D : (K × I → ℤ) → ℝ) : ℝ :=
  finiteDensityMass (selectedResidueSmoothWeight modulus G V) D

theorem selectedResidueDensityMass_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueDensityMass modulus G V D : ℂ) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (D x : ℂ) := by
  simp only [selectedResidueDensityMass, finiteDensityMass_complex, selectedResidueSmoothPMF_toReal]

noncomputable def selectedResidueDensityPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) : PMF (K × I → ℤ) :=
  finiteDensityTiltPMF _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ D hD0 hD

theorem selectedResidueDensityPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (x : K × I → ℤ) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal =
      (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * D x /
        selectedResidueDensityMass modulus G V D := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_toReal, selectedResidueSmoothPMF_toReal]

theorem selectedResidueDensityPMF_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((D x : ℂ) * f x)) /
        (selectedResidueDensityMass modulus G V D : ℂ) := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_complexMean,
    selectedResidueSmoothPMF_toReal]

theorem selectedResidueDensityPMF_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ)
    {a : ℂ} {E ε B : ℝ} (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    (herror : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
      ((D x : ℂ) * f x)) - a‖ ≤ E)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ ε) (hcap : ‖a‖ ≤ B) :
    ‖(∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) - a‖ ≤
      2 * E + 2 * B * ε := by
  rw [selectedResidueDensityPMF_complexMean]
  exact complex_normalization_error hlower herror hmass hcap

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem selectedResidueDensityMass_integral {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride cells V x)
    (f : (K × I → ℤ) → ℝ)
    (hf : Integrable f (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure) :
    selectedResidueDensityMass stride cells V f =
      ∫ x, f x ∂(selectedResidueSmoothPMF stride cells V hV hZ).toMeasure := by
  apply Complex.ofReal_injective
  rw [selectedResidueDensityMass_complex stride cells V hV hZ,
    ← integral_complex_ofReal, PMF.integral_eq_tsum _ _ hf.ofReal]
  simp only [Complex.real_smul]

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueDensityPMF_zero_of_density_zero {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (x : K × I → ℤ) (hx : D x = 0) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal = 0 := by
  rw [selectedResidueDensityPMF_toReal, hx, mul_zero, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def selectedResidueFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  finiteSupportProbability (selectedResidueSmoothWeight modulus G V) (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ

theorem selectedResidueFiniteLaw_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℂ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * f x := by
  simp only [selectedResidueFiniteLaw, finiteSupportProbability_complexMean, selectedResidueSmoothPMF_toReal]

theorem selectedResidueFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x := by
  apply Complex.ofReal_injective
  have h := selectedResidueFiniteLaw_complexMean modulus G V hV hZ (fun x => (f x : ℂ))
  rw [FiniteProbabilityWeights.complexMean_ofReal] at h
  simpa only [Complex.ofReal_tsum, Complex.ofReal_mul] using h

theorem selectedResidueFiniteLaw_densityMass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueFiniteLaw modulus G V hV hZ).mean (fun x => D x.val) =
      selectedResidueDensityMass modulus G V D := by
  rw [selectedResidueFiniteLaw_mean]
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueDensityMass, finiteDensityMass]

theorem selectedResidueDensityPMF_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x) =
      (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (D x * f x)) /
        selectedResidueDensityMass modulus G V D := by
  simp only [selectedResidueDensityPMF_toReal, div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def columnResidueReduction {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i)
    (r : ColumnResiduePattern K I refined) : ColumnResiduePattern K I modulus :=
  fun z => ZMod.castHom (hdiv z.2) (ZMod (modulus z.2)) (r z)

@[simp] theorem columnResidueReduction_pattern {K I : Type*} (modulus refined : I → ℕ)
    (hdiv : ∀ i, modulus i ∣ refined i) (x : K × I → ℤ) :
    columnResidueReduction modulus refined hdiv (columnResiduePattern refined x) =
      columnResiduePattern modulus x := by
  funext z
  exact map_intCast (ZMod.castHom (hdiv z.2) (ZMod (modulus z.2))) (x z)

noncomputable def selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus)) :
    Finset (ColumnResiduePattern K I refined) :=
  Finset.univ.filter (fun r => columnResidueReduction modulus refined hdiv r ∈ G)

@[simp] theorem mem_selectedResidueRefinement {K I : Type*} [Fintype K] [Fintype I]
    (modulus refined : I → ℕ) [∀ i, NeZero (refined i)]
    (hdiv : ∀ i, modulus i ∣ refined i) (G : Finset (ColumnResiduePattern K I modulus))
    (r : ColumnResiduePattern K I refined) :
    r ∈ selectedResidueRefinement modulus refined hdiv G ↔
      columnResidueReduction modulus refined hdiv r ∈ G := by
  simp only [selectedResidueRefinement, Finset.mem_filter, Finset.mem_univ, true_and]

def refinedColumnExtraResidue {K I : Type*} (modulus : I → ℕ) (q : ℕ)
    (r : ColumnResiduePattern K I (fun i => modulus i * q)) : K × I → ZMod q :=
  columnResidueReduction (fun _ => q) (fun i => modulus i * q)
    (fun i => dvd_mul_left q (modulus i)) r

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProbabilityProfile_plateau (x : ℝ) (hx : |x| ≤ 1 / 2) :
    smoothProbabilityProfile x = smoothProbabilityProfile 0 := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have h0 : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, hx', h0]

theorem selectedResidueSmoothWeight_plateau {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (z : K × X → ℤ) (hz : columnResiduePattern q z ∈ cells)
    (hsmall : ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    selectedResidueSmoothWeight q cells V z =
      (smoothProbabilityProfile 0) ^ Fintype.card (K × X) := by
  classical
  simp only [selectedResidueSmoothWeight, hz, ite_true]
  unfold smoothProductProfile
  calc
    _ = ∏ _i : K × X, smoothProbabilityProfile 0 :=
      Finset.prod_congr rfl (fun i _ => smoothProbabilityProfile_plateau _ (hsmall i))
    _ = _ := by simp

theorem selectedResidueDensityMass_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z ∈ cells)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((∑' z, selectedResidueSmoothWeight q cells V z) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q cells V D := by
  apply finiteDensityMass_sum_le_of_weight_lower (selectedResidueSmoothWeight q cells V) D
    (rectangularWeightIndices 0 V 1) window (selectedResidueSmoothWeight_nonneg q cells V)
    (selectedResidueSmoothWeight_zero_off q cells V hV) hD hZ
    (pow_pos smoothProbabilityProfile_pos_zero _)
  intro z hz
  exact (selectedResidueSmoothWeight_plateau q cells V z (hresidue z hz) (hsmall z hz)).ge

theorem selectedResidueSmoothWeight_singleton_mass_upper {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i) :
    (∑' z, selectedResidueSmoothWeight q {r} V z) ≤
      (3 / 2 : ℝ) ^ Fintype.card (K × X) * ∏ i, residueProfileWidth q V i := by
  classical
  have he : selectedResidueSmoothWeight q {r} V =
      residueSmoothWeight (columnResidueRepresentative q r) q V := by
    funext z
    simp only [selectedResidueSmoothWeight, residueSmoothWeight_eq_pattern, Finset.mem_singleton]
  rw [he, ← residueSmoothWeight_mass _ q hq V hV,
    shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  calc
    _ ≤ ∏ i : K × X, 3 * residueProfileWidth q V i / 2 := by
      apply Finset.prod_le_prod
      · intro i _
        exact tsum_nonneg (fun _ => (smoothProbabilityProfile_range _).1)
      · intro i _
        exact (shiftedSmoothSampleSum_bounds _ (hscale i)).2
    _ = _ := by
      simp_rw [show ∀ i : K × X, 3 * residueProfileWidth q V i / 2 =
        (3 / 2 : ℝ) * residueProfileWidth q V i by intro i; ring]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]

theorem selectedResidueDensityMass_singleton_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z = r)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (K × X) * (∏ i, residueProfileWidth q V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q {r} V D := by
  classical
  have hm : 0 ≤ selectedResidueDensityMass q {r} V D := by
    apply tsum_nonneg
    intro z
    exact mul_nonneg (div_nonneg (selectedResidueSmoothWeight_nonneg q {r} V z) hZ.le) (hD z)
  apply (selectedResidueDensityMass_window_bound q {r} V hV hZ D hD window
    (fun z hz => Finset.mem_singleton.mpr (hresidue z hz)) hsmall).trans
  apply mul_le_mul_of_nonneg_right _ hm
  exact div_le_div_of_nonneg_right (selectedResidueSmoothWeight_singleton_mass_upper q hq r V hV hscale)
    (pow_pos smoothProbabilityProfile_pos_zero _).le

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveNormalizationError
namespace OAI

section

namespace Erdos3

theorem complex_remove_normalization {N : ℂ} {Z : ℝ} (hZ : 0 < Z) (hN : ‖N‖ ≤ Z) :
    ‖N/(Z : ℂ)-N‖ ≤ |Z-1| := by
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hunit : ‖N/(Z : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
    exact (div_le_one hZ).mpr hN
  have he : N/(Z : ℂ)-N = (N/(Z : ℂ))*(1-(Z : ℂ)) := by field_simp
  rw [he, norm_mul]
  calc
    _ ≤ 1 * ‖1-(Z : ℂ)‖ := mul_le_mul_of_nonneg_right hunit (norm_nonneg _)
    _ = |Z-1| := by
      rw [one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]

theorem FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ p.mean D := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply p.mean_mono
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD x)]
  exact (mul_le_mul_of_nonneg_left (hf x) (hD x)).trans_eq (mul_one _)

theorem selectedResidueDensityPMF_remove_normalization {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*((D z : ℂ)*f z))‖ ≤
        |selectedResidueDensityMass modulus T W D-1| := by
  rw [selectedResidueDensityPMF_complexMean]
  apply complex_remove_normalization hD
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z),
    ← selectedResidueFiniteLaw_densityMass modulus T W hW hZ D]
  exact FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    (selectedResidueFiniteLaw modulus T W hW hZ)
    (fun z => D z.val) (fun z => hD0 z.val) (fun z => f z.val) (fun z => hf z.val)

theorem selectedResidueDensityPMF_error_of_bounded_test {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    {a : ℂ} {ε η : ℝ}
    (herror : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      (f z*(D z : ℂ)))-a‖ ≤ ε)
    (hmass : |selectedResidueDensityMass modulus T W D-1| ≤ η) :
    ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z)-a‖ ≤ η+ε := by
  have hcomm : (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z)) =
      ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(D z : ℂ)) := by
    apply tsum_congr
    intro z
    rw [mul_comm (D z : ℂ) (f z)]
  have herror' : ‖(∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*
      ((D z : ℂ)*f z))-a‖ ≤ ε := by
    rw [hcomm]
    exact herror
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
    ((selectedResidueDensityPMF_remove_normalization modulus T W hW hZ D hD0 hD f hf).trans hmass)
    herror')

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def reweightPositive {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) : FiniteProbabilityWeights X :=
  ofPositiveWeights (fun x => p.weight x * w x) (fun x => mul_nonneg (p.nonneg x) (hw x)) hm

theorem reweightPositive_weight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (x : X) :
    (p.reweightPositive w hw hm).weight x = p.weight x * w x / p.mean w := rfl

theorem reweightPositive_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℝ) :
    (p.reweightPositive w hw hm).mean f = p.mean (fun x => w x * f x) / p.mean w := by
  simp only [mean, reweightPositive_weight, div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

theorem reweightPositive_complexMean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℂ) :
    (p.reweightPositive w hw hm).complexMean f =
      p.complexMean (fun x => (w x : ℂ) * f x) / (p.mean w : ℂ) := by
  simp only [complexMean, reweightPositive_weight, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem mean_mul_le_of_capped_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D g φ : X → ℝ) {C ε : ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hg : ∀ x, g x ≤ C)
    (he : |p.mean (fun x => D x * φ x) - p.mean (fun x => g x * φ x)| ≤ ε) :
    p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε := by
  have hb : p.mean (fun x => g x * φ x) ≤ C * p.mean φ := by
    rw [← p.mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hg x) (hφ x))
  have ht := (abs_le.mp he).2
  linarith

theorem reweightPositive_test_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < p.mean D) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {C ε a : ℝ} (ha : 0 < a) (hlower : a ≤ p.mean D)
    (he : p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε) :
    (p.reweightPositive D hD0 hD).mean φ ≤ (C * p.mean φ + ε) / a := by
  rw [p.reweightPositive_mean]
  have hnum : 0 ≤ C * p.mean φ + ε :=
    (p.mean_nonneg (fun x => mul_nonneg (hD0 x) (hφ x))).trans he
  exact (div_le_div_of_nonneg_right he hD.le).trans
    (div_le_div_of_nonneg_left hnum ha hlower)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def normalizedDensityTest (D : X → ℝ) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => (D x : ℂ)*f x)/(p.mean D : ℂ)

theorem normalizedDensityTest_norm_le_one (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f‖ ≤ 1 := by
  rw [normalizedDensityTest, norm_div, Complex.norm_real, Real.norm_of_nonneg hmass.le]
  exact (div_le_one hmass).mpr (p.norm_density_weighted_complexMean_le D hD f hf)

variable [MeasurableSpace C]

theorem normalizedDensityTest_measurable (D : C → X → ℝ)
    (hD : ∀ x, Measurable (fun c => D c x)) (f : X → ℂ) :
    Measurable (fun c => p.normalizedDensityTest (D c) f) :=
  (p.complexMean_measurable (fun c x => (D c x : ℂ)*f x)
    (fun x => (Complex.continuous_ofReal.measurable.comp (hD x)).mul_const (f x))).div
    (Complex.continuous_ofReal.measurable.comp (p.mean_measurable D hD))

theorem normalizedDensityTest_integrable (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun c => p.normalizedDensityTest (D c) f) μ :=
  Integrable.of_bound (p.normalizedDensityTest_measurable D hD f).aestronglyMeasurable 1
    (ae_of_all μ (fun c => p.normalizedDensityTest_norm_le_one (D c) (hD0 c) (hmass c) f hf))

theorem integral_normalizedDensityTest_compare (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (F : C → X → ℝ) (hF : ∀ x, Integrable (fun c => F c x) μ)
    (hFmass : ∀ x, (∫ c, F c x ∂μ) = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c, ‖p.normalizedDensityTest (D c) f -
      p.complexMean (fun x => f x*(F c x : ℂ))‖ ≤ ε) :
    ‖(∫ c, p.normalizedDensityTest (D c) f ∂μ)-p.complexMean f‖ ≤ ε := by
  have hi := p.normalizedDensityTest_integrable μ D hD hD0 hmass f hf
  have hterm (x : X) : Integrable (fun c => f x*(F c x : ℂ)) μ := (hF x).ofReal.const_mul (f x)
  have href := p.complexMean_integrable μ (fun c x => f x*(F c x : ℂ)) hterm
  have hmean : (∫ c, p.complexMean (fun x => f x*(F c x : ℂ)) ∂μ) = p.complexMean f := by
    rw [p.integral_complexMean μ _ hterm]
    congr 1
    funext x
    rw [integral_const_mul, integral_complex_ofReal, hFmass x, Complex.ofReal_one, mul_one]
  rw [← hmean, ← integral_sub hi href]
  have h := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) (ae_of_all μ herror)
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem mean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.prod q).mean f = p.mean (fun x => q.mean (fun y => f (x,y))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem mean_mem_Icc (p : FiniteProbabilityWeights X) (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) : p.mean f ∈ Set.Icc a b := by
  constructor
  · exact (p.mean_const a).symm.trans_le (p.mean_mono (fun x => (hf x).1))
  · exact (p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const b)

theorem abs_mean_sub_const_le (p : FiniteProbabilityWeights X) (f : X → ℝ) (c ε : ℝ)
    (hf : ∀ x, |f x-c| ≤ ε) : |p.mean f-c| ≤ ε := by
  have h := p.mean_mem_Icc f (a := c-ε) (b := c+ε) (fun x => by
    have hx := abs_le.mp (hf x)
    constructor <;> linarith)
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem reweightPositive_complexMean_eq_normalizedDensityTest
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) :
    (p.reweightPositive D hD hmass).complexMean f = p.normalizedDensityTest D f :=
  p.reweightPositive_complexMean D hD hmass f

theorem normalizedDensityTest_remove_normalization (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (hmass : 0 < p.mean D)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f - p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ |p.mean D-1| :=
  complex_remove_normalization hmass (p.norm_density_weighted_complexMean_le D hD f hf)

theorem joint_normalization_compare (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x,y))) (hglobal : 0 < (p.prod q).mean D)
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ x, |q.mean (fun y => D (x,y))-1| ≤ ε) :
    ‖(p.prod q).normalizedDensityTest D f -
      p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))‖ ≤ 2*ε := by
  have hmass : |(p.prod q).mean D-1| ≤ ε := by
    rw [mean_prod]
    exact p.abs_mean_sub_const_le _ 1 ε hclose
  have hj := ((p.prod q).normalizedDensityTest_remove_normalization D hD hglobal f hf).trans hmass
  have hl := p.norm_complexMean_sub_le
    (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))
    (fun x => q.complexMean (fun y => (D (x,y) : ℂ)*f (x,y))) (fun _ => ε)
    (fun x _ => (q.normalizedDensityTest_remove_normalization _ (fun y => hD (x,y))
      (hlocal x) _ (fun y => hf (x,y))).trans (hclose x))
  rw [p.mean_const, ← complexMean_prod p q (fun z => (D z : ℂ)*f z)] at hl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((p.prod q).normalizedDensityTest D f)
    ((p.prod q).complexMean (fun z => (D z : ℂ)*f z))
    (p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y))))
  rw [norm_sub_rev ((p.prod q).complexMean _)] at ht
  linarith

noncomputable def uniformFinset {A : Type*} (S : Finset A) (hS : S.Nonempty) :
    FiniteProbabilityWeights S := by
  letI : Nonempty S := hS.to_subtype
  exact uniform S

theorem uniformFinset_mean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (uniformFinset S hS).mean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_mean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

theorem uniformFinset_complexMean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℂ) :
    (uniformFinset S hS).complexMean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_complexMean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem fiberLaw_complexMean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℂ) :
    (p.fiberLaw F).complexMean f = p.complexMean (fun x => f (F x)) := by
  have h := p.complexMean_fiber_factor F (fun _ => 1) f
  simpa only [Complex.ofReal_one, one_mul, complexMean, fiberLaw_weight] using h.symm

theorem fiberLaw_mean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℝ) :
    (p.fiberLaw F).mean f = p.mean (fun x => f (F x)) := by
  have h := congrArg Complex.re (p.fiberLaw_complexMean F (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

noncomputable def siteLaw {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) : FiniteProbabilityWeights X :=
  (p.prod (uniform T)).fiberLaw (fun z => F z.1 z.2)

theorem siteLaw_mean {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) (f : X → ℝ) :
    (p.siteLaw F).mean f = p.mean (fun z => 𝔼 t, f (F z t)) := by
  rw [siteLaw, fiberLaw_mean, mean_prod]
  simp_rw [uniform_mean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def intervalUniformWeights (a b : ℤ) (hab : a < b) :
    FiniteProbabilityWeights (Finset.Ico a b) := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  exact FiniteProbabilityWeights.uniform _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → Y → ℝ) :
    p.mean (fun x => q.mean (F x)) = q.mean (fun y => p.mean (fun x => F x y)) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mean_sum {X J : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (s : Finset J) (F : J → X → ℝ) :
    p.mean (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, p.mean (F j) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_sub {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (f g : X → ℝ) :
    p.mean (fun x => f x - g x) = p.mean f - p.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem exists_code_fiber_mass {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights Ω) (Q : Finset Ω) (code : Ω → I) :
    ∃ i, p.mass Q / Fintype.card I ≤ p.mass (Q.filter (fun x => code x = i)) := by
  have hsum : (∑ i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q := by
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hmean : (𝔼 i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card, hsum]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.ge
  exact ⟨i, hi⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

theorem exists_weighted_exponential_constant_fiber {Ω β : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (f : Ω → β) (A : Set β) (hA : A.Finite) (hf : ∀ x ∈ S, f x ∈ A)
    {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset Ω, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * outer.mass S ≤ outer.mass T := by
  classical
  have hSne : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hS
  obtain ⟨x₀, hx₀⟩ := hSne
  let : Fintype A := hA.fintype
  let default : A := ⟨f x₀, hf x₀ hx₀⟩
  let : Nonempty A := ⟨default⟩
  let code : Ω → A := fun x => if hx : x ∈ S then ⟨f x, hf x hx⟩ else default
  obtain ⟨y, hy⟩ := outer.exists_code_fiber_mass S code
  let T := S.filter (fun x => code x = y)
  have hcard : (Fintype.card A : ℝ) ≤ Real.exp C := by
    simpa only [Set.fintypeCard_eq_ncard] using hcount
  have hcardpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hmass : Real.exp (-C) * outer.mass S ≤ outer.mass T := by
    calc
      _ = outer.mass S / Real.exp C := by
        rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass S / Fintype.card A :=
        div_le_div_of_nonneg_left hS.le hcardpos hcard
      _ ≤ outer.mass T := by
        convert hy using 1
        apply congrArg outer.mass
        ext x
        simp only [T, Finset.mem_filter]
  have hTpos : 0 < outer.mass T := (mul_pos (Real.exp_pos _) hS).trans_le hmass
  have hTne : T.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hTpos
  refine ⟨y.val, y.property, T, Finset.filter_subset _ _, hTne, ?_, hmass⟩
  intro x hx
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
  simpa only [code, dif_pos hxS] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_linear_model_partner {V I : Type*}
    [AddCommGroup V] [Module ℂ V] [Fintype I]
    (test : V →ₗ[ℂ] ℂ) (v e : V) (Q : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • Q i) + e) {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 < M) (hc : (∑ i, ‖c i‖) ≤ M)
    (herr : ‖test e‖ ≤ delta / 2) (hscore : delta ≤ ‖test v‖) :
    ∃ i, delta / (2 * M) ≤ ‖test (Q i)‖ := by
  have hid : test v = (∑ i, c i * test (Q i)) + test e := by
    rw [hmodel, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : delta / 2 ≤ ‖∑ i, c i * test (Q i)‖ := by
    have ht := norm_add_le (∑ i, c i * test (Q i)) (test e)
    rw [← hid] at ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c (fun i => test (Q i))
    (by positivity : 0 < delta / 2) hM hc hsum
  refine ⟨i, ?_⟩
  convert hi using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_injective_mean_le {B X : Type*}
    [Fintype B] [Nonempty B] [Fintype X] [Nonempty X]
    (F : B → X) (hF : Function.Injective F) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    (uniform B).mean (fun b => φ (F b)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
  have hsum : (∑ b, φ (F b)) ≤ ∑ x, φ x :=
    Finset.sum_le_sum_of_injOn F hF.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun x _ _ => hφ x)
  rw [uniform_mean, uniform_mean, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ x, φ x) / Fintype.card B := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem uniform_base_reweight_test_le {B Ω X : Type*}
    [Fintype B] [Nonempty B] [Fintype Ω] [Fintype X] [Nonempty X]
    (q : FiniteProbabilityWeights Ω) (D : B × Ω → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hZ : 0 < ((uniform B).prod q).mean D)
    (F : B × Ω → X) (hF : ∀ z, Function.Injective (fun b => F (b, z)))
    (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {M ε a : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hlower : a ≤ ((uniform B).prod q).mean D)
    (hlocal : ∀ b, q.mean (fun z => D (b, z) * φ (F (b, z))) ≤
      M * q.mean (fun z => φ (F (b, z))) + ε) :
    (((uniform B).prod q).reweightPositive D hD hZ).mean (fun z => φ (F z)) ≤
      ((M * ((Fintype.card X : ℝ) / Fintype.card B)) * (uniform X).mean φ + ε) / a := by
  have href : ((uniform B).prod q).mean (fun z => φ (F z)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
    rw [mean_prod, mean_comm]
    exact (q.mean_mono (fun z => uniform_injective_mean_le _ (hF z) φ hφ)).trans_eq
      (q.mean_const _)
  have hraw : ((uniform B).prod q).mean (fun z => D z * φ (F z)) ≤
      M * ((uniform B).prod q).mean (fun z => φ (F z)) + ε := by
    rw [mean_prod, mean_prod]
    exact ((uniform B).mean_mono hlocal).trans_eq (by rw [mean_add, mean_const_mul, mean_const])
  have hnorm := ((uniform B).prod q).reweightPositive_test_le D hD hZ
    (fun z => φ (F z)) (fun z => hφ (F z)) ha hlower hraw
  apply hnorm.trans
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    _ ≤ M * (((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ) + ε := by
      gcongr
    _ = _ := by ring

theorem siteLaw_excessMass_le_of_test_bound {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (r : FiniteProbabilityWeights X) (F : Ω → T → X)
    {C ε : ℝ}
    (htest : ∀ (φ : X → ℝ), (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ t, p.mean (fun z => φ (F z t)) ≤ C * r.mean φ + ε) :
    r.excessMass (p.siteLaw F) C ≤ ε := by
  apply excessMass_le_of_mass_le
  intro A
  let φ : X → ℝ := fun x => if x ∈ A then 1 else 0
  have hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := by intro x; dsimp only [φ]; split_ifs <;> norm_num
  have hmean : (p.siteLaw F).mean φ ≤ C * r.mean φ + ε := by
    rw [siteLaw_mean]
    simp_rw [← uniform_mean]
    rw [mean_comm]
    exact ((uniform T).mean_mono (htest φ hφ)).trans_eq ((uniform T).mean_const _)
  have hfilter : Finset.univ.filter (fun x => x ∈ A) = A := by ext x; simp
  simpa only [mean, φ, mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter,
    mass] using hmean

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxPairDivisibility
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def integerBoxUniformWeights {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) :
    FiniteProbabilityWeights (∀ j, Finset.Ico (lo j) (hi j)) :=
  FiniteProbabilityWeights.pi (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem shiftedAdaptedSubmodule_antitone : Antitone (F.shiftedAdaptedSubmodule w) := by
  intro i j hij p hp α
  exact F.antitone (Nat.add_le_add_left hij _) (hp α)

noncomputable def shiftedPolynomialIdeal (k : ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w k).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      change ⁅p.val, q.val⁆ ∈ F.shiftedAdaptedSubmodule w k
      have hq' : q.val ∈ F.shiftedAdaptedSubmodule w k := hq
      simpa only [Nat.zero_add] using F.lie_mem_shiftedAdaptedSubmodule w hp hq' }

@[simp] theorem mem_shiftedPolynomialIdeal (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    p ∈ F.shiftedPolynomialIdeal w k ↔
      ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + k) := Iff.rfl

theorem shiftedPolynomialIdeal_antitone : Antitone (F.shiftedPolynomialIdeal w) := by
  intro i j hij p hp
  exact F.shiftedAdaptedSubmodule_antitone w hij hp

@[simp] theorem shiftedPolynomialIdeal_one : F.shiftedPolynomialIdeal w 1 = F.shiftedAdaptedIdeal w := by
  rfl

theorem shiftedPolynomialIdeal_lie_mem {i j : ℕ} {p q : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedPolynomialIdeal w i) (hq : q ∈ F.shiftedPolynomialIdeal w j) :
    ⁅p, q⁆ ∈ F.shiftedPolynomialIdeal w (i + j) :=
  F.lie_mem_shiftedAdaptedSubmodule w hp hq

theorem adaptedConstant_mem_shiftedPolynomialIdeal (k : ℕ) {x : L} (hx : x ∈ F.layer k) :
    F.adaptedConstant w x ∈ F.shiftedPolynomialIdeal w k := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_zero, Nat.zero_add] using hx

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultidegreeDilationDegree
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairDegreeLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.dilationPairLayer q a

theorem dilationPairLayer_le_degree (q : ℚ) (n : ℕ) (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ F.dilationPairDegreeLayer q n :=
  le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem dilationPairDegreeLayer_le_ordinary (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n ≤ F.ordinary.dilationPairLayer q n := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  exact (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairDegree_higher (q : ℚ) (n : ℕ) (c d : ℚ) {x : L}
    (hx : x ∈ F.ordinary.layer (n + 1)) : (c • x, d • x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := (c • LinearMap.id).prod (d • LinearMap.id)
  have hφ : F.ordinary.layer (n + 1) ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro b
    apply iSup_le
    intro hb x hx
    obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor_above b n hb
    apply F.dilationPairLayer_le_degree q n a ha
    exact F.dilationPairLayer_of_strictUpper q a
      ((F.strictUpperLayer a).smul_mem c (F.layer_le_strictUpperLayer hab hx))
      ((F.strictUpperLayer a).smul_mem d (F.layer_le_strictUpperLayer hab hx))
  exact hφ hx

theorem dilationPairDegree_diagonal (q : ℚ) (n : ℕ) {x : L}
    (hx : x ∈ F.ordinary.layer n) : (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := ((q ^ n) • LinearMap.id).prod LinearMap.id
  have hφ : F.ordinary.layer n ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha x hx
    change (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n
    by_cases hna : n = ∑ i, a i
    · apply F.dilationPairLayer_le_degree q n a ha
      simpa only [hna] using F.dilationPairLayer_diagonal q a hx
    · have hhigh : x ∈ F.ordinary.layer (n + 1) :=
        F.ordinary.antitone (by omega : n + 1 ≤ ∑ i, a i) (F.layer_le_ordinary a hx)
      simpa only [one_smul] using F.dilationPairDegree_higher q n (q ^ n) 1 hhigh
  exact hφ hx

theorem dilationPairDegreeLayer_eq (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n = F.ordinary.dilationPairLayer q n := by
  apply le_antisymm (F.dilationPairDegreeLayer_le_ordinary q n)
  intro x hx
  have hleft : (x.1 - q ^ n • x.2, (0 : L)) ∈ F.dilationPairDegreeLayer q n := by
    simpa only [one_smul, zero_smul, scaledPairDifference_apply] using
      F.dilationPairDegree_higher q n 1 0 hx.2.2
  have hright := F.dilationPairDegree_diagonal q n hx.2.1
  have heq : x = (x.1 - q ^ n • x.2, (0 : L)) + (q ^ n • x.2, x.2) := by
    apply Prod.ext <;> simp
  rw [heq]
  exact (F.dilationPairDegreeLayer q n).add_mem hleft hright

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueConstantMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_discard_error {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  simp_rw [selectedResidueSmoothPMF_toReal] at hdiscard ⊢
  exact normalized_finite_weight_discard_error _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w c u keep hc hτ hdiscard

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_const {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (c : ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * c) = c := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  rw [← finiteSupportProbability_complexMean _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ (fun _ => c)]
  exact FiniteProbabilityWeights.complexMean_const _ c

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCenterMix
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedResidueDensityPMF_normalizedDensityTest {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D) (f : (K × I → ℤ) → ℂ) :
    (∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) =
      (selectedResidueFiniteLaw modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.val) (fun z => f z.val) := by
  rw [selectedResidueDensityPMF_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z)]

theorem selectedResidue_center_mixture_compare {C K I : Type*} [MeasurableSpace C]
    [Fintype K] [Fintype I] (μ : Measure C) [IsProbabilityMeasure μ]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : C → (K × I → ℤ) → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z) (hD : ∀ c, 0 < selectedResidueDensityMass modulus T W (D c))
    (F : C → (K × I → ℤ) → ℝ) (hF : ∀ z, Integrable (fun c => F c z) μ)
    (hFmass : ∀ z, (∫ c, F c z ∂μ) = 1)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c,
      ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z) -
        (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(F c z : ℂ)))‖ ≤ ε) :
    ‖(∫ c, ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z ∂μ) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*f z)‖ ≤ ε := by
  simp_rw [selectedResidueDensityPMF_normalizedDensityTest]
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ f]
  apply FiniteProbabilityWeights.integral_normalizedDensityTest_compare
    (selectedResidueFiniteLaw modulus T W hW hZ) μ
    (fun c z => D c z.val) (fun z => hDm z.val) (fun c z => hD0 c z.val)
    (fun c => by rw [selectedResidueFiniteLaw_densityMass]; exact hD c)
    (fun c z => F c z.val) (fun z => hF z.val) (fun z => hFmass z.val)
    (fun z => f z.val) (fun z => hf z.val)
  intro c
  have h := herror c
  rw [selectedResidueDensityPMF_normalizedDensityTest,
    ← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => f z*(F c z : ℂ))] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def normalizedSliceTest {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) (t : T) : ℂ :=
  ((Fintype.card T : ℂ) / S.card) * (if t ∈ S then w t else 0)

theorem normalizedSliceTest_norm_le {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) {K : ℝ}
    (hsize : (Fintype.card T : ℝ) / S.card ≤ K) (hw : ∀ t, ‖w t‖ ≤ 1) (t : T) :
    ‖normalizedSliceTest S w t‖ ≤ K := by
  have hr : 0 ≤ (Fintype.card T : ℝ) / S.card := by positivity
  by_cases ht : t ∈ S
  · simp only [normalizedSliceTest, ht, ite_true, norm_mul, norm_div, Complex.norm_natCast]
    exact (mul_le_of_le_one_right hr (hw t)).trans hsize
  · simpa only [normalizedSliceTest, ht, ite_false, mul_zero, norm_zero] using hr.trans hsize

theorem normalizedSliceTest_mean {T : Type*} [Fintype T] [Nonempty T]
    (S : Finset T) (hS : S.Nonempty) (w f : T → ℂ) :
    (𝔼 t, f t * normalizedSliceTest S w t) = 𝔼 t ∈ S, f t * w t := by
  have hT : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hS0 : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have he : (∑ t, f t * normalizedSliceTest S w t) =
      ((Fintype.card T : ℂ) / S.card) * ∑ t ∈ S, f t * w t := by
    rw [Finset.mul_sum]
    have hterm (t : T) : f t * normalizedSliceTest S w t =
        if t ∈ S then ((Fintype.card T : ℂ) / S.card) * (f t * w t) else 0 := by
      by_cases ht : t ∈ S <;> simp only [normalizedSliceTest, ht, ite_true, ite_false, mul_zero]
      ring
    simp_rw [hterm]
    simp
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, he]
  field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledTestLinearMap {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, v (F t) * w t
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_expect]

noncomputable def sampledSingleTestSeminorm {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (sampledTestLinearMap F w)

theorem sampledSingleTestSeminorm_le {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) {K : ℝ} (hw : ∀ t, ‖w t‖ ≤ K) (v : X → ℂ) :
    sampledSingleTestSeminorm F w v ≤ K * (𝔼 t, ‖v (F t)‖) := by
  change ‖𝔼 t, v (F t) * w t‖ ≤ _
  rw [Finset.mul_expect]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro t _
  rw [norm_mul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hw t) (norm_nonneg _)

noncomputable def sampledTestSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  Seminorm.of (fun v => p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (F z) (w z j)) v))
    (fun u v => by
      rw [← p.mean_add]
      exact p.mean_mono (fun z => map_add_le_add _ _ _))
    (fun a v => by
      simp only [map_smul_eq_mul]
      exact p.mean_const_mul ‖a‖ _)

theorem sampledSingleTestSeminorm_bddAbove {Ω T X : Type*} [Fintype T]
    {J : Ω → Type*} (F : Ω → T → X) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (z : Ω) :
    BddAbove (Set.range (fun j => sampledSingleTestSeminorm (F z) (w z j))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  refine ⟨K * (𝔼 t, ‖v (F z t)‖), ?_⟩
  rintro _ ⟨j, rfl⟩
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

theorem sampledTestSeminorm_apply {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v = p.mean (fun z => ⨆ j, ‖𝔼 t, v (F z t) * w z j t‖) := by
  change p.mean _ = p.mean _
  congr 1
  funext z
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove F w hw z)]
  rfl

theorem sampledTestSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (v : X → ℂ) :
    sampledTestSeminorm p F w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) := by
  rw [sampledTestSeminorm_apply p F w hw, p.siteLaw_mean, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  apply ciSup_le
  intro j
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledSliceSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  sampledTestSeminorm p F (fun z j => normalizedSliceTest (S z j) (w z j))

theorem sampledSliceSeminorm_apply {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v =
      p.mean (fun z => ⨆ j, ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖) := by
  rw [sampledSliceSeminorm, sampledTestSeminorm_apply p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t)]
  have he (z) (j) := normalizedSliceTest_mean (S z j) (hS z j) (w z j) (fun t => v (F z t))
  simp only [he]

theorem sampledSliceSeminorm_le_siteLaw {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) :
    sampledSliceSeminorm p F S w v ≤ K * (p.siteLaw F).mean (fun x => ‖v x‖) :=
  sampledTestSeminorm_le_siteLaw p F _
    (fun z j t => normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t) v

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

noncomputable def centeredFiniteMarginal : FiniteProbabilityWeights Ω where
  weight z := ∫ c, (law c).weight z ∂μ
  nonneg z := integral_nonneg (fun c => (law c).nonneg z)
  total := by
    rw [← integral_finsetSum _ (fun z _ => centeredFinite_weight_integrable μ law hweight z)]
    simp only [FiniteProbabilityWeights.total, integral_const, probReal_univ, one_smul]

theorem centeredFiniteMarginal_mean (f : Ω → ℝ) :
    (centeredFiniteMarginal μ law hweight).mean f = ∫ c, (law c).mean f ∂μ := by
  unfold FiniteProbabilityWeights.mean
  rw [integral_finsetSum _ (fun z _ =>
    (centeredFinite_weight_integrable μ law hweight z).mul_const (f z))]
  simp only [integral_mul_const, centeredFiniteMarginal]

section Joint
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

end Joint
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productive_mass_mul_le_sampledSliceSeminorm
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (weight : ∀ z, J z → T → ℂ)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (signal : X → ℂ) (δ : ℝ)
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      δ ≤ ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖) :
    δ * p.mass good ≤ sampledSliceSeminorm p physical slices weight signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (weight z j)
  have hsize (z) (j) : (Fintype.card T : ℝ) / (slices z j).card ≤ Fintype.card T := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hslices z j).card_pos)).mpr
    have hcard : (1 : ℝ) ≤ (slices z j).card := by exact_mod_cast (hslices z j).card_pos
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card T)]
  have hW (z) (j) (t) : ‖W z j t‖ ≤ Fintype.card T :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (hweight z j) t
  have hpoint (z) : (if z ∈ good then δ else 0) ≤
      (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal := by
    by_cases hz : z ∈ good
    · rw [if_pos hz]
      obtain ⟨j, hj⟩ := hcorr z hz
      rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
      apply hj.trans
      have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
          ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖ := by
        change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
        rw [normalizedSliceTest_mean _ (hslices z j)]
      rw [← he]
      exact le_ciSup (Seminorm.bddAbove_range_iff.mp
        (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j
    · rw [if_neg hz]
      exact apply_nonneg _ _
  calc
    δ * p.mass good = p.mean (fun z => if z ∈ good then δ else 0) := by
      rw [← p.mean_indicator good, ← p.mean_const_mul]
      apply congrArg p.mean
      funext z
      split_ifs <;> simp
    _ ≤ p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal) :=
      p.mean_mono hpoint
    _ = sampledSliceSeminorm p physical slices weight signal := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_sampled_slice_model {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    {atoms : Set (X → ℂ)} (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatomBound : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (hdetect : ∀ psi : X → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B^2 ≤ sampledSliceSeminorm p F S w psi →
        ∃ Q ∈ atoms, beta ≤ ‖r.correlation psi Q‖)
    (hexcess : r.excessMass (p.siteLaw F) C ≤ ε)
    (b : X → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (e : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2/beta ∧
      sampledSliceSeminorm p F S w e ≤ 2*tau + 2*K*(B+2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4*(K*(2*C))^2/(beta^2*tau^2) :=
  exists_model_of_marginal_excess r (p.siteLaw F) hr (sampledSliceSeminorm p F S w)
    hbal hatoms hatomBound hK hC hB hbeta htau
    (sampledSliceSeminorm_le_siteLaw p F S w hsize hw) hdetect hexcess b hb

end Erdos3

end

section

namespace Erdos3

theorem sampledSliceSeminorm_congr_values {Ω T X Y : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω)
    (F : Ω → T → X) (G : Ω → T → Y)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1)
    (f : X → ℂ) (g : Y → ℂ) (hvalue : ∀ z t, f (F z t) = g (G z t)) :
    sampledSliceSeminorm p F S w f = sampledSliceSeminorm p G S w g := by
  have hb (z) (j) (t) := normalizedSliceTest_norm_le (S z j) (w z j) (hsize z j) (hw z j) t
  unfold sampledSliceSeminorm
  rw [sampledTestSeminorm_apply p F _ hb, sampledTestSeminorm_apply p G _ hb]
  simp only [hvalue]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_nearly_maximizing_sampled_slice_tests {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ∀ z, J z, sampledSliceSeminorm p F S w v ≤
      p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖) + ε := by
  have hchoice (z : Ω) : ∃ j : J z,
      (⨆ i, ‖𝔼 t ∈ S z i, v (F z t) * w z i t‖) - ε <
        ‖𝔼 t ∈ S z j, v (F z t) * w z j t‖ :=
    exists_lt_of_lt_ciSup (sub_lt_self _ hε)
  choose j hj using hchoice
  refine ⟨j, ?_⟩
  rw [sampledSliceSeminorm_apply p F S w hS hsize hw]
  calc
    _ ≤ p.mean (fun z => ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ + ε) :=
      p.mean_mono (fun z => by linarith [hj z])
    _ = _ := by rw [p.mean_add, p.mean_const]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

include hweight

theorem centeredFinite_excessMass_integrable (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    Integrable (fun c => reference.excessMass (law c) cap) μ := by
  apply integrable_finsetSum
  intro z _
  exact ((centeredFinite_weight_integrable μ law hweight z).sub
    (integrable_const _)).sup (integrable_const 0)

theorem centeredFiniteMarginal_excessMass_le (reference : FiniteProbabilityWeights Ω) (cap : ℝ) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤
      ∫ c, reference.excessMass (law c) cap ∂μ := by
  unfold FiniteProbabilityWeights.excessMass
  have hmax (z : Ω) : Integrable (fun c => max ((law c).weight z - cap * reference.weight z) 0) μ :=
    ((centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))).sup (integrable_const 0)
  rw [integral_finsetSum _ (fun z _ => hmax z)]
  apply Finset.sum_le_sum
  intro z _
  change max ((∫ c, (law c).weight z ∂μ) - cap * reference.weight z) 0 ≤ _
  apply max_le
  · have hi := (centeredFinite_weight_integrable μ law hweight z).sub
      (integrable_const (cap * reference.weight z))
    have hm := hi.sup (integrable_const 0)
    have h := integral_mono hi hm (fun c => le_max_left ((law c).weight z - cap * reference.weight z) 0)
    change (∫ c, (law c).weight z - cap * reference.weight z ∂μ) ≤
      ∫ c, max ((law c).weight z - cap * reference.weight z) 0 ∂μ at h
    simpa only [integral_sub (centeredFinite_weight_integrable μ law hweight z)
      (integrable_const _), integral_const, probReal_univ, one_smul] using h
  · exact integral_nonneg (fun _ => le_max_right _ _)

theorem centeredFiniteMarginal_excessMass_le_of_ae (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ᵐ c ∂μ, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε := by
  apply (centeredFiniteMarginal_excessMass_le μ law hweight reference cap).trans
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae (centeredFinite_excessMass_integrable μ law hweight reference cap)
      (integrable_const ε) h

theorem centeredFiniteMarginal_excessMass_le_of_uniform (reference : FiniteProbabilityWeights Ω)
    (cap ε : ℝ) (h : ∀ c, reference.excessMass (law c) cap ≤ ε) :
    reference.excessMass (centeredFiniteMarginal μ law hweight) cap ≤ ε :=
  centeredFiniteMarginal_excessMass_le_of_ae μ law hweight reference cap ε (ae_of_all μ h)

section Site

variable {T X : Type*} [Fintype T] [Nonempty T] [Fintype X]
variable (physical : Ω → T → X)

include hweight in
theorem centeredFinite_siteLaw_weight_measurable (x : X) :
    Measurable (fun c => ((law c).siteLaw physical).weight x) := by
  have h := centeredFinite_mean_measurable law hweight
    (fun _ z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖)
    (fun _ => measurable_const)
  have he (c : C) : (law c).mean
      (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) =
      ((law c).siteLaw physical).weight x := by
    exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
      (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
        (FiniteProbabilityWeights.mean_single_norm _ x)
  simpa only [he] using h

theorem centeredFiniteMarginal_siteLaw :
    (centeredFiniteMarginal μ law hweight).siteLaw physical =
      centeredFiniteMarginal μ (fun c => (law c).siteLaw physical)
        (centeredFinite_siteLaw_weight_measurable law hweight physical) := by
  apply FiniteProbabilityWeights.ext_weight
  funext x
  change ((centeredFiniteMarginal μ law hweight).siteLaw physical).weight x =
    ∫ c, ((law c).siteLaw physical).weight x ∂μ
  calc
    _ = ((centeredFiniteMarginal μ law hweight).siteLaw physical).mean
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖) :=
      (FiniteProbabilityWeights.mean_single_norm _ x).symm
    _ = ∫ c, (law c).mean
        (fun z => 𝔼 t, ‖(Pi.single x (1 : ℂ) : X → ℂ) (physical z t)‖) ∂μ := by
      rw [FiniteProbabilityWeights.siteLaw_mean, centeredFiniteMarginal_mean]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with c
      exact (FiniteProbabilityWeights.siteLaw_mean (law c) physical
        (fun y => ‖(Pi.single x (1 : ℂ) : X → ℂ) y‖)).symm.trans
          (FiniteProbabilityWeights.mean_single_norm _ x)

end Site

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def centeredFiniteSliceResidualEnvelope
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) : ℝ :=
  (⨆ j, sampledSingleTestSeminorm (physical z)
    (normalizedSliceTest (slices z j) (tests z j))) signal

theorem centeredFiniteSliceResidualEnvelope_nonneg
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) :
    0 ≤ centeredFiniteSliceResidualEnvelope physical slices tests signal z :=
  apply_nonneg _ _

theorem centeredFiniteSliceResidualEnvelope_dominates
    {Ω T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (z : Ω) (j : J z) :
    ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ ≤
      centeredFiniteSliceResidualEnvelope physical slices tests signal z := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  change _ ≤ (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hS z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousComponentTopSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : MvPolynomial σ R) (n : ℕ) (hp : p ∈ weightedSupportLE w n) :
    weightedHomogeneousComponent v n (aeval β p) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (weightedHomogeneousComponent w n p) := by
  classical
  let top : σ → MvPolynomial τ R :=
    fun i => weightedHomogeneousComponent v (w i) (β i)
  have hdiff : aeval β p - aeval top p ∈ weightedSupportLT v n := by
    apply weightedComparison_difference w v (aeval β) (aeval top) _ _ _ hp
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_remainder_lt v (hβ i)
  have hzero : weightedHomogeneousComponent v n (aeval β p - aeval top p) = 0 := by
    ext α
    rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hα
    · by_contra hc
      have hlt := hdiff (mem_support_iff.mpr hc)
      change Finsupp.weight v α < n at hlt
      omega
    · rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.trans (aeval_weightedHomogeneousComponent w v top
    (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) n p).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem top_coeff_polynomialTranslate (P : MvPolynomial I R) (v : I → R)
    (a : I →₀ ℕ) (hP : P.totalDegree ≤ a.degree) :
    (polynomialTranslate v P).coeff a = P.coeff a := by
  have ht := polynomialTranslate_sub_mem_weightedSupportLT v (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P a.degree).mpr hP)
  have hz : (polynomialTranslate v P - P).coeff a = 0 := by
    by_contra hn
    have hh : Finsupp.weight (1 : I → ℕ) a < a.degree := ht (mem_support_iff.mpr hn)
    have he : Finsupp.weight (1 : I → ℕ) a = a.degree := by
      simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
    rw [he] at hh
    exact (lt_irrefl _) hh
  simpa only [coeff_sub, sub_eq_zero] using hz

noncomputable def conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) : MvPolynomial J R :=
  killCompl hf (polynomialTranslate (fun i => if i ∈ Set.range f then 0 else v i) P)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BlockMonomialWeight
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ R : Type*} [Fintype ι] [Fintype σ] [CommMonoid R]

theorem blockExponent_weight (π : ι → σ) (a : ι →₀ ℕ) (x : σ → R) :
    (a.prod fun j n => x (π j) ^ n) = (blockExponent π a).prod (fun i n => x i ^ n) := by
  classical
  rw [a.prod_fintype _ (fun _ => pow_zero _),
    (blockExponent π a).prod_fintype _ (fun _ => pow_zero _)]
  simp only [blockExponent_apply]
  calc
    (∏ j, x (π j) ^ a j) =
        ∏ i, ∏ j ∈ Finset.univ.filter (fun j => π j = i), x (π j) ^ a j :=
      (Finset.prod_fiberwise Finset.univ π (fun j => x (π j) ^ a j)).symm
    _ = ∏ i, x i ^ blockDegree π a i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [blockDegree_apply, ← Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X]

noncomputable def selectedResidueCellWeight (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) : ℝ :=
  (∑' z, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V z) /
    (∑' z, selectedResidueSmoothWeight modulus T V z)

theorem selectedResidueCellWeight_nonneg (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ) (r : T) :
    0 ≤ selectedResidueCellWeight modulus T V r := by
  apply div_nonneg
  · apply tsum_nonneg
    intro z
    unfold residueSmoothWeight
    split
    · exact (smoothProductProfile_range (K × X) _).1
    · exact le_rfl
  · exact tsum_nonneg (selectedResidueSmoothWeight_nonneg modulus T V)

theorem selectedResidueCellWeight_sum (modulus : X → ℕ)
    (T : Finset (ColumnResiduePattern K X modulus)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z) :
    (∑ r : T, selectedResidueCellWeight modulus T V r) = 1 := by
  simp only [selectedResidueCellWeight, ← Finset.sum_div]
  rw [← selectedResidueSmoothWeight_mass modulus T V hV, div_self hZ.ne']

theorem selectedResidueSmoothPMF_bounded_mixture (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * φ z) =
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∑' z, ((residueSmoothPMF (boundedColumnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) * φ z := by
  have hm (r : T) := residueSmoothMass_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val)
  have ho (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V) := by rw [hm r]; exact hc r
  rw [selectedResidueSmoothPMF_mixture modulus hmodulus T V hV hZ ho]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueSmoothPMF_congr _ _ modulus hmodulus V hV
    (boundedColumnResidueRepresentative_congr modulus r.val) (ho r) (hc r)]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K X Y : Type*} [Fintype K] [Fintype X]

theorem selectedResidueSmoothPMF_bind_toReal_mixture
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal =
      ∑ r : T, selectedResidueCellWeight q T V r *
        (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
          q hq V hV (hc r)).bind F) y).toReal := by
  apply Complex.ofReal_injective
  simp only [pmf_bind_toReal, Complex.ofReal_tsum, Complex.ofReal_sum, Complex.ofReal_mul]
  exact selectedResidueSmoothPMF_bounded_mixture q hq T V hV hZ hc
    (fun z => ((F z y).toReal : ℂ))

theorem selectedResidueSmoothPMF_bind_le_of_cells
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern K X q))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative q r.val) q)
      (residueProfileWidth q V))
    (F : (K × X → ℤ) → PMF Y) (y : Y) (δ : ℝ)
    (hbound : ∀ r : T, (((residueSmoothPMF (boundedColumnResidueRepresentative q r.val)
      q hq V hV (hc r)).bind F) y).toReal ≤ δ) :
    (((selectedResidueSmoothPMF q T V hV hZ).bind F) y).toReal ≤ δ := by
  rw [selectedResidueSmoothPMF_bind_toReal_mixture q hq T V hV hZ hc F y]
  calc
    _ ≤ ∑ r : T, selectedResidueCellWeight q T V r * δ :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hbound r)
        (selectedResidueCellWeight_nonneg q T V r))
    _ = δ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum q T V hV hZ, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedLieSpan
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def markedLieSpan (v : I → L) (w : I → ℕ) (marked : I → Bool) (d k l : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length ∧ lieTreeEval v a = x}

theorem markedLieSpan_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedLieSpan v w marked e m n ≤ markedLieSpan v w marked d k l := by
  apply Submodule.span_mono
  rintro x ⟨a, hd, hk, hl, rfl⟩
  exact ⟨a, hde.trans hd, hkm.trans hk, hln.trans hl, rfl⟩

theorem markedLieSpan_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {x y : L}
    (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : y ∈ markedLieSpan v w marked e m n) :
    ⁅x, y⁆ ∈ markedLieSpan v w marked (d + e) (k + m) (l + n) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, hd, hk, hl, rfl⟩ := hx
    obtain ⟨b, he, hm, hn, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add hd he,
      Nat.add_le_add hk hm, Nat.add_le_add hl hn, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem markedLieSpan_leaf (v : I → L) (w : I → ℕ) (marked : I → Bool) (i : I) :
    v i ∈ markedLieSpan v w marked (w i) (if marked i then 1 else 0) 1 :=
  Submodule.subset_span ⟨.of i, le_rfl, le_rfl, le_rfl, rfl⟩

theorem markedLieSpan_zero_marked (v : I → L) (w : I → ℕ) (marked : I → Bool) (d l : ℕ) :
    markedLieSpan v w marked d 0 l = weightedLieDegreeLengthSpan v w d l := by
  unfold markedLieSpan weightedLieDegreeLengthSpan
  congr 1
  ext x
  simp only [Nat.zero_le, true_and]

theorem markedLieSpan_le_layer {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer d l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, _, hl, rfl⟩
  exact F.degree_antitone l hd
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

theorem markedLieSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k : ℕ) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r →
      k ≤ lieTreeMarkedCount marked a → η (lieTreeEval v a) = 0) :
    markedLieSpan v w marked s k r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, hd, hk, hl, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases he : lieTreeWeight w a = s
  · by_cases hn : a.length = r
    · exact hzero a he hn hk
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨he.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

theorem markedLieSpan_marked_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d l : ℕ) :
    markedLieSpan v w marked d (s + 1) l = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, _, rfl⟩
  have hcount := (lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a)
  have hs : s < lieTreeWeight w a := by omega
  have hm := F.lieTreeEval_mem_length v w hv a
  rw [F.layer_eq_bot_of_past_top (Or.inl hs)] at hm
  exact hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

noncomputable def frozenCoordinate (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (i : I) : MvPolynomial {i // keep i} R :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩)

noncomputable def freezePolynomial (keep : I → Prop) (fixed : {i // ¬keep i} → R) :
    MvPolynomial I R →ₐ[R] MvPolynomial {i // keep i} R :=
  aeval (frozenCoordinate keep fixed)

theorem frozenCoordinate_support (keep : I → Prop) (fixed : {i // ¬keep i} → R) (i : I) :
    frozenCoordinate keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dif_pos hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dif_neg hi]
    exact weightedSupportLE_C (fun _ : {i // keep i} => 1) 1 (fixed ⟨i, hi⟩)

theorem freezePolynomial_support (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P ∈ weightedSupportLE (fun _ => 1) d :=
  weightedSupportLE_aeval (fun _ => 1) (fun _ => 1) _ (frozenCoordinate_support keep fixed) hP

theorem freezePolynomial_eval (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (P : MvPolynomial I R) (x : {i // keep i} → R) :
    eval x (freezePolynomial keep fixed P) = eval (finiteSplitPoint keep x fixed) P := by
  calc
    _ = eval (fun i => eval x (frozenCoordinate keep fixed i)) P :=
      MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval x) P
    _ = _ := by
      apply congrArg (fun y => eval y P)
      funext i
      by_cases hi : keep i <;> simp [frozenCoordinate, finiteSplitPoint, hi]

theorem freezePolynomial_sub_lower (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P - freezePolynomial keep fixed' P ∈
      weightedSupportLT (fun _ => 1) d := by
  apply weightedComparison_difference (fun _ => 1) (fun _ => 1)
    (freezePolynomial keep fixed) (freezePolynomial keep fixed')
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed i)
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed' i)
    _ hP
  intro i
  by_cases hi : keep i
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_pos hi, sub_self]
    exact Submodule.zero_mem _
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_neg hi, ← map_sub]
    exact weightedSupportLE_lt_succ (weightedSupportLE_C (fun _ => 1) 0 _)

theorem freezePolynomial_top_independent (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      homogeneousComponent d (freezePolynomial keep fixed' P) := by
  have hlower := freezePolynomial_sub_lower keep fixed fixed'
    ((mem_weightedSupportLE_one_iff _ _).mpr hP)
  change weightedHomogeneousComponent (fun _ => 1) d _ =
    weightedHomogeneousComponent (fun _ => 1) d _
  ext α
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  split_ifs with hα
  · have hz : (freezePolynomial keep fixed P - freezePolynomial keep fixed' P).coeff α = 0 := by
      by_contra hn
      have hlt := hlower (mem_support_iff.mpr hn)
      exact (Nat.lt_irrefl d) (hα ▸ hlt)
    exact sub_eq_zero.mp (by simpa only [MvPolynomial.coeff_sub] using hz)
  · rfl

theorem freezePolynomial_map {S : Type*} [CommRing S] (φ : R →+* S)
    (keep : I → Prop) (fixed : {i // ¬keep i} → R) (P : MvPolynomial I R) :
    MvPolynomial.map φ (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => φ (fixed i)) (MvPolynomial.map φ P) := by
  change MvPolynomial.map φ (eval₂ C (frozenCoordinate keep fixed) P) =
    eval₂ C (frozenCoordinate keep (fun i => φ (fixed i))) (MvPolynomial.map φ P)
  rw [map_eval₂]
  apply congrArg (fun f => eval₂ C f (MvPolynomial.map φ P))
  funext i
  by_cases hi : keep i <;> simp [frozenCoordinate, hi]

theorem frozenCoordinate_zero_homogeneous (keep : I → Prop) (i : I) :
    (frozenCoordinate keep (0 : {i // ¬keep i} → R) i).IsWeightedHomogeneous
      (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dif_pos hi]
    exact isWeightedHomogeneous_X R (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dif_neg hi, Pi.zero_apply, map_zero]
    exact isWeightedHomogeneous_zero R (fun _ : {i // keep i} => 1) 1

theorem freezePolynomial_top (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      freezePolynomial keep 0 (homogeneousComponent d P) := by
  rw [freezePolynomial_top_independent keep fixed 0 hP]
  exact (aeval_weightedHomogeneousComponent (fun _ : I => 1) (fun _ => 1)
    (frozenCoordinate keep 0) (frozenCoordinate_zero_homogeneous keep) d P).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueL1Surrogate
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators NNReal

theorem selectedResidueDensityMass_l1_surrogate
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (s : (K × I → ℤ) → X) (f ideal g : X → ℂ)
    (hf : Measurable f) (hi : Measurable ideal) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ x, ‖g x‖ ≤ Cg)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - g (s z)‖) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - ideal (s z)‖) ≤ E + 2 * δ + ε := by
  let ν := (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure
  have hib (x) : ‖ideal x‖ ≤ δ + Cg := by
    calc
      _ ≤ ‖ideal x - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (happrox x) (hgb x)
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable Cf (Filter.Eventually.of_forall hfb)
  have hii : Integrable ideal μ := Integrable.of_bound hi.aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall hib)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable Cg (Filter.Eventually.of_forall hgb)
  have hfs : Integrable (fun z => f (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cf (Filter.Eventually.of_forall (fun z => hfb _))
  have his : Integrable (fun z => ideal (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall (fun z => hib _))
  have hgs : Integrable (fun z => g (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cg (Filter.Eventually.of_forall (fun z => hgb _))
  have hs' : (∫ z, ‖f (s z) - g (s z)‖ ∂ν) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε := by
    exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub hgs).norm).symm.trans_le hsample
  exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub his).norm).trans_le
    (l1_sampling_via_uniform_surrogate μ ν s f ideal g hfi hii hgi hfs his hgs happrox hmass hs')

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerIntegerPolynomialOutput {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Sigma J) : ℤ :=
  eval (fun v => ((crtInput (fun l => p l ^ A l) hq
    (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v) v).val : ℤ))
      (F j.1 j.2)

def taggedPolynomialOutputCurry {s : ℕ} (J : Fin s → Type*) (N : ℕ) :
    (Sigma J → ZMod N) ≃+ (∀ j, J j → ZMod N) :=
  { Equiv.piCurry (fun _ (_ : J _) => ZMod N) with map_add' := fun _ _ => rfl }

section RankBounds

variable {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
  (p A b e : L → ℕ) [∀ l, NeZero (p l)]
  (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
  (C : ℝ) (hC : 0 ≤ C)
  (F : ∀ j, J j → MvPolynomial V ℤ)
  (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
  (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
    (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
    integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
  (r : ∀ l, V → ZMod (p l ^ A l))

include hs hp hinj hC hF hrank

end RankBounds

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def localPrimePowerIntegerPolynomialOutput
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) : ℤ :=
  eval (fun v => ((r v + (p : ZMod (p ^ A)) ^ e * x v).val : ℤ)) (F j.1 j.2)

@[simp] theorem localPrimePowerIntegerPolynomialOutput_reduce
    {V : Type*} {s : ℕ} {J : Fin s → Type*}
    (p A e : ℕ) [NeZero (p ^ A)] (F : ∀ j, J j → MvPolynomial V ℤ)
    (r x : V → ZMod (p ^ A)) (j : Sigma J) :
    (localPrimePowerIntegerPolynomialOutput p A e F r x j : ZMod (p ^ A)) =
      eval₂ (Int.castRingHom (ZMod (p ^ A)))
        (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j.1 j.2) := by
  unfold localPrimePowerIntegerPolynomialOutput
  change (Int.castRingHom (ZMod (p ^ A))) (eval₂ (RingHom.id ℤ) _ _) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]
  congr 1
  funext v
  simp only [Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def prescribedCRTPolynomialInput
    (p A e : L → ℕ)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) : V → ZMod (∏ l, p l ^ A l) :=
  crtInput (fun l => p l ^ A l) hq
    (fun l v => origin l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)

local instance crtInputModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

noncomputable def crtPolynomialInputLaw
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    FiniteProbabilityWeights (V → ZMod (∏ l, p l ^ A l)) :=
  (crtPrimePowerPolynomialLaw (V := V) p A).fiberLaw
    (prescribedCRTPolynomialInput p A e hq origin)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtInputAddEquiv (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ l, V → ZMod (q l)) ≃+ (V → ZMod (∏ l, q l)) where
  toFun := crtInput q hq
  invFun x l v := ZMod.prodEquivPi q hq (x v) l
  left_inv x := by
    funext l v
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun k => x k v)) l
  right_inv x := by
    funext v
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (x v)
  map_add' x y := by
    funext v
    exact map_add (ZMod.prodEquivPi q hq).symm (fun l => x l v) (fun l => y l v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModularVectorCoefficientRank
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def vectorDesignatedRankFailureProbability {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (c : B → A → ZMod N) : ℝ :=
  𝔼 u : Fin n → I → ZMod N,
    if polynomialLinearRow (polynomialIterDifference n
      (∑ b, w b • designatedVectorComponent S Q c b) u) = 0 then 1 else 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothCoefficientRankBadProduct
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

def scalarCoefficientTupleEquiv {T D V : Type*} {B : T → Type*} [AddCommGroup V] :
    ((Σ t, B t × D) → V) ≃+ (∀ t, B t → D → V) where
  toFun x t b d := x ⟨t, (b,d)⟩
  invFun c j := c j.1 j.2.1 j.2.2
  left_inv x := by
    funext j
    rcases j with ⟨t,b,d⟩
    rfl
  right_inv c := rfl
  map_add' x y := rfl

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def scalarCoefficientBad (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I ℤ) (C : ℝ) (M : ℕ) [NeZero M]
    (x : (Σ t, B t × D) → ZMod M) : Prop :=
  ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
    (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
      (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
      (fun b d => x ⟨t,(b,d)⟩)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights _root_.MvPolynomial

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_monomial_eq_C_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (c : R) :
    freezePolynomial keep fixed (monomial d c) =
      C (eval (finiteSplitPoint keep (0 : {i // keep i} → R) fixed) (monomial d c)) := by
  classical
  simp only [freezePolynomial, aeval_monomial, eval_monomial,
    map_mul, map_finsuppProd, map_pow]
  congr 1
  apply Finsupp.prod_congr
  intro i hi
  have hkeep : ¬keep i := fun h => hd ⟨i, h, Finsupp.mem_support_iff.mp hi⟩
  simp [frozenCoordinate, finiteSplitPoint, hkeep]

theorem freezePolynomial_monomial_coeff_eq_zero_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (freezePolynomial keep fixed (monomial d (1 : R))).coeff α = 0 := by
  rw [freezePolynomial_monomial_eq_C_of_no_keep keep fixed d hd]
  exact coeff_C_of_ne_zero hα _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_eval_mem {J τ R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial τ R) (K : Submodule R (J → R))
    (hP : ∀ α, (fun j => (P j).coeff α) ∈ K) (x : τ → R) :
    (fun j => MvPolynomial.eval x (P j)) ∈ K := by
  classical
  let S : Finset (τ →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  have he (j : J) : MvPolynomial.eval x (P j) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) * (P j).coeff α := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum]
    simp only [eval_monomial, mul_comm]
    apply Finset.sum_subset
    · intro α hα
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hα⟩
    · intro α _ hα
      have hz : (P j).coeff α = 0 := by
        simpa only [mem_support_iff, not_not] using hα
      rw [hz]
      simp
  have he' : (fun j => MvPolynomial.eval x (P j)) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) • (fun j => (P j).coeff α) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  exact K.sum_mem (fun α _ => K.smul_mem _ (hP α))

theorem longChart_top_eval_mem {J Full Long : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (f : Long ↪ Full) (r : ℕ)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : Long →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain f) : ℤ) : ℝ)) ∈ K)
    (x : Long → ℝ) :
    (fun j => MvPolynomial.eval x
      (killCompl f.injective (homogeneousComponent r
        (MvPolynomial.map (Int.castRingHom ℝ) (β j))))) ∈ K := by
  apply polynomialFamily_eval_mem
  intro α
  simp only [coeff_killCompl, coeff_homogeneousComponent, Finsupp.degree_mapDomain,
    coeff_map, Int.coe_castRingHom]
  by_cases hα : α.degree = r
  · simp only [if_pos hα]
    exact hcoeff α hα
  · simp only [if_neg hα]
    exact K.zero_mem

theorem longChart_freezePolynomial_zero_eq_killCompl {I R : Type*} [CommRing R]
    (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬ keep i} → R) =
      killCompl (Subtype.val_injective (p := keep)) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : keep i
  · let a : {i // keep i} := ⟨i, hi⟩
    have hk := killCompl_rename_app (R := R) (Subtype.val_injective (p := keep))
      (MvPolynomial.X a)
    simp only [rename_X] at hk
    simpa only [freezePolynomial, aeval_X, frozenCoordinate, dif_pos hi] using hk.symm
  · have hrange : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨a, rfl⟩
      exact hi a.property
    simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_neg hi,
      Pi.zero_apply, map_zero, killCompl, aeval_X, dif_neg hrange]

theorem longChart_frozen_top_eval_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (r : ℕ)
    (hdegree : ∀ j, (β j).totalDegree ≤ r)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : {i // keep i} →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain Subtype.val) : ℤ) : ℝ)) ∈ K)
    (x : {i // keep i} → ℝ) :
    (fun j => MvPolynomial.eval x (homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))))) ∈ K := by
  have htop (j : J) : homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))) =
      killCompl (Subtype.val_injective (p := keep))
        (homogeneousComponent r (MvPolynomial.map (Int.castRingHom ℝ) (β j))) := by
    rw [freezePolynomial_map, freezePolynomial_top keep _
      ((totalDegree_map_le _ _).trans (hdegree j)), longChart_freezePolynomial_zero_eq_killCompl]
  simp only [htop]
  exact longChart_top_eval_mem β (Function.Embedding.subtype keep) r K hcoeff x

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_freeze_coeff_mem {I J R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (keep : I → Prop)
    (fixed : {i // ¬ keep i} → R) (K : Submodule R (J → R))
    (hP : ∀ d, (∃ i, keep i ∧ d i ≠ 0) → (fun j => (P j).coeff d) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j => (freezePolynomial keep fixed (P j)).coeff α) ∈ K := by
  classical
  let S : Finset (I →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  let c (d : I →₀ ℕ) : R := (freezePolynomial keep fixed (monomial d 1)).coeff α
  have hm (d : I →₀ ℕ) (r : R) :
      (freezePolynomial keep fixed (monomial d r)).coeff α = c d * r := by
    have hr : monomial d r = r • monomial d (1 : R) := by
      simp only [smul_monomial, smul_eq_mul, mul_one]
    rw [hr, map_smul, coeff_smul]
    exact mul_comm r (c d)
  have he (j : J) : (freezePolynomial keep fixed (P j)).coeff α =
      ∑ d ∈ S, c d * (P j).coeff d := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum, coeff_sum]
    simp only [hm]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hd⟩
    · intro d _ hd
      have hz : (P j).coeff d = 0 := by
        simpa only [mem_support_iff, not_not] using hd
      rw [hz, mul_zero]
  have he' : (fun j => (freezePolynomial keep fixed (P j)).coeff α) =
      ∑ d ∈ S, c d • (fun j => (P j).coeff d) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  apply K.sum_mem
  intro d _
  by_cases hd : ∃ i, keep i ∧ d i ≠ 0
  · exact K.smul_mem _ (hP d hd)
  · have hc : c d = 0 :=
      freezePolynomial_monomial_coeff_eq_zero_of_no_keep keep fixed d hd α hα
    rw [hc, zero_smul]
    exact K.zero_mem

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialFamily_eval_sub_zero_mem {J I R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (K : Submodule R (J → R))
    (hP : ∀ d, d ≠ 0 → (fun j => (P j).coeff d) ∈ K) (x : I → R) :
    (fun j => eval x (P j) - eval (0 : I → R) (P j)) ∈ K := by
  classical
  have h := polynomialFamily_eval_mem
    (fun j => P j - C (constantCoeff (P j))) K (fun d => ?_) x
  · simpa only [map_sub, eval_C, eval_zero] using h
  · by_cases hd : d = 0
    · subst d
      simp only [coeff_sub, coeff_C, ↓reduceIte, constantCoeff_eq, sub_self]
      exact K.zero_mem
    · simpa [coeff_C, Ne.symm hd] using hP d hd

theorem frozenPolynomialFamily_coeff_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (((β j).coeff d : ℤ) : ℝ)) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j =>
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))).coeff α) ∈ K := by
  have hreal : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (MvPolynomial.map (Int.castRingHom ℝ) (β j)).coeff d) ∈ K := by
    intro d hd
    simpa only [coeff_map, Int.coe_castRingHom] using hcoeff d hd
  have h := polynomialFamily_freeze_coeff_mem
    (fun j => MvPolynomial.map (Int.castRingHom ℝ) (β j)) keep
    (fun i => (fixed i : ℝ)) K hreal α hα
  simpa only [freezePolynomial_map, Int.coe_castRingHom] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointExceptionalPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_spatialMatrixBlock_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P E : ℝ} {n : ℕ}, 0 ≤ P →
      (n : ℝ) ≤ P → 0 ≤ E → E ≤ P →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E + ((n : ℝ)+1)^2+1 ≤
        (P+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E ≤ (P+A)^A := by
  let c : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  have hc : (probabilityProfileLipschitz : ℝ) ≤ (c : ℝ) := Nat.le_ceil _
  let p : Polynomial ℕ :=
    2 * Polynomial.X ^ 3 + 2 +
      2 * Polynomial.X ^ 3 * (11 * Polynomial.X ^ 2 + 11 * Polynomial.X + 5) +
      3 * Polynomial.X ^ 2 + 2 * Polynomial.X + 10 + Polynomial.C c
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget p
  refine ⟨A, hA, ?_⟩
  intro P E n hP hn hE hEP
  have hthreshold : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E ≤
      2*P^3+2+2*P^3*(11*P^2+11*P+5) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E =
        2*(n : ℝ)^3+2+2*(n : ℝ)^3*(11*(n : ℝ)^2+10*n+E+5) := by
      unfold smoothMatrixBlockThresholdLogBudget smoothMatrixBlockConstantLogBudget
      push_cast
      ring
    rw [hstep]
    calc
      _ ≤ 2*P^3+2+2*P^3*(11*P^2+10*P+P+5) := by gcongr
      _ = _ := by ring
  have hev : Polynomial.eval₂ (Nat.castRingHom ℝ) P p =
      2*P^3+2+2*P^3*(11*P^2+11*P+5)+3*P^2+2*P+10+c := by
    simp [p, Polynomial.eval₂_pow]
  have hbudget := hbound P hP
  rw [hev] at hbudget
  constructor
  · apply le_trans _ hbudget
    have hsq : ((n : ℝ)+1)^2 ≤ (P+1)^2 := by gcongr
    nlinarith [Nat.cast_nonneg (α := ℝ) c, sq_nonneg P]
  · apply le_trans _ hbudget
    have heq : smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E =
        smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E +
          3*(n : ℝ)^2+2*n+9+probabilityProfileLipschitz := by
      unfold smoothMatrixBlockWidthLogBudget smoothMatrixBlockMeshLogBudget
      push_cast
      ring
    rw [heq]
    have hsq : (n : ℝ)^2 ≤ P^2 := by gcongr
    nlinarith

end Erdos3

end

section

namespace Erdos3

theorem exists_jointExceptional_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ g₀ : ℝ} {n : ℕ}, 0 ≤ P₀ →
      (n : ℝ) ≤ P₀ → 0 ≤ g₀ → g₀ ≤ P₀ →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 (g₀+8) +
          ((n : ℝ)+1)^2+1 ≤ (P₀+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (g₀+8) ≤ (P₀+A)^A := by
  obtain ⟨a, ha, hbudget⟩ := exists_spatialMatrixBlock_polynomial_budget
  refine ⟨a + 8, by omega, ?_⟩
  intro P₀ g₀ n hP hn hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget (P := P₀ + 8) (E := g₀ + 8)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (P₀ + 8 + a : ℝ) = P₀ + (a + 8 : ℕ) := by push_cast; ring
  have hpow : (P₀ + 8 + a : ℝ)^a ≤ (P₀ + (a + 8 : ℕ))^(a + 8) := by
    rw [hbase]
    apply pow_le_pow_right₀
    · push_cast
      linarith
    · omega
  exact ⟨hthreshold.trans hpow, hwidth.trans hpow⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedFrozenPolynomialMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem realPolynomialMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (fixed : {i // ¬ keep i} → ℝ) (hfixed : ∀ i, |fixed i| ≤ 1)
    (P : MvPolynomial I ℝ) :
    realPolynomialMass (freezePolynomial keep fixed P) ≤ realPolynomialMass P := by
  have hf : ∀ i, realPolynomialMass (frozenCoordinate keep fixed i) ≤ 1 := by
    intro i
    classical
    by_cases hi : keep i
    · simp only [frozenCoordinate, dif_pos hi, realPolynomialMass_X, le_refl]
    · simpa only [frozenCoordinate, dif_neg hi, realPolynomialMass_C] using hfixed ⟨i, hi⟩
  have h := realPolynomialMass_substitution_le P (frozenCoordinate keep fixed)
    (M := 1) le_rfl hf le_rfl
  change realPolynomialMass (eval₂Hom C (frozenCoordinate keep fixed) P) ≤ _
  simpa only [one_pow, mul_one] using h

theorem scaleMvPolynomialAxes_freezePolynomial {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, T i ≠ 0) (fixed : {i // ¬ keep i} → ℝ)
    (P : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => fixed i / T i.val) (scaleMvPolynomialAxes T P) := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval, freezePolynomial_eval,
    freezePolynomial_eval, scaleMvPolynomialAxes_eval]
  apply congrArg (fun y => MvPolynomial.eval y P)
  funext i
  by_cases hi : keep i
  · simp only [finiteSplitPoint, dif_pos hi]
  · simp only [finiteSplitPoint, dif_neg hi]
    field_simp [hT i]

theorem normalizedMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) (fixed : {i // ¬ keep i} → ℝ)
    (hfixed : ∀ i, |fixed i| ≤ T i.val) (P : MvPolynomial I ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T P) := by
  rw [scaleMvPolynomialAxes_freezePolynomial keep T (fun i => (hT i).ne')]
  apply realPolynomialMass_freezePolynomial_le
  intro i
  rw [abs_div, abs_of_pos (hT i.val)]
  exact (div_le_one (hT i.val)).mpr (hfixed i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedComparisonGridPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedComparisonSourcePolynomial (t : ℝ) : ℝ :=
  2 + t * t + 2 * t

def preparedComparisonGridPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  preparedComparisonSourcePolynomial t +
    (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 +
    (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ)

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {R σ : Fin m → ℝ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}

variable {cost : ℝ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityTestMass
namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityMass_bound_of_constant_test
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus T V x)
    (D : (K × I → ℤ) → ℝ) {ε : ℝ}
    (htest : ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * (D z : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * 1‖ ≤ ε) :
    |selectedResidueDensityMass modulus T V D - 1| ≤ ε := by
  rw [selectedResidueSmoothPMF_const] at htest
  simp only [one_mul] at htest
  rw [← selectedResidueDensityMass_complex modulus T V hV hZ D,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htest
  exact htest

end Erdos3

end

end OAI

end


