-- Prove2me | Definitions.Def_OAIErdos3B094
-- name    : OAIErdos3B094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T15:09:48.339129+00:00
-- url     : https://prove2.me/theorems/4316fac9-ad7c-4e55-afb3-aa73b0af9048
-- title:
--   OpenAI Erdős-3 split, definitions bundle 95 of 99
-- statement:
--   Definitions bundle 95 of 99 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B093`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 95 available.
--
--   Modules: `OAI.Erdos3.BohrWidthBudget.exp_neg_budget_le_reciprocal`, `OAI.Erdos3.BohrWidthBudget.polynomial_denominator_le_exp`, `OAI.Erdos3.BohrWidthBudget.rational_width_ge_exponential`, `OAI.Erdos3.BohrWidthBudget.rational_width_lower_bound`, `OAI.Erdos3.BohrWidthBudget.selector_scale_lower_bound`, `OAI.Erdos3.BoundedPrime`, `OAI.Erdos3.HasLayerSamplingRank.residueAffine`, `OAI.Erdos3.MultidegreeLieFiltration.Adapted`, `OAI.Erdos3.MultidegreeLieFiltration.PolynomialOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.PolynomialOrbit.adapted`, `OAI.Erdos3.MultidegreeLieFiltration.PolynomialOrbit.log`, `OAI.Erdos3.MultidegreeLieFiltration.WeightedAdapted`, `OAI.Erdos3.MultidegreeLieFiltration.active_lie_weighted`, `OAI.Erdos3.MultidegreeLieFiltration.adaptedLieSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.adaptedSubmodule`, `OAI.Erdos3.MultidegreeLieFiltration.adapted_coefficient_mem_coordinate`, `OAI.Erdos3.MultidegreeLieFiltration.adapted_coefficient_zero_of_coordinate`, `OAI.Erdos3.MultidegreeLieFiltration.adapted_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleFiltrationLayerEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleFirst`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayerEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer_coordinates`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleLayer_top_relation`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleProjection`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleProjection_one`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleProjection_two`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleProjection_zero`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleProjections_mem`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleSecond`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleThird`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleToPi`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleToPi_injective`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTripleTop_relation`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTriple_top_group_relation`, `OAI.Erdos3.MultidegreeLieFiltration.coordinateActiveLayer`, `OAI.Erdos3.MultidegreeLieFiltration.coordinateActiveLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.coordinateActiveLayer_realification`, `OAI.Erdos3.MultidegreeLieFiltration.coordinateIdeal_abelian`, `OAI.Erdos3.MultidegreeLieFiltration.exists_additiveTriple_layer_basis`, `OAI.Erdos3.MultidegreeLieFiltration.lie_mem_adaptedSubmodule`, `OAI.Erdos3.MultidegreeLieFiltration.mem_additiveTripleLayer`, `OAI.Erdos3.MultidegreeLieFiltration.mem_weightedFiltration_layer`, `OAI.Erdos3.MultidegreeLieFiltration.monomial_mem_adaptedSubmodule`, `OAI.Erdos3.MultidegreeLieFiltration.omitted_weighted_top`, `OAI.Erdos3.MultidegreeLieFiltration.orbitEquivOfEq`, `OAI.Erdos3.MultidegreeLieFiltration.orbitEquivOfEq_eval`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitEval`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitEval_coord`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitEval_eq_of_zero_coordinate`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialSubgroup`, `OAI.Erdos3.MultidegreeLieFiltration.quotientMultidegree`, `OAI.Erdos3.MultidegreeLieFiltration.quotientMultidegree_layer_eq_bot`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTripleProjection`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTripleProjection_coord`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTripleProjection_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTriple_top_group_relation`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTriple_top_phase`, `OAI.Erdos3.MultidegreeLieFiltration.realTripleEquiv_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleEquiv_coe`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleEquiv_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleEquiv_projection`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleEquiv_symm_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedTripleLayerEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedEquiv_coe`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedEquiv_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedEquiv_symm_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.restrictWeightedOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.restrictWeightedOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.restrictWeightedPolynomial`, `OAI.Erdos3.MultidegreeLieFiltration.restrictWeightedPolynomial_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.restrictWeightedPolynomial_eval`, `OAI.Erdos3.MultidegreeLieFiltration.split_substitution_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.split_substitution_add`, `OAI.Erdos3.MultidegreeLieFiltration.split_substitution_sub_mem_active`, `OAI.Erdos3.MultidegreeLieFiltration.split_substitution_sub_mem_coordinate`, `OAI.Erdos3.MultidegreeLieFiltration.split_substitution_zero_weighted`, `OAI.Erdos3.MultidegreeLieFiltration.toOrdinaryOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.toOrdinaryOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdaptedLieSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdaptedSubmodule`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_bch`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_coefficients_mem`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_constant`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_lie`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_monomial`, `OAI.Erdos3.MultidegreeLieFiltration.weightedAdapted_substitute`, `OAI.Erdos3.MultidegreeLieFiltration.weightedFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_le_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_realification`, `OAI.Erdos3.MultidegreeLieFiltration.weightedSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.weighted_lie_active`, `OAI.Erdos3.NilpotentLieFiltration.adapted_quotientLie`, `OAI.Erdos3.NilpotentLieFiltration.mem_realQuotientStepHom_ker`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareFiltration_top`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareLattice`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareLieSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.quotientInducedMark_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.quotientLie`, `OAI.Erdos3.NilpotentLieFiltration.quotientLie_mem`, `OAI.Erdos3.NilpotentLieFiltration.quotientPolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.quotientPolynomialOrbit_log`, `OAI.Erdos3.NilpotentLieFiltration.quotientStepHom`, `OAI.Erdos3.NilpotentLieFiltration.quotientStepHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.quotientTop`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_eq_span_basis`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_le_span_scaled_basis`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientPolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientPolynomialOrbit_eval`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientStepHom`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientStepHom_surjective`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientStep_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.squareFiltration`, `OAI.Erdos3.NilpotentLieFiltration.squareFst`, `OAI.Erdos3.NilpotentLieFiltration.squareFstHom`, `OAI.Erdos3.NilpotentLieFiltration.squareFstHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.squareFst_apply`, `OAI.Erdos3.NilpotentLieFiltration.squareLattice`, `OAI.Erdos3.NilpotentLieFiltration.squareLattice_le_fst`, `OAI.Erdos3.NilpotentLieFiltration.squareLattice_le_snd`, `OAI.Erdos3.NilpotentLieFiltration.squareLayer`, `OAI.Erdos3.NilpotentLieFiltration.squareLayer_antitone`, `OAI.Erdos3.NilpotentLieFiltration.squareLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.squareLieSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.squareObservable`, `OAI.Erdos3.NilpotentLieFiltration.squareObservable_mk`, `OAI.Erdos3.NilpotentLieFiltration.squareObservable_top_invariant`, `OAI.Erdos3.NilpotentLieFiltration.squareSnd`, `OAI.Erdos3.NilpotentLieFiltration.squareSndHom`, `OAI.Erdos3.NilpotentLieFiltration.squareSndHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.squareSnd_apply`, `OAI.Erdos3.NilpotentLieFiltration.square_top_projections`, `OAI.Erdos3.NilpotentLieFiltration.top_commutes`, `OAI.Erdos3.NilpotentLieFiltration.top_layer_central`, `OAI.Erdos3.PolynomialRationalApproximation.affine_pullback`, `OAI.Erdos3.PolynomialRationalApproximation.homogeneous_dilation_pullback`, `OAI.Erdos3.RankPreparationFamily`, `OAI.Erdos3.RankPreparationFamily.Sized`, `OAI.Erdos3.RankPreparationFamily.Sized.mono`, `OAI.Erdos3.RankPreparationFamily.Sized.uniform`, `OAI.Erdos3.RankPreparationFamily.absorb`, `OAI.Erdos3.RankPreparationFamily.descend`, `OAI.Erdos3.RankPreparationFamily.integerRemainder`, `OAI.Erdos3.RankPreparationFamily.polynomial`, `OAI.Erdos3.RankPreparationFamily.potential`, `OAI.Erdos3.RankPreparationFamily.pullback`, `OAI.Erdos3.RankPreparationFamily.pullback_potential`, `OAI.Erdos3.RankPreparationFamily.reindex`, `OAI.Erdos3.RankPreparationFamily.reindex_potential`, `OAI.Erdos3.RankPreparationFamily.value`, `OAI.Erdos3.RankPreparationLayer.Valid`, `OAI.Erdos3.RankPreparationLayer.Valid.mono_height`, `OAI.Erdos3.RankPreparationLayer.appendLine`, `OAI.Erdos3.RankPreparationLayer.casesOn`, `OAI.Erdos3.RankPreparationLayer.cut`, `OAI.Erdos3.RankPreparationLayer.empty`, `OAI.Erdos3.RankPreparationLayer.empty_rank`, `OAI.Erdos3.RankPreparationLayer.empty_valid`, `OAI.Erdos3.RankPreparationLayer.empty_value`, `OAI.Erdos3.RankPreparationLayer.initial`, `OAI.Erdos3.RankPreparationLayer.initial_rank`, `OAI.Erdos3.RankPreparationLayer.initial_space`, `OAI.Erdos3.RankPreparationLayer.initial_value`, `OAI.Erdos3.RankPreparationLayer.pullback`, `OAI.Erdos3.RankPreparationLayer.pullback_rank`, `OAI.Erdos3.RankPreparationLayer.pullback_space`, `OAI.Erdos3.RankPreparationLayer.rank`, `OAI.Erdos3.RankPreparationLayer.reindex`, `OAI.Erdos3.RankPreparationLayer.reindex_rank`, `OAI.Erdos3.RankPreparationLayer.reindex_space`, `OAI.Erdos3.RankPreparationLayer.space`, `OAI.Erdos3.RankPreparationLayer.value`, `OAI.Erdos3.RelativeChangSanders.localChangBaseScale_ge_of_dimension_le`, `OAI.Erdos3.RelativeChangSanders.localChangDimension_half_le_of_card`, `OAI.Erdos3.VectorPolynomial.coefficients_residueAffine_nonzero_mem`, `OAI.Erdos3.VectorPolynomial.coefficients_substitute_nonzero_mem`, `OAI.Erdos3.VectorPolynomial.coefficients_substitute_update_sub_mem`, `OAI.Erdos3.VectorPolynomial.eval_eq_of_zero_coordinate`, `OAI.Erdos3.VectorPolynomial.eval_residueAffine`, `OAI.Erdos3.VectorPolynomial.exists_jointRationalSpace_defining_matrix`, `OAI.Erdos3.VectorPolynomial.integerCoordinates`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_residueAffine`, `OAI.Erdos3.VectorPolynomial.rankCutDirectionHeight`, `OAI.Erdos3.VectorPolynomial.residueAffine`, `OAI.Erdos3.VectorPolynomial.substitute_update_add`, `OAI.Erdos3.affineFramePolynomial`, `OAI.Erdos3.affineFramePolynomial_degree`, `OAI.Erdos3.affineFramePolynomial_eval`, `OAI.Erdos3.affineFramePolynomial_map`, `OAI.Erdos3.affineFramePolynomial_top_one`, `OAI.Erdos3.algebraic_major_affine_top_dilation_identity`, `OAI.Erdos3.algebraic_major_dilation_pullback_identity`, `OAI.Erdos3.algebraic_major_restore_integer_coefficients`, `OAI.Erdos3.algebraic_major_weighted_affine_top_pullback_decomposition`, `OAI.Erdos3.algebraic_major_weighted_dilation_pullback_decomposition`, `OAI.Erdos3.boundedPrime`, `OAI.Erdos3.boundedPrimeExponent`, `OAI.Erdos3.boundedPrimePower`, `OAI.Erdos3.boundedPrimePower_neZero`, `OAI.Erdos3.boundedPrimePower_pos`, `OAI.Erdos3.boundedPrimeProduct`, `OAI.Erdos3.boundedPrime_prime`, `OAI.Erdos3.boundedPrimes`, `OAI.Erdos3.coeff_polynomial_dilation`, `OAI.Erdos3.cosetMap_smul`, `OAI.Erdos3.existsUnique_translation_of_shear_exp`, `OAI.Erdos3.exists_uniform_family_member_net`, `OAI.Erdos3.exists_uniform_family_member_net_half`, `OAI.Erdos3.exists_uniform_family_member_net_of_polynomial_log`, `OAI.Erdos3.homogeneousComponent_polynomialTranslate`, `OAI.Erdos3.homogeneousComponent_polynomial_dilation`, `OAI.Erdos3.horizontal_parts_separation_equiv`, `OAI.Erdos3.integerPolynomial_map_rat_real`, `OAI.Erdos3.jointResidueAffinePolynomial`, `OAI.Erdos3.jointResidueAffinePolynomial_degree`, `OAI.Erdos3.jointResidueAffinePolynomial_eval`, `OAI.Erdos3.jointResidueAffinePolynomial_sub_axes_lower`, `OAI.Erdos3.jointResidueAffinePolynomial_weightedHomogeneousComponent`, `OAI.Erdos3.jointResidueAffinePolynomial_weightedHomogeneousComponent_eval`, `OAI.Erdos3.jointSpaceDefiningHeight_le_exp`, `OAI.Erdos3.lieQuotientDescend`, `OAI.Erdos3.lieQuotientDescend_mk`, `OAI.Erdos3.majorParameterRename_degree`, `OAI.Erdos3.majorParameterRename_homogeneous`, `OAI.Erdos3.majorParameterRename_lower`, `OAI.Erdos3.majorParameterRename_slot_degree_zero`, `OAI.Erdos3.majorSlowDilationPullback`, `OAI.Erdos3.majorSlowDilationPullback_eval`, `OAI.Erdos3.majorSlowDilationPullback_mass_le`, `OAI.Erdos3.majorSlowDilationPullback_mem_weightedSupportLE`, `OAI.Erdos3.majorTranslationJointPolynomial`, `OAI.Erdos3.majorTranslationJointPolynomial_degree`, `OAI.Erdos3.majorTranslationJointPolynomial_eq_sub_aeval`, `OAI.Erdos3.majorTranslationJointPolynomial_lower`, `OAI.Erdos3.majorTranslationJointPolynomial_slot_lower`, `OAI.Erdos3.majorTranslationJointPolynomial_specialize`, `OAI.Erdos3.majorTranslationJointPolynomial_specialize_lower`, `OAI.Erdos3.majorTranslationJointPolynomial_sub`, `OAI.Erdos3.majorTranslationJointPolynomial_sub_top_lower`, `OAI.Erdos3.majorTranslationJointPolynomial_top_homogeneous`, `OAI.Erdos3.majorTranslationJointPolynomial_weightedHomogeneousComponent`, `OAI.Erdos3.majorTranslationTopCoordinates`, `OAI.Erdos3.majorTranslationTopCoordinates_degree`, `OAI.Erdos3.majorTranslationTopCoordinates_homogeneous`, `OAI.Erdos3.majorTranslationTopCoordinates_remainder`, `OAI.Erdos3.mem_boundedPrimes`, `OAI.Erdos3.monomialScale_const_mul_degree`, `OAI.Erdos3.monomialScale_le_const_mul`, `OAI.Erdos3.multidegreeWeight_finsupp`, `OAI.Erdos3.multidegreeWeight_le_sum`, `OAI.Erdos3.omittedCoordinateWeight`, `OAI.Erdos3.omittedCoordinateWeight_le_one`, `OAI.Erdos3.omittedCoordinateWeight_total`, `OAI.Erdos3.polynomialParameterEval_monomial`, `OAI.Erdos3.polynomialSlotCoefficient`, `OAI.Erdos3.polynomialSlotCoefficient_coeff`, `OAI.Erdos3.polynomialSlotCoefficient_degree`, `OAI.Erdos3.polynomialSlotCoefficient_eval`, `OAI.Erdos3.polynomialSlotCoefficient_monomial`, `OAI.Erdos3.polynomialSlotCoefficient_weightedHomogeneousComponent`, `OAI.Erdos3.polynomial_dilation_monomial`, `OAI.Erdos3.quotientInducedMark`, `OAI.Erdos3.quotientInducedMark_comp`, `OAI.Erdos3.quotientInducedMark_mk`, `OAI.Erdos3.quotientInducedMark_real_comp`, `OAI.Erdos3.quotientInducedMark_real_mk`, `OAI.Erdos3.rationalLieInclusion_central`, `OAI.Erdos3.residueAffinePolynomial_eq_dilation_translate`, `OAI.Erdos3.residueAffinePolynomial_eval_real`, `OAI.Erdos3.residueAffinePolynomial_homogeneousComponent`, `OAI.Erdos3.residueAffinePolynomial_homogeneousComponent_eval`, `OAI.Erdos3.residueAffinePolynomial_weightedHomogeneousComponent_eval`, `OAI.Erdos3.restoredMajorRemainder`, `OAI.Erdos3.restoredMajorRemainder_coefficientGrid`, `OAI.Erdos3.restoredMajorRemainder_degree`, `OAI.Erdos3.restoredMajorRemainder_eval`, `OAI.Erdos3.samplingDensity_le_of_smallDoubling`, `OAI.Erdos3.scaleMvPolynomialAxes_C_mul`, `OAI.Erdos3.scaleMvPolynomialAxes_affineFrame_eq_const_add_top`, `OAI.Erdos3.scaleMvPolynomialAxes_affineFrame_top_one`, `OAI.Erdos3.scaled_basis_mem_bchSubgroup`, `OAI.Erdos3.scaled_real_basis_central`, `OAI.Erdos3.scaled_real_basis_coordinate_bound`, `OAI.Erdos3.scaled_real_basis_mem_realification`, `OAI.Erdos3.slowPolynomialSliceRadius`, `OAI.Erdos3.slowPolynomialSliceRadius_eq`, `OAI.Erdos3.slowPolynomialSliceRadius_pos`, `OAI.Erdos3.slowPolynomialSliceSlope`, `OAI.Erdos3.slowPolynomialSliceSlope_le_exp`, `OAI.Erdos3.slowPolynomialSliceSlope_nonneg`, `OAI.Erdos3.slowPolynomialSlice_log_cost`, `OAI.Erdos3.spatialAffineFull_inv_mul_mass_le`, `OAI.Erdos3.spatialAffineFull_mass_le`, `OAI.Erdos3.spatialAffineFull_scaled_inv_mul_mass_le`, `OAI.Erdos3.spatialAffineTop_inv_mul_mass_le`, `OAI.Erdos3.spatialAffineTop_mass_le`, `OAI.Erdos3.spatialAffineTop_scaled_inv_mul_mass_le`, `OAI.Erdos3.specializeMajorParameters_mem_weightedSupportLT`, `OAI.Erdos3.splitCoordinatePolynomial`, `OAI.Erdos3.splitCoordinatePolynomial_eval`, `OAI.Erdos3.splitCoordinatePolynomial_support`, `OAI.Erdos3.splitCoordinatePolynomial_zero_support`, `OAI.Erdos3.sumExponent_injective`, `OAI.Erdos3.sumExponent_weight`, `OAI.Erdos3.translationShear_derivation_rename`, `OAI.Erdos3.translationShear_exp_extra_coordinate`, `OAI.Erdos3.tripleToPi`, `OAI.Erdos3.tripleToPi_injective`, `OAI.Erdos3.tripleToPi_one`, `OAI.Erdos3.tripleToPi_two`, `OAI.Erdos3.tripleToPi_zero`, `OAI.Erdos3.uniformFamilyMemberNet_half_log_budget`, `OAI.Erdos3.weightedHomogeneousComponent_fractional_restoration`, `_private.Lattices.AlgebraicMajorWeightedAffineTopPullback.0.OAI.Erdos3.jointResidueAffine_variables_degree`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B096

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedSubalgebra (c : σ → ℕ) : LieSubalgebra ℚ L :=
  (F.weightedLayer c 1).toLieSubalgebra

noncomputable def weightedFiltration (c : σ → ℕ) :
    NilpotentLieFiltration (F.weightedSubalgebra c) (multidegreeWeight c bound) where
  layer n := (F.weightedLayer c (max 1 n)).toSubmodule.comap (F.weightedSubalgebra c).incl.toLinearMap
  antitone := by
    intro i j hij x hx
    exact F.weightedLayer_antitone c (max_le_max_left 1 hij) hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := by
    intro i j x y hx hy
    change ⁅(x : L), (y : L)⁆ ∈ F.weightedLayer c (max 1 (i + j))
    exact F.weightedLayer_antitone c (by omega : max 1 (i + j) ≤ max 1 i + max 1 j)
      (F.weightedLayer_lie_mem c hx hy)
  terminal := by
    apply bot_unique
    intro x hx
    change (x : L) ∈ F.weightedLayer c (max 1 (multidegreeWeight c bound + 1)) at hx
    rw [max_eq_right (by omega : 1 ≤ multidegreeWeight c bound + 1), F.weightedLayer_terminal c] at hx
    change x = 0
    exact Subtype.ext ((LieSubmodule.mem_bot (x : L)).mp hx)

theorem mem_weightedFiltration_layer (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (x : F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).layer n ↔ (x : L) ∈ F.weightedLayer c n := by
  change (x : L) ∈ F.weightedLayer c (max 1 n) ↔ _
  rw [max_eq_right hn]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_le_sum {σ : Type*} [Fintype σ]
    (c a : σ → ℕ) (hc : ∀ i, c i ≤ 1) : multidegreeWeight c a ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using Nat.mul_le_mul_right (a i) (hc i)

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_le_ordinary (c : σ → ℕ) (hc : ∀ i, c i ≤ 1) (n : ℕ) :
    (F.weightedLayer c n).toSubmodule ≤ F.ordinary.layer n := by
  change (⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val).toSubmodule ≤ _
  rw [LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro a
  exact (F.layer_le_ordinary a.val).trans
    (F.ordinary.antitone (a.property.trans (multidegreeWeight_le_sum c a.val hc)))

theorem coordinateIdeal_abelian [DecidableEq σ] (i : σ) (hi : bound i ≤ 1)
    {x y : L} (hx : x ∈ F.layerIdeal (Pi.single i 1))
    (hy : y ∈ F.layerIdeal (Pi.single i 1)) : ⁅x, y⁆ = 0 := by
  have hnot : ¬(Pi.single i 1 + Pi.single i 1 : σ → ℕ) ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  have h := F.lie_mem hx hy
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def coordinateActiveLayer (i : σ) (n : ℕ) : Submodule ℚ L :=
  F.layer (Pi.single i 1) ⊓ F.ordinary.layer n

theorem coordinateActiveLayer_antitone (i : σ) : Antitone (F.coordinateActiveLayer i) :=
  fun _ _ h _ hx => ⟨hx.1, F.ordinary.antitone h hx.2⟩

theorem weighted_lie_active (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.weightedLayer c m) (hy : y ∈ F.coordinateActiveLayer i n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨(F.layerIdeal (Pi.single i 1)).lie_mem hy.1,
    F.ordinary.lie_mem (F.weightedLayer_le_ordinary c hc m hx) hy.2⟩

theorem active_lie_weighted (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.coordinateActiveLayer i m) (hy : y ∈ F.weightedLayer c n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨lie_mem_left (R := ℚ) (L := L) (F.layerIdeal (Pi.single i 1)) x y hx.1,
    F.ordinary.lie_mem hx.2 (F.weightedLayer_le_ordinary c hc n hy)⟩

noncomputable def additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) :
    Submodule ℚ (L × L × L) :=
  ((F.weightedLayer c n).toSubmodule.comap tripleNeutral) ⊓
    ((F.coordinateActiveLayer i n).comap tripleLeft ⊓
      (F.coordinateActiveLayer i n).comap tripleRight)

theorem mem_additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) (x : L × L × L) :
    x ∈ F.additiveTripleLayer i c n ↔
      tripleNeutral x ∈ F.weightedLayer c n ∧
      tripleLeft x ∈ F.coordinateActiveLayer i n ∧
      tripleRight x ∈ F.coordinateActiveLayer i n := Iff.rfl

theorem additiveTripleLayer_antitone (i : σ) (c : σ → ℕ) : Antitone (F.additiveTripleLayer i c) := by
  intro m n h x hx
  exact ⟨F.weightedLayer_antitone c h hx.1,
    F.coordinateActiveLayer_antitone i h hx.2.1, F.coordinateActiveLayer_antitone i h hx.2.2⟩

theorem additiveTripleLayer_lie_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {m n : ℕ} {x y : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c m) (hy : y ∈ F.additiveTripleLayer i c n) :
    ⁅x, y⁆ ∈ F.additiveTripleLayer i c (m + n) := by
  have heq : ⁅x, y⁆ = tripleAssemble ⁅tripleNeutral x, tripleNeutral y⁆
      (⁅tripleNeutral x, tripleLeft y⁆ + ⁅tripleLeft x, tripleNeutral y⁆)
      (⁅tripleNeutral x, tripleRight y⁆ + ⁅tripleRight x, tripleNeutral y⁆) := by
    calc
      ⁅x, y⁆ = ⁅tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x),
          tripleAssemble (tripleNeutral y) (tripleLeft y) (tripleRight y)⁆ := by
        rw [tripleAssemble_decompose, tripleAssemble_decompose]
      _ = _ := tripleAssemble_lie _ _ _ _ _ _
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.2.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.2.1)
  rw [heq, F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble, tripleRight_assemble]
  exact ⟨F.weightedLayer_lie_mem c hx.1 hy.1,
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.1) (F.active_lie_weighted i c hc hx.2.1 hy.1),
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.2) (F.active_lie_weighted i c hc hx.2.2 hy.1)⟩

theorem additiveTripleLayer_coordinates (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {n : ℕ} {x : L × L × L} (hx : x ∈ F.additiveTripleLayer i c n) :
    x.1 ∈ F.ordinary.layer n ∧ x.2.1 ∈ F.ordinary.layer n ∧ x.2.2 ∈ F.ordinary.layer n := by
  have ha := F.weightedLayer_le_ordinary c hc n hx.1
  have hb := hx.2.1.2
  have hc' := hx.2.2.2
  have heq := tripleAssemble_decompose x
  rw [← heq]
  exact ⟨(F.ordinary.layer n).add_mem ((F.ordinary.layer n).add_mem ha hb) hc',
    (F.ordinary.layer n).add_mem ha hb, (F.ordinary.layer n).add_mem ha hc'⟩

theorem additiveTripleLayer_terminal (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleLayer i c (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := F.additiveTripleLayer_coordinates i c hc hx
  simp only [F.ordinary.terminal, Submodule.mem_bot] at h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

theorem additiveTripleLayer_top_relation (i : σ) (c : σ → ℕ)
    (htop : F.weightedLayer c s = ⊥) {x : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c s) : x.1 = x.2.1 + x.2.2 := by
  have h : tripleNeutral x ∈ F.weightedLayer c s := hx.1
  rw [htop, LieSubmodule.mem_bot] at h
  change x.2.1 + x.2.2 - x.1 = 0 at h
  exact (sub_eq_zero.mp h).symm

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleSubalgebra (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) : LieSubalgebra ℚ (L × L × L) :=
  { F.additiveTripleLayer i c 1 with
    lie_mem' := fun hx hy => F.additiveTripleLayer_antitone i c (by decide : 1 ≤ 1 + 1)
      (F.additiveTripleLayer_lie_mem i hi c hc hx hy) }

noncomputable def additiveTripleFiltration (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    NilpotentLieFiltration (F.additiveTripleSubalgebra i hi c hc) s where
  layer n := (F.additiveTripleLayer i c n).comap (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.additiveTripleLayer_antitone i c h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.additiveTripleLayer_lie_mem i hi c hc hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    have h : (x : L × L × L) ∈ F.additiveTripleLayer i c (s + 1) := hx
    rw [F.additiveTripleLayer_terminal i c hc, Submodule.mem_bot] at h
    exact h

noncomputable def additiveTripleFirst (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl

noncomputable def additiveTripleSecond (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

noncomputable def additiveTripleThird (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

theorem additiveTripleProjections_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {n : ℕ}
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer n) :
    F.additiveTripleFirst i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleSecond i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleThird i hi c hc x ∈ F.ordinary.layer n :=
  F.additiveTripleLayer_coordinates i c hc hx

theorem additiveTripleTop_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer s) :
    F.additiveTripleFirst i hi c hc x =
      F.additiveTripleSecond i hi c hc x + F.additiveTripleThird i hi c hc x :=
  F.additiveTripleLayer_top_relation i c htop hx

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleToPi : (L × L × L) →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  liePiMap ![LieHom.fst ℚ L (L × L),
    (LieHom.fst ℚ L L).comp (LieHom.snd ℚ L (L × L)),
    (LieHom.snd ℚ L L).comp (LieHom.snd ℚ L (L × L))]

@[simp] theorem tripleToPi_zero (x : L × L × L) : tripleToPi x 0 = x.1 := rfl

@[simp] theorem tripleToPi_one (x : L × L × L) : tripleToPi x 1 = x.2.1 := rfl

@[simp] theorem tripleToPi_two (x : L × L × L) : tripleToPi x 2 = x.2.2 := rfl

theorem tripleToPi_injective : Function.Injective (tripleToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleToPi (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  tripleToPi.comp (F.additiveTripleSubalgebra i hi c hc).incl

theorem additiveTripleToPi_injective (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Function.Injective (F.additiveTripleToPi i hi c hc) :=
  fun _ _ h => Subtype.ext (tripleToPi_injective h)

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_realification (c : σ → ℕ) (n : ℕ) :
    (F.realification.weightedLayer c n).toSubmodule =
      ((F.weightedLayer c n).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [weightedLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

noncomputable def realifiedWeightedEquiv (c : σ → ℕ) :
    (ℝ ⊗[ℚ] F.weightedSubalgebra c) ≃ₗ[ℚ] F.realification.weightedSubalgebra c :=
  ((realificationSubmoduleEquiv (F.weightedSubalgebra c).toSubmodule).restrictScalars ℚ).trans
    (LinearEquiv.ofEq _ _ (F.weightedLayer_realification c 1).symm)

theorem realifiedWeightedEquiv_coe (c : σ → ℕ) (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) =
      realificationLieHom (F.weightedSubalgebra c).incl x := rfl

theorem realifiedWeightedEquiv_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).realification.layer n ↔
      F.realifiedWeightedEquiv c x ∈ (F.realification.weightedFiltration c).layer n := by
  change x ∈ ((F.weightedLayer c (max 1 n)).toSubmodule.comap
    (F.weightedSubalgebra c).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change (F.weightedSubalgebra c).incl.toLinearMap.baseChange ℝ x ∈
    (F.weightedLayer c (max 1 n)).toSubmodule.baseChange ℝ ↔
      (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) ∈ F.realification.weightedLayer c (max 1 n)
  rw [F.realifiedWeightedEquiv_coe]
  have h := F.weightedLayer_realification c (max 1 n)
  change _ = _ at h
  change _ ↔ _ ∈ (F.realification.weightedLayer c (max 1 n)).toSubmodule
  rw [h]
  rfl

theorem realifiedWeightedEquiv_symm_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : F.realification.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c).symm x ∈ (F.weightedFiltration c).realification.layer n ↔
      x ∈ (F.realification.weightedFiltration c).layer n := by
  rw [F.realifiedWeightedEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem coordinateActiveLayer_realification (i : σ) (n : ℕ) :
    F.realification.coordinateActiveLayer i n =
      ((F.coordinateActiveLayer i n).baseChange ℝ).restrictScalars ℚ := by
  rw [coordinateActiveLayer, coordinateActiveLayer, realification_inf]
  rfl

theorem realTripleEquiv_mem_layer (i : σ) (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L × L)) :
    realTripleEquiv x ∈ F.realification.additiveTripleLayer i c n ↔
      x ∈ (F.additiveTripleLayer i c n).baseChange ℝ := by
  have hw (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.weightedLayer c n ↔
      y ∈ (F.weightedLayer c n).toSubmodule.baseChange ℝ := by
    change y ∈ (F.realification.weightedLayer c n).toSubmodule ↔ _
    rw [F.weightedLayer_realification]
    rfl
  have ha (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.coordinateActiveLayer i n ↔
      y ∈ (F.coordinateActiveLayer i n).baseChange ℝ := by
    rw [F.coordinateActiveLayer_realification]
    rfl
  rw [F.realification.mem_additiveTripleLayer, hw, ha, ha,
    realTripleEquiv_neutral, realTripleEquiv_left, realTripleEquiv_right]
  simp only [additiveTripleLayer, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    ((F.additiveTripleLayer i c n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.additiveTripleLayer i c n where
  toFun x := ⟨realTripleEquiv x.val, (F.realTripleEquiv_mem_layer i c n x.val).mpr x.property⟩
  invFun x := ⟨realTripleEquiv.symm x.val, (F.realTripleEquiv_mem_layer i c n _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realTripleEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realTripleEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realTripleEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realTripleEquiv.restrictScalars ℚ).map_smul r x.val)

noncomputable def realifiedAdditiveTripleEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    (ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) ≃ₗ[ℚ]
      F.realification.additiveTripleSubalgebra i hi c hc :=
  ((realificationSubmoduleEquiv (F.additiveTripleLayer i c 1)).restrictScalars ℚ).trans
    (F.realifiedTripleLayerEquiv i c 1)

theorem realifiedAdditiveTripleEquiv_coe (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc x :
      (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
        realTripleEquiv (realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x) := rfl

theorem realifiedAdditiveTripleEquiv_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    x ∈ (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      F.realifiedAdditiveTripleEquiv i hi c hc x ∈
        (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  change x ∈ ((F.additiveTripleLayer i c n).comap
    (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x ∈
    (F.additiveTripleLayer i c n).baseChange ℝ ↔
      (F.realifiedAdditiveTripleEquiv i hi c hc x :
        (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
          F.realification.additiveTripleLayer i c n
  rw [F.realifiedAdditiveTripleEquiv_coe, F.realTripleEquiv_mem_layer]

theorem realifiedAdditiveTripleEquiv_symm_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : F.realification.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc).symm x ∈
        (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      x ∈ (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  rw [F.realifiedAdditiveTripleEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ τ R V : Type*} [DecidableEq σ] [CommRing R] [AddCommGroup V] [Module R V]

theorem substitute_update_add (f : σ → MvPolynomial τ R) (i : σ)
    (u v : MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (hp : ∀ a, 1 < a i → coefficients p a = 0) :
    substitute (Function.update f i (u + v)) p =
      substitute (Function.update f i u) p + substitute (Function.update f i v) p -
      substitute (Function.update f i 0) p := by
  apply coefficients.injective
  ext b
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply, coefficients_substitute]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i ≤ 1
  · rw [aeval_monomial_update_add (R := R) f i u v a ha,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_add, sub_smul, add_smul]
  · simp only [hp a (Nat.lt_of_not_ge ha), smul_zero, add_zero, sub_zero]

theorem coefficients_substitute_update_sub_mem (P : Submodule R V)
    (f : σ → MvPolynomial τ R) (i : σ) (u v : MvPolynomial τ R)
    (p : VectorPolynomial σ R V) (hp : ∀ a, 0 < a i → coefficients p a ∈ P)
    (b : τ →₀ ℕ) :
    coefficients (substitute (Function.update f i u) p - substitute (Function.update f i v) p) b ∈ P := by
  classical
  simp only [map_sub, Finsupp.sub_apply, coefficients_substitute]
  rw [← Finset.sum_sub_distrib]
  apply P.sum_mem
  intro a _
  by_cases ha : a i = 0
  · rw [aeval_monomial_update_eq_of_zero (R := R) f i u v a ha, sub_self]
    exact P.zero_mem
  · exact P.sub_mem (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))
      (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def Adapted (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.layer (fun i => a i)

noncomputable def adaptedSubmodule : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro a
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp a) (hq a)
  smul_mem' c p hp := by
    intro a
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp a)

theorem monomial_mem_adaptedSubmodule (a : σ →₀ ℕ) {x : L} (hx : x ∈ F.layer (fun i => a i)) :
    monomial (R := ℚ) a x ∈ F.adaptedSubmodule := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem lie_mem_adaptedSubmodule {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule) (hq : q ∈ F.adaptedSubmodule) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  exact F.lie_mem (hp a) (hq b)

noncomputable def adaptedLieSubalgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule with lie_mem' := F.lie_mem_adaptedSubmodule }

theorem adapted_ordinary {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ => 1) p := by
  apply (F.ordinary.adapted_iff_coefficients _ _).mpr
  intro a
  have h := F.layer_le_ordinary (fun i => a i) (hp a)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

noncomputable def polynomialSubgroup : Subgroup
    (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.ordinary.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup F.adaptedLieSubalgebra

abbrev PolynomialOrbit := ↥F.polynomialSubgroup

def PolynomialOrbit.log (p : F.PolynomialOrbit) : VectorPolynomial σ ℚ L := p.val.coord

theorem PolynomialOrbit.adapted (p : F.PolynomialOrbit) : F.Adapted (p.log F) := p.property

noncomputable def polynomialOrbitEval (x : σ → ℤ) : F.PolynomialOrbit →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp F.polynomialSubgroup.subtype

@[simp] theorem polynomialOrbitEval_coord (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x p).coord = eval (fun i => (x i : ℚ)) (p.log F) := rfl

noncomputable def toOrdinaryOrbit : F.PolynomialOrbit →* F.ordinary.PolynomialOrbit (fun _ : σ => 1) where
  toFun p := ⟨p.val, (F.ordinary.mem_adaptedSubmodule _ _).mpr (F.adapted_ordinary p.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toOrdinaryOrbit_eval (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.polynomialOrbitEval (fun _ => 1) x (F.toOrdinaryOrbit p) = F.polynomialOrbitEval x p := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_finsupp {σ : Type*} [Fintype σ] (c : σ → ℕ) (a : σ →₀ ℕ) :
    multidegreeWeight c (fun i => a i) = Finsupp.weight c a := by
  simp only [multidegreeWeight, Finsupp.weight_eq_sum, smul_eq_mul, mul_comm]

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def WeightedAdapted (c : σ → ℕ) (v : τ → ℕ) (p : VectorPolynomial τ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.weightedLayer c (Finsupp.weight v a)

noncomputable def weightedAdaptedSubmodule (c : σ → ℕ) (v : τ → ℕ) :
    Submodule ℚ (VectorPolynomial τ ℚ L) where
  carrier := {p | F.WeightedAdapted c v p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, LieSubmodule.zero_mem]
  add_mem' hp hq := by
    intro a
    rw [map_add, Finsupp.add_apply]
    exact (F.weightedLayer c _).add_mem (hp a) (hq a)
  smul_mem' r p hp := by
    intro a
    rw [map_smul, Finsupp.smul_apply]
    exact (F.weightedLayer c _).smul_mem r (hp a)

theorem weightedAdapted_monomial (c : σ → ℕ) (v : τ → ℕ) (a : τ →₀ ℕ) {x : L}
    (hx : x ∈ F.weightedLayer c (Finsupp.weight v a)) :
    F.WeightedAdapted c v (monomial a x) := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem weightedAdapted_lie (c : σ → ℕ) (v : τ → ℕ) {p q : VectorPolynomial τ ℚ L}
    (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v ⁅p, q⁆ := by
  classical
  change ⁅p, q⁆ ∈ F.weightedAdaptedSubmodule c v
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  apply F.weightedAdapted_monomial
  rw [map_add]
  exact F.weightedLayer_lie_mem c (hp a) (hq b)

noncomputable def weightedAdaptedLieSubalgebra (c : σ → ℕ) (v : τ → ℕ) :
    LieSubalgebra ℚ (VectorPolynomial τ ℚ L) :=
  { F.weightedAdaptedSubmodule c v with lie_mem' := F.weightedAdapted_lie c v }

theorem weightedAdapted_bch (c : σ → ℕ) (v : τ → ℕ) (t : ℕ)
    {p q : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v (lieBCH t p q) :=
  lieBCH_mem (F.weightedAdaptedLieSubalgebra c v) t hp hq

theorem weightedAdapted_constant (c : σ → ℕ) (v : τ → ℕ) (x : L) :
    F.WeightedAdapted c v (monomial 0 x) := by
  apply F.weightedAdapted_monomial
  simp only [map_zero, F.weightedLayer_zero, LieSubmodule.mem_top]

theorem weightedAdapted_substitute (c : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (c i)) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) : F.WeightedAdapted c v (VectorPolynomial.substitute f p) := by
  intro a
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro b _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial b 1)).coeff a = 0
  · rw [hc, zero_smul]
    exact LieSubmodule.zero_mem _
  · apply Submodule.smul_mem
    have hb : coefficients p b ∈ F.weightedLayer c (Finsupp.weight c b) :=
      F.layer_le_weightedLayer c (fun i => b i) _ (by rw [multidegreeWeight_finsupp]) (hp b)
    exact F.weightedLayer_antitone c
      (aeval_monomial_weightedSupport f c v hf b (MvPolynomial.mem_support_iff.mpr hc)) hb

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def omittedCoordinateWeight (i j : σ) : ℕ := if j = i then 0 else 1

theorem omittedCoordinateWeight_le_one (i j : σ) : omittedCoordinateWeight i j ≤ 1 := by
  unfold omittedCoordinateWeight
  split_ifs <;> omega

theorem omittedCoordinateWeight_total [Fintype σ] (i : σ) (bound : σ → ℕ) :
    multidegreeWeight (omittedCoordinateWeight i) bound + bound i = ∑ j, bound j := by
  have h (j : σ) : omittedCoordinateWeight i j * bound j + (if j = i then bound i else 0) = bound j := by
    by_cases hj : j = i <;> simp [omittedCoordinateWeight, hj]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => h j)
  simpa [Finset.sum_add_distrib, multidegreeWeight] using hs

noncomputable def splitCoordinatePolynomial (i : σ) (u : MvPolynomial (Option σ) ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  Function.update (fun j => MvPolynomial.X (some j)) i u

theorem splitCoordinatePolynomial_support (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1) (j : σ) :
    splitCoordinatePolynomial i u j ∈ weightedSupportLE (fun _ : Option σ => 1) 1 := by
  by_cases hj : j = i
  · subst j
    simpa only [splitCoordinatePolynomial, Function.update_self] using hu
  · rw [splitCoordinatePolynomial, Function.update_of_ne hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

theorem splitCoordinatePolynomial_zero_support (i j : σ) :
    splitCoordinatePolynomial i 0 j ∈
      weightedSupportLE (fun _ : Option σ => 1) (omittedCoordinateWeight i j) := by
  by_cases hj : j = i
  · subst j
    simp only [splitCoordinatePolynomial, Function.update_self, omittedCoordinateWeight, ite_true]
    exact Submodule.zero_mem _
  · simp only [splitCoordinatePolynomial, Function.update_of_ne hj, omittedCoordinateWeight, if_neg hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

theorem splitCoordinatePolynomial_eval (i j : σ) (u : MvPolynomial (Option σ) ℚ)
    (x : Option σ → ℚ) :
    MvPolynomial.aeval (R := ℚ) x (splitCoordinatePolynomial i u j) =
      Function.update (fun k => x (some k)) i (MvPolynomial.aeval (R := ℚ) x u) j := by
  by_cases hj : j = i <;> simp [splitCoordinatePolynomial, hj, Function.update_of_ne]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedAdapted_coefficients_mem (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (a : τ →₀ ℕ) : coefficients p a ∈ F.weightedSubalgebra c := by
  classical
  by_cases ha : a = 0
  · rw [ha, hzero]
    exact (F.weightedSubalgebra c).zero_mem
  · have hi : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hpos : 1 ≤ Finsupp.weight v a := (hv i).trans_le (Finsupp.le_weight_of_ne_zero' v hi)
    exact F.weightedLayer_antitone c hpos (hp a)

noncomputable def restrictWeightedPolynomial (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    VectorPolynomial τ ℚ (F.weightedSubalgebra c) :=
  restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero)

theorem restrictWeightedPolynomial_adapted (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).Adapted v (F.restrictWeightedPolynomial c v hv p hp hzero) := by
  apply ((F.weightedFiltration c).adapted_iff_coefficients v _).mpr
  intro a
  change (coefficients (restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
      (F.weightedAdapted_coefficients_mem c v hv hp hzero)) a : L) ∈
    F.weightedLayer c (max 1 (Finsupp.weight v a))
  rw [coefficients_restrictCoefficients]
  by_cases hn : 1 ≤ Finsupp.weight v a
  · rw [max_eq_right hn]
    exact hp a
  · have hz : Finsupp.weight v a = 0 := by omega
    rw [hz]
    exact F.weightedAdapted_coefficients_mem c v hv hp hzero a

theorem restrictWeightedPolynomial_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℚ) :
    (eval (V := F.weightedSubalgebra c) x
      (F.restrictWeightedPolynomial c v hv p hp hzero) : L) = eval x p :=
  eval_restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero) x

noncomputable def restrictWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog (F.restrictWeightedPolynomial c v hv p hp hzero)
    (F.restrictWeightedPolynomial_adapted c v hv p hp hzero)

theorem restrictWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℤ) :
    (((F.weightedFiltration c).polynomialOrbitEval v x
      (F.restrictWeightedOrbit c v hv p hp hzero)).coord : L) =
      eval (fun i => (x i : ℚ)) p :=
  F.restrictWeightedPolynomial_eval c v hv p hp hzero (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientDescend (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  { toLinearMap := I.toSubmodule.liftQ f.toLinearMap hI
    map_lie' {x y} := by
      obtain ⟨a, rfl⟩ := lieQuotientMap_surjective I x
      obtain ⟨b, rfl⟩ := lieQuotientMap_surjective I y
      exact f.map_lie a b }

@[simp] theorem lieQuotientDescend_mk (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) (x : L) :
    lieQuotientDescend I f hI (lieQuotientMap I x) = f x := rfl

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def quotientLie (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    NilpotentLieFiltration (L ⧸ I) t where
  layer j := (F.layer j).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hij => Submodule.map_mono (F.antitone hij)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

theorem quotientLie_mem (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    {j : ℕ} {x : L} (hx : x ∈ F.layer j) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j := ⟨x, hx, rfl⟩

theorem adapted_quotientLie {σ : Type*} (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (w : σ → ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    (F.quotientLie I hI).Adapted w (VectorPolynomial.map (lieQuotientMap I).toLinearMap p) :=
  F.adapted_map (F.quotientLie I hI) (lieQuotientMap I).toLinearMap
    (fun _ _ hx => F.quotientLie_mem I hI hx) w hp

def quotientTop (F : NilpotentLieFiltration L (s + 1)) :
    NilpotentLieFiltration (L ⧸ F.layerIdeal (s + 1)) s :=
  F.quotientLie (F.layerIdeal (s + 1)) le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def quotientStepHom : F.Group →* (F.quotientLie I hI).Group :=
  mapOfSteps (lieQuotientMap I)

@[simp] theorem quotientStepHom_coord (g : F.Group) :
    (F.quotientStepHom I hI g).coord = lieQuotientMap I g.coord := rfl

noncomputable def quotientPolynomialOrbit {σ : Type*} {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    (F.quotientLie I hI).PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map (lieQuotientMap I).toLinearMap p.log)
    (F.adapted_quotientLie I hI w p.adapted)

@[simp] theorem quotientPolynomialOrbit_log {σ : Type*} {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    (F.quotientPolynomialOrbit I hI p).log =
      VectorPolynomial.map (lieQuotientMap I).toLinearMap p.log := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def quotientMultidegree (I : LieIdeal ℚ L) :
    MultidegreeLieFiltration σ (L ⧸ I) s bound where
  ordinary := F.ordinary.quotientLie I (by rw [F.ordinary.terminal]; exact bot_le)
  layer a := (F.layer a).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hab => Submodule.map_mono (F.antitone hab)
  zero_eq_top := by
    rw [F.zero_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro a b x y ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨⁅p, q⁆, F.lie_mem hp hq, (lieQuotientMap I).map_lie p q⟩
  terminal := by
    intro a ha
    rw [F.terminal a ha, Submodule.map_bot]
  degree_eq := by
    intro n
    change (F.ordinary.layer n).map (lieQuotientMap I).toLinearMap = _
    rw [F.degree_eq]
    simp only [Submodule.map_iSup]

theorem quotientMultidegree_layer_eq_bot (I : LieIdeal ℚ L) (a : σ → ℕ)
    (ha : F.layer a ≤ I.toSubmodule) : (F.quotientMultidegree I).layer a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero I y).mpr (ha hy)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def realQuotientStepHom :
    F.realification.Group →* (F.quotientLie I hI).realification.Group :=
  realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := (F.quotientLie I hI).lowerCentralSeries_eq_bot) (lieQuotientMap I)

theorem realQuotientStepHom_surjective : Function.Surjective (F.realQuotientStepHom I hI) := by
  intro g
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

theorem mem_realQuotientStepHom_ker (g : F.realification.Group) :
    g ∈ (F.realQuotientStepHom I hI).ker ↔ g.coord ∈ I.toSubmodule.baseChange ℝ := by
  constructor
  · intro hg
    apply (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mp
    exact congrArg (fun z : (F.quotientLie I hI).realification.Group => z.coord)
      (MonoidHom.mem_ker.mp hg)
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply NilpotentLieBCHGroup.ext
    exact (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mpr hg

theorem realQuotientStep_mem_layer {j : ℕ} {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientLie I hI).realification.layer j := by
  have hmap : (F.layer j).baseChange ℝ ≤
      (((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ).comap
        (realificationLieHom (lieQuotientMap I)).toLinearMap := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℚ] (lieQuotientMap I a) ∈
      ((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨a, ha, rfl⟩
  exact hmap hx

noncomputable def realQuotientPolynomialOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) : (F.quotientLie I hI).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log)
    (F.realification.adapted_map (F.quotientLie I hI).realification _
      (fun _ _ hx => F.realQuotientStep_mem_layer I hI hx) w q.adapted)

theorem realQuotientPolynomialOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    (F.quotientLie I hI).realification.polynomialOrbitEval w x
      (F.realQuotientPolynomialOrbit I hI q) =
        F.realQuotientStepHom I hI (F.realification.polynomialOrbitEval w x q) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log) = _
  rw [eval_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L) (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)

noncomputable def quotientInducedMark : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  lieQuotientDescend I π hker

@[simp] theorem quotientInducedMark_mk (x : L) :
    quotientInducedMark I π hker (lieQuotientMap I x) = π x := rfl

@[simp] theorem quotientInducedMark_comp :
    (quotientInducedMark I π hker).comp (lieQuotientMap I) = π := by
  ext x
  rfl

@[simp] theorem quotientInducedMark_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (quotientInducedMark I π hker)
      (realificationLieHom (lieQuotientMap I) x) = realificationLieHom π x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem quotientInducedMark_real_comp :
    (realificationLieHom (quotientInducedMark I π hker)).comp
      (realificationLieHom (lieQuotientMap I)) = realificationLieHom π := by
  ext x
  exact quotientInducedMark_real_mk I π hker x

namespace NilpotentLieFiltration

variable {s t u : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M u)

theorem quotientInducedMark_mem_layer
    (I : LieIdeal ℚ L) (hkill : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)
    (hπ : ∀ j, ∀ x ∈ F.layer j, π x ∈ G.layer j)
    (j : ℕ) (y : L ⧸ I) (hy : y ∈ (F.quotientLie I hkill).layer j) :
    quotientInducedMark I π hker y ∈ G.layer j := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact hπ j x hx

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealifiedTripleProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.additiveTripleToPi i hi c hc)

@[simp] theorem additiveTripleProjection_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 0 = F.additiveTripleFirst i hi c hc := rfl

@[simp] theorem additiveTripleProjection_one (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 1 = F.additiveTripleSecond i hi c hc := rfl

@[simp] theorem additiveTripleProjection_two (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 2 = F.additiveTripleThird i hi c hc := rfl

noncomputable def realAdditiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    (F.additiveTripleFiltration i hi c hc).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.additiveTripleFiltration i hi c hc).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.additiveTripleProjection i hi c hc j)

theorem realifiedAdditiveTripleEquiv_projection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc x).val j =
      realificationLieHom (F.additiveTripleProjection i hi c hc j) x := by
  rw [F.realifiedAdditiveTripleEquiv_coe]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [realificationLieHom_tmul, realTripleEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realAdditiveTripleProjection_coord (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group) :
    (F.realAdditiveTripleProjection i hi c hc j g).coord =
      tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc g.coord).val j :=
  (F.realifiedAdditiveTripleEquiv_projection i hi c hc j g.coord).symm

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareLayer (j : ℕ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1)}
  zero_mem' := by simp
  add_mem' hx hy := by
    refine ⟨(F.layer j).add_mem hx.1 hy.1, (F.layer j).add_mem hx.2.1 hy.2.1, ?_⟩
    change _ + _ - (_ + _) ∈ F.layer (j + 1)
    rw [show ∀ a b c d : L, a + b - (c + d) = (a - c) + (b - d) by intros; abel]
    exact (F.layer (j + 1)).add_mem hx.2.2 hy.2.2
  smul_mem' r x hx := by
    refine ⟨(F.layer j).smul_mem r hx.1, (F.layer j).smul_mem r hx.2.1, ?_⟩
    change r • x.1 - r • x.2 ∈ F.layer (j + 1)
    rw [← smul_sub]
    exact (F.layer (j + 1)).smul_mem r hx.2.2

@[simp] theorem mem_squareLayer (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔
      x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := Iff.rfl

theorem squareLayer_antitone : Antitone F.squareLayer := by
  intro i j hij x hx
  exact ⟨F.antitone hij hx.1, F.antitone hij hx.2.1,
    F.antitone (Nat.add_le_add_right hij 1) hx.2.2⟩

theorem squareLayer_lie_mem {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.squareLayer i) (hy : y ∈ F.squareLayer j) :
    ⁅x, y⁆ ∈ F.squareLayer (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have he : ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ =
      ⁅x.1 - x.2, y.1⁆ + ⁅x.2, y.1 - y.2⁆ := by
    simp only [sub_lie, lie_sub]
    abel
  rw [he]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    (by simpa only [Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2)

def squareLieSubalgebra : LieSubalgebra ℚ (L × L) :=
  { F.squareLayer 1 with
    lie_mem' := fun hx hy => F.squareLayer_antitone (by omega) (F.squareLayer_lie_mem hx hy) }

@[simp] theorem mem_squareLieSubalgebra (x : L × L) :
    x ∈ F.squareLieSubalgebra ↔ x.1 - x.2 ∈ F.layer 2 := by
  change x ∈ F.squareLayer 1 ↔ _
  simp only [mem_squareLayer, F.one_eq_top, Submodule.mem_top, true_and]

def squareFiltration : NilpotentLieFiltration F.squareLieSubalgebra s where
  layer j := (F.squareLayer j).comap F.squareLieSubalgebra.incl.toLinearMap
  antitone := fun _ _ hij x hx => F.squareLayer_antitone hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.squareLayer_lie_mem hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    apply Prod.ext
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

@[simp] theorem mem_squareFiltration_layer (j : ℕ) (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer j ↔ (x : L × L) ∈ F.squareLayer j := Iff.rfl

theorem mem_squareFiltration_top (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer s ↔ x.val.1 ∈ F.layer s ∧ x.val.1 = x.val.2 := by
  change x.val ∈ F.squareLayer s ↔ _
  rw [mem_squareLayer, F.terminal, Submodule.mem_bot, sub_eq_zero]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, h.2 ▸ h.1, h.2⟩

def squareFst : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp F.squareLieSubalgebra.incl

def squareSnd : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp F.squareLieSubalgebra.incl

@[simp] theorem squareFst_apply (x : F.squareLieSubalgebra) : F.squareFst x = x.val.1 := rfl
@[simp] theorem squareSnd_apply (x : F.squareLieSubalgebra) : F.squareSnd x = x.val.2 := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem NilpotentLieFiltration.top_layer_central (F : NilpotentLieFiltration L s)
    {v : L} (hv : v ∈ F.layer s) (w : L) : ⁅v, w⁆ = 0 := by
  have hw : w ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem hv hw
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem rationalLieInclusion_central (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (w : ℝ ⊗[ℚ] L) : ⁅rationalLieInclusion v, w⁆ = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r w => simp only [rationalLieInclusion_apply, LieAlgebra.ExtendScalars.bracket_tmul,
      hv, TensorProduct.tmul_zero]
  | add x y hx hy => rw [lie_add, hx, hy, add_zero]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem scaled_basis_mem_bchSubgroup (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℚ) • b j⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
  classical
  have hx : b.equivFun ((N : ℚ) • b j) ∈ scaledIntegerGrid N := by
    refine ⟨fun k => if k = j then 1 else 0, ?_⟩
    ext k
    by_cases h : k = j
    · subst k
      simp [Basis.equivFun_apply]
    · simp [Basis.equivFun_apply, h]
  have h := hgrid hx
  change (⟨b.equivFun.symm (b.equivFun ((N : ℚ) • b j))⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem scaled_real_basis_mem_realification (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℝ) • (b.baseChange ℝ) j⟩ : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil)) ∈ Γ.map realificationHom := by
  refine Subgroup.mem_map.mpr ⟨⟨(N : ℚ) • b j⟩, scaled_basis_mem_bchSubgroup b Γ N hgrid j, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change rationalLieInclusion ((N : ℚ) • b j) = (N : ℝ) • (b.baseChange ℝ) j
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul, Basis.baseChange_apply, rationalLieInclusion_apply]

omit [Fintype κ] in
theorem scaled_real_basis_central (b : Basis κ ℚ L) (j : κ)
    (hv : ∀ w : L, ⁅b j, w⁆ = 0) (N : ℕ) (w : ℝ ⊗[ℚ] L) :
    ⁅(N : ℝ) • (b.baseChange ℝ) j, w⁆ = 0 := by
  rw [smul_lie, Basis.baseChange_apply]
  change (N : ℝ) • ⁅rationalLieInclusion (b j), w⁆ = 0
  rw [rationalLieInclusion_central _ hv, smul_zero]

omit [Fintype κ] in
theorem scaled_real_basis_coordinate_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (N : ℕ) (j : κ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B) :
    coordinateL2Norm ((e.baseChange ℝ).equivFun ((N : ℝ) • (b.baseChange ℝ) j)) ≤
      (Fintype.card ι + 1) * ((N : ℝ) * B) := by
  apply coordinateL2Norm_le_card_bound _ (mul_nonneg (Nat.cast_nonneg N) hB)
  intro i
  change |(e.baseChange ℝ).repr ((N : ℝ) • (b.baseChange ℝ) j) i| ≤ _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  simpa [Basis.baseChange_apply, Basis.baseChange_repr_tmul, Algebra.smul_def] using hb i

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem omitted_weighted_top (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) :
    F.weightedLayer (omittedCoordinateWeight i) s = ⊥ := by
  have h := omittedCoordinateWeight_total i bound
  rw [hi, hs] at h
  simpa only [h] using F.weightedLayer_terminal (omittedCoordinateWeight i)

theorem additiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).subgroup s) :
    (NilpotentLieBCHGroup.map (F.additiveTripleFirst i hi c hc) g : F.Group) =
      NilpotentLieBCHGroup.map (F.additiveTripleSecond i hi c hc) g *
      NilpotentLieBCHGroup.map (F.additiveTripleThird i hi c hc) g := by
  apply NilpotentLieBCHGroup.ext
  change F.additiveTripleFirst i hi c hc g.coord =
    lieBCH s (F.additiveTripleSecond i hi c hc g.coord) (F.additiveTripleThird i hi c hc g.coord)
  rw [lieBCH_eq_add_of_lie_eq_zero F.ordinary.lowerCentralSeries_eq_bot
    (F.ordinary.top_layer_central (F.additiveTripleProjections_mem i hi c hc hg).2.1 _)]
  exact F.additiveTripleTop_relation i hi c hc htop hg

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFstHom : F.squareFiltration.Group →* F.Group :=
  map F.squareFst

noncomputable def squareSndHom : F.squareFiltration.Group →* F.Group :=
  map F.squareSnd

@[simp] theorem squareFstHom_coord (g : F.squareFiltration.Group) :
    (F.squareFstHom g).coord = g.coord.val.1 := rfl

@[simp] theorem squareSndHom_coord (g : F.squareFiltration.Group) :
    (F.squareSndHom g).coord = g.coord.val.2 := rfl

noncomputable def squareLattice (Γ : Subgroup F.Group) : Subgroup F.squareFiltration.Group :=
  Γ.comap F.squareFstHom ⊓ Γ.comap F.squareSndHom

theorem mem_squareLattice (Γ : Subgroup F.Group) (g : F.squareFiltration.Group) :
    g ∈ F.squareLattice Γ ↔ F.squareFstHom g ∈ Γ ∧ F.squareSndHom g ∈ Γ := Iff.rfl

theorem squareLattice_le_fst (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareFstHom :=
  fun _ h => h.1

theorem squareLattice_le_snd (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareSndHom :=
  fun _ h => h.2

theorem square_top_projections {g : F.squareFiltration.Group}
    (hg : g ∈ F.squareFiltration.subgroup s) :
    F.squareFstHom g ∈ F.subgroup s ∧ F.squareFstHom g = F.squareSndHom g := by
  have h := (F.mem_squareFiltration_top g.coord).mp hg
  exact ⟨h.1, NilpotentLieBCHGroup.ext h.2⟩

theorem top_commutes (g : F.Group) (hg : g ∈ F.subgroup s) (h : F.Group) : Commute g h :=
  commute_of_lie_eq_zero g h (F.top_layer_central hg h.coord)

end Erdos3.NilpotentLieFiltration

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

theorem cosetMap_smul (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (g : G) (x : G ⧸ Γ) :
    cosetMap Γ Λ φ hφ (g • x) = φ g • cosetMap Γ Λ φ hφ x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (φ (g * a)) : H ⧸ Λ) = QuotientGroup.mk (φ g * φ a)
    rw [map_mul]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realLayer_eq_span_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) :
    (F.realLayer i).toSubmodule = Submodule.span ℝ (b.baseChange ℝ '' S) := by
  change (F.layer i).baseChange ℝ = _
  rw [hS, Submodule.baseChange_span, Set.image_image]
  congr 2
  funext j
  exact (Basis.baseChange_apply ℝ b j).symm

theorem realLayer_le_span_scaled_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) (N : ℕ) (hN : 0 < N) :
    (F.realLayer i).toSubmodule ≤
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) := by
  rw [F.realLayer_eq_span_basis b i S hS]
  apply Submodule.span_le.mpr
  rintro v ⟨j, hj, rfl⟩
  change b.baseChange ℝ j ∈
    Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j))
  have h : (N : ℝ)⁻¹ • ((N : ℝ) • b.baseChange ℝ j) ∈
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  simpa only [smul_smul, inv_mul_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),
    one_smul] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realAdditiveTripleProjection_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) {n : ℕ}
    {g : (F.additiveTripleFiltration i hi c hc).realification.Group}
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup n) :
    F.realAdditiveTripleProjection i hi c hc j g ∈ F.realification.ordinary.subgroup n := by
  have hm := (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc n g.coord).mp hg
  obtain ⟨h₀, h₁, h₂⟩ := F.realification.additiveTripleProjections_mem i hi c hc hm
  change (F.realAdditiveTripleProjection i hi c hc j g).coord ∈ F.realification.ordinary.layer n
  rw [F.realAdditiveTripleProjection_coord]
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂

theorem realAdditiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    F.realAdditiveTripleProjection i hi c hc 0 g =
      F.realAdditiveTripleProjection i hi c hc 1 g *
        F.realAdditiveTripleProjection i hi c hc 2 g := by
  let q : (F.realification.additiveTripleFiltration i hi c hc).Group :=
    ⟨F.realifiedAdditiveTripleEquiv i hi c hc g.coord⟩
  have hq : q ∈ (F.realification.additiveTripleFiltration i hi c hc).subgroup s :=
    (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc s g.coord).mp hg
  have he (j : Fin 3) : F.realAdditiveTripleProjection i hi c hc j g =
      (NilpotentLieBCHGroup.map (F.realification.additiveTripleProjection i hi c hc j) q :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realAdditiveTripleProjection_coord i hi c hc j g
  rw [he 0, he 1, he 2]
  exact F.realification.additiveTriple_top_group_relation i hi c hc htop q hq

theorem realAdditiveTriple_top_phase {A : Type*} [Add A]
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (χ : F.realification.Group → A)
    (hχ : ∀ z w, z ∈ F.realification.ordinary.subgroup s →
      w ∈ F.realification.ordinary.subgroup s → χ (z * w) = χ z + χ w)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    χ (F.realAdditiveTripleProjection i hi c hc 0 g) =
      χ (F.realAdditiveTripleProjection i hi c hc 1 g) +
        χ (F.realAdditiveTripleProjection i hi c hc 2 g) := by
  rw [F.realAdditiveTriple_top_group_relation i hi c hc htop g hg]
  exact hχ _ _ (F.realAdditiveTripleProjection_mem i hi c hc 1 hg)
    (F.realAdditiveTripleProjection_mem i hi c hc 2 hg)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

noncomputable def squareObservable (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) : ℂ :=
  u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
    star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))

theorem squareObservable_mk (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (g : F.squareFiltration.Group) :
    F.squareObservable Γ ε u (QuotientGroup.mk g) =
      u (QuotientGroup.mk (ε * F.squareFstHom g)) * star (u (QuotientGroup.mk (F.squareSndHom g))) := rfl

theorem squareObservable_top_invariant (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (χ : F.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.Group) (hk : k ∈ F.squareFiltration.subgroup s)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) :
    F.squareObservable Γ ε u (k • x) = F.squareObservable Γ ε u x := by
  obtain ⟨hz, heq⟩ := F.square_top_projections hk
  let z := F.squareFstHom k
  have hε : ∀ y : F.Group ⧸ Γ, ε • (z • y) = z • (ε • y) := by
    intro y
    rw [← mul_smul, ← mul_smul, (F.top_commutes z hz ε).eq]
  simp only [squareObservable, cosetMap_smul, ← heq]
  rw [hε, hu z hz, hu z hz, star_mul]
  have hc : character (χ z) * star (character (χ z)) = 1 := by
    rw [← character_neg, ← character_add, add_neg_cancel, character_zero]
  calc
    _ = (character (χ z) * star (character (χ z))) *
        (u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
          star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))) := by ring
    _ = _ := by rw [hc, one_mul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem sumExponent_injective (β : τ →₀ ℕ) :
    Function.Injective (fun α : σ →₀ ℕ => α.sumElim β) := by
  intro α γ h
  ext i
  exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inl i)) h

noncomputable def polynomialSlotCoefficient (β : τ →₀ ℕ) :
    MvPolynomial (σ ⊕ τ) R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).repr.symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (fun α : σ →₀ ℕ => α.sumElim β) (sumExponent_injective β)).comp
      (MvPolynomial.basisMonomials (σ ⊕ τ) R).repr.toLinearMap)

theorem polynomialSlotCoefficient_coeff (β : τ →₀ ℕ) (α : σ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    (polynomialSlotCoefficient β P).coeff α = P.coeff (α.sumElim β) := by
  change ((MvPolynomial.basisMonomials σ R).repr
    ((MvPolynomial.basisMonomials σ R).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem sumExponent_weight (v : σ → ℕ) (w : τ → ℕ) (α : σ →₀ ℕ) (β : τ →₀ ℕ) :
    Finsupp.weight (Sum.elim v w) (α.sumElim β) =
      Finsupp.weight v α + Finsupp.weight w β := by
  simp only [Finsupp.weight_apply, Finsupp.sum_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]

theorem polynomialSlotCoefficient_degree (v : σ → ℕ) (w : τ → ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ τ) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) n) (β : τ →₀ ℕ) :
    polynomialSlotCoefficient β P ∈ weightedSupportLE v (n - Finsupp.weight w β) := by
  intro α hα
  change α ∈ (polynomialSlotCoefficient β P).support at hα
  have hne : (polynomialSlotCoefficient β P).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  rw [polynomialSlotCoefficient_coeff] at hne
  have h : Finsupp.weight (Sum.elim v w) (α.sumElim β) ≤ n :=
    hP (MvPolynomial.mem_support_iff.mpr hne)
  rw [sumExponent_weight] at h
  change Finsupp.weight v α ≤ n - Finsupp.weight w β
  omega

theorem polynomialSlotCoefficient_monomial [DecidableEq τ] (α : σ →₀ ℕ) (β γ : τ →₀ ℕ) (c : R) :
    polynomialSlotCoefficient β (monomial (α.sumElim γ) c) =
      if γ = β then monomial α c else 0 := by
  classical
  ext δ
  rw [polynomialSlotCoefficient_coeff]
  by_cases hγ : γ = β
  · subst γ
    simp only [ite_true, coeff_monomial]
    simp only [(sumExponent_injective β).eq_iff]
  · have hne : α.sumElim γ ≠ δ.sumElim β := by
      intro h
      apply hγ
      ext i
      exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inr i)) h
    simp only [hγ, ite_false, MvPolynomial.coeff_zero,
      coeff_monomial, hne]

theorem polynomialParameterEval_monomial (t : σ → R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (c : R) :
    aeval (Sum.elim (fun i => C (t i)) X) (monomial (α.sumElim β) c) =
      monomial β (aeval t (monomial α c)) := by
  classical
  simp only [aeval_monomial, Finsupp.prod_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  simp only [← map_pow, ← map_finsuppProd, Algebra.algebraMap_self, RingHom.id_apply]
  rw [← mul_assoc, ← map_mul]
  rw [← monomial_eq]

theorem polynomialSlotCoefficient_eval (t : σ → R) (β : τ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    aeval t (polynomialSlotCoefficient β P) =
      (aeval (Sum.elim (fun i => C (t i)) X) P).coeff β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    let e : (σ ⊕ τ →₀ ℕ) ≃ (σ →₀ ℕ) × (τ →₀ ℕ) := Finsupp.sumFinsuppEquivProdFinsupp
    obtain ⟨⟨α, γ⟩, hm⟩ := e.symm.surjective m
    change α.sumElim γ = m at hm
    rw [← hm, polynomialSlotCoefficient_monomial, polynomialParameterEval_monomial]
    by_cases h : γ = β <;> simp [h, coeff_monomial]
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.coeff_add, hP, hQ]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialSlotCoefficient_weightedHomogeneousComponent
    {U B R : Type*} [CommRing R] (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) (α : B →₀ ℕ) :
    weightedHomogeneousComponent v (d - Finsupp.weight w α) (polynomialSlotCoefficient α P) =
      polynomialSlotCoefficient α (weightedHomogeneousComponent (Sum.elim v w) d P) := by
  classical
  ext β
  rw [coeff_weightedHomogeneousComponent, polynomialSlotCoefficient_coeff,
    polynomialSlotCoefficient_coeff, coeff_weightedHomogeneousComponent, sumExponent_weight]
  by_cases hc : P.coeff (β.sumElim α) = 0
  · simp only [hc, ite_self]
  · have hdegree : Finsupp.weight (Sum.elim v w) (β.sumElim α) ≤ d :=
      hP (mem_support_iff.mpr hc)
    rw [sumExponent_weight] at hdegree
    have heq : Finsupp.weight v β = d - Finsupp.weight w α ↔
        Finsupp.weight v β + Finsupp.weight w α = d := by omega
    simp only [heq]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem specializeMajorParameters_mem_weightedSupportLT (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLT (Sum.elim (fun _ : U => 0) w) d)
    (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d := by
  change aeval (Sum.elim (fun i => C (u i)) X) P ∈ weightedSupportLT w d
  apply weightedSupportLT_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl j => exact weightedSupportLE_C w 0 (u j)
  | inr j => exact weightedSupportLE_X w j

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def majorTranslationJointPolynomial
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  D - eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
    (specializeMajorParameters (RingHom.id ℝ) D 0)

theorem majorTranslationJointPolynomial_eq_sub_aeval
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x =
      D - aeval (Sum.elim (fun _ : U => 0)
        (fun j => X (Sum.inr j) - rename Sum.inl (x j))) D := by
  have hfreeze : specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (R := ℝ) (Sum.elim (fun _ : U => 0) (X : B → MvPolynomial B ℝ)) D := by
    simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
    rfl
  rw [majorTranslationJointPolynomial, hfreeze]
  congr 1
  change aeval (R := ℝ) (fun j => X (Sum.inr j) - rename Sum.inl (x j))
      (aeval (Sum.elim (fun _ : U => 0) X) D) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f D)
  funext i
  cases i <;> simp

theorem majorTranslationJointPolynomial_specialize
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      (algebraicMajorSymbol D (specializeMajorParameters (RingHom.id ℝ) D 0) x u).polynomial := by
  have hsub : specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u =
      specializeMajorParameters (RingHom.id ℝ) D u -
      specializeMajorParameters (RingHom.id ℝ)
        (eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
          (specializeMajorParameters (RingHom.id ℝ) D 0)) u := by
    simp only [majorTranslationJointPolynomial, specializeMajorParameters, map_sub]
  rw [hsub, specializeMajorParameters_translatedSlice]
  rfl

theorem majorParameterRename_degree (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  apply polynomialHom_preserves_weightedDegree v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_slot_degree_zero (w : B → ℕ) (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈
      weightedSupportLE (Sum.elim (fun _ : U => 0) w) 0 := by
  apply majorParameterRename_degree
  intro α _
  simp [Finsupp.weight_apply]

theorem majorTranslationJointPolynomial_degree (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (hx : ∀ j, (x j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLE _ _).sub_mem hD
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (x j) (w j)).mpr (hx j)))

theorem majorTranslationJointPolynomial_slot_lower (w : B → ℕ) (hw : ∀ j, 0 < w j)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLT (Sum.elim (fun _ : U => 0) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply weightedComparison_difference (Sum.elim (fun _ : U => 1) w)
    (Sum.elim (fun _ : U => 0) w) (AlgHom.id ℝ _)
    (aeval (Sum.elim (fun _ : U => 0)
      (fun j => X (Sum.inr j) - rename Sum.inl (x j)))) _ _ _ hD
  · intro i
    cases i with
    | inl i =>
        exact weightedSupportLE_mono (by decide : 0 ≤ 1)
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j)
  · intro i
    simp only [aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j))
          (weightedSupportLE_mono (Nat.zero_le _) (majorParameterRename_slot_degree_zero w (x j)))
  · intro i
    simp only [AlgHom.id_apply, aeval_X]
    cases i with
    | inl i =>
        simp only [Sum.elim_inl, sub_zero]
        exact weightedSupportLE_lt_succ
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j =>
        simp only [Sum.elim_inr, sub_sub_cancel]
        intro α hα
        exact (majorParameterRename_slot_degree_zero w (x j) hα).trans_lt (hw j)

theorem majorTranslationJointPolynomial_specialize_lower (w : B → ℕ)
    (hw : ∀ j, 0 < w j) {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u ∈
      weightedSupportLT w d :=
  specializeMajorParameters_mem_weightedSupportLT w
    (majorTranslationJointPolynomial_slot_lower w hw hD x) u

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def majorTranslationTopCoordinates (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) : MvPolynomial U ℝ :=
  weightedHomogeneousComponent (fun _ : U => 1) (w j) (A j)

theorem majorTranslationTopCoordinates_homogeneous (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).IsWeightedHomogeneous (fun _ : U => 1) (w j) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem majorTranslationTopCoordinates_degree (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).totalDegree ≤ w j := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro α hα
  exact (majorTranslationTopCoordinates_homogeneous w A j (mem_support_iff.mp hα)).le

theorem majorTranslationTopCoordinates_remainder (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (j : B) :
    A j - majorTranslationTopCoordinates w A j ∈ weightedSupportLT (fun _ : U => 1) (w j) :=
  weightedTopPart_remainder_lt (fun _ : U => 1)
    ((mem_weightedSupportLE_one_iff _ _).mpr (hA j))

theorem majorParameterRename_lower (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLT v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLT (Sum.elim v w) d := by
  apply weightedSupportLT_map v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_homogeneous (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P.IsWeightedHomogeneous v d) :
    (rename (Sum.inl : U → U ⊕ B) P).IsWeightedHomogeneous (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun i => isWeightedHomogeneous_X (R := ℝ) (Sum.elim v w) (Sum.inl i)) hP

theorem majorTranslationJointPolynomial_top_homogeneous (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply hD.sub
  apply aeval_isWeightedHomogeneous _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact isWeightedHomogeneous_zero ℝ _ _
  | inr j =>
      exact (isWeightedHomogeneous_X (R := ℝ) (Sum.elim (fun _ : U => 1) w) (Sum.inr j)).sub
        (majorParameterRename_homogeneous (fun _ => 1) w
          (majorTranslationTopCoordinates_homogeneous w A j))

theorem majorTranslationJointPolynomial_sub_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (A j)))
  let G := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)))
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [F, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (hA j)))
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [G, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (majorTranslationTopCoordinates_degree w A j)))
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    simp only [F, G, aeval_X]
    cases i with
    | inl i => simp only [Sum.elim_inl, sub_self]; exact Submodule.zero_mem _
    | inr j =>
        have h := (weightedSupportLT v (w j)).neg_mem
          (majorParameterRename_lower (fun _ => 1) w (majorTranslationTopCoordinates_remainder w A hA j))
        change (X (Sum.inr j) - rename Sum.inl (A j)) -
          (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) ∈
            weightedSupportLT v (w j)
        have he : (X (Sum.inr j) - rename Sum.inl (A j)) -
            (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) =
            -rename (Sum.inl : U → U ⊕ B) (A j - majorTranslationTopCoordinates w A j) := by
          rw [map_sub]
          abel
        rw [he]
        exact h
  have h := (weightedSupportLT v d).neg_mem (weightedComparison_difference v v F G hF hG hdiff hD)
  rw [majorTranslationJointPolynomial_eq_sub_aeval, majorTranslationJointPolynomial_eq_sub_aeval]
  change (D - F D) - (D - G D) ∈ weightedSupportLT v d
  convert h using 1
  abel

theorem majorTranslationJointPolynomial_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) := by
  have hle : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hα => (hD (mem_support_iff.mp hα)).le
  have hlower := majorTranslationJointPolynomial_sub_top_lower w hle A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, (majorTranslationJointPolynomial_top_homogeneous w hD A).weightedHomogeneousComponent_same,
    sub_eq_zero] at hzero
  exact hzero

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationJointLower
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLT (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLT _ _).sub_mem hD
  apply weightedSupportLT_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (A j) (w j)).mpr (hA j)))

theorem majorTranslationJointPolynomial_sub
    (D E : MvPolynomial (U ⊕ B) ℝ) (A : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial (D - E) A =
      majorTranslationJointPolynomial D A - majorTranslationJointPolynomial E A := by
  simp only [majorTranslationJointPolynomial_eq_sub_aeval, map_sub]
  abel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationShearExponentialOver
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {R σ : Type*} [CommRing R] [Algebra ℚ R]
  {w : σ ⊕ Unit → ℕ}

omit [Algebra ℚ R] in
theorem translationShear_derivation_rename
    (D : PolynomialShearLieAlgebra w R) (b : σ → R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i)) (P : MvPolynomial σ R) :
    ∃ Q : MvPolynomial σ R, D.val (rename Sum.inl P) = rename Sum.inl Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp⟩
  | add P Q hP hQ =>
      obtain ⟨P', hP'⟩ := hP
      obtain ⟨Q', hQ'⟩ := hQ
      exact ⟨P' + Q', by simp only [map_add, hP', hQ']⟩
  | mul_X P i hP =>
      obtain ⟨P', hP'⟩ := hP
      refine ⟨P * C (b i) + X i * P', ?_⟩
      simp only [map_mul, rename_X, D.val.leibniz, hb, hP', smul_eq_mul,
        map_add, rename_C]

theorem translationShear_exp_extra_coordinate
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃ Q : MvPolynomial σ R,
      polynomialShearExp D (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q := by
  classical
  let S : Submodule R (MvPolynomial (σ ⊕ Unit) R) :=
    LinearMap.range (rename (R := R) (Sum.inl : σ → σ ⊕ Unit)).toLinearMap
  have hpow (k : ℕ) : (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) ∈ S := by
    induction k with
    | zero => exact ⟨P, by simpa using hP.symm⟩
    | succ k ih =>
        obtain ⟨Q, hQ⟩ := ih
        obtain ⟨Q', hQ'⟩ := translationShear_derivation_rename D b hb Q
        refine ⟨Q', ?_⟩
        rw [pow_succ', Module.End.mul_apply, ← hQ]
        exact hQ'.symm
  have hmem : polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) ∈ S := by
    rw [polynomialShearExp_eq_sum D (weightedSupportLE_X w (Sum.inr ())),
      Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
      one_smul, add_sub_cancel_right]
    apply (S.restrictScalars ℚ).sum_mem
    intro k hk
    exact (S.restrictScalars ℚ).smul_mem _ (hpow k)
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨Q, ?_⟩
  change rename Sum.inl Q = polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) at hQ
  rw [hQ]
  abel

theorem existsUnique_translation_of_shear_exp
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃! g : PolynomialTranslationGroupOver R σ,
      PolynomialTranslationGroupOver.actionMonoidHom g = (polynomialShearExpAut D).val := by
  obtain ⟨Q, hQ⟩ := translationShear_exp_extra_coordinate D b P hb hP
  apply PolynomialTranslationGroupOver.existsUnique_action_of_shape
    (polynomialShearExpAut D).val b Q
  · intro i
    exact polynomialShearExp_X_of_derivation_eq_C D (Sum.inl i) (b i) (hb i)
  · exact hQ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFamilyMemberNet
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_uniform_family_member_net {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ 2 * ε := by
  classical
  let occupied (i : I) : Prop := ∃ x, ∀ y, ‖F x y - centers i y‖ ≤ ε
  let rep (i : I) : X := if h : occupied i then h.choose else Classical.choice inferInstance
  have hrep (i : I) (hi : occupied i) : ∀ y, ‖F (rep i) y - centers i y‖ ≤ ε := by
    simp only [rep, dif_pos hi]
    exact hi.choose_spec
  refine ⟨rep, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hnet x
  refine ⟨i, fun y => ?_⟩
  calc
    ‖F x y - F (rep i) y‖ ≤ ‖F x y - centers i y‖ + ‖centers i y - F (rep i) y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + ε := add_le_add (hi y) (by
      rw [norm_sub_rev]
      exact hrep i ⟨x, hi⟩ y)
    _ = 2 * ε := by ring

theorem exists_uniform_family_member_net_half {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε / 2) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ ε := by
  simpa only [mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
    exists_uniform_family_member_net F centers hnet

end Erdos3

end

section

namespace Erdos3

theorem uniformFamilyMemberNet_half_log_budget (E : ℕ) {p ε : ℝ}
    (hp : 0 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (p + Real.log (1 / (ε / 2)) + E) ^ E ≤
      (p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2) := by
  have hrecip : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hlogε : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hrecip
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hratio : 1 / (ε / 2) = (1 / ε) * 2 := by field_simp
  rw [hratio, Real.log_mul (by positivity) (by norm_num)]
  have hbase : 1 ≤ p + Real.log (1 / ε) + (E + 2 : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) E]
  apply (pow_le_pow_left₀ (by positivity)
    (show p + (Real.log (1 / ε) + Real.log 2) + (E : ℝ) ≤
      p + Real.log (1 / ε) + (E + 2 : ℕ) by push_cast; linarith) E).trans
  exact pow_le_pow_right₀ hbase (by omega)

theorem exists_uniform_family_member_net_of_polynomial_log
    {O Y : Type*} [Nonempty O] (F : O → Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (E : ℕ)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + E) ^ E) ∧
      ∃ centers : Fin n → Y → ℂ, ∀ o, ∃ i, ∀ y, ‖F o y - centers i y‖ ≤ η)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp
      ((p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2)) ∧
      ∃ rep : Fin n → O, ∀ o, ∃ i, ∀ y, ‖F o y - F (rep i) y‖ ≤ ε := by
  obtain ⟨n, hn, centers, hcenters⟩ := hnet (ε / 2) (by positivity) (by linarith)
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net_half F centers hcenters
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr
    (uniformFamilyMemberNet_half_log_budget E hp hε hε1)), rep, hrep⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalSpectrumBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal Pointwise

theorem samplingDensity_le_of_smallDoubling
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A S T : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) (k : ℕ)
    {K : ℝ} (hK : 0 < K) (hdoubling : ((A + S).card : ℝ) ≤ K * A.card)
    (hcount : (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card)) :
    (S.card : ℝ) / (2 * K ^ k) ≤ T.card := by
  have hsumpos : (0 : ℝ) < (A + S).card := by exact_mod_cast (hA.add hS).card_pos
  have hden : 0 < ((A + S).card : ℝ) ^ k := pow_pos hsumpos _
  have hKden : 0 < 2 * K ^ k := mul_pos (by norm_num) (pow_pos hK _)
  apply le_trans _ hcount
  apply (div_le_div_iff₀ hKden hden).mpr
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hdoubling k
  calc
    _ ≤ (S.card : ℝ) * (K * A.card) ^ k :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

namespace RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem localChangDimension_half_le_of_card
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {K : ℝ} (hK : 0 < K) (k : ℕ)
    (hcount : (B.carrier.card : ℝ) / (2 * K ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + k * Real.log K) := by
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hBpos : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  have hden : 0 < 2 * K ^ k := by positivity
  have hprod := (div_le_iff₀ hden).mp hcount
  have hratio : 2 * (B.carrier.card : ℝ) / T.card ≤ 4 * K ^ k := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (B.carrier.card : ℝ) / T.card) hratio
  rw [Real.log_mul (by norm_num) (pow_ne_zero k hK.ne'), Real.log_pow] at hlog
  unfold localChangDimension
  norm_num
  linarith

theorem localChangBaseScale_ge_of_dimension_le
    (B : CyclicBohr.Set N) (T : Finset (ZMod N)) (eta D : ℝ)
    (hD : localChangDimension B T eta ≤ D) :
    (100 * ((2 * max B.rank 1 : ℕ) : ℝ≥0) *
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹ ≤ localChangBaseScale B T eta := by
  have hcap : localChangCap B T eta ≤ ⌈D⌉₊ + 1 :=
    Nat.add_le_add_right (Nat.ceil_mono hD) 1
  have hcap' : ((2 * localChangCap B T eta + 1 : ℕ) : ℝ≥0) ≤
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcap) 1
  unfold localChangBaseScale
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hcap' (by positivity))

end RelativeChangSanders
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalBohrWidth
namespace OAI

section

namespace Erdos3.BohrWidthBudget

theorem selector_scale_lower_bound {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) :
    1 / (1000 * d * (D + 1)) ≤
      (100 * (2 * d) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ))⁻¹ := by
  have hceil := (Nat.ceil_lt_add_one hD).le
  have hsmall : (((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ)) ≤ 5 * (D + 1) := by
    push_cast
    linarith
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 100 * (2 * d) by positivity)
  nlinarith

theorem polynomial_denominator_le_exp {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
      Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
  have hWexp : W ≤ Real.exp W := by linarith [Real.add_one_le_exp W]
  have hd0 : 0 ≤ d := by linarith
  have hdlog : d ^ 3 ≤ Real.exp (3 * Real.log (2 + d)) := by
    calc
      d ^ 3 ≤ (2 + d) ^ 3 := pow_le_pow_left₀ hd0 (by linarith) 3
      _ = Real.exp (3 * Real.log (2 + d)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : 0 < 2 + d)] using
          (Real.exp_nat_mul (Real.log (2 + d)) 3).symm
  have hppow : (p + 1) ^ 4 ≤ Real.exp (4 * p) := by
    calc
      (p + 1) ^ 4 ≤ Real.exp p ^ 4 :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp p) 4
      _ = Real.exp (4 * p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul p 4).symm
  have hlog : 0 ≤ Real.log (2 + d) := Real.log_nonneg (by linarith)
  calc
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
        Real.exp p * Real.exp W * Real.exp (3 * Real.log (2 + d)) * Real.exp (4 * p) := by
      gcongr
    _ = Real.exp (p + W + 3 * Real.log (2 + d) + 4 * p) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hW.le hp, mul_nonneg hW.le hlog]

theorem exp_neg_budget_le_reciprocal {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity)
    (polynomial_denominator_le_exp hW hp hd)

end Erdos3.BohrWidthBudget

end

section

namespace Erdos3.BohrWidthBudget

theorem rational_width_lower_bound {u d D w v a : ℝ}
    (hu : 0 < u) (hd : 1 ≤ d) (hD : 0 ≤ D) (hw : 0 < w) (hw1 : w ≤ 1)
    (hv : w / (400 * d) ≤ v) (ha : 1 / (1000 * d * (D + 1)) ≤ a) :
    u * w / (10240000000 * d ^ 3 * (D + 1)) ≤
      min ((u / (6400 * d)) * (a * v / 2)) (u / (8 * (D + 1))) / 2 := by
  have hd0 : 0 < d := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hprod : (1 / (1000 * d * (D + 1))) * (w / (400 * d)) ≤ a * v :=
    mul_le_mul ha hv (by positivity) ha0.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply le_min
  · calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (6400 * d)) * ((1 / (1000 * d * (D + 1))) * (w / (400 * d)) / 2) := by
        field_simp
        ring
      _ ≤ (u / (6400 * d)) * (a * v / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by norm_num)) (by positivity)
  · have hd3 : 1 ≤ d ^ 3 := one_le_pow₀ hd
    have hfrac : w / (5120000000 * d ^ 3) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (D + 1)) * (w / (5120000000 * d ^ 3)) := by
        field_simp
        ring
      _ ≤ (u / (D + 1)) * (1 / 8) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = u / (8 * (D + 1)) := by field_simp

theorem rational_width_ge_exponential {epsilon C p d w : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 ≤ C) (hp : 0 ≤ p) (hd : 1 ≤ d) (hw : 0 ≤ w) :
    let W := 10240000000 * (C + 1) / epsilon
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      epsilon * Real.exp (-p) * w / (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) := by
  intro W
  have hW : 0 < W := by dsimp [W]; positivity
  have hd0 : 0 < d := by linarith
  have hbound := mul_le_mul_of_nonneg_left (exp_neg_budget_le_reciprocal hW hp hd) hw
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hden : 10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1) ≤
      10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  calc
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
        w * (1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4)) := hbound
    _ = epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4)) := by
      rw [Real.exp_neg]
      dsimp [W]
      field_simp
    _ ≤ epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end Erdos3.BohrWidthBudget

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateSplit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

omit [DecidableEq σ] in
theorem adapted_coefficient_zero_of_coordinate (i : σ) (hi : bound i ≤ 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 1 < a i) :
    coefficients p a = 0 := by
  have hn : ¬(fun j => a j) ≤ bound := by
    intro h
    exact (not_le_of_gt (hi.trans_lt ha)) (h i)
  have h := hp a
  simpa only [F.terminal _ hn, Submodule.mem_bot] using h

theorem adapted_coefficient_mem_coordinate (i : σ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 0 < a i) :
    coefficients p a ∈ F.layer (Pi.single i 1) := by
  apply F.antitone (show Pi.single i 1 ≤ fun j => a j from ?_) (hp a)
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Pi.single_eq_same] using (Nat.succ_le_of_lt ha)
  · simp [hj]

theorem split_substitution_add (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p =
      VectorPolynomial.substitute (splitCoordinatePolynomial i u) p +
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p :=
  substitute_update_add _ i u v p (F.adapted_coefficient_zero_of_coordinate i hi hp)

theorem split_substitution_sub_mem_coordinate (i : σ)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a ∈ F.layer (Pi.single i 1) :=
  coefficients_substitute_update_sub_mem (F.layer (Pi.single i 1)) _ i u v p
    (F.adapted_coefficient_mem_coordinate i hp) a

theorem split_substitution_adapted (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) :=
  F.ordinary.adapted_substitute (fun _ => 1) (fun _ => 1) _
    (splitCoordinatePolynomial_support i u hu) (F.adapted_ordinary hp)

theorem split_substitution_zero_weighted (i : σ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.WeightedAdapted (omittedCoordinateWeight i) (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) :=
  F.weightedAdapted_substitute _ _ _ (splitCoordinatePolynomial_zero_support i) hp

theorem split_substitution_sub_mem_active (i : σ)
    (u : MvPolynomial (Option σ) ℚ) (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a ∈
        F.coordinateActiveLayer i (Finsupp.weight (fun _ : Option σ => 1) a) := by
  refine ⟨F.split_substitution_sub_mem_coordinate i u 0 hp a, ?_⟩
  rw [map_sub, Finsupp.sub_apply]
  exact (F.ordinary.layer _).sub_mem
    ((F.ordinary.adapted_iff_coefficients _ _).mp (F.split_substitution_adapted i u hu hp) a)
    ((F.ordinary.adapted_iff_coefficients _ _).mp
      (F.split_substitution_adapted i 0 (Submodule.zero_mem _) hp) a)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalSeparationTransport
namespace OAI

section

namespace Erdos3

theorem horizontal_parts_separation_equiv {H ι κ ν σ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) (i : σ)
    (y small rational : H) (k : K) (hsystem : y = small + rational + k.val)
    (hy : y ∈ U) (hs : ‖e small‖ ≤ Real.exp p / T i)
    (hr : e rational ∈ realDenominatorGrid l) :
    small ∈ U ⊔ K ∧ rational ∈ U ⊔ K := by
  classical
  let M := Matrix.fromCols A B
  have hM : ∀ i j, RationalHeightLE (M i j) J := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  have hspan : Submodule.span ℝ (Set.range (fun j i => (M i j : ℝ))) =
      U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
    change Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) = _
    rw [real_column_span_fromCols, hAspan, hBspan]
  have heq : e y = e small + e rational + e k.val := by rw [hsystem, map_add, map_add]
  have hs' : ‖e small‖ ≤ Real.exp p / monomialScale T (Finsupp.single i 1) := by
    simpa [monomialScale] using hs
  have hparts := horizontal_parts_separation (U.map e.toLinearMap) (K.map e.toLinearMap)
    M hspan hJ hl hM hp hι hcols hJp hlp T hT
    (show (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 by simp) (e y) (e small) (e rational) (e k.val)
    heq ⟨y, hy, rfl⟩ ⟨k.val, k.property, rfl⟩ hs' hr
  have hmem (x : H) (hx : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap) : x ∈ U ⊔ K := by
    rw [← Submodule.map_sup, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hx
    exact hx
  exact ⟨hmem small hparts.1, hmem rational hparts.2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeOrbitTransport
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {G : MultidegreeLieFiltration σ L s bound}

noncomputable def orbitEquivOfEq (h : F = G) : F.PolynomialOrbit ≃* G.PolynomialOrbit := by
  subst G
  exact MulEquiv.refl _

theorem orbitEquivOfEq_eval (h : F = G) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    G.polynomialOrbitEval x (F.orbitEquivOfEq h p) = F.polynomialOrbitEval x p := by
  subst G
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorIntegerRestoration
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem weightedHomogeneousComponent_fractional_restoration
    (F : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    weightedHomogeneousComponent w d F =
      weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F) +
        MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) := by
  classical
  conv_lhs => rw [← floorIntegerPolynomial_add_fractionalCoefficientPolynomial F]
  rw [map_add, add_comm]
  congr 1
  ext a
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

noncomputable def restoredMajorRemainder (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  R + MvPolynomial.map (Int.castRingHom ℚ)
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F))

theorem restoredMajorRemainder_coefficientGrid (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (q : ℕ)
    (hR : (fun a => R.coeff a) ∈ denominatorGrid q) :
    (fun a => (restoredMajorRemainder F w d R).coeff a) ∈ denominatorGrid q :=
  add_integerPolynomial_coefficientGrid R
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) q hR

theorem integerPolynomial_map_rat_real (I : MvPolynomial σ ℤ) :
    MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) I) =
      MvPolynomial.map (Int.castRingHom ℝ) I := by
  ext a
  simp only [coeff_map]
  simp

theorem restoredMajorRemainder_eval (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (z : σ → ℝ) :
    eval₂ (algebraMap ℚ ℝ) z (restoredMajorRemainder F w d R) =
      eval₂ (algebraMap ℚ ℝ) z R +
        eval z (MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F))) := by
  rw [restoredMajorRemainder, eval₂_add]
  congr 1
  rw [← eval_map, integerPolynomial_map_rat_real]

theorem restoredMajorRemainder_degree (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ)
    (hR : R ∈ weightedSupportLE w d) :
    restoredMajorRemainder F w d R ∈ weightedSupportLE w d := by
  apply (weightedSupportLE w d).add_mem hR
  intro a ha
  have hi : (MvPolynomial.map (Int.castRingHom ℚ)
      (weightedHomogeneousComponent w d (floorIntegerPolynomial F))).IsWeightedHomogeneous w d := by
    intro a ha
    apply weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) d (floorIntegerPolynomial F)
    intro hz
    apply ha
    simp only [coeff_map, hz, map_zero]
  exact (hi (mem_support_iff.mp ha)).le

theorem algebraic_major_restore_integer_coefficients
    {U B : Type*} (F : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (K : Submodule ℝ (B → ℝ))
    (A : B → MvPolynomial U ℝ) (H : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ)
    (hgrid : (fun a => R.coeff a) ∈ denominatorGrid q)
    (hdegree : R ∈ weightedSupportLE w d)
    (hidentity : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b)
          (weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F)) =
        eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) :
    let R' := restoredMajorRemainder F w d R
    (fun a => R'.coeff a) ∈ denominatorGrid q ∧ R' ∈ weightedSupportLE w d ∧
      ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) (weightedHomogeneousComponent w d F) =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
            eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R' := by
  refine ⟨restoredMajorRemainder_coefficientGrid F w d R q hgrid,
    restoredMajorRemainder_degree F w d R hdegree, ?_⟩
  intro u b hb
  rw [weightedHomogeneousComponent_fractional_restoration, map_add, hidentity u b hb,
    restoredMajorRemainder_eval, add_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def majorSlowDilationPullback (q : ℕ) (H T : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes
    (Sum.elim (fun i => H i / ((q : ℝ) * T i)) (fun _ : B => 1)) S

 theorem majorSlowDilationPullback_eval (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun i => u i / H i) z) (majorSlowDilationPullback q H T S) =
      eval (Sum.elim (fun i => (u i / (q : ℝ)) / T i) z) S := by
  rw [majorSlowDilationPullback, scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x S)
  funext j
  cases j with
  | inl i =>
    dsimp only [Sum.elim_inl]
    field_simp [(hH i).ne', (hT i).ne', (Nat.cast_pos.mpr hq : (0 : ℝ) < q).ne']
  | inr j => simp only [Sum.elim_inr, one_mul]

theorem algebraic_major_dilation_pullback_identity
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowDilationPullback q H T S) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) := by
  rw [majorSlowDilationPullback_eval q hq H T hH hT,
    jointRationalPolynomialDilation_eval₂]
  have hcancel : (fun i => (q : ℝ) * (u i / (q : ℝ))) = u := by
    funext i
    exact mul_div_cancel₀ (u i) (Nat.cast_ne_zero.mpr hq.ne')
  simpa only [hcancel] using hsource (fun i => u i / (q : ℝ)) b hb

 theorem majorSlowDilationPullback_mass_le (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) {c : ℝ} (hc : 1 ≤ c)
    (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (majorSlowDilationPullback q H T S) ≤ c^d * realPolynomialMass S := by
  apply jointPolynomialDilation_mass_le _ S hc _ hS
  intro i
  have hqT : 0 < (q : ℝ) * T i := mul_pos (Nat.cast_pos.mpr hq) (hT i)
  rw [abs_of_nonneg (div_nonneg (hH i).le hqT.le)]
  apply (div_le_iff₀ hqT).mpr
  simpa only [mul_assoc] using hHT i

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorSlowDilationPullback_mem_weightedSupportLE
    (q : ℕ) (H T : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (hS : S ∈ weightedSupportLE w d) :
    majorSlowDilationPullback q H T S ∈ weightedSupportLE w d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ w d hS

theorem algebraic_major_weighted_dilation_pullback_decomposition
    (w : B → ℕ) (hw : ∀ i, 0 < w i)
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) := by
  have hpos : ∀ i : U ⊕ B, 0 < Sum.elim (fun _ : U => 1) w i :=
    Sum.rec (fun _ => Nat.zero_lt_one) hw
  have hSdeg := weightedSupportLE_totalDegree_le_of_pos hpos hS
  have hRdeg := weightedSupportLE_totalDegree_le_of_pos hpos hR
  have hS' := majorSlowDilationPullback_mem_weightedSupportLE q H T S _ d hS
  have hR' := jointRationalPolynomialDilation_mem_weightedSupportLE q R _ d hR
  refine ⟨majorSlowDilationPullback q H T S, jointRationalPolynomialDilation q R,
    rfl, rfl,
    algebraic_major_dilation_pullback_identity K D A S R q hq H T hH hT hsource,
    ?_, hS', hR', weightedSupportLE_totalDegree_le_of_pos hpos hS',
    weightedSupportLE_totalDegree_le_of_pos hpos hR', ?_⟩
  · exact (majorSlowDilationPullback_mass_le q hq H T hH hT S hc hHT hSdeg).trans
      (mul_le_mul_of_nonneg_left hSmass (pow_nonneg (le_trans zero_le_one hc) d))
  · exact jointRationalPolynomialDilation_denominatorGrid R q l d hq hRdeg hRgrid

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U R : Type*} [CommRing R]

theorem homogeneousComponent_polynomialTranslate (h : ℕ) (r : U → R)
    (P : MvPolynomial U R) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (polynomialTranslate r P) = homogeneousComponent h P := by
  have hp : VectorPolynomial.DegreeLE (1 : U → ℕ) h (P ⊗ₜ[R] (1 : R)) := by
    intro α hα
    have hz : P.coeff α = 0 := coeff_eq_zero_of_totalDegree_lt (hP.trans_lt (by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply,
        smul_eq_mul, mul_one] using hα))
    simp only [VectorPolynomial.coefficients_tmul, hz, zero_smul]
  have ht := VectorPolynomial.homogeneousPart_translate r (P ⊗ₜ[R] (1 : R)) hp
  ext α
  have hc := congrArg (fun p => VectorPolynomial.coefficients p α) ht
  simpa only [VectorPolynomial.translate_tmul, VectorPolynomial.homogeneousPart_tmul,
    VectorPolynomial.coefficients_tmul, smul_eq_mul, mul_one] using hc

theorem polynomial_dilation_monomial (a c : R) (α : U →₀ ℕ) :
    aeval (fun i => C a * X i) (monomial α c) = monomial α (a ^ α.degree * c) := by
  classical
  rw [aeval_monomial]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, prod_X_pow_eq_monomial]
  rw [monomial_eq, monomial_eq]
  simp only [map_one, one_mul, map_mul]
  have hd : (∑ i ∈ α.support, α i) = α.degree := rfl
  rw [hd]
  ring

theorem coeff_polynomial_dilation (a : R) (P : MvPolynomial U R) (α : U →₀ ℕ) :
    (aeval (fun i => C a * X i) P).coeff α = a ^ α.degree * P.coeff α := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, polynomial_dilation_monomial, coeff_sum, coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β hβ hβα
      simp [hβα]
    · exact fun h => (h hα).elim
  · rw [Finset.sum_eq_zero]
    · have hz : P.coeff α = 0 := not_ne_iff.mp (fun h => hα (mem_support_iff.mpr h))
      simp only [hz, mul_zero]
    · intro β hβ
      have hβα : β ≠ α := by rintro rfl; exact hα hβ
      simp [hβα]

theorem homogeneousComponent_polynomial_dilation (h : ℕ) (a : R)
    (P : MvPolynomial U R) :
    homogeneousComponent h (aeval (fun i => C a * X i) P) =
      C (a ^ h) * homogeneousComponent h P := by
  classical
  ext α
  rw [coeff_homogeneousComponent, coeff_polynomial_dilation, coeff_C_mul,
    coeff_homogeneousComponent]
  by_cases hα : α.degree = h
  · simp only [hα, ite_true]
  · simp only [hα, ite_false, mul_zero]

theorem residueAffinePolynomial_eq_dilation_translate (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) :
    residueAffinePolynomial q r P =
      aeval (fun i => C (q : ℝ) * X i) (polynomialTranslate (fun i => (r i : ℝ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', polynomialTranslate_X,
      map_add, aeval_X, aeval_C, algebraMap_eq] at *
    rw [hP, add_comm (C (r i : ℝ))]

theorem residueAffinePolynomial_homogeneousComponent (q h : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ h) :
    homogeneousComponent h (residueAffinePolynomial q r P) =
      C ((q : ℝ) ^ h) * homogeneousComponent h P := by
  rw [residueAffinePolynomial_eq_dilation_translate,
    homogeneousComponent_polynomial_dilation, homogeneousComponent_polynomialTranslate h _ P hP]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U : Type*}

theorem residueAffinePolynomial_homogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (homogeneousComponent h (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i) (homogeneousComponent h P) := by
  have hdil : C ((q : ℝ) ^ h) * homogeneousComponent h P =
      aeval (fun i => C (q : ℝ) * X i) (homogeneousComponent h P) := by
    classical
    ext α
    rw [coeff_C_mul, coeff_polynomial_dilation, coeff_homogeneousComponent]
    by_cases hα : α.degree = h
    · simp only [hα, ite_true]
    · simp only [hα, ite_false, mul_zero]
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP, hdil]
  change (aeval v) (aeval (fun i => C (q : ℝ) * X i)
    (homogeneousComponent h P)) = _
  rw [comp_aeval_apply]
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    aeval_eq_eval]

theorem residueAffinePolynomial_weightedHomogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (weightedHomogeneousComponent (fun _ : U => 1) h
      (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i)
        (weightedHomogeneousComponent (fun _ : U => 1) h P) :=
  residueAffinePolynomial_homogeneousComponent_eval q h r P hP v

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def jointResidueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  aeval (Sum.elim (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i))
    (fun j => X (Sum.inr j))) D

theorem jointResidueAffinePolynomial_eval (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) (jointResidueAffinePolynomial q r D) =
      eval (Sum.elim (fun i => (r i : ℝ) + (q : ℝ) * u i) b) D := by
  induction D using MvPolynomial.induction_on with
  | C c => simp [jointResidueAffinePolynomial]
  | add D E hD hE => simpa only [jointResidueAffinePolynomial, map_add] using congrArg₂ (· + ·) hD hE
  | mul_X D i hD =>
    cases i <;> simp [jointResidueAffinePolynomial, map_mul] at hD ⊢ <;> rw [hD] <;> simp

theorem jointResidueAffine_variables_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    (i : U ⊕ B) :
    Sum.elim (fun j => C (r j : ℝ) + C (q : ℝ) * X (Sum.inl j))
      (fun j => X (Sum.inr j)) i ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) (Sum.elim (fun _ : U => 1) w i) := by
  cases i with
  | inl i =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (Sum.elim (fun _ : U => 1) w) 0 (q : ℝ))
      (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inl i))
  | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j)

theorem jointResidueAffinePolynomial_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  weightedSupportLE_aeval _ _ _ (jointResidueAffine_variables_degree w q r) hD

theorem jointResidueAffinePolynomial_sub_axes_lower (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D -
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ B) ℝ := aeval (R := ℝ) (Sum.elim
    (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i)) (fun j => X (Sum.inr j)))
  let T := Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)
  let G := aeval (R := ℝ) (fun i : U ⊕ B => C (T i) * X i)
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [F, aeval_X] using jointResidueAffine_variables_degree w q r i
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [G, aeval_X, zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C v 0 (T i)) (weightedSupportLE_X v i)
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    cases i with
    | inl i =>
      simp only [F, G, T, aeval_X, Sum.elim_inl, add_sub_cancel_right]
      exact weightedSupportLE_lt_succ (weightedSupportLE_C v 0 (r i : ℝ))
    | inr j =>
      simp only [F, G, T, aeval_X, Sum.elim_inr, map_one, one_mul, sub_self]
      exact Submodule.zero_mem _
  rw [scaleMvPolynomialAxes_eq_aeval]
  exact weightedComparison_difference v v F G hF hG hdiff hD

theorem jointResidueAffinePolynomial_weightedHomogeneousComponent (w : B → ℕ)
    (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1))
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  have hlower := jointResidueAffinePolynomial_sub_axes_lower w q r hD
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (jointResidueAffinePolynomial q r D -
        scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, scaleMvPolynomialAxes_weightedHomogeneousComponent]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {U B : Type*}

 theorem jointResidueAffinePolynomial_weightedHomogeneousComponent_eval
    (w : B → ℕ) (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (v : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim v b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D)) =
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent w q d r D hD,
    scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x _)
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, one_mul]

theorem algebraic_major_affine_top_dilation_identity
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (r : U → ℤ) (T : U → ℝ)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (v : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
    eval (Sum.elim (fun i => v i / T i)
      (fun j => b j - eval (fun i => (q : ℝ) * v i) (majorTranslationTopCoordinates w A j))) S +
    eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R := by
  have h := hsource v b hb
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent_eval w q n r D hD] at h
  simp only [majorTranslationTopCoordinates,
    residueAffinePolynomial_weightedHomogeneousComponent_eval q _ r _ (hA _)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem algebraic_major_weighted_affine_top_pullback_decomposition
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
          eval (Sum.elim (fun i => u i / H i)
            (fun j => b j - eval u (majorTranslationTopCoordinates w A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) :=
  algebraic_major_weighted_dilation_pullback_decomposition w hw K _ _ S R q hq H T hH hT
    (algebraic_major_affine_top_dilation_identity K w n D hD A hA S R q r T hsource)
    c C hc hHT d l hS hR hSmass hRgrid

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boundedPrimes (Q : ℕ) : Finset ℕ := (Finset.range (Q + 1)).filter Nat.Prime

abbrev BoundedPrime (Q : ℕ) := {p // p ∈ boundedPrimes Q}

def boundedPrime (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val

def boundedPrimeExponent (Q : ℕ) (p : BoundedPrime Q) : ℕ := Nat.log p.val Q

def boundedPrimePower (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val ^ boundedPrimeExponent Q p

theorem mem_boundedPrimes (Q p : ℕ) : p ∈ boundedPrimes Q ↔ p.Prime ∧ p ≤ Q := by
  simp only [boundedPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

theorem boundedPrime_prime (Q : ℕ) (p : BoundedPrime Q) : (boundedPrime Q p).Prime :=
  ((mem_boundedPrimes Q p.val).mp p.property).1

theorem boundedPrimePower_pos (Q : ℕ) (p : BoundedPrime Q) : 0 < boundedPrimePower Q p :=
  pow_pos (boundedPrime_prime Q p).pos _

instance boundedPrimePower_neZero (Q : ℕ) (p : BoundedPrime Q) : NeZero (boundedPrimePower Q p) :=
  ⟨(boundedPrimePower_pos Q p).ne'⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boundedPrimeProduct (Q : ℕ) : ℕ := ∏ p : BoundedPrime Q, boundedPrimePower Q p

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem monomialScale_const_mul_degree {I : Type*} (T : I → ℝ) (c : ℝ) (α : I →₀ ℕ) :
    monomialScale (fun i => c * T i) α = c ^ α.degree * monomialScale T α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem monomialScale_le_const_mul {I : Type*} (N L : I → ℝ)
    (hN : ∀ i, 0 ≤ N i) (c : ℝ) (hNL : ∀ i, N i ≤ c * L i) (α : I →₀ ℕ) :
    monomialScale N α ≤ c ^ α.degree * monomialScale L α := by
  rw [← monomialScale_const_mul_degree]
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (hN i) _)
    (fun i _ => pow_le_pow_left₀ (hN i) (hNL i) _)

theorem PolynomialRationalApproximation.homogeneous_dilation_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (K : ℝ) (_hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.IsHomogeneous h)
    (happrox : PolynomialRationalApproximation L R (C ((q : ℝ) ^ h) * P)) :
    PolynomialRationalApproximation N R' P := by
  classical
  obtain ⟨D, hD, hDR, Q, hQ⟩ := happrox
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hqpow : 0 < (q : ℝ) ^ h := pow_pos (by exact_mod_cast hq) h
  have hDreal : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hR' : 0 ≤ R' := (mul_nonneg hqpow.le hR).trans hden
  refine ⟨q ^ h * D, Nat.mul_pos (Nat.pow_pos hq) hD, ?_,
    homogeneousComponent h Q, ?_⟩
  · push_cast
    exact (mul_le_mul_of_nonneg_left hDR hqpow.le).trans hden
  · intro α
    by_cases hα : α.degree = h
    · rw [coeff_homogeneousComponent, if_pos hα]
      have hid : P.coeff α - ((Q.coeff α : ℤ) : ℝ) / (q ^ h * D : ℕ) =
          ((q : ℝ) ^ h * P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D) / (q : ℝ) ^ h := by
        push_cast
        field_simp
      rw [hid, abs_div, abs_of_pos hqpow]
      have hscale := monomialScale_le_const_mul N L (fun i => (hN i).le) (K * q) hNL α
      rw [hα, mul_pow] at hscale
      have hscaleN := monomialScale_pos N hN α
      have hscaleL := monomialScale_pos L hL α
      calc
        _ ≤ (R / monomialScale L α) / (q : ℝ) ^ h :=
          div_le_div_of_nonneg_right (by simpa only [coeff_C_mul] using hQ α) hqpow.le
        _ ≤ K ^ h * R / monomialScale N α := by
          rw [div_div]
          apply (div_le_div_iff₀ (mul_pos hscaleL hqpow) hscaleN).mpr
          calc
            R * monomialScale N α ≤ R * (K ^ h * (q : ℝ) ^ h * monomialScale L α) :=
              mul_le_mul_of_nonneg_left hscale hR
            _ = (K ^ h * R) * (monomialScale L α * (q : ℝ) ^ h) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslow hscaleN.le
    · rw [hP.coeff_eq_zero hα, coeff_homogeneousComponent, if_neg hα, Int.cast_zero,
        zero_div, sub_zero, abs_zero]
      exact div_nonneg hR' (monomialScale_pos N hN α).le

theorem PolynomialRationalApproximation.affine_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ) (hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ h)
    (happrox : PolynomialRationalApproximation L R
      (homogeneousComponent h (residueAffinePolynomial q r P))) :
    PolynomialRationalApproximation N R' (homogeneousComponent h P) := by
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP] at happrox
  exact happrox.homogeneous_dilation_pullback N L hN hL q h hq K hK hNL R R'
    hden hslow (homogeneousComponent h P) (homogeneousComponent_isHomogeneous _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueAffinePolynomial_eval_real {I : Type*} (q : ℕ) (r : I → ℤ)
    (x : I → ℝ) (P : MvPolynomial I ℝ) :
    MvPolynomial.eval x (residueAffinePolynomial q r P) =
      MvPolynomial.eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, MvPolynomial.eval₂Hom_X', map_add,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at *
    rw [hP]

namespace VectorPolynomial

noncomputable def residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) : VectorPolynomial I ℝ V →ₗ[ℝ] VectorPolynomial I ℝ V :=
  substitute (fun i => MvPolynomial.C (r i : ℝ) +
    MvPolynomial.C (q : ℝ) * MvPolynomial.X i)

theorem eval_residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) (x : I → ℝ) (P : VectorPolynomial I ℝ V) :
    eval x (residueAffine q r P) = eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  simp only [residueAffine, eval_substitute, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem integerRowPolynomial_residueAffine {I J : Type*} [Fintype J]
    (a : J → ℤ) (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ (J → ℝ)) :
    integerRowPolynomial a (residueAffine q r P) =
      residueAffinePolynomial q r (integerRowPolynomial a P) := by
  apply MvPolynomial.funext
  intro x
  rw [integerRowPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, integerRowPolynomial_eval]

end VectorPolynomial

theorem HasLayerSamplingRank.residueAffine {I J : Type*} [Fintype J]
    {h : ℕ} {N L : I → ℝ} {Rbig Rsmall : ℝ}
    {W : Submodule ℝ (J → ℝ)} {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h N Rbig W P)
    (hP : VectorPolynomial.DegreeLE (fun _ => 1) h P)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (hrow : Rsmall ≤ Rbig)
    (hden : (q : ℝ)^h * Rsmall ≤ Rbig)
    (hslow : K^h * Rsmall ≤ Rbig) :
    HasLayerSamplingRank h L Rsmall W (VectorPolynomial.residueAffine q r P) := by
  intro a ha hw happ
  apply hrank a (fun j => (ha j).trans hrow) hw
  rw [VectorPolynomial.integerRowPolynomial_residueAffine] at happ
  have hcomparison (i : I) : N i ≤ max 1 K * (q : ℝ) * L i := by
    apply (hNL i).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (Nat.cast_nonneg q)) (hL i).le
  have hslow' : (max 1 K)^h * Rsmall ≤ Rbig := by
    by_cases hK : K ≤ 1
    · simpa only [max_eq_left hK, one_pow, one_mul] using hrow
    · simpa only [max_eq_right (le_of_not_ge hK)] using hslow
  exact happ.affine_pullback N L hN hL q h hq r (max 1 K) (le_max_left _ _)
    hcomparison Rsmall Rbig hden hslow' (VectorPolynomial.integerRowPolynomial a P)
    (VectorPolynomial.integerRowPolynomial_totalDegree_le a hP)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlowPolynomialSliceLogCost
namespace OAI

section

namespace Erdos3

def slowPolynomialSliceSlope (d n : ℕ) (M : ℝ) : ℝ :=
  (d + 1 : ℝ) * (n + 1 : ℝ) ^ d * M * n * d

noncomputable def slowPolynomialSliceRadius (d n : ℕ) (M : ℝ) : ℝ :=
  min 1 ((1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1))

theorem slowPolynomialSliceSlope_nonneg (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ slowPolynomialSliceSlope d n M := by
  unfold slowPolynomialSliceSlope
  positivity

theorem slowPolynomialSliceRadius_eq (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    slowPolynomialSliceRadius d n M =
      (1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1) := by
  apply min_eq_right
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hδ : 1 / (20 * Real.pi) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem slowPolynomialSliceRadius_pos (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < slowPolynomialSliceRadius d n M := by
  rw [slowPolynomialSliceRadius_eq d n hM]
  have := slowPolynomialSliceSlope_nonneg d n hM
  positivity

theorem slowPolynomialSliceSlope_le_exp (d n : ℕ) {M p : ℝ}
    (_hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) :
    slowPolynomialSliceSlope d n M ≤
      Real.exp (((d : ℝ) + 2) * p + 3 * d + 1) := by
  have hd1 : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  have hn1 : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hnp : (n : ℝ) ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by
    linarith [Real.add_one_le_exp (d : ℝ)]
  unfold slowPolynomialSliceSlope
  calc
    _ ≤ Real.exp ((d : ℝ) + 1) * (Real.exp (p + 1)) ^ d *
        Real.exp p * Real.exp p * Real.exp (d : ℝ) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem slowPolynomialSlice_log_cost (d n : ℕ) {M p q : ℝ}
    (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) (hq : 0 < q) (hqexp : q ≤ Real.exp p) :
    Real.log (4 * q / slowPolynomialSliceRadius d n M) ≤
      (p + (d + 400 : ℕ)) ^ (d + 400) := by
  let A : ℝ := ((d : ℝ) + 2) * p + 3 * d + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hKexp := slowPolynomialSliceSlope_le_exp d n (by linarith : 0 ≤ p) hn hM hMexp
  have hK1 : slowPolynomialSliceSlope d n M + 1 ≤ Real.exp (A + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hA (le_refl (0 : ℝ))
      hKexp (by simp : (1 : ℝ) ≤ Real.exp 0)
  have hπ : 80 * Real.pi ≤ Real.exp 320 := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (320 : ℝ)]
  have hradius := slowPolynomialSliceRadius_pos d n hM
  have hratio : 4 * q / slowPolynomialSliceRadius d n M =
      (80 * Real.pi) * q * (slowPolynomialSliceSlope d n M + 1) := by
    rw [slowPolynomialSliceRadius_eq d n hM]
    field_simp
    ring
  have hexp : 4 * q / slowPolynomialSliceRadius d n M ≤
      Real.exp (320 + p + (A + 1)) := by
    rw [hratio]
    calc
      _ ≤ Real.exp 320 * Real.exp p * Real.exp (A + 1) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hcost : 320 + p + (A + 1) ≤ (p + (d + 400 : ℕ)) ^ (d + 400) := by
    let t : ℝ := p + (d + 400 : ℕ)
    have hdt : (d : ℝ) + 400 ≤ t := by dsimp [t]; push_cast; linarith
    have hpt : p + 3 ≤ t := by dsimp [t]; push_cast; linarith
    have ht : 1 ≤ t := by dsimp [t]; push_cast; linarith
    calc
      _ ≤ ((d : ℝ) + 400) * (p + 3) := by dsimp [A]; nlinarith
      _ ≤ t * t := mul_le_mul hdt hpt (by linarith) (by linarith)
      _ = t ^ 2 := by ring
      _ ≤ t ^ (d + 400) := pow_le_pow_right₀ ht (by omega)
      _ = _ := rfl
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  exact hexp.trans (Real.exp_le_exp.mpr hcost)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MultiaffineTripleLayerBasis
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    (F.weightedLayer c n × F.coordinateActiveLayer i n × F.coordinateActiveLayer i n)
      ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨tripleAssemble (x.1 : L) (x.2.1 : L) (x.2.2 : L), by
    rw [F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble,
      tripleRight_assemble]
    exact ⟨x.1.property, x.2.1.property, x.2.2.property⟩⟩
  invFun x := (⟨tripleNeutral x.val, x.property.1⟩,
    ⟨tripleLeft x.val, x.property.2.1⟩, ⟨tripleRight x.val, x.property.2.2⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (tripleNeutral_assemble _ _ _)
    · exact Prod.ext (Subtype.ext (tripleLeft_assemble _ _ _))
        (Subtype.ext (tripleRight_assemble _ _ _))
  right_inv x := Subtype.ext (tripleAssemble_decompose x.val)
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp only [tripleAssemble, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, LieSubmodule.coe_add] <;> abel
  map_smul' r x := by
    apply Subtype.ext
    ext <;> simp [tripleAssemble, smul_add]

theorem exists_additiveTriple_layer_basis {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (e : Basis ι ℚ L) (i : σ) (c : σ → ℕ) (n : ℕ)
    (a : Basis α ℚ (F.weightedLayer c n))
    (b : Basis β ℚ (F.coordinateActiveLayer i n))
    {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ q : Basis (Fin (finrank ℚ (F.additiveTripleLayer i c n))) ℚ
        (F.additiveTripleLayer i c n),
      ∀ j k, RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
  classical
  let q := (a.prod (b.prod b)).map (F.additiveTripleLayerEquiv i c n)
  have hzero (k : ι) : RationalHeightLE (e.repr 0 k) H := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  have hq (j : α ⊕ (β ⊕ β)) (k : ι) :
      RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
    rcases j with j | j | j
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H from ⟨ha j k, ha j k, ha j k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H from ⟨hb j k, hb j k, hzero k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H from ⟨hb j k, hzero k, hb j k⟩)
  let r := q.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis q).symm)
  refine ⟨r, fun j k => ?_⟩
  simpa only [r, Basis.reindex_apply] using hq _ k

noncomputable def additiveTripleFiltrationLayerEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (F.additiveTripleFiltration i hi c hc).layer n ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.additiveTripleLayer_antitone i c hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ZeroDegreeCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem eval_eq_of_zero_coordinate {σ R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (p : VectorPolynomial σ R V) (i : σ)
    (hp : ∀ a, a i ≠ 0 → coefficients p a = 0)
    (x y : σ → R) (hxy : ∀ j, j ≠ i → x j = y j) : eval x p = eval y p := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro a ha
  have hi : a i = 0 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, pow_zero]
  · rw [hxy j hj]

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

theorem polynomialOrbitEval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
    (F : MultidegreeLieFiltration σ L s bound) (i : σ) (hi : bound i = 0)
    (g : F.PolynomialOrbit) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    F.polynomialOrbitEval x g = F.polynomialOrbitEval y g := by
  apply NilpotentLieBCHGroup.ext
  apply VectorPolynomial.eval_eq_of_zero_coordinate (g.log F) i
  · intro a ha
    have hn : ¬(fun j => a j) ≤ bound := by
      intro h
      exact ha (Nat.eq_zero_of_le_zero (by simpa only [hi] using h i))
    have h := g.adapted F a
    simpa only [F.terminal _ hn, Submodule.mem_bot] using h
  · intro j hj
    exact congrArg (fun z : ℤ => (z : ℚ)) (hxy j hj)

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointRationalSpaceDefiningMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix

namespace VectorPolynomial

theorem exists_jointRationalSpace_defining_matrix {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ Q : Matrix (J ⊕ V) J ℚ,
      (∀ v j, RationalHeightLE (Q v j)
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)) ∧
      LinearMap.ker (Matrix.of (fun v j => (Q v j : ℝ))).mulVecLin =
        jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ :=
    Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  refine ⟨A', ?_, ?_⟩
  · intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)),
        funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

theorem jointSpaceDefiningHeight_le_exp (ambient columns H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤
      Real.exp ((p+2)^10) := by
  rw [Nat.cast_max]
  exact max_le (imageDefiningHeight_le_exp columns ambient H hp hc ha hH)
    (hR.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 10))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationSizes
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

def rankCutDirectionHeight (ambient columns rows H R : ℕ) : ℕ :=
  (columns + 1) *
    (H * rationalKernelHeight (rows + 1) ((ambient + 1) * (R * H) ^ ambient)) ^ columns

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Matrix
open VectorPolynomial

structure RankPreparationLayer (I J : Type) where
  Coord : Type
  Column : Type
  Row : Type
  coordFinite : Fintype Coord
  columnFinite : Fintype Column
  rowFinite : Fintype Row
  label : Coord → J
  basis : Matrix Coord Column ℚ
  rows : Matrix Row Coord ℚ
  poly : VectorPolynomial I ℝ (Coord → ℝ)

attribute [instance] RankPreparationLayer.coordFinite RankPreparationLayer.columnFinite RankPreparationLayer.rowFinite

namespace RankPreparationLayer

variable {I J : Type}

noncomputable def space (L : RankPreparationLayer I J) : Submodule ℝ (L.Coord → ℝ) :=
  jointRationalSpace L.basis L.rows

noncomputable def rank (L : RankPreparationLayer I J) : ℕ := Module.finrank ℝ L.space

def Valid (L : RankPreparationLayer I J) (degree H R : ℕ) : Prop :=
  DegreeLE (fun _ => 1) degree L.poly ∧
  (∀ α, coefficients L.poly α ∈ L.space) ∧
  (∀ i j, RationalHeightLE (L.basis i j) H) ∧
  (∀ i j, RationalHeightLE (L.rows i j) R)

theorem Valid.mono_height {L : RankPreparationLayer I J} {d H H' R : ℕ}
    (h : L.Valid d H R) (hHH' : H ≤ H') : L.Valid d H' R :=
  ⟨h.1, h.2.1, fun i j => (h.2.2.1 i j).mono hHH', h.2.2.2⟩

noncomputable def value [DecidableEq J] (L : RankPreparationLayer I J) (x : I → ℝ) : J → ℝ :=
  coordinateCopySum L.label (eval x L.poly)

noncomputable def reindex (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    RankPreparationLayer I J := { L with poly := substitute f L.poly }

@[simp] theorem reindex_space (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).space = L.space := rfl

@[simp] theorem reindex_rank (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).rank = L.rank := rfl

noncomputable def cut (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ) :
    RankPreparationLayer I J where
  Coord := L.Coord
  Column := L.Column
  Row := Option L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := inferInstance
  label := L.label
  basis := L.basis
  rows := appendRankCutRow L.rows a
  poly := map (samplingRankProjection a e) L.poly

noncomputable def appendLine (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) : RankPreparationLayer I J where
  Coord := L.Coord ⊕ C
  Column := Option L.Column
  Row := L.Row
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := L.rowFinite
  label := Sum.elim L.label label
  basis := copiedLayerMatrix L.basis e
  rows := copiedLayerRows L.rows
  poly := copiedLayerPolynomial L.poly (l ⊗ₜ[ℝ] (fun i => (e i : ℝ)))

noncomputable def empty : RankPreparationLayer I J where
  Coord := PEmpty
  Column := PEmpty
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := PEmpty.elim
  basis := 0
  rows := 0
  poly := 0

theorem empty_valid (d H R : ℕ) : (empty : RankPreparationLayer I J).Valid d H R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α = 0
    simp only [map_zero, Finsupp.zero_apply]
  · intro α
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α ∈ _
    simp only [map_zero, Finsupp.zero_apply]
    exact Submodule.zero_mem _
  · intro i
    exact i.elim
  · intro i
    exact i.elim

@[simp] theorem empty_rank : (empty : RankPreparationLayer I J).rank = 0 := by
  apply Module.finrank_zero_iff.mpr
  change Subsingleton (jointRationalSpace (0 : Matrix PEmpty PEmpty ℚ) 0)
  infer_instance

@[simp] theorem empty_value [DecidableEq J] (x : I → ℝ) :
    (empty : RankPreparationLayer I J).value x = 0 := by
  have hzero (y : PEmpty → ℝ) : coordinateCopySum (PEmpty.elim : PEmpty → J) y = 0 := by
    ext j
    simp only [coordinateCopySum_apply, Fintype.sum_empty, Pi.zero_apply]
  exact hzero _

noncomputable def initial [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationLayer I J where
  Coord := J
  Column := J
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := id
  basis := 1
  rows := 0
  poly := p

theorem initial_space [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).space = ⊤ := by
  change jointRationalSpace (1 : Matrix J J ℚ) (0 : Matrix PEmpty J ℚ) = ⊤
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) *ᵥ x = x
      have hcast : Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) = 1 := by
        ext i j
        simp only [Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hcast, Matrix.one_mulVec]
    · ext i
      exact i.elim

@[simp] theorem initial_rank [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).rank = Fintype.card J := by
  unfold rank
  rw [initial_space]
  change Module.finrank ℝ (⊤ : Submodule ℝ (J → ℝ)) = Fintype.card J
  simp

@[simp] theorem initial_value [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) (x : I → ℝ) : (initial p).value x = eval x p := by
  ext j
  change (coordinateCopySum (R := ℝ) (id : J → J) (eval x p)) j = _
  simp [coordinateCopySum_apply]

end RankPreparationLayer
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

abbrev RankPreparationFamily (I J : Type) (s : ℕ) := Fin s → RankPreparationLayer I J

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ}

noncomputable def value [DecidableEq J] (L : RankPreparationFamily I J s) (x : I → ℝ) : J → ℝ :=
  ∑ i, (L i).value x

noncomputable def potential (L : RankPreparationFamily I J s) : ℕ :=
  layerRankPotential (fun i => (L i).rank)

noncomputable def reindex (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i => (L i).reindex f

@[simp] theorem reindex_potential (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).potential = L.potential := rfl

noncomputable def descend (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i =>
  if i = upper then (L upper).cut a (fun i => (e i : ℝ))
  else if i = lower then (L lower).appendLine (L upper).label e l
  else L i

noncomputable def absorb (L : RankPreparationFamily I J s) (lowest : Fin s)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) : RankPreparationFamily I J s :=
  fun i => if i = lowest then (L lowest).cut a (fun i => (e i : ℝ)) else L i

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

variable {I J : Type} {s : ℕ}

def Sized (L : RankPreparationFamily I J s) (D t : ℕ) : Prop :=
  ∀ i, Fintype.card (L i).Coord ≤ D * (t + 1) ^ (s - 1 - i.val) ∧
    Fintype.card (L i).Column ≤ D + t ∧ Fintype.card (L i).Row ≤ t

theorem Sized.mono {L : RankPreparationFamily I J s} {D t u : ℕ}
    (h : L.Sized D t) (htu : t ≤ u) : L.Sized D u := by
  intro i
  obtain ⟨hc, hb, hr⟩ := h i
  refine ⟨hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)), by omega, by omega⟩

theorem Sized.uniform {L : RankPreparationFamily I J s} {D t T : ℕ}
    (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ D * (T + 1) ^ s ∧
      Fintype.card (L i).Column ≤ D + T ∧ Fintype.card (L i).Row ≤ T := by
  have hm := h.mono ht
  refine ⟨(hm i).1.trans (Nat.mul_le_mul_left D ?_), (hm i).2⟩
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace VectorPolynomial

noncomputable def integerCoordinates {I J : Type*} [Fintype J] (ip : J → MvPolynomial I ℤ) :
    VectorPolynomial I ℝ (J → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ J) (fun j => MvPolynomial.map (Int.castRingHom ℝ) (ip j))

end VectorPolynomial

namespace RankPreparationFamily

noncomputable def polynomial {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) : VectorPolynomial I ℝ (J → ℝ) :=
  ∑ u, map (coordinateCopySum (L u).label) (L u).poly

end RankPreparationFamily

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PreparedIntegerRemainder
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} [Fintype J] [DecidableEq J] {m : ℕ}
variable (L : RankPreparationFamily X J m)

noncomputable def integerRemainder (ip : J → MvPolynomial X ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) : J → MvPolynomial X ℤ :=
  ip + ∑ u, coordinateCopySum (L u).label (β u)

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPullback
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

end VectorPolynomial

namespace RankPreparationLayer

variable {X Y J : Type}

noncomputable def pullback (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    RankPreparationLayer Y J where
  Coord := L.Coord
  Column := L.Column
  Row := L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := L.rowFinite
  label := L.label
  basis := L.basis
  rows := L.rows
  poly := substitute f L.poly

@[simp] theorem pullback_space (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).space = L.space := rfl

@[simp] theorem pullback_rank (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).rank = L.rank := rfl

end RankPreparationLayer

namespace RankPreparationFamily

variable {X Y J : Type} {m : ℕ}

noncomputable def pullback (L : RankPreparationFamily X J m) (f : X → MvPolynomial Y ℝ) :
    RankPreparationFamily Y J m := fun u => (L u).pullback f

end RankPreparationFamily
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X R : Type*} [Fintype K] [CommRing R] [Nontrivial R]

noncomputable def affineFramePolynomial (frame : Option K → X → R) (i : X) : MvPolynomial K R :=
  MvPolynomial.C (frame none i) + ∑ k, MvPolynomial.C (frame (some k) i) * MvPolynomial.X k

theorem affineFramePolynomial_degree (frame : Option K → X → R) (i : X) :
    (affineFramePolynomial frame i).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

omit [Nontrivial R] in
@[simp] theorem affineFramePolynomial_eval (frame : Option K → X → R) (y : K → R) (i : X) :
    MvPolynomial.aeval y (affineFramePolynomial frame i) =
      frame none i + ∑ k, frame (some k) i * y k := by
  simp [affineFramePolynomial]

omit [Nontrivial R] in
theorem affineFramePolynomial_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (frame : Option K → X → R) (i : X) :
    MvPolynomial.map φ (affineFramePolynomial frame i) =
      affineFramePolynomial (fun k i => φ (frame k i)) i := by
  simp [affineFramePolynomial]

end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {X K : Type} [Fintype K] {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace RankPreparationLayer

variable {I J K : Type}

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J K : Type} {s : ℕ}

@[simp] theorem pullback_potential (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial K ℝ) : (L.pullback f).potential = L.potential := rfl

end RankPreparationFamily

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem affineFramePolynomial_top_one (frame : Option K → X → ℝ) (x : X) :
    homogeneousComponent 1 (affineFramePolynomial frame x) =
      ∑ k, C (frame (some k) x) * MvPolynomial.X k := by
  rw [affineFramePolynomial, map_add,
    homogeneousComponent_eq_zero 1 (C (frame none x)) (by simp), zero_add,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [homogeneousComponent_C_mul,
    homogeneousComponent_eq_self (isHomogeneous_X ℝ k)]

theorem scaleMvPolynomialAxes_affineFrame_top_one
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x)) =
      ∑ k, C (frame (some k) x * T k) * MvPolynomial.X k := by
  apply MvPolynomial.funext
  intro y
  rw [scaleMvPolynomialAxes_eval, affineFramePolynomial_top_one]
  simp only [eval_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem scaleMvPolynomialAxes_C_mul {ι : Type*}
    (T : ι → ℝ) (c : ℝ) (p : MvPolynomial ι ℝ) :
    scaleMvPolynomialAxes T (C c * p) = C c * scaleMvPolynomialAxes T p := by
  apply MvPolynomial.funext
  intro y
  simp only [scaleMvPolynomialAxes_eval, map_mul, eval_C]

theorem spatialAffineTop_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass
      (scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_top_one]
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have h := realPolynomialMass_C_mul_le (frame (some k) x * T k) (MvPolynomial.X k)
  simpa only [realPolynomialMass_X, mul_one, abs_mul, abs_of_nonneg (hT k)] using h

theorem spatialAffineTop_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  exact mul_le_mul_of_nonneg_left (spatialAffineTop_mass_le frame T hT x)
    (inv_nonneg.mpr hN.le)

theorem spatialAffineTop_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * homogeneousComponent 1 (affineFramePolynomial frame x))) ≤
        N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineTop_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem scaleMvPolynomialAxes_affineFrame_eq_const_add_top
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (affineFramePolynomial frame x) =
      C (frame none x) +
        scaleMvPolynomialAxes T
          (homogeneousComponent 1 (affineFramePolynomial frame x)) := by
  apply MvPolynomial.funext
  intro y
  rw [affineFramePolynomial_top_one]
  simp only [scaleMvPolynomialAxes_eval, affineFramePolynomial,
    map_add, eval_C, eval_sum, map_mul, eval_X]

theorem spatialAffineFull_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k) (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
      |frame none x| + ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_affineFrame_eq_const_add_top]
  exact (realPolynomialMass_add_le _ _).trans
    (add_le_add (le_of_eq (realPolynomialMass_C _))
      (spatialAffineTop_mass_le frame T hT x))

theorem spatialAffineFull_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (C N⁻¹ *
      scaleMvPolynomialAxes T (affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  apply (realPolynomialMass_C_mul_le _ _).trans
  rw [abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ N⁻¹ * (|frame none x| + ∑ k, |frame (some k) x| * T k) :=
      mul_le_mul_of_nonneg_left (spatialAffineFull_mass_le frame T hT x)
        (inv_nonneg.mpr hN.le)
    _ = _ := by ring

theorem spatialAffineFull_scaled_inv_mul_mass_le
    (frame : Option K → X → ℝ) (T : K → ℝ) (hT : ∀ k, 0 ≤ T k)
    (x : X) (N : ℝ) (hN : 0 < N) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (C N⁻¹ * affineFramePolynomial frame x)) ≤
        |frame none x| / N + N⁻¹ * ∑ k, |frame (some k) x| * T k := by
  rw [scaleMvPolynomialAxes_C_mul]
  exact spatialAffineFull_inv_mul_mass_le frame T hT x N hN

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {I K R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_nonzero_mem (W : Submodule R V)
    (f : I → MvPolynomial K R) (P : VectorPolynomial I R V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : K →₀ ℕ) (hα : α ≠ 0) :
    coefficients (substitute f P) α ∈ W := by
  classical
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hβ0 : β = 0
  · subst β
    simp [MvPolynomial.coeff_one, Ne.symm hα]
  · exact W.smul_mem _ (hP β hβ0)

theorem coefficients_residueAffine_nonzero_mem {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : I →₀ ℕ) (hα : α ≠ 0) :
    coefficients (residueAffine q r P) α ∈ W :=
  coefficients_substitute_nonzero_mem W _ P hP α hα

end Erdos3.VectorPolynomial

end

end OAI

end


