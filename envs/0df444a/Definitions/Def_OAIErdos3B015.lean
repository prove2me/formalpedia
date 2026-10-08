-- Prove2me | Definitions.Def_OAIErdos3B015
-- name    : OAIErdos3B015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T11:25:41.343712+00:00
-- url     : https://prove2.me/theorems/f0bf8913-7f23-4e51-ae8f-262b95221883
-- title:
--   OpenAI Erdős-3 split, definitions bundle 16 of 88
-- statement:
--   Definitions bundle 16 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B014`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 16 available.
--
--   Modules: `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.centerParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coefficientBox`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval_centerParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval_mem_carrier`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanAffine`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanAffine_eq`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanAffine_pred_add_step`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanHom`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanHom_coeff`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanHom_injOn`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.freimanStep`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.image_freimanHom`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.mem_coefficientBox`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.mem_coefficientBox_iff_abs_le`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.sum_predParam_smul_add`, `OAI.Erdos3.CellRefinement.refinementContraction`, `OAI.Erdos3.CellRefinement.replacementIntegralSum`, `OAI.Erdos3.DegreeRankLieFiltration.Group`, `OAI.Erdos3.DegreeRankLieFiltration.HigherHorizontal`, `OAI.Erdos3.DegreeRankLieFiltration.associatedDegree`, `OAI.Erdos3.DegreeRankLieFiltration.associatedDegree_layer`, `OAI.Erdos3.DegreeRankLieFiltration.degree_antitone`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalAmbient`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalAmbient_apply`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalLayer`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalMap`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalAmbient`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalAmbient_injective`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalAmbient_mk`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalKernel`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalMk`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalMk_eq`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalMk_representative`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalMk_surjective`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalRepresentative`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalRepresentative_zero`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalTreeValue`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalTreeValue_mk`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalTreeValue_zero_of_leaf`, `OAI.Erdos3.DegreeRankLieFiltration.layerIdeal`, `OAI.Erdos3.DegreeRankLieFiltration.layer_eq_bot_of_past_top`, `OAI.Erdos3.DegreeRankLieFiltration.layer_eq_rankFlag`, `OAI.Erdos3.DegreeRankLieFiltration.layer_le_associatedDegree`, `OAI.Erdos3.DegreeRankLieFiltration.lieTreeEval_mem_length`, `OAI.Erdos3.DegreeRankLieFiltration.lieTreeEval_sub_mem`, `OAI.Erdos3.DegreeRankLieFiltration.mem_fourHorizontalLayer`, `OAI.Erdos3.DegreeRankLieFiltration.mem_layerIdeal`, `OAI.Erdos3.DegreeRankLieFiltration.mem_pi_layer`, `OAI.Erdos3.DegreeRankLieFiltration.mem_subgroup`, `OAI.Erdos3.DegreeRankLieFiltration.monomial_mem_polynomialFiltration`, `OAI.Erdos3.DegreeRankLieFiltration.noConfusion`, `OAI.Erdos3.DegreeRankLieFiltration.pi`, `OAI.Erdos3.DegreeRankLieFiltration.piLayerEquiv`, `OAI.Erdos3.DegreeRankLieFiltration.pi_associatedDegree`, `OAI.Erdos3.DegreeRankLieFiltration.polynomialFiltration`, `OAI.Erdos3.DegreeRankLieFiltration.polynomialFiltration_layer`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_antitone`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_decode_lt`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_encode`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_encode_lt`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_lie_mem`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_mul`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_terminal`, `OAI.Erdos3.DegreeRankLieFiltration.rankFlag_zero`, `OAI.Erdos3.DegreeRankLieFiltration.rank_antitone`, `OAI.Erdos3.DegreeRankLieFiltration.real_higherHorizontalAmbient_injective`, `OAI.Erdos3.DegreeRankLieFiltration.subgroup`, `OAI.Erdos3.DegreeRankLieFiltration.subgroup_le_associatedDegree`, `OAI.Erdos3.DegreeRankLieFiltration.top_lieTreeEval_congr`, `OAI.Erdos3.DegreeRankLieFiltration.zero_eq_top`, `OAI.Erdos3.FilteredLieTree.map_eval_mem_degreeLengthSpan`, `OAI.Erdos3.FilteredLieTree.map_eval_mem_degreeRank`, `OAI.Erdos3.LieGradingExpansion.component`, `OAI.Erdos3.LieGradingExpansion.component_apply`, `OAI.Erdos3.LieGradingExpansion.component_eq_zero`, `OAI.Erdos3.LieGradingExpansion.component_mem_span`, `OAI.Erdos3.LieGradingExpansion.component_tree`, `OAI.Erdos3.LieGradingExpansion.recOn`, `OAI.Erdos3.LieGradingExpansion.span_inter`, `OAI.Erdos3.MultidegreeLieFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.Group`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_diagonal`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_le_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_le_subalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_of_strictUpper`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_top_relation`, `OAI.Erdos3.MultidegreeLieFiltration.layerIdeal`, `OAI.Erdos3.MultidegreeLieFiltration.layer_le_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.layer_le_strictUpperLayer`, `OAI.Erdos3.MultidegreeLieFiltration.layer_le_weightedLayer`, `OAI.Erdos3.MultidegreeLieFiltration.layer_lie_strictUpper`, `OAI.Erdos3.MultidegreeLieFiltration.mem_dilationPairLayer`, `OAI.Erdos3.MultidegreeLieFiltration.mem_layerIdeal`, `OAI.Erdos3.MultidegreeLieFiltration.mem_pi_layer`, `OAI.Erdos3.MultidegreeLieFiltration.mem_subgroup`, `OAI.Erdos3.MultidegreeLieFiltration.ofLayers`, `OAI.Erdos3.MultidegreeLieFiltration.pi`, `OAI.Erdos3.MultidegreeLieFiltration.piLayerEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.pi_degree_eq`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeAdaptedModule`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMonomial_component_mem`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMonomial_mem_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_le_layer`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_le_ordinary`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_top`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpper_lie_layer`, `OAI.Erdos3.MultidegreeLieFiltration.subgroup`, `OAI.Erdos3.MultidegreeLieFiltration.successor_le_strictUpperLayer`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.weightedLayer_zero`, `OAI.Erdos3.NilpotentLieFiltration.Adapted`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.adapted`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.degreeLE`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.log`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstant`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstant_mem_shiftedIdeal`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLieSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialFiltration`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.adapted_bch`, `OAI.Erdos3.NilpotentLieFiltration.adapted_constant`, `OAI.Erdos3.NilpotentLieFiltration.adapted_degreeLE`, `OAI.Erdos3.NilpotentLieFiltration.adapted_iff_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.adapted_map`, `OAI.Erdos3.NilpotentLieFiltration.adapted_substitute`, `OAI.Erdos3.NilpotentLieFiltration.adapted_translate`, `OAI.Erdos3.NilpotentLieFiltration.canonicalDegreeRank`, `OAI.Erdos3.NilpotentLieFiltration.canonicalDegreeRank_associatedDegree_eq`, `OAI.Erdos3.NilpotentLieFiltration.canonicalDegreeRank_associatedDegree_layer`, `OAI.Erdos3.NilpotentLieFiltration.dilationPair_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.eq_of_layer_eq`, `OAI.Erdos3.NilpotentLieFiltration.lie_mem_adaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.lie_mem_polynomialLayer`, `OAI.Erdos3.NilpotentLieFiltration.lie_mem_shiftedAdaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.map_rankLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_adaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.mem_rankSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.monomial_mem_adaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.monomial_mem_polynomialLayer`, `OAI.Erdos3.NilpotentLieFiltration.monomial_mem_shiftedAdaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.orbitEquivOfEq`, `OAI.Erdos3.NilpotentLieFiltration.orbitEquivOfEq_eval`, `OAI.Erdos3.NilpotentLieFiltration.polynomialFiltration`, `OAI.Erdos3.NilpotentLieFiltration.polynomialLayer`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_coord`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_step_zero`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitOfLog`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitOfLog_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitSubstitute`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitSubstitute_eval`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitSubstitute_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.rankSubgroup`, `OAI.Erdos3.NilpotentLieFiltration.restrictLieSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.shiftedAdaptedIdeal`, `OAI.Erdos3.NilpotentLieFiltration.shiftedAdaptedSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.translate_sub_coefficient_mem`, `OAI.Erdos3.PolynomialPotentialRelation.compatible_partials`, `OAI.Erdos3.PolynomialPotentialRelation.linear_combination_mem`, `OAI.Erdos3.PolynomialPotentialRelation.polynomial_eq_linear_combination`, `OAI.Erdos3.PolynomialPotentialRelation.pure_eq_zero`, `OAI.Erdos3.PolynomialPotentialRelation.rec`, `OAI.Erdos3.PolynomialPotentialRelation.weighted_potential_derivative`, `OAI.Erdos3.PolynomialTranslationGroup`, `OAI.Erdos3.PolynomialTranslationGroup.action`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_C`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_X_inl`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_X_inr`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_mul`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_one`, `OAI.Erdos3.PolynomialTranslationGroup.actionHom_rename`, `OAI.Erdos3.PolynomialTranslationGroup.actionMonoidHom`, `OAI.Erdos3.PolynomialTranslationGroup.actionMonoidHom_injective`, `OAI.Erdos3.PolynomialTranslationGroup.base_inv`, `OAI.Erdos3.PolynomialTranslationGroup.base_mul`, `OAI.Erdos3.PolynomialTranslationGroup.base_one`, `OAI.Erdos3.PolynomialTranslationGroup.exponentialElement`, `OAI.Erdos3.PolynomialTranslationGroup.instGroup`, `OAI.Erdos3.PolynomialTranslationGroup.instInv`, `OAI.Erdos3.PolynomialTranslationGroup.instMul`, `OAI.Erdos3.PolynomialTranslationGroup.instOne`, `OAI.Erdos3.PolynomialTranslationGroup.polynomial_inv`, `OAI.Erdos3.PolynomialTranslationGroup.polynomial_mul`, `OAI.Erdos3.PolynomialTranslationGroup.polynomial_one`, `OAI.Erdos3.PolynomialTranslationGroup.potentialElement`, `OAI.Erdos3.PolynomialTranslationGroup.potentialElement_base`, `OAI.Erdos3.PolynomialTranslationGroup.potentialElement_polynomial`, `OAI.Erdos3.PolynomialTranslationGroup.potentialElement_zero`, `OAI.Erdos3.PolynomialTranslationGroup.potentialFlow`, `OAI.Erdos3.PolynomialTranslationGroup.potentialFlow_eq`, `OAI.Erdos3.PolynomialTranslationGroup.potentialFlow_zero`, `OAI.Erdos3.RelativeChangSanders.AddDissociatedMod`, `OAI.Erdos3.RelativeChangSanders.AddDissociatedMod.isWeightedDissociated`, `OAI.Erdos3.RelativeChangSanders.AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow`, `OAI.Erdos3.RelativeChangSanders.AddDissociatedMod.mono`, `OAI.Erdos3.RelativeChangSanders.AddDissociatedMod.weighted_riesz_randomisation_le`, `OAI.Erdos3.RelativeChangSanders.addDissociatedMod_empty`, `OAI.Erdos3.RelativeChangSanders.exists_maximal_addDissociatedMod`, `OAI.Erdos3.RelativeChangSanders.exists_maximal_addDissociatedMod_card_le`, `OAI.Erdos3.RelativeChangSanders.exists_relativeLargeSpectrum_cover`, `OAI.Erdos3.RelativeChangSanders.localChangBaseScale`, `OAI.Erdos3.RelativeChangSanders.localChangCap`, `OAI.Erdos3.RelativeChangSanders.localChangDimension`, `OAI.Erdos3.RelativeChangSanders.neg_mem_chang_largeSpectrum`, `OAI.Erdos3.RelativeChangSanders.zero_mem_chang_largeSpectrum_half`, `OAI.Erdos3.SquarefreeIndex.disjointAdd`, `OAI.Erdos3.SquarefreePolynomial`, `OAI.Erdos3.VectorPolynomial.DegreeLE.smul`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateForwardControlInput`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateForwardControlInput_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateForwardControlInput_cost_bound`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateForwardControlInput_denominator_bound`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateForwardControlInput_power_bound`, `OAI.Erdos3.VectorPolynomial.coefficientLieSubalgebra`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial_degree`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial_eval`, `OAI.Erdos3.VectorPolynomial.coefficientSubmodule`, `OAI.Erdos3.VectorPolynomial.coefficientSupport_lie`, `OAI.Erdos3.VectorPolynomial.coefficients_dilationPair`, `OAI.Erdos3.VectorPolynomial.coefficients_linearPolynomial_of_ne`, `OAI.Erdos3.VectorPolynomial.coefficients_linearPolynomial_single`, `OAI.Erdos3.VectorPolynomial.coefficients_linearPolynomial_zero`, `OAI.Erdos3.VectorPolynomial.coefficients_smul_mem`, `OAI.Erdos3.VectorPolynomial.coefficients_substitute`, `OAI.Erdos3.VectorPolynomial.coefficients_substitute_monomial`, `OAI.Erdos3.VectorPolynomial.coefficients_translate`, `OAI.Erdos3.VectorPolynomial.coefficients_translate_mem`, `OAI.Erdos3.VectorPolynomial.coefficients_translate_monomial`, `OAI.Erdos3.VectorPolynomial.coefficients_translate_sub`, `OAI.Erdos3.VectorPolynomial.coefficients_translate_sub_eq_zero_of_degreeLE`, `OAI.Erdos3.VectorPolynomial.coefficients_translate_sub_monomial`, `OAI.Erdos3.VectorPolynomial.coefficients_weightedDilation`, `OAI.Erdos3.VectorPolynomial.coordinate_eval₂`, `OAI.Erdos3.VectorPolynomial.degreeLE_finset_sum`, `OAI.Erdos3.VectorPolynomial.degreeLE_substitute_affine`, `OAI.Erdos3.VectorPolynomial.degreeLE_tmul_totalDegree`, `OAI.Erdos3.VectorPolynomial.degreeLE_translate`, `OAI.Erdos3.VectorPolynomial.dehomogenize_homogenize`, `OAI.Erdos3.VectorPolynomial.dehomogenize_monomial`, `OAI.Erdos3.VectorPolynomial.dilationPair`, `OAI.Erdos3.VectorPolynomial.eq_of_eval₂_eq_on_grid`, `OAI.Erdos3.VectorPolynomial.eq_zero_of_eval_zero`, `OAI.Erdos3.VectorPolynomial.eq_zero_of_eval₂_eq_zero_on_grid`, `OAI.Erdos3.VectorPolynomial.eq_zero_of_eval₂_zero`, `OAI.Erdos3.VectorPolynomial.evalLie`, `OAI.Erdos3.VectorPolynomial.evalLie_apply`, `OAI.Erdos3.VectorPolynomial.eval_dilationPair`, `OAI.Erdos3.VectorPolynomial.eval_homogenize`, `OAI.Erdos3.VectorPolynomial.eval_lieBCH`, `OAI.Erdos3.VectorPolynomial.eval_mem_iff_coefficients`, `OAI.Erdos3.VectorPolynomial.eval_substitute`, `OAI.Erdos3.VectorPolynomial.eval_translate`, `OAI.Erdos3.VectorPolynomial.eval_weightedDilation`, `OAI.Erdos3.VectorPolynomial.eval₂`, `OAI.Erdos3.VectorPolynomial.eval₂Lie`, `OAI.Erdos3.VectorPolynomial.eval₂Lie_apply`, `OAI.Erdos3.VectorPolynomial.eval₂_algebraMap`, `OAI.Erdos3.VectorPolynomial.eval₂_linearPolynomial`, `OAI.Erdos3.VectorPolynomial.eval₂_map`, `OAI.Erdos3.VectorPolynomial.eval₂_mem_iff_coefficients`, `OAI.Erdos3.VectorPolynomial.eval₂_monomial`, `OAI.Erdos3.VectorPolynomial.eval₂_ofCoordinates`, `OAI.Erdos3.VectorPolynomial.eval₂_tmul`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForwardSchedule_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForwardStage_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForward_composed_phase_cap`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForward_polynomial_cap`, `OAI.Erdos3.VectorPolynomial.homogeneousPart_translate`, `OAI.Erdos3.VectorPolynomial.homogeneous_finset_sum`, `OAI.Erdos3.VectorPolynomial.homogenize`, `OAI.Erdos3.VectorPolynomial.homogenize_apply`, `OAI.Erdos3.VectorPolynomial.homogenize_homogeneous`, `OAI.Erdos3.VectorPolynomial.integerRowLinear`, `OAI.Erdos3.VectorPolynomial.integerRowLinear_apply`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_coeff`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_homogeneous`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_smul`, `OAI.Erdos3.VectorPolynomial.le_preparedFiniteForwardCount`, `OAI.Erdos3.VectorPolynomial.le_preparedFiniteForwardCumulative`, `OAI.Erdos3.VectorPolynomial.le_preparedFiniteForwardParameter`, `OAI.Erdos3.VectorPolynomial.lie_monomial`, `OAI.Erdos3.VectorPolynomial.linearPolynomial`, `OAI.Erdos3.VectorPolynomial.linearPolynomial_apply`, `OAI.Erdos3.VectorPolynomial.lowerCentralSeries_eq_bot`, `OAI.Erdos3.VectorPolynomial.map_substitute`, `OAI.Erdos3.VectorPolynomial.mem_outsideDownsetIdeal`, `OAI.Erdos3.VectorPolynomial.mem_restrictedOutsideDownsetIdeal`, `OAI.Erdos3.VectorPolynomial.monomial_mem_coefficientSubmodule`, `OAI.Erdos3.VectorPolynomial.outsideDownsetIdeal`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardBranch`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardBranchPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardBranch_eq`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardBranch_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCapPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap_eq`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap_le_count`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap_le_cumulative`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap_le_cumulative_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCap_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCount`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCountPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCount_eq`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCount_le_parameter`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCount_le_parameter_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCount_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCumulative`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCumulative_le_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCumulative_monotone`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCumulative_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardCumulative_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardModelPrecision`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameterPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameterPolynomial_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameterPolynomial_zero`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_le_count`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_monotone`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_prefix`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_strictMono`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_succ`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardParameter_zero`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardPrefixLog`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardSourcePrecision`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardWork`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardWorkPolynomial`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardWork_eq`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardWork_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_branch_count_log`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_controlled_slice_bounds`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_model_precision_bounds`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_model_scalar_bounds`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_phase_cap`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_prefix_bounds`, `OAI.Erdos3.VectorPolynomial.restrictedOutsideDownsetIdeal`, `OAI.Erdos3.VectorPolynomial.substitute`, `OAI.Erdos3.VectorPolynomial.substituteLie`, `OAI.Erdos3.VectorPolynomial.substitute_comp`, `OAI.Erdos3.VectorPolynomial.substitute_tmul`, `OAI.Erdos3.VectorPolynomial.translate`, `OAI.Erdos3.VectorPolynomial.translate_tmul`, `OAI.Erdos3.VectorPolynomial.weightedDilation`, `OAI.Erdos3.VectorPolynomial.weightedDilation_lie`, `OAI.Erdos3.VectorPolynomial.weightedDilation_monomial`, `OAI.Erdos3.VectorPolynomial.weightedDilation_one`, `OAI.Erdos3.VectorPolynomial.weighted_monomial_dilation`, `OAI.Erdos3.WeightedLoweringAut.degreeAction`, `OAI.Erdos3.WeightedLoweringAut.degreeActionHom`, `OAI.Erdos3.WeightedLoweringAut.degreeActionHom_injective`, `OAI.Erdos3.WeightedLoweringAut.degreeAction_apply_coe`, `OAI.Erdos3.WeightedLoweringAut.degreeAction_difference_nilpotent`, `OAI.Erdos3.WeightedLoweringAut.degreeAction_difference_pow_coe`, `OAI.Erdos3.WeightedLoweringAut.degreeAction_difference_pow_zero`, `OAI.Erdos3.abs_aeval_sub_aeval_mass_box_bound`, `OAI.Erdos3.abs_eval_sub_eval_normalized_mass_bound`, `OAI.Erdos3.abs_eval_sub_eval_unit_mass_bound`, `OAI.Erdos3.abs_monomialScale_le_pow`, `OAI.Erdos3.aeval_isWeightedHomogeneous`, `OAI.Erdos3.aeval_weightedHomogeneousComponent`, `OAI.Erdos3.affineProbabilityProfile_scaled_support`, `OAI.Erdos3.allocatedIntegerCoefficient_bound`, `OAI.Erdos3.allocatedIntegerPolynomialCoordinatePMF`, `OAI.Erdos3.allocatedIntegerPolynomial_box`, `OAI.Erdos3.allocatedProfile_term_bound`, `OAI.Erdos3.coeff_zero_polynomialLinearRestriction`, `OAI.Erdos3.coefficient_zero_of_squarefreeKernel`, `OAI.Erdos3.coefficients_realMatrixPolynomialMap`, `OAI.Erdos3.continuousPolynomialDensity`, `OAI.Erdos3.continuousPolynomialDensity_box`, `OAI.Erdos3.continuousPolynomialDensity_width_pos`, `OAI.Erdos3.coordinateJoin`, `OAI.Erdos3.coordinateJoin_eta`, `OAI.Erdos3.coordinateJoin_injective`, `OAI.Erdos3.coordinateJoin_other`, `OAI.Erdos3.coordinateJoin_pivot`, `OAI.Erdos3.coordinateWeightProjection`, `OAI.Erdos3.degreeOf_rename_inl_inr`, `OAI.Erdos3.dehomogenize_monomial`, `OAI.Erdos3.embeddedMatrixDeterminantLip_le_exp`, `OAI.Erdos3.eval_linearCoordinatePolynomial`, `OAI.Erdos3.eval_polynomialLinearRestriction`, `OAI.Erdos3.exists_generalReconstructionLogBudget_bound`, `OAI.Erdos3.exists_image_cover_reconstruction_budget`, `OAI.Erdos3.exists_rationalPolynomial_of_realCoefficientGrid`, `OAI.Erdos3.exists_translationMajorDecomposition_budget`, `OAI.Erdos3.generalReconstructionLogBudget`, `OAI.Erdos3.generalReconstructionLogBudget_bounds`, `OAI.Erdos3.homogeneousLieSpan`, `OAI.Erdos3.homogeneousLieSpan_empty`, `OAI.Erdos3.homogeneousLieSpan_mono`, `OAI.Erdos3.imageLatticeBound_le_exp`, `OAI.Erdos3.imageLatticeLogBudget`, `OAI.Erdos3.imageLatticeLogBudget_nonneg`, `OAI.Erdos3.imageRepresentativeLogBudget`, `OAI.Erdos3.independentProductPMF_coordinate_cap`, `OAI.Erdos3.independentProductPMF_coordinate_split`, `OAI.Erdos3.integerMonomialArrayPolynomial`, `OAI.Erdos3.integerMonomialArrayPolynomial_degree`, `OAI.Erdos3.integerMonomialArrayPolynomial_map`, `OAI.Erdos3.integerPolynomialCoordinatePMF`, `OAI.Erdos3.integerPolynomialCoordinatePMF_bound`, `OAI.Erdos3.integerPolynomialCoordinatePMF_box`, `OAI.Erdos3.integer_shifts_small_box_injective`, `OAI.Erdos3.integralBasisPolynomialCoordinates`, `OAI.Erdos3.integralBasisPolynomialCoordinates_totalDegree`, `OAI.Erdos3.integralBasisPolynomialCoordinates_weightedDegree`, `OAI.Erdos3.isWeightedHomogeneous_aeval_monomial`, `OAI.Erdos3.isWeightedHomogeneous_algHom`, `OAI.Erdos3.isWeightedHomogeneous_mul_pderiv`, `OAI.Erdos3.jointPolynomialDilation_coefficientGrid`, `OAI.Erdos3.jointPolynomialDilation_mass_le`, `OAI.Erdos3.jointRationalPolynomialDilation`, `OAI.Erdos3.jointRationalPolynomialDilation_denominatorGrid`, `OAI.Erdos3.jointRationalPolynomialDilation_eval₂`, `OAI.Erdos3.jointRationalPolynomialDilation_map`, `OAI.Erdos3.jointRationalPolynomialDilation_mem_weightedSupportLE`, `OAI.Erdos3.layer_le_multidegreeTotalLayer`, `OAI.Erdos3.linearCoordinatePolynomial`, `OAI.Erdos3.linearCoordinatePolynomial_eq_sum`, `OAI.Erdos3.linearCoordinatePolynomial_isWeightedHomogeneous`, `OAI.Erdos3.linearCoordinatePolynomial_realCoefficientGrid`, `OAI.Erdos3.linearCoordinatePolynomial_realMass_le`, `OAI.Erdos3.linearMap_apply_sum_coordinates`, `OAI.Erdos3.linearMap_baseChange_lieBCH_eq_add`, `OAI.Erdos3.linearMap_baseChange_lie_eq_zero`, `OAI.Erdos3.linearMap_coordinateGradeProjection`, `OAI.Erdos3.linearMap_lieBCH_eq_add`, `OAI.Erdos3.lipschitzOn_realPolynomialVector_mass_box`, `OAI.Erdos3.lipschitzOn_realPolynomial_mass_box`, `OAI.Erdos3.majorRationalPolynomial_weightedSupportLE`, `OAI.Erdos3.majorShiftCoordinates_weightedSupportLE`, `OAI.Erdos3.majorShiftSubstitution_weightedSupportLE`, `OAI.Erdos3.majorSlowPolynomial_weightedSupportLE`, `OAI.Erdos3.map_polynomialLinearRestriction_ratCast`, `OAI.Erdos3.modularBoundedCoefficientPolynomial`, `OAI.Erdos3.modularBoundedCoefficientPolynomial_selected`, `OAI.Erdos3.modularBoundedCoefficientPolynomial_selected_top`, `OAI.Erdos3.modularMonomialArrayPolynomial_selected`, `OAI.Erdos3.modularUnselectedCoefficientPolynomial`, `OAI.Erdos3.monomialArrayPolynomial_box_bound`, `OAI.Erdos3.monomialArrayPolynomial_box_budget`, `OAI.Erdos3.monomialExponentSet`, `OAI.Erdos3.monomial_abs_le_scale`, `OAI.Erdos3.multiaffine_bias_approximation`, `OAI.Erdos3.multidegreeTotalLayer`, `OAI.Erdos3.multidegreeTotalLayer_antitone`, `OAI.Erdos3.multidegreeTotalLayer_eq`, `OAI.Erdos3.multidegreeTotalLayer_lie_mem`, `OAI.Erdos3.multidegreeTotalLayer_terminal`, `OAI.Erdos3.multidegreeWeight`, `OAI.Erdos3.multidegreeWeight_add`, `OAI.Erdos3.multidegreeWeight_mono`, `OAI.Erdos3.natPolynomial_eval_mono_nonneg`, `OAI.Erdos3.nearInteger_rational_approximation`, `OAI.Erdos3.nonprincipalCoefficientSlots`, `OAI.Erdos3.nonprincipalDilation`, `OAI.Erdos3.parameterLinearCoordinate`, `OAI.Erdos3.parameterPolynomialPullback`, `OAI.Erdos3.parameterPolynomialPullback_degree`, `OAI.Erdos3.parameterPolynomialPullback_eval`, `OAI.Erdos3.polynomialDenominator_coefficientGrid`, `OAI.Erdos3.polynomialExponentialCoordinate`, `OAI.Erdos3.polynomialExponentialCoordinate_C`, `OAI.Erdos3.polynomialExponentialCoordinate_formula`, `OAI.Erdos3.polynomialExponentialCoordinate_neg_series_of_nilpotent`, `OAI.Erdos3.polynomialExponentialCoordinate_potential`, `OAI.Erdos3.polynomialExponentialCoordinate_zero`, `OAI.Erdos3.polynomialExponentialPath`, `OAI.Erdos3.polynomialExponentialPath_C`, `OAI.Erdos3.polynomialExponentialPath_derivative`, `OAI.Erdos3.polynomialExponentialPath_eval_potential`, `OAI.Erdos3.polynomialExponentialPath_eval_zero`, `OAI.Erdos3.polynomialExponentialPath_potential`, `OAI.Erdos3.polynomialExponentialPath_translate_reflection`, `OAI.Erdos3.polynomialExponentialPath_unique`, `OAI.Erdos3.polynomialExponentialPath_zero`, `OAI.Erdos3.polynomialLinearRestriction`, `OAI.Erdos3.polynomialLinearRestriction_C`, `OAI.Erdos3.polynomialLinearRestriction_X`, `OAI.Erdos3.polynomialLinearRestriction_coeff_abs_le`, `OAI.Erdos3.polynomialLinearRestriction_denominatorGrid`, `OAI.Erdos3.polynomialLinearRestriction_exponentialCoordinate`, `OAI.Erdos3.polynomialLinearRestriction_exponentialPath`, `OAI.Erdos3.polynomialLinearRestriction_height`, `OAI.Erdos3.polynomialLinearRestriction_isWeightedHomogeneous`, `OAI.Erdos3.polynomialLinearRestriction_leftInverse`, `OAI.Erdos3.polynomialLinearRestriction_monomial_homogeneous`, `OAI.Erdos3.polynomialLinearRestriction_realMass_le`, `OAI.Erdos3.polynomialLinearRestriction_translationPath`, `OAI.Erdos3.polynomialTranslate_comp`, `OAI.Erdos3.polynomialTranslate_exponentialCoordinate`, `OAI.Erdos3.polynomialTranslate_exponentialCoordinate_series`, `OAI.Erdos3.polynomialTranslate_exponentialCoordinate_series_of_nilpotent`, `OAI.Erdos3.polynomialTranslationPath_linearCoordinatePolynomial`, `OAI.Erdos3.polynomialTranslationPath_neg_coeff`, `OAI.Erdos3.polynomialTranslationPath_neg_derivative`, `OAI.Erdos3.polynomialTranslationPath_neg_support_of_nilpotent`, `OAI.Erdos3.polynomialTranslationPath_translate_reflection`, `OAI.Erdos3.polynomialTranslationPath_zero`, `OAI.Erdos3.positiveIntegerPeriodization`, `OAI.Erdos3.positiveIntegerPeriodization_lipschitz`, `OAI.Erdos3.positiveIntegerPeriodization_local`, `OAI.Erdos3.positiveIntegerPeriodization_periodic`, `OAI.Erdos3.positiveIntegerPeriodization_range`, `OAI.Erdos3.rationalAxisScaling_map_real`, `OAI.Erdos3.rationalAxisScaling_mem_weightedSupportLE`, `OAI.Erdos3.rationalAxisScaling_support_subset`, `OAI.Erdos3.rationalHeightLE_of_integral_mul_of_abs_le`, `OAI.Erdos3.rationalPolynomial_realMass_le`, `OAI.Erdos3.realMatrixPolynomialMap`, `OAI.Erdos3.realPolynomialMass_translationDirectionalDerivative`, `OAI.Erdos3.realPolynomialMass_translationDirectionalDerivative_pow`, `OAI.Erdos3.realPolynomialMass_translationDirectionalSeries`, `OAI.Erdos3.realSquarefreeMonomial_ne`, `OAI.Erdos3.realSquarefreeMonomial_self`, `OAI.Erdos3.realSquarefreePolynomialEquiv`, `OAI.Erdos3.realSquarefreePolynomialEquiv_tmul`, `OAI.Erdos3.rectangularWeightIndices_normalized_bound`, `OAI.Erdos3.scalarDirectionalDerivative_linearCoordinatePolynomial`, `OAI.Erdos3.scalarDirectionalDerivative_linearRestriction`, `OAI.Erdos3.scalarDirectionalDerivative_neg`, `OAI.Erdos3.scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport`, `OAI.Erdos3.scalarDirectionalDerivative_single`, `OAI.Erdos3.scalarDirectionalDerivative_zero`, `OAI.Erdos3.scaleMvPolynomialAxes`, `OAI.Erdos3.scaleMvPolynomialAxes_coeff`, `OAI.Erdos3.scaleMvPolynomialAxes_eq_aeval`, `OAI.Erdos3.scaleMvPolynomialAxes_eval`, `OAI.Erdos3.scaleMvPolynomialAxes_mass_le`, `OAI.Erdos3.scaleMvPolynomialAxes_mass_le_of_abs_le`, `OAI.Erdos3.scaleMvPolynomialAxes_mem_weightedSupportLE`, `OAI.Erdos3.scaleMvPolynomialAxes_support_subset`, `OAI.Erdos3.scaleMvPolynomialAxes_totalDegree_le`, `OAI.Erdos3.scaleMvPolynomialAxes_weightedHomogeneousComponent`, `OAI.Erdos3.scaledCoefficientDensity`, `OAI.Erdos3.scaledCoefficientDensity_box_bound`, `OAI.Erdos3.scaledCoefficientDensity_coefficient_bound`, `OAI.Erdos3.scaledCoefficientDensity_support`, `OAI.Erdos3.shiftedSmoothPositiveGrid`, `OAI.Erdos3.shiftedSmoothPositiveGridWeights`, `OAI.Erdos3.shiftedSmoothPositiveGridWeights_weight`, `OAI.Erdos3.shiftedSmoothPositiveGrid_zero_off`, `OAI.Erdos3.shiftedSmoothProductFiniteWeights_event_eq_map`, `OAI.Erdos3.shiftedSmoothProductFiniteWeights_mean_eq_tsum`, `OAI.Erdos3.shiftedSmoothProductFiniteWeights_point_le`, `OAI.Erdos3.shiftedSmoothProductMass_coordinate_pos`, `OAI.Erdos3.shiftedSmoothProductMass_restrict_pos`, `OAI.Erdos3.shiftedSmoothProductPMF_coordinate_cap`, `OAI.Erdos3.shiftedSmoothProductPMF_eq_independent`, `OAI.Erdos3.shiftedSmoothProductPMF_point_le`, `OAI.Erdos3.shiftedSmoothProductPMF_selected_marginal`, `OAI.Erdos3.shiftedSmoothProduct_polynomial_family_threshold`, `OAI.Erdos3.shiftedSmoothProduct_polynomial_sublevel`, `OAI.Erdos3.shiftedSmoothSublevelConstant`, `OAI.Erdos3.shiftedSmoothSublevelConstant_le_exp`, `OAI.Erdos3.shiftedSmoothSublevelConstant_nonneg`, `OAI.Erdos3.shiftedSmoothSublevelThreshold`, `OAI.Erdos3.shiftedSmoothSublevelThreshold_pos`, `OAI.Erdos3.small_coordinate_lift_unique`, `OAI.Erdos3.smoothInputJoin`, `OAI.Erdos3.smoothInputSplit`, `OAI.Erdos3.smoothMatrixBlockConstantLogBudget`, `OAI.Erdos3.smoothMatrixBlockConstantLogBudget_nonneg`, `OAI.Erdos3.smoothMatrixBlockMesh`, `OAI.Erdos3.smoothMatrixBlockMeshLogBudget`, `OAI.Erdos3.smoothMatrixBlockMeshLogBudget_nonneg`, `OAI.Erdos3.smoothMatrixBlockMesh_inv_le_exp`, `OAI.Erdos3.smoothMatrixBlockMesh_inv_le_exp_of_lip_bound`, `OAI.Erdos3.smoothMatrixBlockMesh_spec`, `OAI.Erdos3.smoothMatrixBlockMesh_width_spec`, `OAI.Erdos3.smoothMatrixBlockThresholdLogBudget`, `OAI.Erdos3.smoothMatrixBlockThresholdLogBudget_nonneg`, `OAI.Erdos3.smoothMatrixBlockWidthLogBudget`, `OAI.Erdos3.smoothMatrixBlock_actual_mesh_inverse_le_exp`, `OAI.Erdos3.smoothMatrixBlock_actual_width_le_exp`, `OAI.Erdos3.smoothMatrixBlock_bad_probability`, `OAI.Erdos3.smoothMatrixBlock_scale_le_exp`, `OAI.Erdos3.smoothMatrixBlock_threshold_inverse_le_exp`, `OAI.Erdos3.some_degree_le`, `OAI.Erdos3.squarefreeKernel_lie_mem`, `OAI.Erdos3.squarefreeMk`, `OAI.Erdos3.squarefreeMk_monomial_zero`, `OAI.Erdos3.squarefreeMonomial`, `OAI.Erdos3.squarefreeMonomial_apply`, `OAI.Erdos3.squarefreeMonomial_lie_coefficient`, `OAI.Erdos3.squarefreeMonomial_lie_disjoint`, `OAI.Erdos3.squarefreeMonomial_lie_overlap`, `OAI.Erdos3.squarefreeMonomial_mem_support`, `OAI.Erdos3.squarefreePolynomialEquiv`, `OAI.Erdos3.squarefreePolynomialEquiv_mk`, `OAI.Erdos3.squarefreePolynomialEquiv_monomial_ne`, `OAI.Erdos3.squarefreePolynomialEquiv_monomial_self`, `OAI.Erdos3.squarefreePolynomialIdeal`, `OAI.Erdos3.squarefreeSupportModule`, `OAI.Erdos3.squarefree_lie_coefficient`, `OAI.Erdos3.sum_squarefreeMonomial`, `OAI.Erdos3.translationDirectionalDerivative`, `OAI.Erdos3.translationDirectionalDerivative_apply`, `OAI.Erdos3.translationDirectionalDerivative_degreeOf_le`, `OAI.Erdos3.translationDirectionalDerivative_isWeightedHomogeneous`, `OAI.Erdos3.translationDirectionalDerivative_pow_degreeOf_le`, `OAI.Erdos3.translationDirectionalDerivative_pow_isWeightedHomogeneous`, `OAI.Erdos3.translationDirectionalSeries`, `OAI.Erdos3.translationDirectionalSeries_coefficient_abs_le_one`, `OAI.Erdos3.translationDirectionalSeries_isWeightedHomogeneous`, `OAI.Erdos3.weightedHomogeneousComponent_eq_of_sub_lower`, `OAI.Erdos3.weightedLieDegreeLengthSpan`, `OAI.Erdos3.weightedLieDegreeLengthSpan_antitone`, `OAI.Erdos3.weightedLieDegreeLengthSpan_lie_mem`, `OAI.Erdos3.weightedLieDegreeLengthSpan_top_le_ker`, `OAI.Erdos3.weightedLieUpperSpan_map_le_degreeLengthSpan`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.norm_signedCoefficient_le`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.rieszProduct_eq_signedExpansion`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.signedCoefficient`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.signedFrequency`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.signedFrequency_not_mem`, `_private.Estimates.CyclicRelativeChang.0.OAI.Erdos3.RelativeChangSanders.weightedRiesz_eq_signedExpansion`, `_private.Linear.SmoothMatrixBlockBudget.0.OAI.Erdos3.matrixBlock_decide_eq_classical`, `_private.Polynomial.JointPolynomialDilationGrid.0.OAI.Erdos3.abs_prod_sub_prod_unit_sum`, `_private.Polynomial.ShiftedSmoothPolynomialSublevel.0.OAI.Erdos3.decide_eq_classical`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def eval₂ (x : σ → S) : VectorPolynomial σ R V →ₗ[R] V :=
  TensorProduct.lift ((Algebra.lsmul R R V).toLinearMap.comp (MvPolynomial.aeval x).toLinearMap)

@[simp] theorem eval₂_tmul (x : σ → S) (p : MvPolynomial σ R) (v : V) :
    eval₂ x (p ⊗ₜ[R] v) = MvPolynomial.aeval x p • v := rfl

@[simp] theorem eval₂_monomial (x : σ → S) (α : σ →₀ ℕ) (v : V) :
    eval₂ x (monomial (R := R) α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.aeval_monomial]

theorem eval₂_algebraMap (x : σ → R) (p : VectorPolynomial σ R V) :
    eval₂ (fun i => algebraMap R S (x i)) p = eval x p := by
  have heval (q : MvPolynomial σ R) :
      MvPolynomial.aeval (fun i => algebraMap R S (x i)) q =
        algebraMap R S (MvPolynomial.aeval x q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp only [eval₂_tmul, eval_tmul, heval, IsScalarTower.algebraMap_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coordinate_eval₂ (f : V →ₗ[S] S) (x : σ → S) (p : VectorPolynomial σ R V) :
    f (eval₂ x p) = MvPolynomial.eval x (coordinate f.toAddMonoidHom p) := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, coordinate_sum, coordinate_monomial,
    eval₂_monomial, MvPolynomial.eval_monomial, map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eval₂_ofCoordinates {ι : Type*} [Fintype ι] (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (x : σ → S) :
    eval₂ x (ofCoordinates (R := R) e p) =
      e.equivFun.symm (fun i => MvPolynomial.eval x (p i)) := by
  apply e.equivFun.injective
  funext i
  rw [e.equivFun.apply_symm_apply]
  change e.coord i (eval₂ x (ofCoordinates (R := R) e p)) = _
  rw [coordinate_eval₂]
  exact congrArg (MvPolynomial.eval x) (coordinate_ofCoordinates e p i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def integerRowLinear {J : Type*} [Fintype J] (a : J → ℤ) :
    (J → ℝ) →ₗ[ℝ] ℝ := ∑ j, (a j : ℝ) • LinearMap.proj j

theorem integerRowLinear_apply {J : Type*} [Fintype J] (a : J → ℤ) (w : J → ℝ) :
    integerRowLinear a w = ∑ j, (a j : ℝ) * w j := by
  simp [integerRowLinear]

noncomputable def integerRowPolynomial {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) : MvPolynomial I ℝ :=
  coordinate (integerRowLinear a).toAddMonoidHom p

theorem integerRowPolynomial_coeff {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (α : I →₀ ℕ) :
    (integerRowPolynomial a p).coeff α = ∑ j, (a j : ℝ) * coefficients p α j := by
  simp only [integerRowPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    integerRowLinear_apply]

theorem integerRowPolynomial_eval {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial a p) = ∑ j, (a j : ℝ) * eval w p j := by
  have he : eval₂ w p = eval w p := by
    simpa using (eval₂_algebraMap (S := ℝ) w p)
  rw [integerRowPolynomial, ← coordinate_eval₂, he, integerRowLinear_apply]

theorem integerRowPolynomial_homogeneous {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) {h : ℕ} (hp : Homogeneous h p) :
    (integerRowPolynomial a p).IsHomogeneous h := by
  intro α hα
  by_contra hn
  have hd : α.degree ≠ h := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hn
  apply hα
  simp only [integerRowPolynomial_coeff, hp α hd, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

variable {X D E : Type*}

noncomputable def integralBasisPolynomialCoordinates
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U) : E → MvPolynomial X ℝ :=
  fun e => coordinate (b.coord e).toAddMonoidHom (restrictCoefficients U p hmem)

theorem integralBasisPolynomialCoordinates_weightedDegree
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U)
    {w : X → ℕ} {d : ℕ} (hp : DegreeLE w d p) (e : E) :
    (integralBasisPolynomialCoordinates U b p hmem e).weightedTotalDegree w ≤ d := by
  apply (scalar_weightedDegree_le_iff w d _).mpr
  intro α hα
  change (b.coord e) (coefficients (restrictCoefficients U p hmem) α) = 0
  have hz : coefficients (restrictCoefficients U p hmem) α = 0 := by
    apply Subtype.ext
    exact (coefficients_restrictCoefficients U p hmem α).trans (hp α hα)
  rw [hz, map_zero]

theorem integralBasisPolynomialCoordinates_totalDegree
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U)
    {d : ℕ} (hp : DegreeLE (1 : X → ℕ) d p) (e : E) :
    (integralBasisPolynomialCoordinates U b p hmem e).totalDegree ≤ d := by
  simpa only [MvPolynomial.weightedTotalDegree_one] using
    integralBasisPolynomialCoordinates_weightedDegree U b p hmem hp e

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def linearPolynomial : (σ → V) →ₗ[R] VectorPolynomial σ R V where
  toFun a := ∑ i, monomial (Finsupp.single i 1) (a i)
  map_add' a b := by
    simp only [Pi.add_apply, monomial, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, monomial, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem linearPolynomial_apply (a : σ → V) :
    linearPolynomial (R := R) a = ∑ i, monomial (Finsupp.single i 1) (a i) := rfl

theorem coefficients_linearPolynomial_single (a : σ → V) (i : σ) :
    coefficients (linearPolynomial (R := R) a) (Finsupp.single i 1) = a i := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro j _ hji
    rw [coefficients_monomial, Finsupp.single_eq_of_ne]
    exact fun h => hji ((Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)) h.symm)
  · simp

theorem coefficients_linearPolynomial_of_ne (a : σ → V) (α : σ →₀ ℕ)
    (hα : ∀ i, Finsupp.single i 1 ≠ α) : coefficients (linearPolynomial (R := R) a) α = 0 := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm (hα i))]

@[simp] theorem coefficients_linearPolynomial_zero (a : σ → V) :
    coefficients (linearPolynomial (R := R) a) 0 = 0 := by
  apply coefficients_linearPolynomial_of_ne
  intro i h
  have hi := congrArg (fun α : σ →₀ ℕ => α i) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply, Nat.one_ne_zero] at hi

theorem eval₂_linearPolynomial {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V] (a : σ → V) (t : σ → S) :
    eval₂ t (linearPolynomial (R := R) a) = ∑ i, t i • a i := by
  simp [linearPolynomial_apply, eval₂_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R S V : Type*} [Finite σ] [CommRing R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eq_zero_of_eval₂_eq_zero_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i), eval₂ (fun i => x i (j i)) p = 0) :
    p = 0 := by
  classical
  let e := Module.Free.chooseBasis S V
  have hcoord (k : Module.Free.ChooseBasisIndex S V) :
      coordinate (e.coord k).toAddMonoidHom p = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _
      (fun i => Finset.univ.image (x i))
    · intro i
      rw [Finset.card_image_of_injective _ (hinj i), Finset.card_univ,
        Fintype.card_fin]
      exact lt_of_le_of_lt
        ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
          ((degreeLE_one_iff_basis_totalDegree e d p).mp hp k)) (hlen i)
    · intro y hy
      have hy' : ∀ i, ∃ j, x i j = y i := by
        intro i
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hy i
      choose j hj using hy'
      have hx : (fun i => x i (j i)) = y := funext hj
      rw [← hx, ← coordinate_eval₂, heval, map_zero]
  apply coefficients.injective
  ext α
  simp only [map_zero, Finsupp.zero_apply]
  apply e.repr.injective
  ext k
  have hk := congrArg (fun polynomial : MvPolynomial σ S => polynomial.coeff α) (hcoord k)
  simpa only [coeff_coordinate, MvPolynomial.coeff_zero, map_zero,
    Finsupp.zero_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply] using hk

theorem eq_of_eval₂_eq_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p q : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i),
      eval₂ (fun i => x i (j i)) p = eval₂ (fun i => x i (j i)) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_eq_zero_on_grid length x hinj
  · intro α hα
    simp only [map_sub, Finsupp.sub_apply, hp α hα, hq α hα, sub_self]
  · exact hlen
  · intro j
    rw [map_sub, heval j, sub_self]

end Erdos3.VectorPolynomial

end

section

open scoped Matrix

namespace Erdos3

noncomputable def realMatrixPolynomialMap {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) :
    VectorPolynomial σ ℚ (κ → ℝ) →ₗ[ℚ] VectorPolynomial σ ℚ (ι → ℝ) :=
  VectorPolynomial.map ((Matrix.mulVecLin (fun i j => (A i j : ℝ))).restrictScalars ℚ)

@[simp] theorem coefficients_realMatrixPolynomialMap {ι κ σ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (v : VectorPolynomial σ ℚ (κ → ℝ)) (α : σ →₀ ℕ) :
    VectorPolynomial.coefficients (realMatrixPolynomialMap A v) α =
      (fun i j => (A i j : ℝ)) *ᵥ VectorPolynomial.coefficients v α := by
  rw [realMatrixPolynomialMap, VectorPolynomial.coefficients_map]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix
open VectorPolynomial

variable {η κ σ : Type*} [Fintype κ] {ρ : η → Type*}

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial

open scoped Matrix
open VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simp] theorem lie_monomial (α β : σ →₀ ℕ) (a b : L) :
    ⁅monomial (R := R) α a, monomial (R := R) β b⁆ = monomial (R := R) (α + β) ⁅a, b⁆ := by
  simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
    MvPolynomial.monomial_mul, one_mul]

noncomputable def evalLie (x : σ → R) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval x
  map_lie' {p q} := by
    change eval x ⁅p, q⁆ = ⁅eval x p, eval x q⁆
    induction p using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (zero_lie (M := VectorPolynomial σ R L) q)).trans (by rw [map_zero, zero_lie])
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero =>
        exact (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (a ⊗ₜ[R] v))).trans (by rw [map_zero, lie_zero])
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem evalLie_apply (x : σ → R) (p : VectorPolynomial σ R L) :
    evalLie x p = eval x p := rfl

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem eval_lieBCH (x : σ → ℚ) (s : ℕ) (p q : VectorPolynomial σ ℚ L) :
    eval x (lieBCH s p q) = lieBCH s (eval x p) (eval x q) :=
  map_lieBCH (evalLie x) s p q

theorem lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
  have hpoly : LieModule.lowerCentralSeries (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L)
    (VectorPolynomial σ ℚ L) s : Set (VectorPolynomial σ ℚ L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s, hpoly]
  rfl

end Rational
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :
    LieIdeal R (VectorPolynomial σ R L) :=
  { coefficientSupport Jᶜ with
    lie_mem := by
      classical
      intro p q hq
      change ∀ a, a ∉ Jᶜ → coefficients q a = 0 at hq
      have hq' : ∀ a ∈ J, coefficients q a = 0 := by
        simpa only [Set.mem_compl_iff, not_not] using hq
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum]
      apply (coefficientSupport Jᶜ).sum_mem
      intro a _
      apply (coefficientSupport Jᶜ).sum_mem
      intro b hb
      rw [lie_monomial]
      apply monomial_mem_coefficientSupport
      intro hab
      have hle : b ≤ a + b := by
        intro i
        simp only [Finsupp.add_apply]
        omega
      exact (Finsupp.mem_support_iff.mp hb) (hq' b (hJ hle hab)) }

@[simp] theorem mem_outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)
    (p : VectorPolynomial σ R L) :
    p ∈ outsideDownsetIdeal (R := R) (L := L) J hJ ↔ ∀ a ∈ J, coefficients p a = 0 := by
  change (∀ a, a ∉ Jᶜ → coefficients p a = 0) ↔ _
  simp only [Set.mem_compl_iff, not_not]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S L : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieAlgebra S L] [IsScalarTower R S L]

noncomputable def eval₂Lie (x : σ → S) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval₂ x
  map_lie' {p q} := by
    change eval₂ x ⁅p, q⁆ = ⁅eval₂ x p, eval₂ x q⁆
    induction p using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (zero_lie (M := VectorPolynomial σ R L) q)).trans (by rw [map_zero, zero_lie])
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero =>
        exact (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (a ⊗ₜ[R] v))).trans (by rw [map_zero, lie_zero])
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval₂_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem eval₂Lie_apply (x : σ → S) (p : VectorPolynomial σ R L) :
    eval₂Lie (R := R) (L := L) x p = eval₂ x p := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

section Values

variable {σ K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem eq_zero_of_eval_zero (p : VectorPolynomial σ K V) (hp : ∀ x : σ → K, eval x p = 0) : p = 0 := by
  let b := Module.Free.chooseBasis K V
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hc : coordinate (b.coord i).toAddMonoidHom p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, ← coordinate_eval₂]
    have he : eval₂ x p = 0 := by
      simpa using (eval₂_algebraMap (S := K) x p).trans (hp x)
    rw [he, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

theorem eval_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ K V) :
    (∀ x : σ → K, eval x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map U.mkQ p = 0 := by
      apply eq_zero_of_eval_zero
      intro x
      rw [eval_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ K (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Values

section Lie

variable {σ K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

noncomputable def coefficientSubmodule (U : Submodule K L) : Submodule K (VectorPolynomial σ K L) where
  carrier := {p | ∀ α, coefficients p α ∈ U}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using U.add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem c (hp α)

theorem monomial_mem_coefficientSubmodule (U : Submodule K L) (α : σ →₀ ℕ) {v : L} (hv : v ∈ U) :
    monomial (R := K) α v ∈ coefficientSubmodule U := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hv
  · simp [h]

noncomputable def coefficientLieSubalgebra (U : LieSubalgebra K L) :
    LieSubalgebra K (VectorPolynomial σ K L) :=
  { coefficientSubmodule U.toSubmodule with
    lie_mem' := by
      intro p q hp hq
      classical
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients p).support (coefficients q).support
        (fun α => monomial (R := K) α (coefficients p α))
        (fun β => monomial (R := K) β (coefficients q β))]
      apply Submodule.sum_mem
      intro α _
      apply Submodule.sum_mem
      intro β _
      rw [lie_monomial]
      exact monomial_mem_coefficientSubmodule U.toSubmodule _ (U.lie_mem (hp α) (hq β)) }

end Lie

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficient_zero_of_squarefreeKernel (p : VectorPolynomial ι ℚ L)
    (hp : p ∈ LinearMap.ker squarefreeCoefficients) (a : ι →₀ ℕ) (ha : SquarefreeExponent a) :
    coefficients p a = 0 :=
  congrFun (LinearMap.mem_ker.mp hp) ⟨a, ha⟩

theorem squarefreeKernel_lie_mem (p q : VectorPolynomial ι ℚ L)
    (hq : q ∈ LinearMap.ker squarefreeCoefficients) :
    ⁅p, q⁆ ∈ LinearMap.ker squarefreeCoefficients := by
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
  by_cases hb : SquarefreeExponent b
  · rw [coefficient_zero_of_squarefreeKernel q hq b hb, lie_zero]
    simpa only [monomial, TensorProduct.tmul_zero] using
      (LinearMap.ker (squarefreeCoefficients (ι := ι) (L := L))).zero_mem
  · exact monomial_mem_squarefreeKernel (a + b) (not_squarefreeExponent_add_right a b hb) _

noncomputable def squarefreePolynomialIdeal : LieIdeal ℚ (VectorPolynomial ι ℚ L) :=
  { LinearMap.ker squarefreeCoefficients with
    lie_mem := fun {p q} hq => squarefreeKernel_lie_mem p q hq }

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDilation (w : σ → ℕ) (r : R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => r ^ Finsupp.weight w α • coefficients p α) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact hα (by rw [hz, smul_zero])))
  map_add' p q := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_add, Finsupp.add_apply, smul_add]
  map_smul' c p := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_smul, Finsupp.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp] theorem coefficients_weightedDilation (w : σ → ℕ) (r : R)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDilation w r p) α = r ^ Finsupp.weight w α • coefficients p α := by
  simp only [weightedDilation, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
    Finsupp.onFinset_apply]

theorem weightedDilation_monomial (w : σ → ℕ) (r : R) (α : σ →₀ ℕ) (v : V) :
    weightedDilation w r (monomial α v) = r ^ Finsupp.weight w α • monomial α v := by
  classical
  apply coefficients.injective
  ext β
  by_cases h : α = β <;> simp [h]

@[simp] theorem weightedDilation_one (w : σ → ℕ) (p : VectorPolynomial σ R V) :
    weightedDilation w 1 p = p := by
  apply coefficients.injective
  ext α
  simp

theorem weighted_monomial_dilation (w : σ → ℕ) (r : R) (x : σ → R) (α : σ →₀ ℕ) :
    α.prod (fun i n => (r ^ w i * x i) ^ n) =
      r ^ Finsupp.weight w α * α.prod (fun i n => x i ^ n) := by
  classical
  simp only [Finsupp.prod, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

theorem eval_weightedDilation (w : σ → ℕ) (r : R) (x : σ → R)
    (p : VectorPolynomial σ R V) :
    eval x (weightedDilation w r p) = eval (fun i => r ^ w i * x i) p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedDilation_monomial, map_smul, eval_monomial,
    weighted_monomial_dilation, smul_smul]

section Lie

variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem weightedDilation_lie (w : σ → ℕ) (r : R) (p q : VectorPolynomial σ R L) :
    weightedDilation w r ⁅p, q⁆ = ⁅weightedDilation w r p, weightedDilation w r q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, map_sum, sum_lie_sum, weightedDilation_monomial,
    lie_monomial, map_add, pow_add]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [smul_lie (r ^ Finsupp.weight w α) (monomial (R := R) α (coefficients p α))
      (r ^ Finsupp.weight w β • monomial (R := R) β (coefficients q β)),
    lie_smul (r ^ Finsupp.weight w β) (monomial (R := R) α (coefficients p α))
      (monomial (R := R) β (coefficients q β)),
    lie_monomial, smul_smul]

end Lie
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def translate (h : σ → R) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (polynomialTranslate h).toLinearMap.rTensor V

@[simp] theorem translate_tmul (h : σ → R) (p : MvPolynomial σ R) (v : V) :
    translate h (p ⊗ₜ[R] v) = polynomialTranslate h p ⊗ₜ[R] v := rfl

theorem coefficients_translate_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v)) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, translate_tmul, coefficients_tmul]

theorem coefficients_translate_sub_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v) - monomial α v) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1) -
        MvPolynomial.monomial α 1).coeff β • v := by
  rw [monomial, translate_tmul, ← TensorProduct.sub_tmul, coefficients_tmul]

theorem eval_translate (h x : σ → R) (p : VectorPolynomial σ R V) :
    eval x (translate h p) = eval (fun i => x i + h i) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [translate_tmul, eval_tmul]
    congr 1
    rw [polynomialTranslate, MvPolynomial.comp_aeval_apply]
    simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coefficients_translate (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_translate_monomial]

theorem coefficients_translate_sub (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1) -
        MvPolynomial.monomial β 1).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, ← Finset.sum_sub_distrib,
    Finsupp.finsetSum_apply, coefficients_translate_sub_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

theorem eval₂_map (f : V →ₗ[S] W) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (map (f.restrictScalars R) p) = f (eval₂ x p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    change eval₂ x (q ⊗ₜ[R] f v) = f (eval₂ x (q ⊗ₜ[R] v))
    rw [eval₂_tmul, eval₂_tmul, map_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

section Field

variable {K : Type*} [Field K] [Infinite K] [Algebra R K]
  [Module K V] [IsScalarTower R K V]

theorem eq_zero_of_eval₂_zero (p : VectorPolynomial σ R V) (hp : ∀ x : σ → K, eval₂ x p = 0) :
    p = 0 := by
  let b := Module.Free.chooseBasis K V
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hc : coordinate (b.coord i).toAddMonoidHom p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, ← coordinate_eval₂, hp, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

theorem eval₂_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ R V) :
    (∀ x : σ → K, eval₂ x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map (U.mkQ.restrictScalars R) p = 0 := by
      apply eq_zero_of_eval₂_zero (K := K)
      intro x
      rw [eval₂_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ R (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval₂_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Field

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreePolynomialQuotient
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev SquarefreePolynomial (ι L : Type*) [LieRing L] [LieAlgebra ℚ L] :=
  VectorPolynomial ι ℚ L ⧸ (squarefreePolynomialIdeal (ι := ι) (L := L))

noncomputable def squarefreeMk : VectorPolynomial ι ℚ L →ₗ⁅ℚ⁆ SquarefreePolynomial ι L :=
  lieQuotientMap squarefreePolynomialIdeal

theorem squarefreeMk_monomial_zero (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    squarefreeMk (monomial a v) = (0 : SquarefreePolynomial ι L) :=
  (lieQuotientMap_eq_zero _ _).mpr (monomial_mem_squarefreeKernel a ha v)

noncomputable def squarefreeMonomial (a : SquarefreeIndex ι) : L →ₗ[ℚ] SquarefreePolynomial ι L where
  toFun v := squarefreeMk (monomial a.val v)
  map_add' v w := by simp only [monomial, TensorProduct.tmul_add, map_add]
  map_smul' r v := by simp only [monomial, TensorProduct.tmul_smul, map_smul, RingHom.id_apply]

theorem squarefreeMonomial_apply (a : SquarefreeIndex ι) (v : L) :
    squarefreeMonomial a v = squarefreeMk (monomial a.val v) := rfl

noncomputable def squarefreePolynomialEquiv [Fintype ι] :
    SquarefreePolynomial ι L ≃ₗ[ℚ] (SquarefreeIndex ι → L) :=
  LinearMap.quotKerEquivOfSurjective (squarefreeCoefficients (ι := ι) (L := L))
    (squarefreeCoefficients_surjective (ι := ι) (L := L))

@[simp] theorem squarefreePolynomialEquiv_mk [Fintype ι] (p : VectorPolynomial ι ℚ L) :
    squarefreePolynomialEquiv (squarefreeMk p) = squarefreeCoefficients p := rfl

theorem squarefreePolynomialEquiv_monomial_self [Fintype ι] (a : SquarefreeIndex ι) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) a = v :=
  squarefreeCoefficients_monomial_self a v

theorem squarefreePolynomialEquiv_monomial_ne [Fintype ι]
    (a b : SquarefreeIndex ι) (hab : a ≠ b) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) b = 0 :=
  squarefreeCoefficients_monomial_ne a b hab v

theorem sum_squarefreeMonomial [Fintype ι] (x : SquarefreePolynomial ι L) :
    (∑ a : SquarefreeIndex ι, squarefreeMonomial a (squarefreePolynomialEquiv x a)) = x := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreePolynomialEquiv_monomial_self b _
  · intro a _ h
    exact squarefreePolynomialEquiv_monomial_ne a b h _
  · simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def SquarefreeIndex.disjointAdd {ι : Type*} (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) : SquarefreeIndex ι :=
  ⟨a.val + b.val, (squarefreeExponent_add_iff a.val b.val a.property b.property).mpr h⟩

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_disjoint (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      squarefreeMonomial (a.disjointAdd b h) ⁅v, w⁆ := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  rfl

theorem squarefreeMonomial_lie_overlap (a b : SquarefreeIndex ι)
    (h : ¬Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ = 0 := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  exact squarefreeMk_monomial_zero _
    (fun hs => h ((squarefreeExponent_add_iff a.val b.val a.property b.property).mp hs)) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_coefficient (a b c : SquarefreeIndex ι) (x y : L) :
    squarefreePolynomialEquiv (⁅squarefreeMonomial a x, squarefreeMonomial b y⁆) c =
      if a.val + b.val = c.val then ⁅x, y⁆ else 0 := by
  by_cases hs : a.val + b.val = c.val
  · have hd : Disjoint a.val.support b.val.support :=
      (squarefreeExponent_add_iff a.val b.val a.property b.property).mp (hs.symm ▸ c.property)
    rw [if_pos hs, squarefreeMonomial_lie_disjoint a b hd]
    have he : a.disjointAdd b hd = c := Subtype.ext hs
    rw [he, squarefreePolynomialEquiv_monomial_self]
  · rw [if_neg hs]
    by_cases hd : Disjoint a.val.support b.val.support
    · rw [squarefreeMonomial_lie_disjoint a b hd]
      exact squarefreePolynomialEquiv_monomial_ne _ c
        (fun h => hs (congrArg Subtype.val h)) _
    · rw [squarefreeMonomial_lie_overlap a b hd, map_zero, Pi.zero_apply]

theorem squarefree_lie_coefficient (x y : SquarefreePolynomial ι L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅x, y⁆ c =
      ∑ a : SquarefreeIndex ι, ∑ b : SquarefreeIndex ι,
        if a.val + b.val = c.val then
          ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ else 0 := by
  conv_lhs => rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  simp only [map_sum, Finset.sum_apply, squarefreeMonomial_lie_coefficient]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (σ L : Type*) [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

structure MultidegreeLieFiltration (s : ℕ) (bound : σ → ℕ) where
  ordinary : NilpotentLieFiltration L s
  layer : (σ → ℕ) → Submodule ℚ L
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  lie_mem : ∀ {a b : σ → ℕ} {x y : L}, x ∈ layer a → y ∈ layer b → ⁅x, y⁆ ∈ layer (a + b)
  terminal : ∀ a, ¬a ≤ bound → layer a = ⊥
  degree_eq : ∀ n, ordinary.layer n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), layer a

namespace MultidegreeLieFiltration

variable {σ L} {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def layerIdeal (a : σ → ℕ) : LieIdeal ℚ L :=
  { F.layer a with
    lie_mem := by
      intro x y hy
      change ⁅x, y⁆ ∈ F.layer a
      have hx : x ∈ F.layer 0 := by simp only [F.zero_eq_top, Submodule.mem_top]
      simpa only [zero_add] using F.lie_mem hx hy }

@[simp] theorem mem_layerIdeal (a : σ → ℕ) (x : L) :
    x ∈ F.layerIdeal a ↔ x ∈ F.layer a := Iff.rfl

theorem layer_le_ordinary (a : σ → ℕ) : F.layer a ≤ F.ordinary.layer (∑ i, a i) := by
  rw [F.degree_eq]
  exact le_iSup_of_le a (le_iSup_of_le le_rfl le_rfl)

abbrev Group := F.ordinary.Group

def subgroup (a : σ → ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal a).toLieSubalgebra

@[simp] theorem mem_subgroup (a : σ → ℕ) (x : F.Group) :
    x ∈ F.subgroup a ↔ x.coord ∈ F.layer a := Iff.rfl

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) : Submodule ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ ∑ i, a i}, P a.val

theorem layer_le_multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (a : σ → ℕ) (n : ℕ)
    (ha : n ≤ ∑ i, a i) : P a ≤ multidegreeTotalLayer P n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ ∑ i, b i} => P b.val) ⟨a, ha⟩

theorem multidegreeTotalLayer_antitone (P : (σ → ℕ) → Submodule ℚ L) :
    Antitone (multidegreeTotalLayer P) := by
  intro i j hij
  apply iSup_le
  intro a
  exact layer_le_multidegreeTotalLayer P a.val i (hij.trans a.property)

theorem multidegreeTotalLayer_eq (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) :
    multidegreeTotalLayer P n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), P a := by
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact layer_le_multidegreeTotalLayer P a n ha

theorem multidegreeTotalLayer_lie_mem (P : (σ → ℕ) → Submodule ℚ L)
    (hP : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    {i j : ℕ} {x y : L} (hx : x ∈ multidegreeTotalLayer P i) (hy : y ∈ multidegreeTotalLayer P j) :
    ⁅x, y⁆ ∈ multidegreeTotalLayer P (i + j) := by
  refine Submodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
  · intro a u hu
    refine Submodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply layer_le_multidegreeTotalLayer P (a.val + b.val) (i + j) _ (hP hu hv)
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add a.property b.property
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro u v hu hv
      rw [lie_add]
      exact Submodule.add_mem _ hu hv
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

theorem multidegreeTotalLayer_terminal (P : (σ → ℕ) → Submodule ℚ L) (bound : σ → ℕ)
    (hP : ∀ a, ¬a ≤ bound → P a = ⊥) (s : ℕ) (hs : (∑ i, bound i) ≤ s) :
    multidegreeTotalLayer P (s + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have ha : ¬a.val ≤ bound := by
    intro h
    have hsum : (∑ i, a.val i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => h i)
    have hn := a.property
    omega
  rw [hP a.val ha]

noncomputable def MultidegreeLieFiltration.ofLayers
    (P : (σ → ℕ) → Submodule ℚ L) (hmono : Antitone P) (hzero : P 0 = ⊤)
    (hlie : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    (hpositive : multidegreeTotalLayer P 1 = ⊤)
    (bound : σ → ℕ) (hterminal : ∀ a, ¬a ≤ bound → P a = ⊥)
    (s : ℕ) (hs : (∑ i, bound i) ≤ s) : MultidegreeLieFiltration σ L s bound where
  ordinary :=
    { layer := multidegreeTotalLayer P
      antitone := multidegreeTotalLayer_antitone P
      one_eq_top := hpositive
      lie_mem := multidegreeTotalLayer_lie_mem P hlie
      terminal := multidegreeTotalLayer_terminal P bound hterminal s hs }
  layer := P
  antitone := hmono
  zero_eq_top := hzero
  lie_mem := hlie
  terminal := hterminal
  degree_eq := multidegreeTotalLayer_eq P

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def strictUpperLayer (a : σ → ℕ) : LieIdeal ℚ L :=
  ⨆ i : σ, F.layerIdeal (a + Pi.single i 1)

theorem successor_le_strictUpperLayer (a : σ → ℕ) (i : σ) :
    F.layerIdeal (a + Pi.single i 1) ≤ F.strictUpperLayer a :=
  le_iSup (fun j => F.layerIdeal (a + Pi.single j 1)) i

theorem strictUpperLayer_le_layer (a : σ → ℕ) :
    F.strictUpperLayer a ≤ F.layerIdeal a := by
  apply iSup_le
  intro i
  exact F.antitone (fun j => Nat.le_add_right (a j) _)

theorem strictUpperLayer_antitone : Antitone F.strictUpperLayer := by
  intro a b hab
  apply iSup_le
  intro i
  exact (F.antitone (fun j => Nat.add_le_add_right (hab j) _)).trans
    (F.successor_le_strictUpperLayer a i)

theorem layer_le_strictUpperLayer {a b : σ → ℕ} (hab : a < b) :
    F.layerIdeal b ≤ F.strictUpperLayer a := by
  obtain ⟨i, hi⟩ := not_forall.mp hab.not_ge
  have hstep : a + Pi.single i 1 ≤ b := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    · simpa only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] using hab.le j
  exact (F.antitone hstep).trans (F.successor_le_strictUpperLayer a i)

theorem strictUpperLayer_le_ordinary (a : σ → ℕ) :
    (F.strictUpperLayer a).toSubmodule ≤ F.ordinary.layer ((∑ i, a i) + 1) := by
  rw [strictUpperLayer, LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro i
  change F.layer (a + Pi.single i 1) ≤ _
  have hsum : (∑ j, (a + Pi.single i 1 : σ → ℕ) j) = (∑ j, a j) + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    congr 1
    simp
  rw [← hsum]
  exact F.layer_le_ordinary (a + Pi.single i 1)

theorem strictUpperLayer_top : F.strictUpperLayer bound = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro i
  have hnot : ¬bound + Pi.single i 1 ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer (bound + Pi.single i 1) := hx
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

theorem strictUpper_lie_layer {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.layer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  change x ∈ ⨆ i : σ, F.layerIdeal (a + Pi.single i 1) at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.strictUpperLayer (a + b)) ?_ ?_ ?_
  · intro i u hu
    apply F.successor_le_strictUpperLayer (a + b) i
    change ⁅u, y⁆ ∈ F.layer (a + b + Pi.single i 1)
    simpa only [add_right_comm a (Pi.single i 1) b] using F.lie_mem hu hy
  · simpa only [zero_lie] using (F.strictUpperLayer (a + b)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.strictUpperLayer (a + b)).add_mem hu hv

theorem layer_lie_strictUpper {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.layer a) (hy : y ∈ F.strictUpperLayer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  have h := (F.strictUpperLayer (b + a)).neg_mem (F.strictUpper_lie_layer hy hx)
  change ⁅x, y⁆ ∈ (F.strictUpperLayer (a + b)).toSubmodule
  simpa only [lie_skew, add_comm b a] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def multidegreeWeight {σ : Type*} [Fintype σ] (c a : σ → ℕ) : ℕ := ∑ i, c i * a i

theorem multidegreeWeight_add {σ : Type*} [Fintype σ] (c a b : σ → ℕ) :
    multidegreeWeight c (a + b) = multidegreeWeight c a + multidegreeWeight c b := by
  simp only [multidegreeWeight, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem multidegreeWeight_mono {σ : Type*} [Fintype σ] (c : σ → ℕ) {a b : σ → ℕ}
    (hab : a ≤ b) : multidegreeWeight c a ≤ multidegreeWeight c b :=
  Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (c i) (hab i))

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayer (c : σ → ℕ) (n : ℕ) : LieIdeal ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val

theorem layer_le_weightedLayer (c a : σ → ℕ) (n : ℕ) (ha : n ≤ multidegreeWeight c a) :
    F.layerIdeal a ≤ F.weightedLayer c n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ multidegreeWeight c b} => F.layerIdeal b.val) ⟨a, ha⟩

theorem weightedLayer_antitone (c : σ → ℕ) : Antitone (F.weightedLayer c) := by
  intro m n hmn
  apply iSup_le
  intro a
  exact F.layer_le_weightedLayer c a.val m (hmn.trans a.property)

theorem weightedLayer_zero (c : σ → ℕ) : F.weightedLayer c 0 = ⊤ := by
  apply top_unique
  intro x _
  apply F.layer_le_weightedLayer c 0 0 (Nat.zero_le _)
  change x ∈ F.layer 0
  simp only [F.zero_eq_top, Submodule.mem_top]

theorem weightedLayer_terminal (c : σ → ℕ) :
    F.weightedLayer c (multidegreeWeight c bound + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have hnot : ¬a.val ≤ bound := by
    intro ha
    have h := (multidegreeWeight_mono c ha)
    have h' := a.property
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer a.val := hx
  simpa only [F.terminal a.val hnot, Submodule.mem_bot] using h

theorem weightedLayer_lie_mem (c : σ → ℕ) {i j : ℕ} {x y : L}
    (hx : x ∈ F.weightedLayer c i) (hy : y ∈ F.weightedLayer c j) :
    ⁅x, y⁆ ∈ F.weightedLayer c (i + j) := by
  change x ∈ ⨆ a : {a : σ → ℕ // i ≤ multidegreeWeight c a}, F.layerIdeal a.val at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
  · intro a u hu
    change y ∈ ⨆ b : {b : σ → ℕ // j ≤ multidegreeWeight c b}, F.layerIdeal b.val at hy
    refine LieSubmodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply F.layer_le_weightedLayer c (a.val + b.val) (i + j)
        (by rw [multidegreeWeight_add]; exact Nat.add_le_add a.property b.property)
      exact F.lie_mem hu hv
    · simpa only [lie_zero] using (F.weightedLayer c (i + j)).zero_mem
    · intro v z hv hz
      rw [LieRing.lie_add]
      exact (F.weightedLayer c (i + j)).add_mem hv hz
  · simpa only [zero_lie] using (F.weightedLayer c (i + j)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.weightedLayer c (i + j)).add_mem hu hv

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}

theorem pi_degree_eq (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (n : ℕ) :
    Submodule.pi Set.univ (fun i => (F i).ordinary.layer n) =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ j, a j), Submodule.pi Set.univ (fun i => (F i).layer a) := by
  classical
  apply le_antisymm
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [(F i).degree_eq]
    simp only [Submodule.map_iSup]
    refine iSup_le fun a => iSup_le fun ha => ?_
    apply le_trans (Submodule.map_le_iff_le_comap.mpr
      (Submodule.le_comap_single_pi (fun i => (F i).layer a)))
    exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)
  · refine iSup_le fun a => iSup_le fun ha => ?_
    exact Submodule.pi_mono fun i _ => ((F i).layer_le_ordinary a).trans ((F i).ordinary.antitone ha)

noncomputable def pi (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) :
    MultidegreeLieFiltration σ (∀ i, L i) s bound where
  ordinary := NilpotentLieFiltration.pi (fun i => (F i).ordinary)
  layer a := Submodule.pi Set.univ (fun i => (F i).layer a)
  antitone _ _ h := Submodule.pi_mono (fun i _ => (F i).antitone h)
  zero_eq_top := by simp only [zero_eq_top, Submodule.pi_top]
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal a ha := by
    simp only [show ∀ i, (F i).layer a = ⊥ from fun i => (F i).terminal a ha, Submodule.pi_univ_bot]
  degree_eq := pi_degree_eq F

@[simp] theorem mem_pi_layer (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)
    (a : σ → ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer a ↔ ∀ i, x i ∈ (F i).layer a := by
  simp only [pi, Submodule.mem_pi, Set.mem_univ, forall_true_left]

def piLayerEquiv (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (a : σ → ℕ) :
    (∀ i, (F i).layer a) ≃ₗ[ℚ] (pi F).layer a where
  toFun x := ⟨fun i => x i, (mem_pi_layer F a _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F a _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeAdaptedModule : Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a : SquarefreeIndex ι,
    squarefreePolynomialEquiv x a ∈ F.layer (blockDegree π a.val) ∧
      (a.val = 0 → squarefreePolynomialEquiv x a = 0)}
  zero_mem' := by
    intro a
    simp only [map_zero, Pi.zero_apply]
    exact ⟨(F.layer _).zero_mem, fun _ => True.intro⟩
  add_mem' := by
    intro x y hx hy a
    simp only [map_add, Pi.add_apply]
    exact ⟨(F.layer _).add_mem (hx a).1 (hy a).1,
      fun ha => by rw [(hx a).2 ha, (hy a).2 ha, add_zero]⟩
  smul_mem' := by
    intro r x hx a
    simp only [map_smul, Pi.smul_apply]
    exact ⟨(F.layer _).smul_mem r (hx a).1,
      fun ha => by rw [(hx a).2 ha, smul_zero]⟩

theorem squarefreeMonomial_mem_adapted (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : L) (hv : v ∈ F.layer (blockDegree π a.val)) :
    squarefreeMonomial a v ∈ F.squarefreeAdaptedModule π := by
  intro b
  by_cases hab : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self]
    exact ⟨hv, fun he => False.elim (ha he)⟩
  · rw [squarefreePolynomialEquiv_monomial_ne a b hab v]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

theorem squarefreeMonomial_component_mem (x : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (a : SquarefreeIndex ι) :
    squarefreeMonomial a (squarefreePolynomialEquiv x a) ∈ F.squarefreeAdaptedModule π := by
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  · exact F.squarefreeMonomial_mem_adapted π a ha _ (hx a).1

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLayer (q : ℚ) (a : σ → ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i)

theorem mem_dilationPairLayer (q : ℚ) (a : σ → ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q a ↔ x.1 ∈ F.layer a ∧ x.2 ∈ F.layer a ∧
      x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro a b hab x hx
  by_cases heq : a = b
  · subst b
    exact hx
  have hlt : a < b := lt_iff_le_not_ge.mpr ⟨hab, fun hba => heq (le_antisymm hab hba)⟩
  refine ⟨F.antitone hab hx.1, F.antitone hab hx.2.1, ?_⟩
  change x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a
  have hdiff : x.1 - q ^ (∑ i, a i) • x.2 =
      (x.1 - q ^ (∑ i, b i) • x.2) + (q ^ (∑ i, b i) - q ^ (∑ i, a i)) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.strictUpperLayer a).add_mem (F.strictUpperLayer_antitone hab hx.2.2)
    ((F.strictUpperLayer a).smul_mem _ (F.layer_le_strictUpperLayer hlt hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {a b : σ → ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q a) (hy : y ∈ F.dilationPairLayer q b) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (a + b) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ ∈ F.strictUpperLayer (a + b)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ (∑ i, a i) • x.2, y.1⁆ +
        q ^ (∑ i, a i) • ⁅x.2, y.1 - q ^ (∑ i, b i) • y.2⁆ := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sub_lie, lie_sub,
      smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  have h₁ := F.strictUpper_lie_layer hx.2.2 hy.1
  have h₂ := F.layer_lie_strictUpper hx.2.1 hy.2.2
  rw [scaledPairDifference_apply] at h₁ h₂
  exact (F.strictUpperLayer (a + b)).add_mem h₁ ((F.strictUpperLayer (a + b)).smul_mem _ h₂)

theorem dilationPairLayer_le_ordinary (q : ℚ) (a : σ → ℕ) :
    F.dilationPairLayer q a ≤ F.ordinary.dilationPairLayer q (∑ i, a i) := by
  intro x hx
  exact ⟨F.layer_le_ordinary a hx.1, F.layer_le_ordinary a hx.2.1,
    F.strictUpperLayer_le_ordinary a hx.2.2⟩

theorem dilationPairLayer_le_subalgebra (q : ℚ) (a : σ → ℕ) (ha : 1 ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ (F.ordinary.dilationPairSubalgebra q).toSubmodule :=
  (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairLayer_terminal (q : ℚ) (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.dilationPairLayer q a = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.2.1)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q bound) : x.1 = q ^ (∑ i, bound i) • x.2 := by
  have h : x.1 - q ^ (∑ i, bound i) • x.2 ∈ F.strictUpperLayer bound := hx.2.2
  rw [F.strictUpperLayer_top, LieSubmodule.mem_bot, sub_eq_zero] at h
  exact h

theorem dilationPairLayer_diagonal (q : ℚ) (a : σ → ℕ) {x : L} (hx : x ∈ F.layer a) :
    (q ^ (∑ i, a i) • x, x) ∈ F.dilationPairLayer q a :=
  ⟨(F.layer a).smul_mem _ hx, hx, by simp⟩

theorem dilationPairLayer_of_strictUpper (q : ℚ) (a : σ → ℕ) {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.strictUpperLayer a) :
    (x, y) ∈ F.dilationPairLayer q a :=
  ⟨F.strictUpperLayer_le_layer a hx, F.strictUpperLayer_le_layer a hy,
    (F.strictUpperLayer a).sub_mem hx ((F.strictUpperLayer a).smul_mem _ hy)⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_rational_approximation {θ ε : ℝ} {q : ℕ} (hq : 0 < q)
    (hnear : NearInteger ε ((q : ℝ)*θ)) :
    ∃ m : ℤ, |θ-(m : ℝ)/q| ≤ ε := by
  obtain ⟨m,hm⟩ := hnear
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : θ-(m : ℝ)/q = ((q : ℝ)*θ-m)/q := by field_simp
  refine ⟨m, ?_⟩
  rw [he, abs_div, abs_of_pos hqp]
  exact (div_le_div_of_nonneg_right hm hqp.le).trans
    (div_le_self ((abs_nonneg _).trans hm) hq1)

theorem multiaffine_bias_approximation {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hM : multiaffineBiasBudget n ζ ≤ M)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M,
      multiaffineIntervalPhase a b u w x t‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |a Finset.univ-(m : ℝ)/q| ≤
        multiaffineBiasBudget n ζ / ((M : ℝ)*∏ i, (N i : ℝ)) := by
  have hQ := multiaffineBiasBudget_pos n hζ
  have hNp : ∀ i, 0 < N i := fun i => by exact_mod_cast hQ.trans_le (hN i)
  have hMp : 0 < M := by exact_mod_cast hQ.trans_le hM
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  obtain ⟨hLQ,hQmul⟩ := multiaffineBiasBudget_bounds n hζ hζ1
  have hMlarge : denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ (M : ℝ)*ζ^(2^n) := by
    rw [← hQmul]
    exact mul_le_mul_of_nonneg_right hM hp.le
  obtain ⟨q,hq,hqL,hnear⟩ := product_difference_bias_approximation n N M hMp hp hp1
    (fun i => hLQ.trans (hN i)) hMlarge
    (multiaffine_phase_box_bias N hNp M hMp a b u w hζ.le hbias)
  refine ⟨q,hq,hqL.trans hLQ,nearInteger_rational_approximation hq ?_⟩
  convert hnear using 1
  unfold multiaffineBiasBudget
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_coordinate_pos {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (i : I) :
    0 < shiftedSmoothSampleSum (a i) (S i) := by
  have hp : (∏ j, shiftedSmoothSampleSum (a j) (S j)) ≠ 0 := by
    rw [← shiftedSmoothProductMass_eq_prod a S hS]
    exact hZ.ne'
  have hn := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have h0 : 0 ≤ shiftedSmoothSampleSum (a i) (S i) :=
    tsum_nonneg (fun k => (smoothProbabilityProfile_range _).1)
  exact lt_of_le_of_ne h0 hn.symm

theorem shiftedSmoothProductPMF_eq_independent {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    shiftedSmoothProductPMF a S hS hZ = independentProductPMF
      (fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
        (shiftedSmoothProductMass_coordinate_pos a S hS hZ i)) := by
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedSmoothProductPMF_toReal, independentProductPMF_toReal]
  simp_rw [shiftedSmoothCoefficientPMF_apply]
  rw [Finset.prod_div_distrib, ← shiftedSmoothProductMass_eq_prod a S hS]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

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

theorem shiftedSmoothProductMass_restrict_pos {A J : Type*} [Fintype A] [Fintype J]
    (e : A → J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    0 < shiftedSmoothProductMass (fun i => a (e i)) (fun i => S (e i)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun i => hS (e i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (e i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def smoothInputSplit {I J D X : Type*} (e : (I ⊕ J) ≃ D) (z : D → X) :
    (I → X) × (J → X) := (fun i => z (e (.inl i)), fun j => z (e (.inr j)))

def smoothInputJoin {I J D X : Type*} (e : (I ⊕ J) ≃ D) (p : (I → X) × (J → X)) : D → X :=
  fun d => Sum.elim p.1 p.2 (e.symm d)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_selected_marginal
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z i => z (e i)) =
      shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) := by
  simp only [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_marginal _ e e.injective

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*}

noncomputable def polynomialExponentialPath (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    Polynomial (MvPolynomial σ ℚ) :=
  polynomialPrimitive (polynomialTranslationPath x P)

@[simp] theorem polynomialExponentialPath_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).derivative = polynomialTranslationPath x P :=
  polynomialPrimitive_derivative _

@[simp] theorem polynomialExponentialPath_eval_zero (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : (polynomialExponentialPath x P).eval 0 = 0 :=
  polynomialPrimitive_eval_zero _

theorem polynomialExponentialPath_unique (x : σ → ℚ) (P : MvPolynomial σ ℚ)
    {F : Polynomial (MvPolynomial σ ℚ)}
    (hderiv : F.derivative = polynomialTranslationPath x P) (hzero : F.eval 0 = 0) :
    polynomialExponentialPath x P = F :=
  polynomialPrimitive_unique hderiv hzero

theorem polynomialExponentialPath_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialPath x (scalarDirectionalDerivative x V) =
      Polynomial.C V - polynomialTranslationPath x V := by
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_sub, Polynomial.derivative_C,
      polynomialTranslationPath_derivative, zero_sub, neg_neg]
  · simp

theorem polynomialExponentialPath_eval_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) (t : ℚ) :
    (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t) =
      V - polynomialTranslate (fun i => -(t * x i)) V := by
  rw [polynomialExponentialPath_potential, Polynomial.eval_sub, Polynomial.eval_C,
    polynomialTranslationPath_eval]

noncomputable def polynomialExponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (polynomialExponentialPath x P).eval 1

theorem polynomialExponentialCoordinate_formula (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x P =
      ∑ n ∈ (polynomialTranslationPath x P).support,
        (((n + 1 : ℕ) : ℚ)⁻¹ • (polynomialTranslationPath x P).coeff n) := by
  classical
  simp only [polynomialExponentialCoordinate, polynomialExponentialPath,
    polynomialPrimitive, Polynomial.sum_def, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]

theorem polynomialExponentialCoordinate_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x (scalarDirectionalDerivative x V) =
      V - polynomialTranslate (-x) V := by
  have h := polynomialExponentialPath_eval_potential x V 1
  have hx : (fun i => -(1 * x i)) = -x := by funext i; simp
  rw [map_one, hx] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

@[simp] theorem polynomialTranslationPath_zero (P : MvPolynomial σ ℚ) :
    polynomialTranslationPath (0 : σ → ℚ) P = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem polynomialExponentialPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialPath x (C c) = Polynomial.C (C c) * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialPath_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialPath (0 : σ → ℚ) P = Polynomial.C P * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialCoordinate_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialCoordinate x (C c) = C c := by
  simp [polynomialExponentialCoordinate]

@[simp] theorem polynomialExponentialCoordinate_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate (0 : σ → ℚ) P = P := by
  simp [polynomialExponentialCoordinate]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialTranslationPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x P).map (polynomialTranslate x).toRingHom =
      (polynomialTranslationPath (-x) P).comp (1 - Polynomial.X) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.mul_comp]
    rw [hp]
    congr 1
    simp only [polynomialTranslationPath_X, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialTranslate_X, polynomialTranslate_C, Polynomial.sub_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Pi.neg_apply,
      map_neg, map_add, Polynomial.neg_comp]
    ring

theorem polynomialExponentialPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).map (polynomialTranslate x).toRingHom =
      Polynomial.C (polynomialExponentialCoordinate (-x) P) -
        (polynomialExponentialPath (-x) P).comp (1 - Polynomial.X) := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialTranslationPath_translate_reflection, Polynomial.derivative_sub,
      Polynomial.derivative_C, Polynomial.derivative_comp_one_sub_X,
      polynomialExponentialPath_derivative, zero_sub, neg_neg]
  · have hz := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
        (polynomialTranslate x).toRingHom 0
    simp only [map_zero, polynomialExponentialPath_eval_zero] at hz
    rw [hz]
    simp [polynomialExponentialCoordinate, Polynomial.eval_comp]

theorem polynomialTranslate_exponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      polynomialExponentialCoordinate (-x) P := by
  have h := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.eval 1)
    (polynomialExponentialPath_translate_reflection x P)
  have he := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
    (polynomialTranslate x).toRingHom 1
  simp only [map_one] at he
  rw [he] at h
  simpa [polynomialExponentialCoordinate, Polynomial.eval_comp] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialTranslate_comp (h k : σ → ℚ) (V : MvPolynomial σ ℚ) :
    polynomialTranslate h (polynomialTranslate k V) = polynomialTranslate (h + k) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C,
      Pi.add_apply]
    rw [add_assoc]

@[ext] structure PolynomialTranslationGroup (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationGroup

noncomputable instance : Mul (PolynomialTranslationGroup σ) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance : One (PolynomialTranslationGroup σ) where
  one := ⟨0, 0⟩

noncomputable instance : Inv (PolynomialTranslationGroup σ) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroup σ) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroup σ).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroup σ).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroup σ) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroup σ) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

noncomputable instance : Group (PolynomialTranslationGroup σ) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroup.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroup.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroup.ext
      · simp
      · simp [polynomialTranslate_comp])

noncomputable def potentialElement (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    PolynomialTranslationGroup σ := ⟨x, V - polynomialTranslate (-x) V⟩

@[simp] theorem potentialElement_base (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    (potentialElement V x).base = x := rfl

@[simp] theorem potentialElement_polynomial (V : MvPolynomial σ ℚ) (x : σ → ℚ) :
    (potentialElement V x).polynomial = V - polynomialTranslate (-x) V := rfl

@[simp] theorem potentialElement_zero (V : MvPolynomial σ ℚ) :
    potentialElement V 0 = 1 := by
  apply PolynomialTranslationGroup.ext <;> simp

noncomputable def exponentialElement (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    PolynomialTranslationGroup σ := ⟨x, polynomialExponentialCoordinate x P⟩

noncomputable def potentialFlow [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ)
    (t : ℚ) : PolynomialTranslationGroup σ :=
  ⟨t • x, (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t)⟩

theorem potentialFlow_eq [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) (t : ℚ) :
    potentialFlow x V t = potentialElement V (t • x) := by
  apply PolynomialTranslationGroup.ext
  · rfl
  · change (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t) = _
    rw [polynomialExponentialPath_eval_potential, potentialElement_polynomial]
    congr 2

@[simp] theorem potentialFlow_zero [Fintype σ] (x : σ → ℚ) (V : MvPolynomial σ ℚ) :
    potentialFlow x V 0 = 1 := by
  rw [potentialFlow_eq, zero_smul, potentialElement_zero]

end PolynomialTranslationGroup
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

structure PolynomialPotentialRelation (σ : Type*) [Fintype σ] where
  space : Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ)
  bracket_mem : ∀ x P z Q, (x, P) ∈ space → (z, Q) ∈ space →
    (0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P) ∈ space
  pure_constant_zero : ∀ Q, (0, Q) ∈ space → Q.coeff 0 = 0

@[simp] theorem scalarDirectionalDerivative_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

@[simp] theorem scalarDirectionalDerivative_single [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

namespace PolynomialPotentialRelation

variable [DecidableEq σ] (A : PolynomialPotentialRelation σ)
  (P : σ → MvPolynomial σ ℚ)
  (hlift : ∀ i, (Pi.single i 1, P i) ∈ A.space)

include hlift

theorem pure_eq_zero (Q : MvPolynomial σ ℚ) (hQ : (0, Q) ∈ A.space) : Q = 0 := by
  apply polynomial_eq_zero_of_pderiv_closed {Q | (0, Q) ∈ A.space} ?_ ?_ Q hQ
  · intro R hR i
    change (0, pderiv i R) ∈ A.space
    have h := A.bracket_mem (Pi.single i 1) (P i) 0 R (hlift i) hR
    simpa only [scalarDirectionalDerivative_single, scalarDirectionalDerivative_zero,
      sub_zero] using h
  · exact A.pure_constant_zero

theorem compatible_partials (i j : σ) : pderiv i (P j) = pderiv j (P i) := by
  have h := A.bracket_mem (Pi.single i 1) (P i) (Pi.single j 1) (P j) (hlift i) (hlift j)
  simp only [scalarDirectionalDerivative_single] at h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ h)

theorem linear_combination_mem (x : σ → ℚ) : (x, ∑ i, x i • P i) ∈ A.space := by
  have h : (∑ i, x i • (Pi.single i 1, P i)) ∈ A.space :=
    A.space.sum_mem (fun i _ => A.space.smul_mem (x i) (hlift i))
  have heq : (∑ i, x i • (Pi.single i 1, P i)) = (x, ∑ i, x i • P i) := by
    apply Prod.ext
    · ext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rwa [heq] at h

theorem polynomial_eq_linear_combination (x : σ → ℚ) (Q : MvPolynomial σ ℚ)
    (hQ : (x, Q) ∈ A.space) : Q = ∑ i, x i • P i := by
  have h := A.space.sub_mem hQ (A.linear_combination_mem P hlift x)
  have hpure : (0, Q - ∑ i, x i • P i) ∈ A.space := by simpa using h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ hpure)

theorem weighted_potential_derivative (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (x : σ → ℚ) (Q : MvPolynomial σ ℚ) (hQ : (x, Q) ∈ A.space) :
    scalarDirectionalDerivative x (weightedPolynomialPotential w d P) = Q := by
  rw [scalarDirectionalDerivative_apply]
  simp only [weightedPolynomialPotential_pderiv w hd P hweight hhom
    (A.compatible_partials P hlift)]
  exact (A.polynomial_eq_linear_combination P hlift x Q hQ).symm

end PolynomialPotentialRelation
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationGroup

open _root_.MvPolynomial
variable {σ : Type*}

noncomputable def actionHom (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ →ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroup σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroup σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroup σ) (r : ℚ) :
    actionHom g (C r) = C r := by simp [actionHom]

theorem actionHom_rename (g : PolynomialTranslationGroup σ) (P : MvPolynomial σ ℚ) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) ℚ) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroup σ) = AlgHom.id ℚ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroup σ)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroup σ) :
    MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroup σ →*
    (MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ] MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
      MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) ℚ (add_left_cancel hh)
  apply PolynomialTranslationGroup.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℚ ≃ₐ[ℚ]
    MvPolynomial (σ ⊕ Unit) ℚ => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp, neg_add_cancel, polynomialTranslate_zero] using hp'

end Erdos3.PolynomialTranslationGroup

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

@[simp] theorem scalarDirectionalDerivative_neg (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (-x) P = -scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.neg_apply, neg_smul,
    Finset.sum_neg_distrib]

theorem polynomialTranslationPath_neg_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (-x) P).derivative =
      polynomialTranslationPath (-x) (scalarDirectionalDerivative x P) := by
  rw [polynomialTranslationPath_derivative, scalarDirectionalDerivative_neg, map_neg, neg_neg]

theorem polynomialTranslationPath_neg_coeff (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) (i : ℕ) :
    (polynomialTranslationPath (-x) P).coeff i =
      ((i.factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  induction i generalizing P with
  | zero =>
      simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
        Module.End.one_apply, Polynomial.coeff_zero_eq_eval_zero]
        using polynomialTranslationPath_eval_zero (-x) P
  | succ i ih =>
      have hc := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.coeff i)
        (polynomialTranslationPath_neg_derivative x P)
      rw [Polynomial.coeff_derivative] at hc
      have hmul : ((i + 1 : ℕ) : ℚ) • (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul']
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      have hinv : (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (((i + 1 : ℕ) : ℚ)⁻¹) •
            (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [← hmul, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)), one_smul]
      rw [hinv, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev,
        pow_succ, Module.End.mul_apply]
      congr 1
      exact mul_comm _ _

theorem scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0 := by
  apply weightedDerivation_pow_eq_zero w _ _ hP
  intro i
  rw [scalarDirectionalDerivative_X, weightedSupportDrop_one]
  intro a ha
  have h : Finsupp.weight w a ≤ 0 := weightedSupportLE_C w 0 (x i) ha
  change Finsupp.weight w a < w i
  exact lt_of_le_of_lt h (hw i)

theorem polynomialTranslationPath_neg_support_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    (polynomialTranslationPath (-x) P).support ⊆ Finset.range (n + 1) := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
  have hz : ((scalarDirectionalDerivative x).toLinearMap ^ i) P = 0 := by
    rw [show i = j + (n + 1) by omega, pow_add, Module.End.mul_apply, hP, map_zero]
  exact Polynomial.mem_support_iff.mp hi (by
    rw [polynomialTranslationPath_neg_coeff, hz, smul_zero])

theorem polynomialExponentialCoordinate_neg_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialExponentialCoordinate (-x) P =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  classical
  rw [polynomialExponentialCoordinate_formula]
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (((i + 1 : ℕ) : ℚ)⁻¹) • (polynomialTranslationPath (-x) P).coeff i := by
      apply Finset.sum_subset (polynomialTranslationPath_neg_support_of_nilpotent x hP)
      intro i hi hni
      rw [Polynomial.notMem_support_iff.mp hni, smul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [polynomialTranslationPath_neg_coeff, smul_smul, Nat.factorial_succ,
        Nat.cast_mul, mul_inv_rev]
      congr 1
      exact mul_comm _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def parameterLinearCoordinate {I K : Type*} [Fintype K] (j : I) :
    MvPolynomial (K × I) (MvPolynomial K ℝ) := ∑ k, C (X k) * X (k, j)

noncomputable def parameterPolynomialPullback {I K : Type*} [Fintype K] :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (K × I) (MvPolynomial K ℝ) :=
  aeval parameterLinearCoordinate

theorem parameterPolynomialPullback_degree {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) {d : ℕ} (hP : P.totalDegree ≤ d) :
    (parameterPolynomialPullback (K := K) P).totalDegree ≤ d := by
  have hc (j : I) : (parameterLinearCoordinate (K := K) j).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro k _
    exact (totalDegree_mul _ _).trans (by simp)
  simpa only [parameterPolynomialPullback, Nat.mul_one] using
    aeval_polynomial_totalDegree_le P parameterLinearCoordinate hP hc

theorem parameterPolynomialPullback_eval {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) (v : K → I → ℝ) :
    eval (fun z => C (v z.1 z.2)) (parameterPolynomialPullback P) =
      aeval (fun j => rowPolynomial (fun k => v k j)) P := by
  let E : MvPolynomial (K × I) (MvPolynomial K ℝ) →ₐ[ℝ] MvPolynomial K ℝ :=
    (aeval (fun z : K × I => C (v z.1 z.2))).restrictScalars ℝ
  have he : E.comp parameterPolynomialPullback =
      aeval (fun j => rowPolynomial (fun k => v k j)) := by
    apply algHom_ext
    intro j
    simp [E, parameterPolynomialPullback, parameterLinearCoordinate, rowPolynomial, mul_comm]
  exact AlgHom.congr_fun he P

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ τ υ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def substitute (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial τ R V :=
  (MvPolynomial.aeval (R := R) f).toLinearMap.rTensor V

@[simp] theorem substitute_tmul (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (v : V) :
    substitute f (p ⊗ₜ[R] v) = MvPolynomial.aeval (R := R) f p ⊗ₜ[R] v := rfl

theorem coefficients_substitute_monomial (f : σ → MvPolynomial τ R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (v : V) :
    coefficients (substitute f (monomial α v)) β =
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, substitute_tmul, coefficients_tmul]

theorem coefficients_substitute (f : σ → MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (α : τ →₀ ℕ) :
    coefficients (substitute f p) α = ∑ β ∈ (coefficients p).support,
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_substitute_monomial]

theorem eval_substitute (f : σ → MvPolynomial τ R) (x : τ → R) (p : VectorPolynomial σ R V) :
    eval x (substitute f p) = eval (fun i => MvPolynomial.aeval (R := R) x (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [substitute_tmul, eval_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem map_substitute (f : σ → MvPolynomial τ R) (g : V →ₗ[R] W)
    (p : VectorPolynomial σ R V) :
    map g (substitute f p) = substitute f (map g p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => rfl
  | add p q hp hq => simp only [map_add, hp, hq]

theorem substitute_comp (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (p : VectorPolynomial σ R V) :
    substitute g (substitute f p) = substitute (fun i => MvPolynomial.aeval (R := R) g (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [substitute_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

noncomputable def substituteLie {L : Type*} [LieRing L] [LieAlgebra R L]
    (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial τ R L where
  toLinearMap := substitute f
  map_lie' {p q} := by
    change substitute f ⁅p, q⁆ = ⁅substitute f p, substitute f q⁆
    induction p using TensorProduct.induction_on with
    | zero => refine (congrArg _ (zero_lie (L := VectorPolynomial σ R L) (M := VectorPolynomial σ R L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm) | exact (zero_lie (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero => refine (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (M := VectorPolynomial σ R L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm) | exact (lie_zero (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm
      | tmul b w => simp only [LieAlgebra.ExtendScalars.bracket_tmul, substitute_tmul, map_mul]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W) :
    MvPolynomial (K × I) ℝ :=
  ∑ d ∈ (coefficients p).support,
    mapPolynomialCoefficients ((TensorProduct.curry L).flip (coefficients p d))
      (parameterPolynomialPullback (MvPolynomial.monomial d 1))

theorem coefficientModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (v : K → I → ℝ) :
    MvPolynomial.eval (fun z => v z.1 z.2) (coefficientModePolynomial L p) =
      L (substitute (fun j => rowPolynomial (fun k => v k j)) p) := by
  unfold coefficientModePolynomial
  rw [map_sum]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, monomial, substitute_tmul,
    mapPolynomialCoefficients_eval, MvPolynomial.algebraMap_eq, parameterPolynomialPullback_eval]
  rfl

theorem coefficientModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : Homogeneous h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hsum : d.sum (fun _ n => n) = h := by
    simpa only [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Pi.one_def,
      smul_eq_mul, mul_one] using homogeneous_support_degree hp hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans_eq hsum

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def Adapted (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, DegreeLE w i (VectorPolynomial.map (F.layer (i + 1)).mkQ p)

theorem adapted_iff_coefficients (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    F.Adapted w p ↔ ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α) := by
  constructor
  · intro hp α
    generalize hd : Finsupp.weight w α = d
    cases d with
    | zero =>
      apply F.antitone (Nat.zero_le 1)
      simp [F.one_eq_top]
    | succ d =>
      have h := hp d α (by rw [hd]; exact Nat.lt_succ_self d)
      rw [coefficients_map] at h
      exact (Submodule.Quotient.mk_eq_zero _).mp h
  · intro hp i α hα
    rw [coefficients_map]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (F.antitone hα (hp α))

noncomputable def adaptedSubmodule (w : σ → ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp α)

theorem mem_adaptedSubmodule (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    p ∈ F.adaptedSubmodule w ↔ F.Adapted w p := (F.adapted_iff_coefficients w p).symm

theorem monomial_mem_adaptedSubmodule (w : σ → ℕ) (α : σ →₀ ℕ) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) :
    monomial (R := ℚ) α a ∈ F.adaptedSubmodule w := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_adaptedSubmodule (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule w) (hq : q ∈ F.adaptedSubmodule w) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule w := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun α => monomial (R := ℚ) α (coefficients p α))
    (fun β => monomial (R := ℚ) β (coefficients q β))]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  rw [map_add]
  exact F.lie_mem (hp α) (hq β)

noncomputable def adaptedLieSubalgebra (w : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule w with lie_mem' := F.lie_mem_adaptedSubmodule w }

theorem adapted_bch (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) (hq : F.Adapted w q) : F.Adapted w (lieBCH s p q) := by
  apply (F.mem_adaptedSubmodule w _).mp
  exact lieBCH_mem (F.adaptedLieSubalgebra w) s
    ((F.mem_adaptedSubmodule w _).mpr hp) ((F.mem_adaptedSubmodule w _).mpr hq)

theorem adapted_degreeLE (w : σ → ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) : DegreeLE w s p := by
  intro α hα
  have h := F.antitone hα ((F.adapted_iff_coefficients w p).mp hp α)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem adapted_map (H : NilpotentLieFiltration M t) (f : L →ₗ[ℚ] M)
    (hf : ∀ i, ∀ a ∈ F.layer i, f a ∈ H.layer i)
    (w : σ → ℕ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    H.Adapted w (VectorPolynomial.map f p) := by
  apply (H.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_map]
  exact hf _ _ ((F.adapted_iff_coefficients w p).mp hp α)

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSubgroup (w : σ → ℕ) :
    Subgroup (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup (F.adaptedLieSubalgebra w)

abbrev PolynomialOrbit (w : σ → ℕ) : Type _ := ↥(F.polynomialSubgroup w)

variable {F}

def PolynomialOrbit.log {w : σ → ℕ} (p : F.PolynomialOrbit w) : VectorPolynomial σ ℚ L :=
  p.val.coord

theorem PolynomialOrbit.adapted {w : σ → ℕ} (p : F.PolynomialOrbit w) : F.Adapted w p.log :=
  (F.mem_adaptedSubmodule w p.log).mp p.property

theorem PolynomialOrbit.degreeLE {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    DegreeLE w s p.log := F.adapted_degreeLE w p.adapted

def polynomialOrbitOfLog {w : σ → ℕ} (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    F.PolynomialOrbit w := ⟨⟨p⟩, (F.mem_adaptedSubmodule w p).mpr hp⟩

@[simp] theorem polynomialOrbitOfLog_log {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    (polynomialOrbitOfLog p hp).log = p := rfl

variable (F)

noncomputable def polynomialOrbitEval (w : σ → ℕ) (x : σ → ℤ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    (F.polynomialOrbitEval w x p).coord = eval (fun i => (x i : ℚ)) p.log := rfl

theorem polynomialOrbitEval_step_zero (F : NilpotentLieFiltration L 0)
    (w : σ → ℕ) (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x p = 1 := by
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitEval w x p).coord = 0
  have h : (F.polynomialOrbitEval w x p).coord ∈ F.layer 1 := by simp [F.one_eq_top]
  simpa only [F.terminal, Submodule.mem_bot] using h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def restrictLieSubalgebra (K : LieSubalgebra ℚ L) : NilpotentLieFiltration K s where
  layer i := (F.layer i).comap K.incl.toLinearMap
  antitone := fun _ _ hij _ hx => F.antitone hij hx
  one_eq_top := by simp only [F.one_eq_top, Submodule.comap_top]
  lie_mem := fun ha hb => F.lie_mem ha hb
  terminal := by
    ext a
    change (a : L) ∈ F.layer (s + 1) ↔ a = 0
    rw [F.terminal, Submodule.mem_bot]
    constructor
    · intro h
      exact Subtype.val_injective h
    · intro h
      rw [h]
      rfl

noncomputable def polynomialLayer (i : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer i}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer i).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer i).smul_mem c (hp α)

theorem monomial_mem_polynomialLayer (i : ℕ) (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer i) :
    monomial (R := ℚ) α a ∈ F.polynomialLayer i := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_polynomialLayer {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.polynomialLayer i) (hq : q ∈ F.polynomialLayer j) :
    ⁅p, q⁆ ∈ F.polynomialLayer (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun α => monomial (R := ℚ) α (coefficients p α))
    (fun β => monomial (R := ℚ) β (coefficients q β))]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  exact F.monomial_mem_polynomialLayer _ _ (F.lie_mem (hp α) (hq β))

noncomputable def polynomialFiltration : NilpotentLieFiltration (VectorPolynomial σ ℚ L) s where
  layer := F.polynomialLayer
  antitone := fun _ _ hij _ hp α => F.antitone hij (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    simp [F.one_eq_top]
  lie_mem := F.lie_mem_polynomialLayer
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    have h := hp α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using h

noncomputable def adaptedPolynomialFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.adaptedLieSubalgebra w) s :=
  F.polynomialFiltration.restrictLieSubalgebra (F.adaptedLieSubalgebra w)

end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_substitute (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted v (VectorPolynomial.substitute f p) := by
  apply (F.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact aeval_monomial_weightedSupport f w v hf β (MvPolynomial.mem_support_iff.mpr hc)

noncomputable def polynomialOrbitSubstitute {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    F.PolynomialOrbit w →* F.PolynomialOrbit v where
  toFun p := polynomialOrbitOfLog (VectorPolynomial.substitute f p.log)
    (F.adapted_substitute w v f hf p.adapted)
  map_one' := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_zero (VectorPolynomial.substitute f)
  map_mul' p q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_lieBCH (VectorPolynomial.substituteLie f) s p.log q.log

@[simp] theorem polynomialOrbitSubstitute_log {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) :
    (F.polynomialOrbitSubstitute f hf p).log = VectorPolynomial.substitute f p.log := rfl

theorem polynomialOrbitSubstitute_eval {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    F.polynomialOrbitEval v x (F.polynomialOrbitSubstitute f hf p) = F.polynomialOrbitEval w y p := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun j => (x j : ℚ)) (VectorPolynomial.substitute f p.log) = _
  rw [VectorPolynomial.eval_substitute]
  simp only [hxy]
  rfl

end Erdos3.NilpotentLieFiltration

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialMassBox
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_mass_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (v w : σ → ℝ) {B δ : ℝ} {s : ℕ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      realPolynomialMass P * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  simp only [RingHom.id_apply]
  calc
    _ ≤ ∑ m ∈ P.support, |P.coeff m * ∏ i, v i ^ m i - P.coeff m * ∏ i, w i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ P.support, |P.coeff m| *
        (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial m hm) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [realPolynomialMass, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

theorem lipschitzOn_realPolynomial_mass_box {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B) (hC : realPolynomialMass P ≤ C)
    (hdegree : P.totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => aeval v P) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  rw [Real.dist_eq]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hdiff (i : σ) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have h := abs_aeval_sub_aeval_mass_box_bound P v w hBr dist_nonneg hv hw hdiff hdegree
  apply h.trans
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pow_nonneg B.coe_nonneg _)) dist_nonneg

theorem lipschitzOn_realPolynomialVector_mass_box {σ τ : Type*} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ ℝ) (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B)
    (hC : ∀ j, realPolynomialMass (P j) ≤ C) (hdegree : ∀ j, (P j).totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => fun j => aeval v (P j)) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro j
  exact (lipschitzOn_realPolynomial_mass_box (P j) C B hB (hC j) (hdegree j)).dist_le_mul v hv w hw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringAction
namespace OAI

section

namespace Erdos3.WeightedLoweringAut

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def degreeAction (e : WeightedLoweringAut w R) (n : ℕ) :
    weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n where
  toFun p := ⟨e.val p, e.preserves_degree p.property⟩
  invFun p := ⟨e.val.symm p, (e⁻¹).preserves_degree p.property⟩
  left_inv p := Subtype.ext (e.val.symm_apply_apply p)
  right_inv p := Subtype.ext (e.val.apply_symm_apply p)
  map_add' p q := Subtype.ext (map_add e.val (p : MvPolynomial σ R) (q : MvPolynomial σ R))
  map_smul' c p := Subtype.ext (map_smul e.val c (p : MvPolynomial σ R))

theorem degreeAction_apply_coe (e : WeightedLoweringAut w R) (n : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    (e.degreeAction n p : MvPolynomial σ R) = e.val p := rfl

noncomputable def degreeActionHom (n : ℕ) :
    WeightedLoweringAut w R →*
      (weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n) where
  toFun e := e.degreeAction n
  map_one' := by
    apply LinearEquiv.ext
    intro p
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro p
    rfl

theorem degreeAction_difference_pow_coe (e : WeightedLoweringAut w R) (n k : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    ((((e.degreeAction n).toLinearMap - 1) ^ k) p : MvPolynomial σ R) =
      (polynomialHomDifference e.val.toAlgHom ^ k) (p : MvPolynomial σ R) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem degreeAction_difference_pow_zero (e : WeightedLoweringAut w R) (n : ℕ) :
    ((e.degreeAction n).toLinearMap - 1) ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change ((((e.degreeAction n).toLinearMap - 1) ^ (n + 1)) p : MvPolynomial σ R) = 0
  rw [degreeAction_difference_pow_coe]
  exact polynomialHomDifference_pow_eq_zero w e.val.toAlgHom e.property p.property

theorem degreeAction_difference_nilpotent (e : WeightedLoweringAut w R) (n : ℕ) :
    IsNilpotent ((e.degreeAction n).toLinearMap - 1) :=
  ⟨n + 1, e.degreeAction_difference_pow_zero n⟩

theorem degreeActionHom_injective (n : ℕ) (hw : ∀ i, w i ≤ n) :
    Function.Injective (degreeActionHom (w := w) (R := R) n) := by
  intro e f h
  have he : e.val.toAlgHom = f.val.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi := congrArg (fun L : weightedSupportLE (R := R) w n ≃ₗ[R]
        weightedSupportLE (R := R) w n =>
      (L ⟨X i, weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)⟩ :
        MvPolynomial σ R)) h
    exact hi
  apply Subtype.ext
  apply DFunLike.ext
  intro p
  exact congrArg (fun F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R => F p) he

end Erdos3.WeightedLoweringAut

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

noncomputable def scaleMvPolynomialAxes {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ α ∈ P.support, monomial α (P.coeff α * monomialScale T α)

theorem scaleMvPolynomialAxes_coeff {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (α : σ →₀ ℕ) :
    (scaleMvPolynomialAxes T P).coeff α = P.coeff α * monomialScale T α := by
  classical
  rw [scaleMvPolynomialAxes, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [notMem_support_iff.mp h, zero_mul]

theorem scaleMvPolynomialAxes_support_subset {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).support ⊆ P.support := by
  intro α hα
  rw [mem_support_iff, scaleMvPolynomialAxes_coeff] at hα
  exact mem_support_iff.mpr (left_ne_zero_of_mul hα)

theorem scaleMvPolynomialAxes_totalDegree_le {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).totalDegree ≤ P.totalDegree :=
  totalDegree_le_of_support_subset (scaleMvPolynomialAxes_support_subset T P)

theorem scaleMvPolynomialAxes_eval {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (x : σ → ℝ) :
    eval x (scaleMvPolynomialAxes T P) = eval (fun i => T i * x i) P := by
  classical
  rw [scaleMvPolynomialAxes, eval_sum, eval_eq]
  apply Finset.sum_congr rfl
  intro α _
  rw [eval_monomial]
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem scaleMvPolynomialAxes_mass_le {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P : MvPolynomial σ ℝ) {M : ℝ}
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ P.support.card * M := by
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      rw [scaleMvPolynomialAxes_coeff, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      exact (le_div_iff₀ (monomialScale_pos T hT α)).mp (hcoeff α)
    _ = P.support.card * M := by simp

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem abs_monomialScale_le_pow {σ : Type*} (T : σ → ℝ) {K : ℝ}
    (hT : ∀ i, |T i| ≤ K) (α : σ →₀ ℕ) :
    |monomialScale T α| ≤ K ^ (α.sum fun _ n => n) := by
  classical
  calc
    _ = ∏ i ∈ α.support, |T i| ^ α i := by
      simp only [monomialScale, Finsupp.prod, Finset.abs_prod, abs_pow]
    _ ≤ ∏ i ∈ α.support, K ^ α i :=
      Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hT i) _)
    _ = K ^ (α.sum fun _ n => n) := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

theorem scaleMvPolynomialAxes_mass_le_of_abs_le {σ : Type*}
    (T : σ → ℝ) (P : MvPolynomial σ ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hT : ∀ i, |T i| ≤ K) {d : ℕ} (hP : P.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ K ^ d * realPolynomialMass P := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * K ^ d := by
      apply Finset.sum_le_sum
      intro α hα
      rw [scaleMvPolynomialAxes_coeff, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_monomialScale_le_pow T hT α).trans
        (pow_le_pow_right₀ hK ((MvPolynomial.le_totalDegree hα).trans hP))
    _ = K ^ d * realPolynomialMass P := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _

theorem jointPolynomialDilation_mass_le {U B : Type*}
    (c : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hc : ∀ i, |c i| ≤ K) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim c (fun _ => 1)) S) ≤
      K ^ d * realPolynomialMass S := by
  apply scaleMvPolynomialAxes_mass_le_of_abs_le _ S hK _ hS
  intro i
  cases i with
  | inl i => exact hc i
  | inr i => simpa only [Sum.elim_inr, abs_one] using hK

end Erdos3

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

theorem abs_prod_sub_prod_unit_sum {ι : Type*} (S : Finset ι)
    (f g e : ι → ℝ) (he : ∀ i ∈ S, 0 ≤ e i)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hg : ∀ i ∈ S, |g i| ≤ 1)
    (hfg : ∀ i ∈ S, |f i - g i| ≤ e i) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, e i := by
  classical
  revert he hf hg hfg
  induction S using Finset.induction_on with
  | empty => intro _ _ _ _; simp
  | @insert a S ha ih =>
    intro he hf hg hfg
    have hrec := ih (fun i hi => he i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have hprod : |∏ i ∈ S, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| +
          |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ 1 * (∑ i ∈ S, e i) + e a * 1 :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) zero_le_one)
          (mul_le_mul (hfg a (Finset.mem_insert_self _ _)) hprod
            (abs_nonneg _) (he a (Finset.mem_insert_self _ _)))
      _ = _ := by ring

theorem abs_eval_sub_eval_unit_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x y : σ → ℝ) {δ : ℝ} {m : ℕ}
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * realPolynomialMass P * δ := by
  classical
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, x i ^ α i) - ∏ i, y i ^ α i| ≤ (m : ℝ) * δ := by
    have he (i : σ) : |x i ^ α i - y i ^ α i| ≤ δ * α i := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (B := (1 : ℝ)) le_rfl hδ (hx i) (hy i) (hxy i) (le_refl (α i))
    have hp := abs_prod_sub_prod_unit_sum Finset.univ
      (fun i => x i ^ α i) (fun i => y i ^ α i) (fun i => δ * α i)
      (fun _ _ => by positivity)
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hx i))
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i))
      (fun i _ => he i)
    have hsum : (∑ i, (α i : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast (show (∑ i, α i) ≤ m by
        have hs : α.sum (fun (_ : σ) (n : ℕ) => n) = ∑ i, α i :=
          Finsupp.sum_fintype α (fun _ n => n) (fun _ => rfl)
        rw [← hs]
        exact (MvPolynomial.le_totalDegree hα).trans hdegree)
    apply hp.trans
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hsum hδ]
  change |P.eval₂ (RingHom.id ℝ) x - P.eval₂ (RingHom.id ℝ) y| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * ((m : ℝ) * δ) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, x i ^ α i - P.coeff α * ∏ i, y i ^ α i| ≤ _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial α hα) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold realPolynomialMass; ring

theorem abs_eval_sub_eval_normalized_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x y : σ → ℝ) {M δ : ℝ} {m : ℕ}
    (hmass : realPolynomialMass (scaleMvPolynomialAxes T P) ≤ M)
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ T i) (hy : ∀ i, |y i| ≤ T i)
    (hxy : ∀ i, |x i - y i| ≤ T i * δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * M * δ := by
  have hunit (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  have hdiff (i : σ) : |x i / T i - y i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i)]
    exact (div_le_iff₀ (hT i)).mpr (by simpa only [mul_comm] using hxy i)
  have hev (v : σ → ℝ) : eval (fun i => v i / T i) (scaleMvPolynomialAxes T P) = eval v P := by
    rw [scaleMvPolynomialAxes_eval]
    apply congrArg (fun z : σ → ℝ => eval z P)
    funext i
    exact mul_div_cancel₀ (v i) (hT i).ne'
  have h := abs_eval_sub_eval_unit_mass_bound (scaleMvPolynomialAxes T P)
    (fun i => x i / T i) (fun i => y i / T i) hδ (hunit x hx) (hunit y hy) hdiff
    ((scaleMvPolynomialAxes_totalDegree_le T P).trans hdegree)
  rw [hev, hev] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)) hδ)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_eq_aeval {σ : Type*} (T : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    scaleMvPolynomialAxes T P =
      MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  change aeval (fun i => T i * x i) P = aeval x (aeval _ P)
  rw [comp_aeval_apply]
  simp

theorem scaleMvPolynomialAxes_mem_weightedSupportLE {σ : Type*} (T : σ → ℝ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℝ}
    (hP : P ∈ weightedSupportLE w d) :
    scaleMvPolynomialAxes T P ∈ weightedSupportLE w d := by
  intro α hα
  exact hP (scaleMvPolynomialAxes_support_subset T P hα)

theorem rationalAxisScaling_map_real {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P) =
      scaleMvPolynomialAxes (fun i => (T i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) := by
  rw [scaleMvPolynomialAxes_eq_aeval]
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, aeval_X, map_X, map_C, hP]; rfl

theorem rationalAxisScaling_support_subset {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P).support ⊆
      P.support := by
  intro α hα
  have hreal : α ∈ (MvPolynomial.map (algebraMap ℚ ℝ)
      (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P)).support := by
    rw [mem_support_iff, coeff_map]
    change ((((aeval fun i => C (T i) * X i) P).coeff α : ℚ) : ℝ) ≠ 0
    exact_mod_cast (mem_support_iff.mp hα)
  rw [rationalAxisScaling_map_real] at hreal
  have hsource := scaleMvPolynomialAxes_support_subset (fun i => (T i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) P) hreal
  apply mem_support_iff.mpr
  intro hz
  rw [mem_support_iff, coeff_map, hz, map_zero] at hsource
  exact hsource rfl

theorem rationalAxisScaling_mem_weightedSupportLE {σ : Type*} (T : σ → ℚ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P ∈
      weightedSupportLE w d := by
  intro α hα
  exact hP (rationalAxisScaling_support_subset T P hα)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointPolynomialDilation_coefficientGrid
    (R : MvPolynomial (U ⊕ B) ℝ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d) (hR : realPolynomialCoefficientGrid l R) :
    realPolynomialCoefficientGrid (q ^ d * l)
      (scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1)) R) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [scaleMvPolynomialAxes_eq_aeval, Nat.mul_comm (q ^ d) l]
  apply realPolynomialCoefficientGrid_substitute R _ l q d hdegree hR
  intro i
  cases i with
  | inl u =>
    apply (realPolynomialCoefficientGrid_iff _ _).mpr
    simp only [Sum.elim_inl]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]
    exact X_mem_integralRealPolynomialSubring _
  | inr b =>
    simpa only [Sum.elim_inr, map_one, one_mul] using
      realPolynomialCoefficientGrid_X q (Sum.inr b : U ⊕ B)

noncomputable def jointRationalPolynomialDilation (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    MvPolynomial (U ⊕ B) ℚ :=
  aeval (fun i => C (Sum.elim (fun _ : U => (q : ℚ)⁻¹) (fun _ : B => 1) i) * X i) R

theorem jointRationalPolynomialDilation_map (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    map (algebraMap ℚ ℝ) (jointRationalPolynomialDilation q R) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1))
        (map (algebraMap ℚ ℝ) R) := by
  rw [jointRationalPolynomialDilation, rationalAxisScaling_map_real]
  congr 1
  funext i
  cases i <;> simp

theorem jointRationalPolynomialDilation_eval₂ (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ)
    (u : U → ℝ) (b : B → ℝ) :
    eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) =
      eval₂ (algebraMap ℚ ℝ) (Sum.elim (fun i => u i / (q : ℝ)) b) R := by
  rw [← eval_map, jointRationalPolynomialDilation_map, scaleMvPolynomialAxes_eval, eval_map]
  congr 1
  funext i
  cases i <;> simp [div_eq_mul_inv, mul_comm]

theorem jointRationalPolynomialDilation_denominatorGrid
    (R : MvPolynomial (U ⊕ B) ℚ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid l) :
    (fun α => (jointRationalPolynomialDilation q R).coeff α) ∈
      denominatorGrid (q ^ d * l) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [jointRationalPolynomialDilation_map]
  apply jointPolynomialDilation_coefficientGrid _ q l d hq
  · apply le_trans (b := R.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro α hα
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) R hα)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hR

theorem jointRationalPolynomialDilation_mem_weightedSupportLE
    (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) (w : U ⊕ B → ℕ) (d : ℕ)
    (hR : R ∈ weightedSupportLE w d) :
    jointRationalPolynomialDilation q R ∈ weightedSupportLE w d :=
  rationalAxisScaling_mem_weightedSupportLE _ w d hR

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

noncomputable def translationDirectionalDerivative (b : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ →ₗ[ℝ] MvPolynomial (U ⊕ B) ℝ :=
  ∑ i, (LinearMap.mulLeft ℝ (rename Sum.inl (b i))).comp (pderiv (Sum.inr i)).toLinearMap

theorem translationDirectionalDerivative_apply (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) :
    translationDirectionalDerivative b P =
      ∑ i, rename Sum.inl (b i) * pderiv (Sum.inr i) P := by
  simp [translationDirectionalDerivative]

noncomputable def translationDirectionalSeries (d : ℕ) (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  ∑ i ∈ Finset.range d, ((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
    ((translationDirectionalDerivative b) ^ i) P

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

omit [Fintype B] in
theorem degreeOf_rename_inl_inr (P : MvPolynomial U ℝ) (i : B) :
    (rename (Sum.inl : U → U ⊕ B) P).degreeOf (Sum.inr i) = 0 := by
  classical
  by_contra h
  obtain ⟨j, _, hj⟩ := mem_vars_rename (Sum.inl : U → U ⊕ B) P
    (mem_vars_iff_degreeOf_ne_zero.mpr h)
  cases hj

theorem translationDirectionalDerivative_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (j : B) :
    (translationDirectionalDerivative b P).degreeOf (Sum.inr j) ≤ d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add]
  exact mvPolynomial_pderiv_degreeOf_le P (Sum.inr i) (Sum.inr j) (hP j)

theorem translationDirectionalDerivative_pow_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (k : ℕ) (j : B) :
    (((translationDirectionalDerivative b) ^ k) P).degreeOf (Sum.inr j) ≤ d := by
  induction k generalizing j with
  | zero => simpa using hP j
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_degreeOf_le b _ d ih j

theorem realPolynomialMass_translationDirectionalDerivative
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) :
    realPolynomialMass (translationDirectionalDerivative b P) ≤
      ((Fintype.card B : ℝ) * d * M) * realPolynomialMass P := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : B, M * ((d : ℝ) * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hb i))
          (realPolynomialMass_pderiv_degreeOf P (Sum.inr i) (hP i))
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem realPolynomialMass_translationDirectionalDerivative_pow
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) (k : ℕ) :
    realPolynomialMass (((translationDirectionalDerivative b) ^ k) P) ≤
      ((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    apply (realPolynomialMass_translationDirectionalDerivative b _ d
      (translationDirectionalDerivative_pow_degreeOf_le b P d hP k) hM hb).trans
    calc
      _ ≤ ((Fintype.card B : ℝ) * d * M) *
          (((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ']; ring

theorem translationDirectionalSeries_coefficient_abs_le_one (i : ℕ) :
    |(-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)| ≤ 1 := by
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg _)]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (i + 1))

theorem realPolynomialMass_translationDirectionalSeries
    (d : ℕ) (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M)
    (hmass : realPolynomialMass P ≤ M) :
    realPolynomialMass (translationDirectionalSeries d b P) ≤
      ((d : ℝ) + 1) * M * (1 + (Fintype.card B : ℝ) * d * M) ^ d := by
  classical
  let A : ℝ := (Fintype.card B : ℝ) * d * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      realPolynomialMass (((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
        ((translationDirectionalDerivative b) ^ i) P) ≤ M * (1 + A) ^ d := by
    rw [realPolynomialMass_smul]
    calc
      _ ≤ 1 * (A ^ i * realPolynomialMass P) :=
        mul_le_mul (translationDirectionalSeries_coefficient_abs_le_one i)
          (realPolynomialMass_translationDirectionalDerivative_pow b P d hP hM hb i)
          (realPolynomialMass_nonneg _) (by norm_num)
      _ ≤ A ^ i * M := by simpa using mul_le_mul_of_nonneg_left hmass (pow_nonneg hA i)
      _ ≤ (1 + A) ^ d * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact (pow_le_pow_left₀ hA (by linarith) i).trans
          (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le)
      _ = _ := mul_comm _ _
  unfold translationDirectionalSeries
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range d, M * (1 + A) ^ d := Finset.sum_le_sum hterm
    _ = (d : ℝ) * (M * (1 + A) ^ d) := by simp
    _ ≤ ((d : ℝ) + 1) * (M * (1 + A) ^ d) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp [A]; ring

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem isWeightedHomogeneous_aeval_monomial (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i)) (a : σ →₀ ℕ) (r : R) :
    (aeval f (monomial a r)).IsWeightedHomogeneous w (Finsupp.weight v a) := by
  classical
  rw [aeval_monomial]
  have hprod := IsWeightedHomogeneous.prod a.support (fun i => f i ^ a i)
    (fun i => a i * v i) (fun i _ => by simpa using (hf i).pow (a i))
  have hweight : (∑ i ∈ a.support, a i * v i) = Finsupp.weight v a := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [MvPolynomial.algebraMap_eq, Finsupp.prod] using hprod.C_mul r

theorem isWeightedHomogeneous_algHom (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, (F (X i)).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (F p).IsWeightedHomogeneous w n := by
  classical
  rw [MvPolynomial.aeval_unique F]
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply IsWeightedHomogeneous.sum
  intro a ha
  have hweight : Finsupp.weight v a = n := hp (mem_support_iff.mp ha)
  rw [← hweight]
  exact isWeightedHomogeneous_aeval_monomial v w (fun i => F (X i)) hF a _

theorem weightedHomogeneousComponent_eq_of_sub_lower (w : σ → ℕ)
    {p q : MvPolynomial σ R} {n : ℕ}
    (hpq : p - q ∈ weightedSupportLT w n) (hq : q.IsWeightedHomogeneous w n) :
    weightedHomogeneousComponent w n p = q := by
  have hzero : weightedHomogeneousComponent w n (p - q) = 0 := by
    apply MvPolynomial.ext
    intro a
    rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with ha
    · by_contra hc
      have hlt := hpq (mem_support_iff.mpr hc)
      change Finsupp.weight w a < n at hlt
      omega
    · rfl
  rw [map_sub, hq.weightedHomogeneousComponent_same, sub_eq_zero] at hzero
  exact hzero

theorem aeval_isWeightedHomogeneous (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (aeval f p).IsWeightedHomogeneous w n := by
  apply isWeightedHomogeneous_algHom v w (aeval f) _ hp
  intro i
  simpa only [aeval_X] using hf i

theorem aeval_weightedHomogeneousComponent (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    (n : ℕ) (p : MvPolynomial σ R) :
    aeval f (weightedHomogeneousComponent v n p) =
      weightedHomogeneousComponent w n (aeval f p) := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro α _
  have hm := isWeightedHomogeneous_monomial v α (p.coeff α) rfl
  have hfα := isWeightedHomogeneous_aeval_monomial v w f hf α (p.coeff α)
  by_cases h : n = Finsupp.weight v α
  · rw [h, hm.weightedHomogeneousComponent_same, hfα.weightedHomogeneousComponent_same]
  · rw [hm.weightedHomogeneousComponent_ne n h, map_zero,
      hfα.weightedHomogeneousComponent_ne n h]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem isWeightedHomogeneous_mul_pderiv {σ R : Type*} [CommRing R]
    (w : σ → ℕ) (i : σ) {Q P : MvPolynomial σ R} {d : ℕ}
    (hQ : Q.IsWeightedHomogeneous w (w i)) (hP : P.IsWeightedHomogeneous w d) :
    (Q * pderiv i P).IsWeightedHomogeneous w d := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum, Finset.mul_sum]
  apply (weightedHomogeneousSubmodule R w d).sum_mem
  intro a ha
  change (Q * pderiv i (monomial a (P.coeff a))).IsWeightedHomogeneous w d
  rw [pderiv_monomial]
  by_cases hi : a i = 0
  · simp only [hi, Nat.cast_zero, mul_zero, monomial_zero]
    exact (weightedHomogeneousSubmodule R w d).zero_mem
  · have hweight := Finsupp.weight_sub_single_add (w := w) hi
    rw [hP (MvPolynomial.mem_support_iff.mp ha)] at hweight
    have hm := hQ.mul (isWeightedHomogeneous_monomial w
      (a - Finsupp.single i 1) (P.coeff a * (a i : R)) rfl)
    simpa only [Nat.add_comm (w i), hweight] using hm

variable {U B : Type*} [Fintype B]

theorem translationDirectionalDerivative_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalDerivative b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  apply isWeightedHomogeneous_mul_pderiv (Sum.elim v w) (Sum.inr i) _ hP
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun j => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl j)) (hb i)

theorem translationDirectionalDerivative_pow_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) (n : ℕ) :
    (((translationDirectionalDerivative b) ^ n) P).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_isWeightedHomogeneous v w b hb ih

theorem translationDirectionalSeries_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (N : ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalSeries N b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  exact (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).smul_mem _
    (translationDirectionalDerivative_pow_isWeightedHomogeneous v w b hb hP i)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem scaleMvPolynomialAxes_weightedHomogeneousComponent
    (w : σ → ℕ) (T : σ → ℝ) (d : ℕ) (P : MvPolynomial σ ℝ) :
    weightedHomogeneousComponent w d (scaleMvPolynomialAxes T P) =
      scaleMvPolynomialAxes T (weightedHomogeneousComponent w d P) := by
  classical
  ext α
  simp only [coeff_weightedHomogeneousComponent, scaleMvPolynomialAxes_coeff]
  split_ifs <;> simp

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) : MvPolynomial τ ℚ := by
  classical
  exact ∑ j, A (Pi.single j 1) i • X j

noncomputable def polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ :=
  aeval (linearCoordinatePolynomial A)

omit [Fintype σ] in
theorem linearMap_apply_sum_coordinates [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    ∑ j, A (Pi.single j 1) i * x j = A x i := by
  classical
  have hx : (∑ j, x j • Pi.single j (1 : ℚ)) = x := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_X
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    polynomialLinearRestriction A (X i) = linearCoordinatePolynomial A i := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_C
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (r : ℚ) :
    polynomialLinearRestriction A (C r) = C r := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem eval_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    eval x (linearCoordinatePolynomial A i) = A x i := by
  classical
  simp only [linearCoordinatePolynomial, map_sum, ← C_mul', map_mul, eval_C, eval_X]
  exact linearMap_apply_sum_coordinates A x i

omit [Fintype σ] in
@[simp] theorem scalarDirectionalDerivative_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    scalarDirectionalDerivative z (linearCoordinatePolynomial A i) = C (A z i) := by
  classical
  rw [linearCoordinatePolynomial, map_sum]
  simp only [Derivation.map_smul, scalarDirectionalDerivative_X]
  simp only [← C_mul', ← map_mul]
  rw [← map_sum, linearMap_apply_sum_coordinates]

omit [Fintype σ] in
theorem eval_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (P : MvPolynomial σ ℚ) :
    eval x (polynomialLinearRestriction A P) = eval (A x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem scalarDirectionalDerivative_linearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative z (polynomialLinearRestriction A P) =
      polynomialLinearRestriction A (scalarDirectionalDerivative (A z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

omit [Fintype σ] in
@[simp] theorem coeff_zero_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    (polynomialLinearRestriction A P).coeff 0 = P.coeff 0 := by
  have h := eval_polynomialLinearRestriction A 0 P
  simpa only [map_zero, eval_zero, constantCoeff_eq] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialTranslationPath_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    polynomialTranslationPath z (linearCoordinatePolynomial A i) =
      Polynomial.C (linearCoordinatePolynomial A i) -
        Polynomial.C (C (A z i)) * Polynomial.X := by
  classical
  have hsum : (∑ j, A (Pi.single j 1) i • C (z j)) = (C (A z i) : MvPolynomial τ ℚ) := by
    simp only [← C_mul', ← map_mul, ← map_sum, linearMap_apply_sum_coordinates]
  rw [linearCoordinatePolynomial, map_sum]
  simp only [map_smul, polynomialTranslationPath_X, smul_sub,
    Finset.sum_sub_distrib, ← smul_mul_assoc, Polynomial.smul_C]
  rw [← map_sum, ← Finset.sum_mul, ← map_sum, hsum]

theorem polynomialLinearRestriction_translationPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialTranslationPath z (polynomialLinearRestriction A P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, hp]
    simp [polynomialTranslationPath_linearCoordinatePolynomial]

theorem polynomialLinearRestriction_exponentialPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialExponentialPath z (polynomialLinearRestriction A P) := by
  symm
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialLinearRestriction_translationPath]
  · simp

theorem polynomialLinearRestriction_exponentialCoordinate
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialLinearRestriction A (polynomialExponentialCoordinate (A z) P) =
      polynomialExponentialCoordinate z (polynomialLinearRestriction A P) := by
  unfold polynomialExponentialCoordinate
  rw [← polynomialLinearRestriction_exponentialPath]
  simp

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem linearCoordinatePolynomial_eq_sum [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    linearCoordinatePolynomial A i = ∑ j, A (Pi.single j 1) i • (X j : MvPolynomial τ ℚ) := by
  unfold linearCoordinatePolynomial
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun c : ℚ => c • (X j : MvPolynomial τ ℚ))
  apply congrArg (fun x : τ → ℚ => A x i)
  funext k
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

theorem linearCoordinatePolynomial_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) (i : σ) :
    (linearCoordinatePolynomial A i).IsWeightedHomogeneous v (w i) := by
  rw [linearCoordinatePolynomial_eq_sum]
  apply (weightedHomogeneousSubmodule ℚ v (w i)).sum_mem
  intro j _
  by_cases hj : v j = w i
  · exact hj ▸ (weightedHomogeneousSubmodule ℚ v (v j)).smul_mem
      (A (Pi.single j 1) i) (isWeightedHomogeneous_X (R := ℚ) v j)
  · rw [hA j i hj, zero_smul]
    exact isWeightedHomogeneous_zero ℚ v (w i)

theorem polynomialLinearRestriction_monomial_homogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (a : σ →₀ ℕ) (c : ℚ) :
    (polynomialLinearRestriction A (monomial a c)).IsWeightedHomogeneous v (Finsupp.weight w a) := by
  rw [monomial_eq]
  simp only [map_mul, polynomialLinearRestriction_C, Finsupp.prod, map_prod,
    map_pow, polynomialLinearRestriction_X]
  have hprod := IsWeightedHomogeneous.prod a.support
    (fun i => linearCoordinatePolynomial A i ^ a i) (fun i => a i * w i)
    (fun i _ => by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (linearCoordinatePolynomial_isWeightedHomogeneous A v w hA i).pow (a i))
  simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id] using hprod.C_mul c

theorem polynomialLinearRestriction_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P.IsWeightedHomogeneous w n) :
    (polynomialLinearRestriction A P).IsWeightedHomogeneous v n := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedHomogeneousSubmodule ℚ v n).sum_mem
  intro a ha
  have h := polynomialLinearRestriction_monomial_homogeneous A v w hA a (P.coeff a)
  change (polynomialLinearRestriction A (monomial a (P.coeff a))).IsWeightedHomogeneous v n
  simpa only [hP (MvPolynomial.mem_support_iff.mp ha)] using h

namespace PolynomialTranslationLie

variable [Fintype σ]

end PolynomialTranslationLie
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLinearBaseProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ] [DecidableEq τ]

theorem linearMap_coordinateGradeProjection
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (n : ℕ) (z : τ → ℚ) :
    A (fun j => if v j = n then z j else 0) =
      fun i => if w i = n then A z i else 0 := by
  classical
  funext i
  rw [← linearMap_apply_sum_coordinates A _ i]
  by_cases hi : w i = n
  · rw [if_pos hi, ← linearMap_apply_sum_coordinates A z i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j = n
    · rw [if_pos hj]
    · rw [if_neg hj, mul_zero, hweight j i (by omega), zero_mul]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : v j = n
    · rw [if_pos hj, hweight j i (by omega), zero_mul]
    · rw [if_neg hj, mul_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotentialExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def coordinateWeightProjection (w : σ → ℕ) (n : ℕ) :
    (σ → ℚ) →ₗ[ℚ] (σ → ℚ) where
  toFun x i := if w i = n then x i else 0
  map_add' x y := by funext i; by_cases hi : w i = n <;> simp [hi]
  map_smul' r x := by funext i; by_cases hi : w i = n <;> simp [hi]

theorem polynomialLinearRestriction_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (hBA : ∀ x, B (A x) = x) (V : MvPolynomial τ ℚ) :
    polynomialLinearRestriction A (polynomialLinearRestriction B V) = V := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialLinearRestriction, eval_polynomialLinearRestriction, hBA]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageCoverBudget
namespace OAI

section

namespace Erdos3

def imageLatticeLogBudget (K : ℕ) (p : ℝ) : ℝ :=
  K + (p + 2) ^ 4 + 2 * p + (p + 2) ^ 9

theorem imageLatticeLogBudget_nonneg (K : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ imageLatticeLogBudget K p := by unfold imageLatticeLogBudget; positivity

theorem imageLatticeBound_le_exp (K d n H l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((K * H ^ (n ^ 3) * (m * (l * rationalKernelHeight n H ^ (d * n))) : ℕ) : ℝ) ≤
      Real.exp (imageLatticeLogBudget K p) := by
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (n ^ 3) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _).trans
    rw [← Real.exp_nat_mul, Nat.cast_pow]
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) ^ 3 * p ≤ (p + 2) ^ 3 * (p + 2) := by gcongr <;> linarith
      _ = _ := by ring
  have hkernel := rationalKernelHeight_le_budget n H hp hn hH
  have hpowK : ((rationalKernelHeight n H ^ (d * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hkernel _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * n * (p + 2) ^ 7 ≤ (p + 2) * (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp K * Real.exp ((p + 2) ^ 4) *
        (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9))) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; unfold imageLatticeLogBudget; congr 1; ring

theorem exists_image_cover_reconstruction_budget (K C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      let q := 2 * p + imageLatticeLogBudget K p
      q ≤ (p + N) ^ N ∧ p * (p + imageLatticeLogBudget K p) ≤ (p + N) ^ N ∧
        (q + C) ^ C ≤ (p + N) ^ N := by
  let L : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 2) ^ 4 +
    2 * Polynomial.X + (Polynomial.X + 2) ^ 9
  let q : Polynomial ℕ := 2 * Polynomial.X + L
  let P : Polynomial ℕ := q + Polynomial.X * (Polynomial.X + L) + (q + Polynomial.C C) ^ C
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have hlog := imageLatticeLogBudget_nonneg K hp
  have hq : 0 ≤ 2 * p + imageLatticeLogBudget K p := by positivity
  have hidx : 0 ≤ p * (p + imageLatticeLogBudget K p) := by positivity
  have hcost : 0 ≤ (2 * p + imageLatticeLogBudget K p + C) ^ C := by positivity
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = (2 * p + imageLatticeLogBudget K p) +
      p * (p + imageLatticeLogBudget K p) + (2 * p + imageLatticeLogBudget K p + C) ^ C := by
    simp [P, q, L, imageLatticeLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hb := hbound p hp
  rw [heq] at hb
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ImageReconstructionLogBudget
namespace OAI

section

namespace Erdos3

def imageRepresentativeLogBudget (C : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 4 + C) ^ C + (p + 2) ^ 2

def generalReconstructionLogBudget (C D E F Z : ℕ) (p : ℝ) : ℝ :=
  let q := p + imageRepresentativeLogBudget C p + 1
  p + (p + 2) ^ 18 + (p + 2) ^ 48 + (p + 2) ^ 24 +
    ((p + Z) ^ Z + 1) + (q + D + E) ^ E + (q + F) ^ F + 1

theorem generalReconstructionLogBudget_bounds (C D E F Z : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := p + imageRepresentativeLogBudget C p + 1
    let r := generalReconstructionLogBudget C D E F Z p
    1 ≤ r ∧ p ≤ r ∧ (p + 2) ^ 18 ≤ r ∧ (p + 2) ^ 48 ≤ r ∧ (p + 2) ^ 24 ≤ r ∧
      (p + Z) ^ Z + 1 ≤ r ∧ (q + D + E) ^ E ≤ r ∧ (q + F) ^ F ≤ r := by
  have hq : 0 ≤ p + imageRepresentativeLogBudget C p + 1 := by
    dsimp [imageRepresentativeLogBudget]
    positivity
  have h18 : 0 ≤ (p + 2) ^ 18 := by positivity
  have h48 : 0 ≤ (p + 2) ^ 48 := by positivity
  have h24 : 0 ≤ (p + 2) ^ 24 := by positivity
  have hZ : 0 ≤ (p + Z) ^ Z + 1 := by positivity
  have hE : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + D + E) ^ E := by positivity
  have hF : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + F) ^ F := by positivity
  dsimp only [generalReconstructionLogBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_generalReconstructionLogBudget_bound (C D E F Z : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      40 * generalReconstructionLogBudget C D E F Z p ≤ (p + N) ^ N := by
  let R : Polynomial ℕ := ((Polynomial.X + 2) ^ 4 + Polynomial.C C) ^ C + (Polynomial.X + 2) ^ 2
  let q : Polynomial ℕ := Polynomial.X + R + 1
  let P : Polynomial ℕ := 40 * (Polynomial.X + (Polynomial.X + 2) ^ 18 +
    (Polynomial.X + 2) ^ 48 + (Polynomial.X + 2) ^ 24 +
    ((Polynomial.X + Polynomial.C Z) ^ Z + 1) +
    (q + Polynomial.C D + Polynomial.C E) ^ E + (q + Polynomial.C F) ^ F + 1)
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = 40 * generalReconstructionLogBudget C D E F Z p := by
    simp [P, q, R, generalReconstructionLogBudget, imageRepresentativeLogBudget,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def monomialExponentSet {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact Finset.univ.image e

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomial_abs_le_scale {K : Type*} (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (e : K →₀ ℕ) : |∏ k ∈ e.support, x k ^ e k| ≤ monomialScale T e := by
  classical
  rw [Finset.abs_prod]
  change (∏ k ∈ e.support, |x k ^ e k|) ≤ ∏ k ∈ e.support, T k ^ e k
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro k _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _

theorem monomialArrayPolynomial_box_bound {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤
      ∑ j, |a j| * monomialScale T (e j) := by
  rw [monomialArrayPolynomial_eval]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (monomial_abs_le_scale T x hx (e j)) (abs_nonneg _)

theorem monomialArrayPolynomial_box_budget {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a B : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (ha : ∀ j, |a j| * monomialScale T (e j) ≤ B j) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, B j :=
  (monomialArrayPolynomial_box_bound e a T x hx).trans (Finset.sum_le_sum (fun j _ => ha j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerMonomialArrayPolynomial {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) : MvPolynomial V ℤ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem integerMonomialArrayPolynomial_map {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) :
    MvPolynomial.map (Int.castRingHom ℝ) (integerMonomialArrayPolynomial e a) =
      monomialArrayPolynomial e (fun j => (a j : ℝ)) := by
  simp only [integerMonomialArrayPolynomial, monomialArrayPolynomial, map_sum,
    MvPolynomial.map_monomial, Int.coe_castRingHom]

theorem integerMonomialArrayPolynomial_degree {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) {s : ℕ} (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) :
    (integerMonomialArrayPolynomial e a).totalDegree ≤ s := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularMonomialArrayPolynomial_selected {E K R A : Type*}
    [Fintype E] [Fintype A] [CommRing R] (exponent : E → K →₀ ℕ)
    (slot : A → E) (hinj : Function.Injective slot)
    (fixed : E → R) (c : A → R) :
    (∑ e, MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)) =
      (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e)) +
      ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
  let F : E → MvPolynomial K R :=
    fun e => MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : E => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hs : (∑ a, F (slot a)) = ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hu : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e) := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hs, hu] at hsum
  exact hsum.symm.trans (add_comm _ _)

noncomputable def modularBoundedCoefficientPolynomial {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e, monomial e.val (c e)

noncomputable def modularUnselectedCoefficientPolynomial {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), monomial e.val (fixed e)

theorem modularBoundedCoefficientPolynomial_selected {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    modularBoundedCoefficientPolynomial h (Function.extend slot c fixed) =
      modularUnselectedCoefficientPolynomial h slot fixed +
        ∑ a, monomial (slot a).val (c a) := by
  let F : BoundedCoefficientExponent K h → MvPolynomial K R :=
    fun e => monomial e.val (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : BoundedCoefficientExponent K h => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hselected : (∑ a, F (slot a)) = ∑ a, monomial (slot a).val (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hunselected : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      modularUnselectedCoefficientPolynomial h slot fixed := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial e.val (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hselected, hunselected] at hsum
  exact hsum.symm.trans (add_comm _ _)

theorem modularBoundedCoefficientPolynomial_selected_top {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = h)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    homogeneousComponent h (modularBoundedCoefficientPolynomial h (Function.extend slot c fixed)) =
      homogeneousComponent h (modularUnselectedCoefficientPolynomial h slot fixed) +
        ∑ a, monomial (slot a).val (c a) := by
  rw [modularBoundedCoefficientPolynomial_selected h slot hinj fixed c, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply homogeneousComponent_eq_self
  exact isHomogeneous_monomial (c a) (hdegree a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem small_coordinate_lift_unique {D : Type*} (f y z : D → ℝ)
    (hy : ∀ d, |y d| < 1 / 2) (hz : ∀ d, |z d| < 1 / 2)
    (hfy : ∀ d, ∃ a : ℤ, f d - y d = a) (hfz : ∀ d, ∃ a : ℤ, f d - z d = a) : y = z := by
  funext d
  obtain ⟨a, ha⟩ := hfy d
  obtain ⟨b, hb⟩ := hfz d
  have hlo : (-1 : ℝ) < (b - a : ℤ) := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).1, (abs_lt.mp (hz d)).2]
  have hhi : ((b - a : ℤ) : ℝ) < 1 := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).2, (abs_lt.mp (hz d)).1]
  have hlo' : (-1 : ℤ) < b - a := by exact_mod_cast hlo
  have hhi' : b - a < (1 : ℤ) := by exact_mod_cast hhi
  have he : b = a := by omega
  rw [he] at hb
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

noncomputable def integerPolynomialCoordinatePMF (j : J) : PMF ℤ := by
  classical
  exact if j = j₀ then constantIntegerPMF K ρ (by exact_mod_cast hK) hρ
    else if j ∈ P then integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap
    else integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL (e j) (he j)

local notation "laws" => integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
  ρ γ ε hρ hγ hε hgap hεL

omit [Fintype J] in
theorem integerPolynomialCoordinatePMF_bound (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (j : J) {k : ℤ} (hk : k ∈ (laws j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤
      |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, abs_zero, zero_add]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_bound hh hK hL hγ hgap hk
      rw [hprincipal j hp]
      have hpos : 0 ≤ 3 * γ / 2 := by positivity
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_of_nonneg hpos]
      linarith
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_zero, zero_add]
      linarith

theorem integerPolynomialCoordinatePMF_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  apply (monomialArrayPolynomial_box_budget e (fun j => (a j : ℝ) / K)
    (fun j => |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j) T x hx
    (fun j => integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL hj₀ he₀ hprincipal j (ha j))).trans
  exact coefficientProfile_budget P j₀ hj₀ hγ.le hε.le

end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineProbabilityProfile_scaled_support {c w S x : ℝ} (hw : 0 < w) (hS : 0 < S)
    (hx : affineProbabilityProfile (c / S) (w / S) x ≠ 0) :
    |x * S - c| < 3 * w / 4 := by
  have hb := mul_lt_mul_of_pos_right
    (affineProbabilityProfile_support (c / S) (div_pos hw hS) hx) hS
  have hl : |x - c / S| * S = |x * S - c| := by
    calc
      _ = |(x - c / S) * S| := by rw [abs_mul, abs_of_pos hS]
      _ = _ := by rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  have hr : 3 * (w / S) / 4 * S = 3 * w / 4 := by field_simp
  rwa [hl, hr] at hb

noncomputable def scaledCoefficientDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (c w : J → ℝ) : (J → ℝ) → ℝ :=
  affineProductProfile (fun j => c j / monomialScale T (e j))
    (fun j => w j / monomialScale T (e j))

theorem scaledCoefficientDensity_support {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j * monomialScale T (e j) - c j| < 3 * w j / 4 := by
  classical
  apply affineProbabilityProfile_scaled_support (hw j) (monomialScale_pos T hT (e j))
  exact (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)

theorem scaledCoefficientDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ |c j| + w j := by
  have hb := scaledCoefficientDensity_support e T hT c w hw ha j
  have ht := abs_add_le (a j * monomialScale T (e j) - c j) (c j)
  rw [sub_add_cancel, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))] at ht
  linarith [hw j]

theorem scaledCoefficientDensity_box_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, (|c j| + w j) :=
  monomialArrayPolynomial_box_budget e a _ T x hx
    (scaledCoefficientDensity_coefficient_bound e T hT c w hw ha)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ContinuousPolynomialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def continuousPolynomialDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (P : Finset J) (j₀ : J) (R σ : ℝ) : (J → ℝ) → ℝ :=
  scaledCoefficientDensity e T (coefficientProfileCenter P (principalProfileSize R P.card))
    (coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)))

theorem continuousPolynomialDensity_width_pos {J : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (j : J) :
    0 < coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)) j :=
  coefficientProfileWidth_pos P j₀ (by positivity) (principalProfileSize_pos hR _)
    (tailProfileSize_pos hR hσ _) j

theorem continuousPolynomialDensity_box {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ 3 * R / 4 := by
  have hb := scaledCoefficientDensity_box_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha x hx
  exact hb.trans ((coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)

variable (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ (tailProfileSize R σ (Fintype.card J)) * L)

noncomputable def allocatedIntegerPolynomialCoordinatePMF : J → PMF ℤ :=
  integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _) hgap hεL

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerPolynomial_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_box P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J)) (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal a ha x hx
  exact hb.trans (allocatedProfile_budget hR.le hσ1 _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedArraySupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem allocatedProfile_term_bound {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (j : J) :
    |coefficientProfileCenter P (principalProfileSize R P.card) j| +
      coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
        (tailProfileSize R σ (Fintype.card J)) j ≤ 3 * R / 4 := by
  classical
  apply (Finset.single_le_sum (s := Finset.univ)
    (fun i _ => add_nonneg (abs_nonneg _) (continuousPolynomialDensity_width_pos P j₀ hR hσ i).le)
    (Finset.mem_univ j)).trans
  exact (coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _)

theorem allocatedIntegerCoefficient_bound {J V : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (j : J) {k : ℤ}
    (hk : k ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal j hk
  exact hb.trans (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeSupportPermutation
namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreeSupportModule (P : SquarefreeIndex ι → Prop) :
    Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a, ¬P a → squarefreePolynomialEquiv x a = 0}
  zero_mem' := by
    intro a _
    exact congrFun (map_zero squarefreePolynomialEquiv) a
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [map_smul, Pi.smul_apply, hx a ha, smul_zero]

theorem squarefreeMonomial_mem_support {P : SquarefreeIndex ι → Prop}
    (a : SquarefreeIndex ι) (ha : P a) (v : L) :
    squarefreeMonomial a v ∈ squarefreeSupportModule P := by
  intro b hb
  exact squarefreePolynomialEquiv_monomial_ne a b
    (fun he => hb (he ▸ ha)) v

end Erdos3

end

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure DegreeRankLieFiltration (s r : ℕ) where
  rank_le_degree : r ≤ s
  layer : ℕ → ℕ → Submodule ℚ L
  lex_antitone : ∀ {d e i j}, d < e ∨ d = e ∧ i ≤ j → layer e j ≤ layer d i
  one_eq_top : layer 1 0 = ⊤
  rank_zero_eq_one : ∀ d, layer d 0 = layer d 1
  overshoot : ∀ d i, d < i → layer d i = layer (d + 1) 0
  lie_mem : ∀ {d e i j} {x y : L}, x ∈ layer d i → y ∈ layer e j →
    ⁅x, y⁆ ∈ layer (d + e) (i + j)
  terminal : layer s (r + 1) = ⊥

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem degree_antitone (i : ℕ) : Antitone (fun d => F.layer d i) := by
  intro d e hde
  rcases lt_or_eq_of_le hde with h | rfl
  · exact F.lex_antitone (Or.inl h)
  · exact le_rfl

theorem rank_antitone (d : ℕ) : Antitone (F.layer d) := by
  intro i j hij
  exact F.lex_antitone (Or.inr ⟨rfl, hij⟩)

theorem zero_eq_top : F.layer 0 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.degree_antitone 0 (by omega)

theorem layer_eq_bot_of_past_top {d i : ℕ} (h : s < d ∨ s = d ∧ r < i) :
    F.layer d i = ⊥ := by
  apply bot_unique
  apply le_trans (b := F.layer s (r + 1))
  · apply F.lex_antitone
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
  · exact F.terminal.le

def associatedDegree : NilpotentLieFiltration L s where
  layer d := F.layer d 0
  antitone := F.degree_antitone 0
  one_eq_top := F.one_eq_top
  lie_mem hx hy := F.lie_mem hx hy
  terminal := F.layer_eq_bot_of_past_top (Or.inl (by omega))

@[simp] theorem associatedDegree_layer (d : ℕ) : F.associatedDegree.layer d = F.layer d 0 := rfl

theorem layer_le_associatedDegree (d i : ℕ) : F.layer d i ≤ F.associatedDegree.layer d :=
  F.rank_antitone d (Nat.zero_le i)

end DegreeRankLieFiltration

namespace NilpotentLieFiltration

variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)

def canonicalDegreeRank : DegreeRankLieFiltration L s s where
  rank_le_degree := le_rfl
  layer := F.rankLayer
  lex_antitone := F.rankLayer_lex_antitone
  one_eq_top := by rw [F.rankLayer_zero, F.one_eq_top]
  rank_zero_eq_one d := by rw [F.rankLayer_zero, F.rankLayer_one]
  overshoot d i h := by rw [F.rankLayer_eq_next_of_degree_lt_rank h, F.rankLayer_zero]
  lie_mem := F.rankLayer_lie_mem
  terminal := F.rankLayer_top_terminal (s + 1) (by omega)

@[simp] theorem canonicalDegreeRank_associatedDegree_layer (d : ℕ) :
    F.canonicalDegreeRank.associatedDegree.layer d = F.layer d := F.rankLayer_zero d

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {ι : Type*} [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ}

def pi (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    DegreeRankLieFiltration (∀ i, L i) s r where
  rank_le_degree := (F (Classical.choice inferInstance)).rank_le_degree
  layer d j := Submodule.pi Set.univ (fun i => (F i).layer d j)
  lex_antitone h := Submodule.pi_mono (fun i _ => (F i).lex_antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  rank_zero_eq_one d := by simp only [rank_zero_eq_one]
  overshoot d j h := congrArg (Submodule.pi Set.univ)
    (funext (fun i => (F i).overshoot d j h))
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ i, DegreeRankLieFiltration (L i) s r)
    (d j : ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer d j ↔ ∀ i, x i ∈ (F i).layer d j := by
  simp [pi, Submodule.mem_pi]

theorem pi_associatedDegree (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    (pi F).associatedDegree = NilpotentLieFiltration.pi (fun i => (F i).associatedDegree) := rfl

def piLayerEquiv (F : ∀ i, DegreeRankLieFiltration (L i) s r) (d j : ℕ) :
    (∀ i, (F i).layer d j) ≃ₗ[ℚ] (pi F).layer d j where
  toFun x := ⟨fun i => x i, (mem_pi_layer F d j _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F d j _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def rankFlag (n : ℕ) : Submodule ℚ L := F.layer (n / (s + 1)) (n % (s + 1))

theorem rankFlag_antitone : Antitone F.rankFlag := by
  intro i j hij
  have hd : i / (s + 1) ≤ j / (s + 1) := Nat.div_le_div_right hij
  rcases lt_or_eq_of_le hd with h | h
  · exact F.lex_antitone (Or.inl h)
  · apply F.lex_antitone (Or.inr ⟨h, ?_⟩)
    have hi := Nat.mod_add_div i (s + 1)
    have hj := Nat.mod_add_div j (s + 1)
    rw [h] at hi
    omega

@[simp] theorem rankFlag_zero : F.rankFlag 0 = ⊤ := by
  simpa only [rankFlag, Nat.zero_div, Nat.zero_mod] using F.zero_eq_top

theorem rankFlag_mul (d : ℕ) : F.rankFlag (d * (s + 1)) = F.layer d 0 := by
  simp [rankFlag, Nat.mul_mod_left]

theorem rankFlag_terminal : F.rankFlag ((s + 1) * (s + 1)) = ⊥ := by
  rw [F.rankFlag_mul]
  exact F.layer_eq_bot_of_past_top (Or.inl (by omega))

theorem rankFlag_lie_mem {n : ℕ} {x y : L} (hy : y ∈ F.rankFlag n) :
    ⁅x, y⁆ ∈ F.rankFlag (n + 1) := by
  have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hbr : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) (n % (s + 1)) := by
    simpa only [add_comm 1, zero_add] using F.lie_mem hx hy
  have hzero : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) 0 :=
    F.rank_antitone _ (Nat.zero_le _) hbr
  rw [← F.rankFlag_mul] at hzero
  apply F.rankFlag_antitone _ hzero
  have hmod : n % (s + 1) < s + 1 := Nat.mod_lt n (by omega)
  have heq := Nat.mod_add_div n (s + 1)
  rw [add_mul, one_mul, Nat.mul_comm (n / (s + 1)) (s + 1)]
  omega

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (F : NilpotentLieFiltration L s) (G : DegreeRankLieFiltration M t r)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ d, ∀ x ∈ F.layer d, φ x ∈ G.layer d 0)

include hφ in
theorem FilteredLieTree.map_eval_mem_degreeRank {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ G.layer d k := by
  induction a with
  | leaf hd x hx =>
    rw [FilteredLieTree.eval_leaf, ← G.rank_zero_eq_one]
    exact hφ _ x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact G.lie_mem ha hb

include hφ in
theorem NilpotentLieFiltration.map_rankLayer {d k : ℕ} {x : L}
    (hx : x ∈ F.rankLayer d k) : φ x ∈ G.layer d k := by
  have hle : F.rankLayer d k ≤ (G.layer d k).comap φ.toLinearMap := by
    apply sup_le
    · intro y hy
      exact G.lex_antitone (Or.inl (Nat.lt_succ_self d)) (hφ (d + 1) y hy)
    · apply Submodule.span_le.mpr
      rintro y ⟨n, hn, a, rfl⟩
      exact G.rank_antitone d hn (a.map_eval_mem_degreeRank F G φ hφ)
  exact hle hx

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def rankSubgroup (d r : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.rankIdeal d r).toLieSubalgebra

@[simp] theorem mem_rankSubgroup (d r : ℕ) (x : F.Group) :
    x ∈ F.rankSubgroup d r ↔ x.coord ∈ F.rankLayer d r := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def polynomialFiltration : DegreeRankLieFiltration (VectorPolynomial σ ℚ L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := coefficientSubmodule (F.layer d i)
  lex_antitone := fun h _ hp α => F.lex_antitone h (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    rw [F.one_eq_top]
    trivial
  rank_zero_eq_one d := by rw [F.rank_zero_eq_one]
  overshoot d i hi := by rw [F.overshoot d i hi]
  lie_mem := by
    intro d e i j p q hp hq
    apply (eval_mem_iff_coefficients (F.layer (d + e) (i + j)) ⁅p, q⁆).mp
    intro t
    have hp' := (eval_mem_iff_coefficients (F.layer d i) p).mpr hp t
    have hq' := (eval_mem_iff_coefficients (F.layer e j) q).mpr hq t
    change evalLie t ⁅p, q⁆ ∈ F.layer (d + e) (i + j)
    rw [LieHom.map_lie]
    exact F.lie_mem hp' hq'
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using hp α

@[simp] theorem polynomialFiltration_layer (d i : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer d i = coefficientSubmodule (F.layer d i) := rfl

theorem monomial_mem_polynomialFiltration (d i : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ F.layer d i) :
    monomial (R := ℚ) α x ∈ (F.polynomialFiltration (σ := σ)).layer d i :=
  monomial_mem_coefficientSubmodule (F.layer d i) α hx

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem lieTreeEval_mem_length (v : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight d a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem lieTreeEval_sub_mem (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I) :
    lieTreeEval v a - lieTreeEval w a ∈
      F.layer (lieTreeWeight d a) (a.length + 1) := by
  induction a using FreeMagma.rec with
  | of i => exact hvw i
  | mul a b ha hb =>
    have h₁ := F.lie_mem ha (F.lieTreeEval_mem_length v d hv b)
    have h₂ := F.lie_mem (F.lieTreeEval_mem_length w d hw a) hb
    have heq : lieTreeEval v (a.mul b) - lieTreeEval w (a.mul b) =
        ⁅lieTreeEval v a - lieTreeEval w a, lieTreeEval v b⁆ +
          ⁅lieTreeEval w a, lieTreeEval v b - lieTreeEval w b⁆ := by
      simp only [lieTreeEval, sub_lie, lie_sub]
      abel
    rw [heq]
    apply Submodule.add_mem
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h₁
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc] using h₂

theorem top_lieTreeEval_congr (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) :
    lieTreeEval v a = lieTreeEval w a := by
  have h := F.lieTreeEval_sub_mem v w d hv hw hvw a
  rw [hd, hr, F.terminal, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankFlag_encode (i j : ℕ) (hj : j ≤ s) :
    F.rankFlag (i * (s + 1) + j) = F.layer i j := by
  have hA : 0 < s + 1 := by omega
  have hjA : j < s + 1 := by omega
  unfold rankFlag
  rw [Nat.mul_comm i (s + 1), Nat.mul_add_div hA, Nat.div_eq_of_lt hjA,
    add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hjA]

theorem rankFlag_encode_lt (i j : ℕ) (hi : i ≤ s) (hj : j ≤ s) :
    i * (s + 1) + j < (s + 1) * (s + 1) := by
  have h := Nat.mul_le_mul_right (s + 1) hi
  nlinarith

theorem rankFlag_decode_lt {k : ℕ} (hk : k < (s + 1) * (s + 1)) :
    k / (s + 1) ≤ s ∧ k % (s + 1) ≤ s := by
  have hA : 0 < s + 1 := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul hA).mpr hk
  have hmod : k % (s + 1) < s + 1 := Nat.mod_lt k hA
  omega

theorem layer_eq_rankFlag (i j : ℕ) :
    ∃ k : Fin ((s + 1) * (s + 1) + 1), F.layer i j = F.rankFlag k.val := by
  by_cases hi : i ≤ s
  · by_cases hj : j ≤ s
    · exact ⟨⟨i * (s + 1) + j, by have := rankFlag_encode_lt i j hi hj; omega⟩,
        (F.rankFlag_encode i j hj).symm⟩
    · rw [F.overshoot i j (by omega)]
      refine ⟨⟨(i + 1) * (s + 1), ?_⟩, (F.rankFlag_mul (i + 1)).symm⟩
      have h := Nat.mul_le_mul_right (s + 1) (show i + 1 ≤ s + 1 by omega)
      omega
  · refine ⟨⟨(s + 1) * (s + 1), by omega⟩, ?_⟩
    rw [F.rankFlag_terminal, F.layer_eq_bot_of_past_top (Or.inl (by omega))]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalKernel (i : ℕ) : Submodule ℚ (F.layer i 1) :=
  (F.layer i 2).comap (F.layer i 1).subtype

abbrev HigherHorizontal (i : ℕ) := (F.layer i 1) ⧸ F.higherHorizontalKernel i

def higherHorizontalMk (i : ℕ) : F.layer i 1 →ₗ[ℚ] F.HigherHorizontal i :=
  (F.higherHorizontalKernel i).mkQ

theorem higherHorizontalMk_eq (i : ℕ) (x y : F.layer i 1) :
    F.higherHorizontalMk i x = F.higherHorizontalMk i y ↔ x.val - y.val ∈ F.layer i 2 :=
  Submodule.Quotient.eq (F.higherHorizontalKernel i)

theorem higherHorizontalMk_surjective (i : ℕ) : Function.Surjective (F.higherHorizontalMk i) :=
  (F.higherHorizontalKernel i).mkQ_surjective

noncomputable def higherHorizontalRepresentative (i : ℕ) (v : F.HigherHorizontal i) : F.layer i 1 := by
  classical
  exact if v = 0 then 0 else Classical.choose (F.higherHorizontalMk_surjective i v)

@[simp] theorem higherHorizontalRepresentative_zero (i : ℕ) :
    F.higherHorizontalRepresentative i 0 = 0 := by
  classical
  simp [higherHorizontalRepresentative]

theorem higherHorizontalMk_representative (i : ℕ) (v : F.HigherHorizontal i) :
    F.higherHorizontalMk i (F.higherHorizontalRepresentative i v) = v := by
  classical
  by_cases hv : v = 0
  · simp [higherHorizontalRepresentative, hv]
  · simpa [higherHorizontalRepresentative, hv] using
      Classical.choose_spec (F.higherHorizontalMk_surjective i v)

noncomputable def horizontalTreeValue (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) : L :=
  lieTreeEval (fun i => (F.higherHorizontalRepresentative (d i) (v i)).val) a

theorem horizontalTreeValue_mk (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) (v : ∀ i, F.layer (d i) 1) :
    F.horizontalTreeValue d a (fun i => F.higherHorizontalMk (d i) (v i)) =
      lieTreeEval (fun i => (v i).val) a := by
  apply F.top_lieTreeEval_congr _ _ d
    (fun i => (F.higherHorizontalRepresentative (d i) (F.higherHorizontalMk (d i) (v i))).property)
    (fun i => (v i).property) _ a hd hr
  intro i
  exact (F.higherHorizontalMk_eq (d i) _ _).mp (F.higherHorizontalMk_representative _ _)

theorem horizontalTreeValue_zero_of_leaf (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) {i : I} (hi : i ∈ lieTreeSupport a)
    (hv : v i = 0) : F.horizontalTreeValue d a v = 0 := by
  apply lieTreeEval_eq_zero_of_leaf _ a hi
  simp only [hv, higherHorizontalRepresentative_zero, ZeroMemClass.coe_zero]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def fourHorizontalLayer (d : ℕ) : Submodule ℚ (Fin 4 → L) :=
  Submodule.pi Set.univ (fun _ => F.layer d 1)

theorem mem_fourHorizontalLayer (d : ℕ) (v : Fin 4 → L) :
    v ∈ F.fourHorizontalLayer d ↔ ∀ k, v k ∈ F.layer d 1 := by
  simp [fourHorizontalLayer, Submodule.mem_pi]

def fourHorizontalMap (d : ℕ) : F.fourHorizontalLayer d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) where
  toFun v k := F.higherHorizontalMk d ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
  map_add' x y := by
    funext k
    exact map_add (F.higherHorizontalMk d)
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩
      ⟨y.val k, (F.mem_fourHorizontalLayer d y.val).mp y.property k⟩
  map_smul' c x := by
    funext k
    exact map_smul (F.higherHorizontalMk d) c
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L E : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup E] [Module ℚ E]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSquarefreeCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def realSquarefreePolynomialEquiv :
    (ℝ ⊗[ℚ] SquarefreePolynomial ι L) ≃ₗ[ℝ] (SquarefreeIndex ι → ℝ ⊗[ℚ] L) := by
  classical
  exact ((squarefreePolynomialEquiv (ι := ι) (L := L)).baseChange ℚ ℝ _ _).trans
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : SquarefreeIndex ι => L))

theorem realSquarefreePolynomialEquiv_tmul (r : ℝ) (x : SquarefreePolynomial ι L)
    (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (r ⊗ₜ[ℚ] x) c = r ⊗ₜ[ℚ] squarefreePolynomialEquiv x c := rfl

theorem realSquarefreeMonomial_self (a : SquarefreeIndex ι) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) a = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_self]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realSquarefreeMonomial_ne (a c : SquarefreeIndex ι) (hac : a ≠ c) (x : ℝ ⊗[ℚ] L) :
    realSquarefreePolynomialEquiv ((squarefreeMonomial a).baseChange ℝ x) c = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      squarefreePolynomialEquiv_monomial_ne a c hac, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DegreeRankBCH
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def layerIdeal (d i : ℕ) : LieIdeal ℚ L :=
  { F.layer d i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
      exact F.lex_antitone (Or.inl (show d < 1 + d by omega)) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (d i : ℕ) (x : L) :
    x ∈ F.layerIdeal d i ↔ x ∈ F.layer d i := Iff.rfl

abbrev Group := F.associatedDegree.Group

def subgroup (d i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal d i).toLieSubalgebra

@[simp] theorem mem_subgroup (d i : ℕ) (x : F.Group) :
    x ∈ F.subgroup d i ↔ x.coord ∈ F.layer d i := Iff.rfl

theorem subgroup_le_associatedDegree (d i : ℕ) : F.subgroup d i ≤ F.associatedDegree.subgroup d :=
  fun _ hx => F.layer_le_associatedDegree d i hx

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalRankCompatibility
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem eq_of_layer_eq {F G : NilpotentLieFiltration L s} (h : F.layer = G.layer) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (F : NilpotentLieFiltration L s)

theorem canonicalDegreeRank_associatedDegree_eq : F.canonicalDegreeRank.associatedDegree = F :=
  eq_of_layer_eq (funext F.canonicalDegreeRank_associatedDegree_layer)

noncomputable def orbitEquivOfEq {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) : F.PolynomialOrbit w ≃* G.PolynomialOrbit w := by
  subst G
  exact MulEquiv.refl _

theorem orbitEquivOfEq_eval {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) (g : F.PolynomialOrbit w) (x : σ → ℤ) :
    G.polynomialOrbitEval w x (F.orbitEquivOfEq h w g) = F.polynomialOrbitEval w x g := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedTranslation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) : F.Adapted w (translate h p) := by
  apply (F.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact (polynomialTranslate_monomial_bounds h w hw β).1 (MvPolynomial.mem_support_iff.mpr hc)

theorem translate_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  rw [coefficients_translate_sub]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1) -
      MvPolynomial.monomial β 1).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h w hw β).2
      (MvPolynomial.mem_support_iff.mpr hc))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedAdaptedIdeal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + k)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' r p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem r (hp α)

theorem monomial_mem_shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ)
    (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer (Finsupp.weight w α + k)) :
    monomial (R := ℚ) α a ∈ F.shiftedAdaptedSubmodule w k := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_shiftedAdaptedSubmodule (w : σ → ℕ) {i j : ℕ}
    {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    ⁅p, q⁆ ∈ F.shiftedAdaptedSubmodule w (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem (hp α) (hq β)

noncomputable def shiftedAdaptedIdeal (w : σ → ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w 1).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : (p : VectorPolynomial σ ℚ L) ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      exact F.lie_mem_shiftedAdaptedSubmodule w hp hq }

theorem adapted_constant (w : σ → ℕ) (a : L) : F.Adapted w (monomial 0 a) := by
  apply (F.mem_adaptedSubmodule w _).mp
  apply F.monomial_mem_adaptedSubmodule
  rw [map_zero]
  apply F.antitone (Nat.zero_le 1)
  rw [F.one_eq_top]
  trivial

noncomputable def adaptedConstant (w : σ → ℕ) (a : L) : F.adaptedLieSubalgebra w :=
  ⟨monomial 0 a, (F.mem_adaptedSubmodule w _).mpr (F.adapted_constant w a)⟩

theorem adaptedConstant_mem_shiftedIdeal (w : σ → ℕ) (a : L) :
    F.adaptedConstant w a ∈ F.shiftedAdaptedIdeal w := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simp only [map_zero, Nat.zero_add, F.one_eq_top, Submodule.mem_top]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LinearBCHAbelian
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem linearMap_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    f (lieBCH s a b) = f a + f b := by
  let : LieRing V := {
    toAddCommGroup := inferInstance
    bracket := fun _ _ => 0
    add_lie := fun _ _ _ => (add_zero 0).symm
    lie_add := fun _ _ _ => (add_zero 0).symm
    lie_self := fun _ => rfl
    leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  let : LieAlgebra ℚ V := {
    toModule := inferInstance
    lie_smul := fun t _ _ => (smul_zero t).symm }
  let : IsLieAbelian V := ⟨fun _ _ => rfl⟩
  let φ : L →ₗ⁅ℚ⁆ V := { f with map_lie' := fun {x y} => hf x y }
  exact (map_lieBCH φ s a b).trans (lieBCH_eq_add_of_isLieAbelian hs (f a) (f b))

theorem linearMap_baseChange_lie_eq_zero {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ ⁅a, b⁆ = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.baseChange_tmul, hf,
        TensorProduct.tmul_zero]
    | add b c hb hc => rw [lie_add, map_add, hb, hc, add_zero]
  | add a b ha hb => rw [add_lie, map_add, ha, hb, add_zero]

theorem linearMap_baseChange_lieBCH_eq_add {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ (lieBCH s a b) = f.baseChange ℝ a + f.baseChange ℝ b :=
  linearMap_lieBCH_eq_add ((f.baseChange ℝ).restrictScalars ℚ)
    (linearMap_baseChange_lie_eq_zero f hf) hs a b

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DilationPairPolynomial
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ (L × L) := pair (weightedDilation w q p) p

@[simp] theorem coefficients_dilationPair (w : σ → ℕ) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a =
      (q ^ Finsupp.weight w a • coefficients p a, coefficients p a) := by
  simp only [dilationPair, coefficients_pair, coefficients_weightedDilation]

theorem eval_dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (dilationPair w q p) = (eval (fun i => q ^ w i * x i) p, eval x p) := by
  simp only [dilationPair, eval_pair, eval_weightedDilation]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients (w : σ → ℕ) (q : ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a ∈ F.dilationPairLayer q (Finsupp.weight w a) := by
  rw [coefficients_dilationPair, F.mem_dilationPairLayer]
  have ha := (F.adapted_iff_coefficients w p).mp hp a
  exact ⟨(F.layer _).smul_mem _ ha, ha, by simp⟩

end NilpotentLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorHomogenization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem homogeneous_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, Homogeneous h (p a)) : Homogeneous h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

noncomputable def homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) : VectorPolynomial I R W →ₗ[R] VectorPolynomial (Option I) R W :=
  (Finsupp.lsum R (fun d => TensorProduct.mk R (MvPolynomial (Option I) R) W
    (homogenizingMonomial h d))).comp coefficients.toLinearMap

theorem homogenize_apply {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    homogenize h p = ∑ d ∈ (coefficients p).support,
      homogenizingMonomial h d ⊗ₜ[R] coefficients p d := by
  simp only [homogenize, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsum_apply,
    Finsupp.sum, TensorProduct.mk_apply]

theorem dehomogenize_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) :
    substitute dehomogenizingSubstitution (homogenize h p) = p := by
  rw [homogenize_apply, map_sum]
  simp only [substitute_tmul, homogenizingMonomial_dehomogenize]
  exact sum_monomial_coefficients p

theorem homogenize_homogeneous {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    Homogeneous h (homogenize h p) := by
  rw [homogenize_apply]
  apply homogeneous_finset_sum
  intro d hd
  have hb : d.degree ≤ h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact homogeneous_tmul (homogenizingMonomial_homogeneous h d hb) _

theorem eval_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (x : I → R) :
    eval (fun i : Option I => i.elim 1 x) (homogenize h p) = eval x p := by
  have he := congrArg (eval x) (dehomogenize_homogenize h p)
  rw [eval_substitute] at he
  convert he using 1
  apply congrArg (fun y => eval y (homogenize h p))
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationTopDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {X R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_translate_mem (U : Submodule R V) (a : X → R)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (translate a p) d ∈ U := by
  rw [coefficients_translate]
  exact Submodule.sum_mem U (fun b _ => U.smul_mem _ (hp b))

theorem coefficients_translate_sub_eq_zero_of_degreeLE
    (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p)
    (d : X →₀ ℕ) (hd : n ≤ Finsupp.weight w d) :
    coefficients (translate a p - p) d = 0 := by
  classical
  rw [coefficients_translate_sub]
  apply Finset.sum_eq_zero
  intro b hb
  have hbdeg := (degreeLE_iff w n p).mp hp b hb
  have hc : (polynomialTranslate a (MvPolynomial.monomial b 1) -
      MvPolynomial.monomial b 1).coeff d = 0 := by
    by_contra hne
    have hlt := (polynomialTranslate_monomial_bounds a w hw b).2
      (MvPolynomial.mem_support_iff.mpr hne)
    exact (not_lt_of_ge (hbdeg.trans hd)) hlt
  rw [hc, zero_smul]

theorem degreeLE_translate (w : X → ℕ) (hw : ∀ i, 0 < w i) (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE w n p) :
    DegreeLE w n (translate a p) := by
  intro d hd
  have h := coefficients_translate_sub_eq_zero_of_degreeLE w hw a p hp d hd.le
  simpa only [map_sub, Finsupp.sub_apply, hp d hd, sub_zero] using h

theorem homogeneousPart_translate (a : X → R) {n : ℕ}
    (p : VectorPolynomial X R V) (hp : DegreeLE (1 : X → ℕ) n p) :
    homogeneousPart n (translate a p) = homogeneousPart n p := by
  classical
  apply coefficients.injective
  ext d
  simp only [coefficients_homogeneousPart]
  split
  · rename_i hd
    have hdw : n ≤ Finsupp.weight (1 : X → ℕ) d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd.ge
    have h := coefficients_translate_sub_eq_zero_of_degreeLE (1 : X → ℕ)
      (fun _ => by norm_num) a p hp d hdw
    simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using h
  · rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorCoefficientScaling
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem DegreeLE.smul {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {w : I → ℕ} {d : ℕ} {p : VectorPolynomial I ℝ V}
    (hp : DegreeLE w d p) (r : ℝ) : DegreeLE w d (r • p) := by
  intro α hα
  simp only [map_smul, Finsupp.smul_apply, hp α hα, smul_zero]

theorem coefficients_smul_mem {I J : Type*} (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) (hm : ∀ d, coefficients p d ∈ U) (r : ℝ) :
    ∀ d, coefficients (r • p) d ∈ U := by
  intro d
  simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem r (hm d)

theorem integerRowPolynomial_smul {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (r : ℝ) :
    integerRowPolynomial a (r • p) = r • integerRowPolynomial a p := by
  ext α
  simp only [integerRowPolynomial_coeff, MvPolynomial.coeff_smul, map_smul,
    Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem degreeLE_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (weight : I → ℕ) (h : ℕ) (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, DegreeLE weight h (p a)) : DegreeLE weight h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

theorem degreeLE_tmul_totalDegree {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (P : MvPolynomial I R) (w : W) {h : ℕ} (hP : P.totalDegree ≤ h) :
    DegreeLE (1 : I → ℕ) h (P ⊗ₜ[R] w) := by
  intro d hd
  have hsum : h < ∑ i ∈ d.support, d i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_def, smul_eq_mul, mul_one] using hd
  rw [coefficients_tmul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hP.trans_lt hsum), zero_smul]

theorem degreeLE_substitute_affine {I K R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (f : I → MvPolynomial K R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute f p) := by
  classical
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply degreeLE_finset_sum
  intro d hd
  rw [monomial, substitute_tmul]
  apply degreeLE_tmul_totalDegree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  simpa only [Nat.mul_one] using aeval_polynomial_totalDegree_le (MvPolynomial.monomial d (1 : R)) f
    ((MvPolynomial.totalDegree_monomial_le d 1).trans hb) hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DehomogenizedExponent
namespace OAI

section

namespace Erdos3

theorem some_degree_le {K : Type*} [Fintype K] (d : Option K →₀ ℕ) :
    d.some.degree ≤ d.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_option]
  simp only [Finsupp.some_apply]
  omega

theorem dehomogenize_monomial {K R : Type*} [CommRing R]
    (d : Option K →₀ ℕ) (c : R) :
    MvPolynomial.aeval dehomogenizingSubstitution (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d.some c := by
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_option_index d _ (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  simp only [dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.algebraMap_eq]
  exact MvPolynomial.monomial_eq.symm

theorem VectorPolynomial.dehomogenize_monomial {K R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (d : Option K →₀ ℕ) (w : W) :
    VectorPolynomial.substitute dehomogenizingSubstitution (VectorPolynomial.monomial (R := R) d w) =
      VectorPolynomial.monomial (R := R) d.some w := by
  simp only [VectorPolynomial.monomial, VectorPolynomial.substitute_tmul, Erdos3.dehomogenize_monomial]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PositiveIntegerPeriodization
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def positiveIntegerPeriodization (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, H (fun i => x i + (n i : ℝ))

omit [Fintype D] in
theorem integer_shifts_small_box_injective (x : D → ℝ) (n m : D → ℤ)
    (hn : ∀ i, |x i + (n i : ℝ)| < 1/2) (hm : ∀ i, |x i + (m i : ℝ)| < 1/2) : n = m := by
  have he := small_coordinate_lift_unique x (fun i => x i + (n i : ℝ))
    (fun i => x i + (m i : ℝ)) hn hm
    (fun i => ⟨-n i, by push_cast; ring⟩) (fun i => ⟨-m i, by push_cast; ring⟩)
  funext i
  apply Int.cast_injective (α := ℝ)
  have hi := congrFun he i
  linarith

omit [Fintype D] in
theorem positiveIntegerPeriodization_periodic (H : (D → ℝ) → ℝ) (x : D → ℝ) (m : D → ℤ) :
    positiveIntegerPeriodization H (fun i => x i + (m i : ℝ)) = positiveIntegerPeriodization H x := by
  unfold positiveIntegerPeriodization
  have h := (Equiv.addRight m).tsum_eq (fun n : D → ℤ => H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  funext i
  change x i + (m i : ℝ) + (n i : ℝ) = x i + ((n i + m i : ℤ) : ℝ)
  push_cast
  ring

omit [Fintype D] in
theorem positiveIntegerPeriodization_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) :
    positiveIntegerPeriodization H x = H x := by
  unfold positiveIntegerPeriodization
  rw [tsum_eq_single (0 : D → ℤ)]
  · simp
  · intro n hn
    by_contra hnonzero
    apply hn
    exact integer_shifts_small_box_injective x n 0 (hs _ hnonzero) (by simpa using hx)

theorem positiveIntegerPeriodization_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hH : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (positiveIntegerPeriodization H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    exact h
  · intro n x
    exact h0 _
  · intro x n m hn hm
    exact integer_shifts_small_box_injective x n m (hs _ hn) (hs _ hm)

omit [Fintype D] in
theorem positiveIntegerPeriodization_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    0 ≤ positiveIntegerPeriodization H x ∧ positiveIntegerPeriodization H x ≤ B := by
  refine ⟨tsum_nonneg (fun n => (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have he : positiveIntegerPeriodization H x = H (fun i => x i + (n i : ℝ)) := by
      apply tsum_eq_single n
      intro m hm
      by_contra hnonzero
      exact hm (integer_shifts_small_box_injective x m n (hs _ hnonzero) (hs _ hn))
    rw [he]
    exact (hH _).2
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 :=
      fun n => not_ne_iff.mp (fun hn => hx ⟨n, hn⟩)
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
    exact hB

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateProductCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def coordinateJoin {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : D → X :=
  fun d => if h : d = j then x else tail ⟨d,h⟩

@[simp] theorem coordinateJoin_pivot {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : coordinateJoin j tail x j = x := by
  simp [coordinateJoin]

@[simp] theorem coordinateJoin_other {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) (d : {d : D // d ≠ j}) :
    coordinateJoin j tail x d.val = tail d := by
  simp [coordinateJoin, d.property]

theorem coordinateJoin_eta {D X : Type*} [DecidableEq D] (j : D) (z : D → X) :
    coordinateJoin j (fun d => z d.val) (z j) = z := by
  funext d
  by_cases h : d = j <;> simp [coordinateJoin, h]

theorem coordinateJoin_injective {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) : Function.Injective (coordinateJoin j tail) := by
  intro x y h
  simpa only [coordinateJoin_pivot] using congrFun h j

theorem independentProductPMF_coordinate_split {D X : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) :
    independentProductPMF p =
      (independentProductPMF (fun d : {d : D // d ≠ j} => p d.val)).bind
        (fun tail => (p j).map (coordinateJoin j tail)) := by
  ext z
  let tail := fun d : {d : D // d ≠ j} => z d.val
  have hz : coordinateJoin j tail (z j) = z := coordinateJoin_eta j z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (coordinateJoin_injective j tail)]
    simp only [independentProductPMF_apply]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [coordinateJoin_pivot, coordinateJoin_other]
    exact mul_comm _ _
  · intro other hother
    have hr : coordinateJoin j tail (z j) ∉ Set.range (coordinateJoin j other) := by
      rintro ⟨x, he⟩
      apply hother
      funext d
      simpa only [coordinateJoin_other] using congrFun he d.val
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_coordinate_cap {D X Y : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) (f : (D → X) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p j x).toReal ≤ C) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ C := by
  rw [independentProductPMF_coordinate_split p j, PMF.map_bind]
  simp_rw [PMF.map_comp]
  exact pmf_bind_injective_toReal_cap _ _ _ hf hC hp y

theorem shiftedSmoothProductPMF_coordinate_cap {D Y : Type*} [Fintype D] [DecidableEq D]
    (a S : D → ℝ) (hS : ∀ d, 0 < S d) (hZ : 0 < shiftedSmoothProductMass a S)
    (j : D) (f : (D → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ S j) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ 2/S j := by
  rw [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_coordinate_cap _ j f hf (div_nonneg (by norm_num) (hS j).le)
    (fun x => shiftedSmoothCoefficientPMF_le (a j) hscale x) y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HorizontalAmbientQuotient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalAmbient (d : ℕ) : F.HigherHorizontal d →ₗ[ℚ] L ⧸ F.layer d 2 :=
  (F.higherHorizontalKernel d).liftQ
    ((F.layer d 2).mkQ.comp (F.layer d 1).subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero (F.layer d 2)).mpr hx)

@[simp] theorem higherHorizontalAmbient_mk (d : ℕ) (x : F.layer d 1) :
    F.higherHorizontalAmbient d (F.higherHorizontalMk d x) = (F.layer d 2).mkQ x.val := rfl

theorem higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective (F.higherHorizontalAmbient d) := by
  intro x y h
  obtain ⟨x, rfl⟩ := F.higherHorizontalMk_surjective d x
  obtain ⟨y, rfl⟩ := F.higherHorizontalMk_surjective d y
  apply (F.higherHorizontalMk_eq d x y).mpr
  exact (Submodule.Quotient.eq (F.layer d 2)).mp h

theorem real_higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective ((F.higherHorizontalAmbient d).baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (F.higherHorizontalAmbient d) (F.higherHorizontalAmbient_injective d)

def fourHorizontalAmbient (d : ℕ) :
    (Fin 4 → F.HigherHorizontal d) →ₗ[ℚ] (Fin 4 → L ⧸ F.layer d 2) :=
  LinearMap.pi (fun k => (F.higherHorizontalAmbient d).comp (LinearMap.proj k))

@[simp] theorem fourHorizontalAmbient_apply (d : ℕ) (x : Fin 4 → F.HigherHorizontal d) (k : Fin 4) :
    F.fourHorizontalAmbient d x k = F.higherHorizontalAmbient d (x k) := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationExponentialSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem polynomialTranslate_exponentialCoordinate_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  rw [polynomialTranslate_exponentialCoordinate]
  exact polynomialExponentialCoordinate_neg_series_of_nilpotent x hP

theorem polynomialTranslate_exponentialCoordinate_series
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P :=
  polynomialTranslate_exponentialCoordinate_series_of_nilpotent x
    (scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport w hw x hP)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NonprincipalDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) : Finset C := by
  classical
  exact Finset.univ.filter (fun j => e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal)

end Erdos3

end

section

namespace Erdos3

noncomputable def nonprincipalDilation {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) : ℝ := by
  classical
  exact if j ∈ nonprincipalCoefficientSlots e principal then t else 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicProgressionHom
namespace OAI

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

lemma sum_predParam_smul_add (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) (v : Fin Q.rank → G) :
    (∑ j, (Q.predParam x i hi j : ℕ) • v j) + v i = ∑ j, (x j : ℕ) • v j := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ) • v j) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (Q.predParam x i hi j : ℕ) • v j =
      ∑ j ∈ Finset.univ.erase i, (x j : ℕ) • v j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
  have hterm : ((x i : ℕ) - 1) • v i + v i = (x i : ℕ) • v i := by
    simpa only [add_nsmul, one_nsmul] using
      congrArg (fun n : ℕ => n • v i) (Nat.sub_add_cancel hi)
  rw [hrest, Q.predParam_apply_self, add_assoc, hterm]

noncomputable def freimanStep (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (i : Fin Q.rank) : G :=
  if hi : 0 < Q.radius i then L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
  else 0

noncomputable def freimanAffine (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) : G :=
  L (Q.eval Q.minParam) + ∑ i, (x i : ℕ) • Q.freimanStep L i

lemma freimanAffine_pred_add_step (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    Q.freimanAffine L x = Q.freimanAffine L (Q.predParam x i hi) + Q.freimanStep L i := by
  unfold freimanAffine
  rw [add_assoc, Q.sum_predParam_smul_add]

theorem freimanAffine_eq [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanAffine L x = L (Q.eval x) := by
  classical
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hk : k = 0
    · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
      have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
          hsumzero i (Finset.mem_univ i)
      have hx : x = Q.minParam := by
        funext i
        apply Fin.ext
        exact hxzero i
      subst x
      simp [freimanAffine, minParam]
    · have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
      obtain ⟨i, _hiuniv, hi⟩ := hsumpos
      have hradius : 0 < Q.radius i := by
        have hix := (x i).isLt
        change (x i : ℕ) < 2 * Q.radius i + 1 at hix
        omega
      let y := Q.predParam x i hi
      have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) :=
        Q.sum_predParam_add_one x i hi
      have hylt : (∑ j, (y j : ℕ)) < k := by omega
      have ihy : Q.freimanAffine L y = L (Q.eval y) := ih _ hylt y rfl
      have hrel := hadd y (Q.unitParam i hradius) x Q.minParam
        (Q.eval_predParam_add_eval_unitParam x i hi hradius)
      rw [Q.freimanAffine_pred_add_step L x i hi, ihy]
      simp only [freimanStep, dif_pos hradius]
      calc
        L (Q.eval y) + (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
            (L (Q.eval y) + L (Q.eval (Q.unitParam i hradius))) - L (Q.eval Q.minParam) := by abel
        _ = L (Q.eval x) := by rw [hrel, add_sub_cancel_right]

end Erdos3.BohrProgression.CyclicCenteredGAP

end

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

def centerParam (Q : CyclicCenteredGAP N) : Q.Param := fun i => ⟨Q.radius i, by omega⟩

@[simp] lemma eval_centerParam (Q : CyclicCenteredGAP N) : Q.eval Q.centerParam = 0 := by
  simp [eval, coeff, centerParam]

lemma eval_mem_carrier (Q : CyclicCenteredGAP N) (x : Q.Param) : Q.eval x ∈ Q.carrier :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

noncomputable def coefficientBox (Q : CyclicCenteredGAP N) : Finset (Fin Q.rank → ℤ) :=
  Finset.univ.image Q.coeff

lemma mem_coefficientBox (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∃ x : Q.Param, Q.coeff x = z := by
  simp [coefficientBox]

lemma mem_coefficientBox_iff_abs_le (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∀ i, |z i| ≤ (Q.radius i : ℤ) := by
  rw [Q.mem_coefficientBox]
  constructor
  · rintro ⟨x, rfl⟩
    exact Q.coeff_abs_le x
  · intro hz
    let x : Q.Param := fun i => ⟨(z i + Q.radius i).toNat, by
      have hi := abs_le.mp (hz i)
      omega⟩
    refine ⟨x, ?_⟩
    funext i
    have hi := abs_le.mp (hz i)
    dsimp [coeff, x]
    omega

noncomputable def freimanHom (Q : CyclicCenteredGAP N) (L : ZMod N → G) :
    (Fin Q.rank → ℤ) →+ G where
  toFun z := ∑ i, z i • Q.freimanStep L i
  map_zero' := by simp
  map_add' x y := by simp [add_zsmul, Finset.sum_add_distrib]

theorem freimanHom_coeff [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanHom L (Q.coeff x) = L (Q.eval x) := by
  have hx := Q.freimanAffine_eq L hadd x
  have hc := Q.freimanAffine_eq L hadd Q.centerParam
  simp only [freimanAffine, centerParam, eval_centerParam, hzero] at hc
  have heq : Q.freimanHom L (Q.coeff x) =
      (∑ i, (x i : ℕ) • Q.freimanStep L i) -
        ∑ i, Q.radius i • Q.freimanStep L i := by
    change (∑ i, Q.coeff x i • Q.freimanStep L i) = _
    simp only [coeff, sub_zsmul, natCast_zsmul]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq]
  change L (Q.eval Q.minParam) + (∑ i, (x i : ℕ) • Q.freimanStep L i) = _ at hx
  have hbase : L (Q.eval Q.minParam) = -(∑ i, Q.radius i • Q.freimanStep L i) :=
    eq_neg_of_add_eq_zero_left hc
  rw [hbase] at hx
  simpa only [sub_eq_add_neg, add_comm] using hx

theorem freimanHom_injOn [NeZero N] (Q : CyclicCenteredGAP N) (hQ : Q.Proper)
    (L : ZMod N → G) (hL : Set.InjOn L (Q.carrier : Set _)) (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Set.InjOn (Q.freimanHom L) (Q.coefficientBox : Set _) := by
  intro z hz w hw hzw
  obtain ⟨x, rfl⟩ := Q.mem_coefficientBox.mp hz
  obtain ⟨y, rfl⟩ := Q.mem_coefficientBox.mp hw
  rw [Q.freimanHom_coeff L hzero hadd, Q.freimanHom_coeff L hzero hadd] at hzw
  exact congrArg Q.coeff (hQ (hL (Q.eval_mem_carrier x) (Q.eval_mem_carrier y) hzw))

theorem image_freimanHom [NeZero N] [DecidableEq G] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Q.coefficientBox.image (Q.freimanHom L) = Q.carrier.image L := by
  classical
  simp only [coefficientBox, carrier, Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact Q.freimanHom_coeff L hzero hadd x

end Erdos3.BohrProgression.CyclicCenteredGAP

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.VectorPolynomialSupportBracket
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientSupport_lie {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {S T U : Set (σ →₀ ℕ)} (hST : ∀ a ∈ S, ∀ b ∈ T, a + b ∈ U)
    {p q : VectorPolynomial σ R L}
    (hp : p ∈ coefficientSupport S) (hq : q ∈ coefficientSupport T) :
    ⁅p, q⁆ ∈ coefficientSupport U := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply (coefficientSupport U).sum_mem
  intro a ha
  apply (coefficientSupport U).sum_mem
  intro b hb
  rw [lie_monomial]
  apply monomial_mem_coefficientSupport
  apply hST
  · by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  · by_contra h
    exact (Finsupp.mem_support_iff.mp hb) (hq b h)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDownsetQuotients
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (P : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))

noncomputable def restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) : LieIdeal ℚ P :=
  LieIdeal.comap P.incl (outsideDownsetIdeal J hJ)

@[simp] theorem mem_restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (p : P) :
    p ∈ restrictedOutsideDownsetIdeal P J hJ ↔ ∀ a ∈ J, coefficients p.val a = 0 :=
  mem_outsideDownsetIdeal J hJ p.val

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicRelativeChang
namespace OAI

section

noncomputable section

open _root_.Finset Real
open scoped BigOperators ComplexConjugate

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def AddDissociatedMod (S Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ t u : Finset (AddChar G ℂ), t ⊆ Delta → u ⊆ Delta →
    Disjoint t u → (t ∪ u).Nonempty →
      (∑ psi ∈ t, psi) - ∑ psi ∈ u, psi ∉ S

omit [Fintype G] in
theorem addDissociatedMod_empty (S : Finset (AddChar G ℂ)) :
    AddDissociatedMod S ∅ := by
  intro t u ht hu htu hne
  simp only [Finset.subset_empty] at ht hu
  subst t
  subst u
  simp at hne

omit [Fintype G] in
theorem AddDissociatedMod.mono {S : Finset (AddChar G ℂ)}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : AddDissociatedMod S Delta) (hsub : Gamma ⊆ Delta) :
    AddDissociatedMod S Gamma := by
  intro t u ht hu
  exact h t u (ht.trans hsub) (hu.trans hsub)

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod [Finite G]
    (S T : Finset (AddChar G ℂ))
    (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  classical
  let candidates := T.powerset.filter (AddDissociatedMod S)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, addDissociatedMod_empty]
  obtain ⟨Delta, hDelta_mem, hDelta_max⟩ := candidates.exists_maximal hcandidates
  have hDelta := Finset.mem_filter.mp hDelta_mem
  refine ⟨Delta, Finset.mem_powerset.mp hDelta.1, hDelta.2, ?_⟩
  intro psi hpsiT
  by_cases hpsiDelta : psi ∈ Delta
  · exact ⟨psi, Finset.subset_addSpan hpsiDelta, 0, hzero, by simp⟩
  · have hinsert_subset : insert psi Delta ⊆ T :=
      Finset.insert_subset hpsiT (Finset.mem_powerset.mp hDelta.1)
    have hnot : ¬ AddDissociatedMod S (insert psi Delta) := by
      intro hins
      have hinsert_mem : insert psi Delta ∈ candidates := by
        simp [candidates, hinsert_subset, hins]
      have hsub := hDelta_max hinsert_mem (Finset.subset_insert psi Delta)
      exact hpsiDelta (hsub (Finset.mem_insert_self psi Delta))
    rw [AddDissociatedMod] at hnot
    push Not at hnot
    obtain ⟨t, u, ht, hu, htu, hne, hsumS⟩ := hnot
    have hpsi_tu : psi ∈ t ∪ u := by
      by_contra hpsi
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_left u ha))
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_right t ha))
      exact hDelta.2 t u htDelta huDelta htu hne hsumS
    rw [Finset.mem_union] at hpsi_tu
    rcases hpsi_tu with hpsi_t | hpsi_u
    · have hpsi_not_u : psi ∉ u := fun h ↦ Finset.disjoint_left.mp htu hpsi_t h
      have htErase : t.erase psi ⊆ Delta := by
        intro a ha
        have ha' := ht (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_u (h ▸ ha))
      let z := (∑ a ∈ u, a) - ∑ a ∈ t.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan huDelta htErase
      refine ⟨z, hz, (∑ a ∈ t, a) - ∑ a ∈ u, a, hsumS, ?_⟩
      dsimp [z]
      rw [← Finset.sum_erase_add _ _ hpsi_t]
      abel
    · have hpsi_not_t : psi ∉ t := fun h ↦ Finset.disjoint_left.mp htu h hpsi_u
      have huErase : u.erase psi ⊆ Delta := by
        intro a ha
        have ha' := hu (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_t (h ▸ ha))
      let z := (∑ a ∈ t, a) - ∑ a ∈ u.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan htDelta huErase
      let s := -((∑ a ∈ t, a) - ∑ a ∈ u, a)
      have hs : s ∈ S := hS _ hsumS
      refine ⟨z, hz, s, hs, ?_⟩
      dsimp [z, s]
      rw [← Finset.sum_erase_add _ _ hpsi_u]
      abel

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod_card_le [Finite G]
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma : Finset (AddChar G ℂ), Gamma ⊆ T →
      AddDissociatedMod S Gamma → Gamma.card ≤ k →
        (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  obtain ⟨Delta, hDeltaT, hDelta, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hS
  have hcard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaReal : (Gamma.card : ℝ) ≤ D :=
      hdim Gamma (hGammaDelta.trans hDeltaT) (hDelta.mono hGammaDelta)
        (by omega)
    have hkD : (k : ℝ) ≤ D := by simpa [hGammaCard] using hGammaReal
    exact (not_le_of_gt hDk) hkD
  exact ⟨Delta, hDeltaT, hDelta, hdim Delta hDeltaT hDelta hcard, hcover⟩

def signedFrequency (t u : Finset (AddChar G ℂ)) : AddChar G ℂ :=
  (∑ psi ∈ u, psi) - ∑ psi ∈ t \ u, psi

def signedCoefficient (v : AddChar G ℂ → ℂ)
    (t u : Finset (AddChar G ℂ)) : ℂ :=
  ((∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)) /
    (2 : ℂ) ^ t.card

omit [Fintype G] in
lemma rieszProduct_eq_signedExpansion [Finite G]
    (Delta : Finset (AddChar G ℂ)) (v : AddChar G ℂ → ℂ) (x : G) :
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
  let := Fintype.ofFinite G
  calc
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
        ∏ psi ∈ Delta,
          (((v psi * psi x) + conj (v psi * psi x)) / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro psi hpsi
      rw [add_comm, ← Complex.re_eq_add_conj]
      push_cast
      rfl
    _ = ∑ t ∈ Delta.powerset,
        ∏ psi ∈ t, ((v psi * psi x) + conj (v psi * psi x)) / 2 := by
      rw [Finset.prod_add]
      simp
    _ = ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      rw [Finset.prod_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [signedCoefficient, signedFrequency]
      simp only [AddChar.sum_apply, AddChar.sub_apply,
        AddChar.map_neg_eq_conj]
      simp only [Finset.prod_const]
      simp_rw [map_mul, Finset.prod_mul_distrib]
      rw [map_prod]
      ring

lemma weightedRiesz_eq_signedExpansion
    (w : G → ℝ) (Delta : Finset (AddChar G ℂ))
    (v : AddChar G ℂ → ℂ) :
    ((∑ x : G, w x *
        ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u *
          Erdos3.massCoeff w (signedFrequency t u) := by
  simp_rw [Complex.ofReal_prod]
  simp_rw [rieszProduct_eq_signedExpansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos3.massCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [Fintype G] in
lemma signedFrequency_not_mem
    {S Delta t u : Finset (AddChar G ℂ)}
    (hDelta : AddDissociatedMod S Delta)
    (ht : t ⊆ Delta) (ht0 : t.Nonempty) (hu : u ⊆ t) :
    signedFrequency t u ∉ S := by
  apply hDelta u (t \ u)
  · exact hu.trans ht
  · exact Finset.sdiff_subset.trans ht
  · rw [Finset.disjoint_left]
    intro psi hpsiu hpsitu
    exact (Finset.mem_sdiff.mp hpsitu).2 hpsiu
  · simpa [Finset.union_sdiff_of_subset hu] using ht0

omit [Fintype G] in
lemma norm_signedCoefficient_le
    {v : AddChar G ℂ → ℂ} {t u : Finset (AddChar G ℂ)}
    (hu : u ⊆ t) (hv : ∀ psi ∈ t, ‖v psi‖ ≤ 1) :
    ‖signedCoefficient v t u‖ ≤ ((2 : ℝ) ^ t.card)⁻¹ := by
  have hvu : ‖∏ psi ∈ u, v psi‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ hv psi (hu hpsi))
  have hvtu : ‖∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ by
        rw [RCLike.norm_conj]
        exact hv psi (Finset.sdiff_subset hpsi))
  have hnum :
      ‖(∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hvu hvtu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [signedCoefficient, norm_div]
  calc
    _ ≤ 1 / ‖(2 : ℂ) ^ t.card‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = ((2 : ℝ) ^ t.card)⁻¹ := by
      rw [norm_pow]
      norm_num

theorem AddDissociatedMod.weighted_riesz_randomisation_le
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ}
    (hDelta : AddDissociatedMod S Delta)
    (_hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (v : AddChar G ℂ → ℂ) (hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1) :
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
      1 + q * (2 : ℝ) ^ Delta.card := by
  classical
  let F : Finset (AddChar G ℂ) → ℂ := fun t ↦
    ∑ u ∈ t.powerset, signedCoefficient v t u *
      Erdos3.massCoeff w (signedFrequency t u)
  let E : ℂ := ∑ t ∈ Delta.powerset.erase ∅, F t
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ Delta.powerset := by simp
  have hw1c : ∑ x : G, (w x : ℂ) = 1 := by exact_mod_cast hw1
  have hFempty : F ∅ = 1 := by
    simp [F, signedCoefficient, signedFrequency, Erdos3.massCoeff, hw1c]
  have hexp :
      ((∑ x : G, w x *
          ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) = 1 + E := by
    rw [weightedRiesz_eq_signedExpansion]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [hFempty, E, F]
    ring
  have hinner (t : Finset (AddChar G ℂ))
      (ht : t ∈ Delta.powerset.erase ∅) : ‖F t‖ ≤ q := by
    have htDelta : t ⊆ Delta := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have ht0 : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    calc
      ‖F t‖ ≤ ∑ u ∈ t.powerset,
          ‖signedCoefficient v t u *
            Erdos3.massCoeff w (signedFrequency t u)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _u ∈ t.powerset, ((2 : ℝ) ^ t.card)⁻¹ * q := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_signedCoefficient_le (Finset.mem_powerset.mp hu)
            (fun psi hpsi ↦ hv psi (htDelta hpsi))
        · exact hq _ (signedFrequency_not_mem hDelta htDelta ht0
            (Finset.mem_powerset.mp hu))
        · exact norm_nonneg _
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
      _ = q := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul]
  have hEnorm : ‖E‖ ≤ q * (2 : ℝ) ^ Delta.card := by
    calc
      ‖E‖ ≤ ∑ t ∈ Delta.powerset.erase ∅, ‖F t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Delta.powerset.erase ∅, q := by
        exact Finset.sum_le_sum fun t ht ↦ hinner t ht
      _ ≤ ∑ _t ∈ Delta.powerset, q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ hq0)
      _ = q * (2 : ℝ) ^ Delta.card := by
        simp [Finset.card_powerset]
        ring
  let R : ℝ :=
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re)
  have hexpR : (R : ℂ) = 1 + E := by
    calc
      (R : ℂ) = ∑ x : G, (w x : ℂ) *
          (↑(∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) := by
        dsimp [R]
        push_cast
        rfl
      _ = 1 + E := hexp
  have hre : R = 1 + E.re := by
    have := congrArg Complex.re hexpR
    simpa using this
  change R ≤ 1 + q * (2 : ℝ) ^ Delta.card
  calc
    R = 1 + E.re := hre
    _ ≤ 1 + ‖E‖ := add_le_add (le_refl 1) (Complex.re_le_norm E)
    _ ≤ 1 + q * (2 : ℝ) ^ Delta.card := add_le_add (le_refl 1) hEnorm

theorem AddDissociatedMod.isWeightedDissociated
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hqk : q * (2 : ℝ) ^ k ≤ 1) :
    IsWeightedDissociated w 1 Delta := by
  intro v hv
  have hpowNat : 2 ^ Delta.card ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hpow : (2 : ℝ) ^ Delta.card ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hpowNat
  have htail : q * (2 : ℝ) ^ Delta.card ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hq0).trans hqk
  calc
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
        1 + q * (2 : ℝ) ^ Delta.card :=
      hDelta.weighted_riesz_randomisation_le hw0 hw1 hq0 hq v hv
    _ ≤ 2 := by linarith
    _ ≤ exp 1 := Real.exp_one_gt_two.le

theorem AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hq_quarter : q ≤ (1 / 4 : ℝ) ^ k) :
    IsWeightedDissociated w 1 Delta := by
  apply hDelta.isWeightedDissociated hw0 hw1 hq0 hq hcard
  calc
    q * (2 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hq_quarter (pow_nonneg (by norm_num) _)
    _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; congr 1; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem zero_mem_chang_largeSpectrum_half (A : Finset G) :
    (0 : AddChar G ℂ) ∈ Erdos3.Chang.largeSpectrum A (1 / 2 : ℝ) := by
  rw [Erdos3.Chang.mem_largeSpectrum]
  simp [Erdos3.Chang.spectrumSum]
  have hcard : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le A.card
  nlinarith

theorem neg_mem_chang_largeSpectrum {A : Finset G} {eta : ℝ}
    {psi : AddChar G ℂ}
    (hpsi : psi ∈ Erdos3.Chang.largeSpectrum A eta) :
    -psi ∈ Erdos3.Chang.largeSpectrum A eta := by
  rw [Erdos3.Chang.mem_largeSpectrum] at hpsi ⊢
  have hsum : Erdos3.Chang.spectrumSum A (-psi) =
      conj (Erdos3.Chang.spectrumSum A psi) := by
    unfold Erdos3.Chang.spectrumSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [AddChar.neg_apply, AddChar.map_neg_eq_conj]
  rw [hsum, RCLike.norm_conj]
  exact hpsi

end Erdos3.RelativeChangSanders

end

end

section

open _root_.Finset Real
open scoped BigOperators NNReal

namespace Erdos3.RelativeChangSanders

noncomputable section

variable {N : ℕ} [NeZero N]

def localChangDimension (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℝ :=
  2 * (1 + log (2 * (B.carrier.card : ℝ) / X.card)) / eta ^ 2

def localChangCap (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℕ :=
  ⌈localChangDimension B X eta⌉₊ + 1

def localChangBaseScale (B : CyclicBohr.Set N) (X : Finset (ZMod N))
    (eta : ℝ) : NNReal :=
  (100 * ((2 * max B.rank 1 : ℕ) : NNReal) *
    (((2 * localChangCap B X eta + 1 : ℕ) : NNReal)))⁻¹

theorem exists_relativeLargeSpectrum_cover
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ rho : NNReal, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ),
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        ∀ psi ∈ Chang.largeSpectrum X eta,
          ∃ z ∈ Delta.addSpan,
            ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s := by
  classical
  let D : ℝ := localChangDimension B X eta
  let k : ℕ := localChangCap B X eta
  let d : ℕ := 2 * max B.rank 1
  let a : NNReal := localChangBaseScale B X eta
  have haPos : 0 < a := by
    dsimp [a, localChangBaseScale]
    positivity
  have haposR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hbasePos : 0 < (B.ndilate a).radius := by
    rw [CyclicBohr.Set.radius_ndilate]
    exact mul_pos haposR hBpos
  obtain ⟨rho, hrhoHalf, hrhoOne, hregular⟩ :=
    CyclicBohr.Set.exists_rankRegular_ndilate (B.ndilate a) hbasePos
  let tau : NNReal := rho * a
  let C : CyclicBohr.Set N := B.ndilate tau
  have hCreg : C.IsRankRegular := by
    simpa [C, tau] using hregular
  have hd : 0 < d := by simp [d]
  have hk : 0 < k := by simp [k, localChangCap]
  have ha : a =
      (100 * (d : NNReal) * (((2 * k + 1 : ℕ) : NNReal)))⁻¹ := by
    simp [a, localChangBaseScale, d, k]
  have hsmall : (((2 * k : ℕ) : NNReal) * tau) ≤
      1 / (100 * (d : NNReal)) := by
    have hkden : (0 : NNReal) < (((2 * k + 1 : ℕ) : NNReal)) := by positivity
    have hdb : (0 : NNReal) < 100 * (d : NNReal) := by positivity
    calc
      (((2 * k : ℕ) : NNReal) * tau) =
          ((2 * k : ℕ) : NNReal) * (rho * a) := rfl
      _ ≤ ((2 * k : ℕ) : NNReal) * (1 * a) := by gcongr
      _ = (((2 * k : ℕ) : NNReal) /
          (((2 * k + 1 : ℕ) : NNReal))) /
            (100 * (d : NNReal)) := by rw [ha]; field_simp
      _ ≤ 1 / (100 * (d : NNReal)) := by
        gcongr
        exact (div_le_one hkden).2 (by
          exact_mod_cast Nat.le_add_right (2 * k) 1)
  let T : Finset (AddChar (ZMod N) ℂ) := Chang.largeSpectrum X eta
  let S : Finset (AddChar (ZMod N) ℂ) :=
    Chang.largeSpectrum C.carrier (1 / 2)
  let w : (ZMod N) → ℝ := Erdos3.bohrSmoothingMeasure B tau (2 * k)
  let outer : Finset (ZMod N) :=
    (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier
  let c : ℝ := (outer.card : ℝ)⁻¹
  let R : ℝ := 2 * (B.carrier.card : ℝ) / X.card
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact Erdos3.bohrSmoothingMeasure_nonneg B tau (2 * k) x
  have hw1 : ∑ x : (ZMod N), w x = 1 := by
    exact Erdos3.sum_bohrSmoothingMeasure B tau (2 * k)
  have hwconst : ∀ x ∈ B.carrier, w x = c := by
    intro x hx
    simpa [w, c, outer] using
      (Erdos3.bohrSmoothingMeasure_apply_of_mem B tau (2 * k) hx)
  have hOuterCard : outer.card ≤ 2 * B.carrier.card := by
    simpa [outer, d] using
      (Erdos3.card_dilate_one_add_le_two_mul hBreg (2 * k) hsmall)
  have hOuterPos : 0 < outer.card := by
    exact outer.card_pos.mpr (by
      simpa [outer] using
        (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier_nonempty)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hR : (c * X.card)⁻¹ ≤ R := by
    have hOr : (0 : ℝ) < outer.card := by exact_mod_cast hOuterPos
    have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hOr' : (outer.card : ℝ) ≤ 2 * B.carrier.card := by
      exact_mod_cast hOuterCard
    calc
      (c * (X.card : ℝ))⁻¹ = (outer.card : ℝ) / X.card := by
        dsimp [c]
        field_simp
      _ ≤ (2 * B.carrier.card : ℝ) / X.card :=
        (div_le_div_iff_of_pos_right hXr).2 hOr'
      _ = R := by simp [R]
  have hzero : (0 : AddChar (ZMod N) ℂ) ∈ S := by
    exact zero_mem_chang_largeSpectrum_half C.carrier
  have hneg : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    exact neg_mem_chang_largeSpectrum hs
  have hDk : D < (k : ℝ) := by
    calc
      D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
      _ < ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self ⌈D⌉₊
      _ = (k : ℝ) := by simp [k, localChangCap, D]
  have hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D := by
    intro Gamma hGammaT hGammaMod hGammaCard
    have hq : ∀ psi, psi ∉ S →
        ‖Erdos3.massCoeff w psi‖ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
      intro psi hpsi
      calc
        ‖Erdos3.massCoeff w psi‖ ≤
            ‖Erdos3.massCoeff
              (realUniformMass (B.ndilate tau).carrier) psi‖ ^ (2 * k) := by
          exact Erdos3.norm_massCoeff_bohrSmoothingMeasure_le
            B tau (2 * k) psi
        _ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
          gcongr
          exact (Erdos3.norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
            (B.ndilate tau).carrier (B.ndilate tau).carrier_nonempty psi
              (by simpa [S, C] using hpsi)).le
    have hweighted : IsWeightedDissociated w 1 Gamma := by
      apply hGammaMod.isWeightedDissociated_of_le_quarter_pow
        hw0 hw1 (by positivity) hq hGammaCard
      rw [pow_mul]
      norm_num
    have hcard := card_weightedDissociated_realFinsetIndicator_le
      B.carrier X hXB hX w c R eta hw0 hwconst hc hR heta Gamma
        hweighted (by simpa [T] using hGammaT)
    simpa [D, localChangDimension, R] using hcard
  obtain ⟨Delta, hDeltaT, _, hDeltaCard, hcover⟩ :=
    exists_maximal_addDissociatedMod_card_le S T hzero hneg D k hDk hdim
  refine ⟨rho, C, Delta, hrhoHalf, hrhoOne, ?_, hCreg, ?_, ?_, ?_⟩
  · simp [C, tau, a]
  · simpa [D] using hDeltaCard
  · simpa [T] using hDeltaT
  · simpa [T, S] using hcover

end

end Erdos3.RelativeChangSanders

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingChildBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementIntegralSum (A Q : Finset G) (shape : Finset G → Finset G)
    (a g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementIntegral D Q (shape D) a f g +
      replacementIntegralSum A Q shape a g (Peeling.remainder D f) ds

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

noncomputable def refinementContraction (epsilon : ℝ) : ℝ :=
  1 - localMomentGain (flatComparisonDelta epsilon) / 1081600

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousLieSpan
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

def homogeneousLieSpan (v : I → L) (g : I → σ →₀ ℕ) (S : Set (σ →₀ ℕ)) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, lieTreeMultidegree g a ∈ S ∧ lieTreeEval v a = x}

theorem homogeneousLieSpan_mono (v : I → L) (g : I → σ →₀ ℕ)
    {S T : Set (σ →₀ ℕ)} (hST : S ⊆ T) : homogeneousLieSpan v g S ≤ homogeneousLieSpan v g T := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hST ha, rfl⟩

@[simp] theorem homogeneousLieSpan_empty (v : I → L) (g : I → σ →₀ ℕ) :
    homogeneousLieSpan v g ∅ = ⊥ := by
  simp [homogeneousLieSpan]

structure LieGradingExpansion (v : I → L) (g : I → σ →₀ ℕ) where
  expand : L →ₗ[ℚ] VectorPolynomial σ ℚ L
  expand_tree : ∀ a, expand (lieTreeEval v a) = monomial (lieTreeMultidegree g a) (lieTreeEval v a)
  eval_one : ∀ x, eval (fun _ : σ => (1 : ℚ)) (expand x) = x

namespace LieGradingExpansion

variable {v : I → L} {g : I → σ →₀ ℕ} (E : LieGradingExpansion v g)

noncomputable def component (α : σ →₀ ℕ) : L →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp (coefficients.toLinearMap.comp E.expand)

@[simp] theorem component_apply (α : σ →₀ ℕ) (x : L) :
    E.component α x = coefficients (E.expand x) α := rfl

theorem component_tree [DecidableEq σ] (α : σ →₀ ℕ) (a : FreeMagma I) :
    E.component α (lieTreeEval v a) =
      if lieTreeMultidegree g a = α then lieTreeEval v a else 0 := by
  classical
  rw [component_apply, E.expand_tree, coefficients_monomial]
  simp only [Finsupp.single_apply]

theorem component_mem_span {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    (α : σ →₀ ℕ) : E.component α x ∈ homogeneousLieSpan v g (S ∩ {α}) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [E.component_tree]
    split_ifs with h
    · exact Submodule.subset_span ⟨a, ⟨ha, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem component_eq_zero {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    {α : σ →₀ ℕ} (hα : α ∉ S) : E.component α x = 0 := by
  have hc := E.component_mem_span hx α
  have he : S ∩ {α} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro β ⟨hβ, rfl⟩
    exact hα hβ
  rw [he, homogeneousLieSpan_empty, Submodule.mem_bot] at hc
  exact hc

include E in
theorem span_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan v g (S ∩ T) = homogeneousLieSpan v g S ⊓ homogeneousLieSpan v g T := by
  apply le_antisymm
  · exact le_inf (homogeneousLieSpan_mono v g Set.inter_subset_left)
      (homogeneousLieSpan_mono v g Set.inter_subset_right)
  · intro x hx
    have hc : ∀ α, coefficients (E.expand x) α ∈ homogeneousLieSpan v g (S ∩ T) := by
      intro α
      change E.component α x ∈ homogeneousLieSpan v g (S ∩ T)
      by_cases hα : α ∈ T
      · apply homogeneousLieSpan_mono v g _ (E.component_mem_span hx.1 α)
        rintro β ⟨hβ, rfl⟩
        exact ⟨hβ, hα⟩
      · rw [E.component_eq_zero hx.2 hα]
        exact Submodule.zero_mem _
    have h := (eval_mem_iff_coefficients (homogeneousLieSpan v g (S ∩ T)) (E.expand x)).mpr
      hc (fun _ : σ => (1 : ℚ))
    rwa [E.eval_one] at h

end LieGradingExpansion
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLieDegreeLengthSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieDegreeLengthSpan (v : I → L) (w : I → ℕ) (d k : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ k ≤ a.length ∧ lieTreeEval v a = x}

theorem weightedLieDegreeLengthSpan_antitone (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} (hde : d ≤ e) (hkl : k ≤ l) :
    weightedLieDegreeLengthSpan v w e l ≤ weightedLieDegreeLengthSpan v w d k := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, hk, rfl⟩
  exact ⟨a, hde.trans ha, hkl.trans hk, rfl⟩

theorem weightedLieDegreeLengthSpan_lie_mem (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} {x y : L}
    (hx : x ∈ weightedLieDegreeLengthSpan v w d k)
    (hy : y ∈ weightedLieDegreeLengthSpan v w e l) :
    ⁅x, y⁆ ∈ weightedLieDegreeLengthSpan v w (d + e) (k + l) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hk, rfl⟩ := hx
    obtain ⟨b, hb, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, Nat.add_le_add hk hl, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem weightedLieUpperSpan_map_le_degreeLengthSpan (φ : L →ₗ⁅ℚ⁆ M)
    (v : I → L) (w : I → ℕ) (d : ℕ) :
    (weightedLieUpperSpan v w d).map φ.toLinearMap ≤
      weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1 := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1
  rw [map_lieTreeEval]
  exact Submodule.subset_span ⟨a, ha, a.length_pos, rfl⟩

theorem FilteredLieTree.map_eval_mem_degreeLengthSpan {s : ℕ}
    {F : NilpotentLieFiltration L s} (φ : L →ₗ⁅ℚ⁆ M) (v : I → M) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ weightedLieDegreeLengthSpan v w d k := by
  induction a with
  | leaf hd x hx => exact hspan _ hd x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact weightedLieDegreeLengthSpan_lie_mem v w ha hb

theorem weightedLieDegreeLengthSpan_top_le_ker {A : Type*} [AddCommGroup A] [Module ℚ A]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma I, lieTreeWeight w a = s → a.length = r → η (lieTreeEval v a) = 0) :
    weightedLieDegreeLengthSpan v w s r ≤ η.ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, hk, rfl⟩
  change η (lieTreeEval v a) = 0
  by_cases hd : lieTreeWeight w a = s
  · by_cases hr : a.length = r
    · exact hzero a hd hr
    · have hm := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inr ⟨hd.symm, by omega⟩), Submodule.mem_bot] at hm
      rw [hm, map_zero]
  · have hm := F.lieTreeEval_mem_length v w hv a
    rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hm
    rw [hm, map_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SampledFullboxDetectionBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem natPolynomial_eval_mono_nonneg (P : Polynomial ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    P.eval₂ (Nat.castRingHom ℝ) p ≤ P.eval₂ (Nat.castRingHom ℝ) q := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp hpq n) (Nat.cast_nonneg _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardParameterPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 =>
    let P := preparedFiniteForwardParameterPolynomial A stageCountConstant n
    let work := (P + Polynomial.C A) ^ A
    let cap := (4 * P + 4 * work + 16 + Polynomial.C A) ^ A
    let count := P + cap
    let branch := Polynomial.X * cap + (count + 8) ^ 8 +
      (count + Polynomial.C (stageCountConstant n)) ^ stageCountConstant n
    P + cap + branch + 1

noncomputable def preparedFiniteForwardWorkPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCapPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  (4 * preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    4 * preparedFiniteForwardWorkPolynomial A stageCountConstant n + 16 + Polynomial.C A) ^ A

noncomputable def preparedFiniteForwardCountPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  preparedFiniteForwardParameterPolynomial A stageCountConstant n +
    preparedFiniteForwardCapPolynomial A stageCountConstant n

noncomputable def preparedFiniteForwardBranchPolynomial (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  Polynomial.X * preparedFiniteForwardCapPolynomial A stageCountConstant n +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n + 8) ^ 8 +
    (preparedFiniteForwardCountPolynomial A stageCountConstant n +
      Polynomial.C (stageCountConstant n)) ^ stageCountConstant n

@[simp] theorem preparedFiniteForwardParameterPolynomial_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant 0 = Polynomial.X := rfl

theorem preparedFiniteForwardParameterPolynomial_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant (n + 1) =
      preparedFiniteForwardParameterPolynomial A stageCountConstant n +
        preparedFiniteForwardCapPolynomial A stageCountConstant n +
        preparedFiniteForwardBranchPolynomial A stageCountConstant n + 1 := rfl

noncomputable def preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardParameterPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardWork (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardWorkPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCap (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCapPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardCount (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardCountPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

noncomputable def preparedFiniteForwardBranch (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardBranchPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

@[simp] theorem preparedFiniteForwardParameter_zero (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant 0 x = x := by
  simp [preparedFiniteForwardParameter]

theorem preparedFiniteForwardWork_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardWork A stageCountConstant n x =
      (preparedFiniteForwardParameter A stageCountConstant n x + A) ^ A := by
  simp [preparedFiniteForwardWork, preparedFiniteForwardWorkPolynomial,
    preparedFiniteForwardParameter, Polynomial.eval₂_pow]

theorem preparedFiniteForwardCap_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCap A stageCountConstant n x =
      (4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A) ^ A := by
  simp [preparedFiniteForwardCap, preparedFiniteForwardCapPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardWork, Polynomial.eval₂_pow]

theorem preparedFiniteForwardCount_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardCount A stageCountConstant n x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x := by
  simp [preparedFiniteForwardCount, preparedFiniteForwardCountPolynomial,
    preparedFiniteForwardParameter, preparedFiniteForwardCap]

theorem preparedFiniteForwardBranch_eq (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardBranch A stageCountConstant n x =
      x * preparedFiniteForwardCap A stageCountConstant n x +
        (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
        (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
          stageCountConstant n := by
  simp [preparedFiniteForwardBranch, preparedFiniteForwardBranchPolynomial,
    preparedFiniteForwardCap, preparedFiniteForwardCount, Polynomial.eval₂_pow]

theorem preparedFiniteForwardParameter_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant (n + 1) x =
      preparedFiniteForwardParameter A stageCountConstant n x +
        preparedFiniteForwardCap A stageCountConstant n x +
        preparedFiniteForwardBranch A stageCountConstant n x + 1 := by
  simp [preparedFiniteForwardParameter, preparedFiniteForwardParameterPolynomial_succ,
    preparedFiniteForwardCap, preparedFiniteForwardBranch]

theorem preparedFiniteForwardParameter_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardParameter A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardWork_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardWork A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCap_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCap A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardCount_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardBranch_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardBranch A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

theorem preparedFiniteForwardParameter_strictMono (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    StrictMono (fun n => preparedFiniteForwardParameter A stageCountConstant n x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [preparedFiniteForwardParameter_succ]
  have := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith

theorem preparedFiniteForwardParameter_monotone (A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun n => preparedFiniteForwardParameter A stageCountConstant n x) :=
  (preparedFiniteForwardParameter_strictMono A stageCountConstant hx).monotone

theorem le_preparedFiniteForwardParameter (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardParameter A stageCountConstant n x := by
  simpa using preparedFiniteForwardParameter_monotone A stageCountConstant hx (Nat.zero_le n)

theorem exists_preparedFiniteForwardSchedule_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) := by
  let Q : ℕ → Polynomial ℕ := fun n =>
    preparedFiniteForwardParameterPolynomial A stageCountConstant n +
      preparedFiniteForwardWorkPolynomial A stageCountConstant n +
      preparedFiniteForwardCapPolynomial A stageCountConstant n +
      preparedFiniteForwardCountPolynomial A stageCountConstant n +
      preparedFiniteForwardBranchPolynomial A stageCountConstant n
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (∑ n ∈ Finset.range (depth + 1), Q n)
  refine ⟨C, hC, ?_⟩
  intro x hx n hn
  have hentry : (Q n).eval₂ (Nat.castRingHom ℝ) x ≤ (x + C) ^ C := by
    apply le_trans _ (hbudget x hx)
    rw [Polynomial.eval₂_finsetSum]
    exact Finset.single_le_sum (fun i _ => natPolynomial_eval_nonneg (Q i) hx)
      (Finset.mem_range.mpr (by omega))
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hcap := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have hcount := preparedFiniteForwardCount_nonneg A stageCountConstant n hx
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  simp only [Q, Polynomial.eval₂_add] at hentry
  change preparedFiniteForwardParameter A stageCountConstant n x +
      preparedFiniteForwardWork A stageCountConstant n x +
      preparedFiniteForwardCap A stageCountConstant n x +
      preparedFiniteForwardCount A stageCountConstant n x +
      preparedFiniteForwardBranch A stageCountConstant n x ≤ (x + C) ^ C at hentry
  exact ⟨⟨hp, by linarith⟩, ⟨hw, by linarith⟩, ⟨hcap, by linarith⟩,
    ⟨hcount, by linarith⟩, ⟨hbranch, by linarith⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardPrefixLog
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardBranch A stageCountConstant j x

noncomputable def preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, preparedFiniteForwardCap A stageCountConstant j x

noncomputable def preparedFiniteForwardModelPrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog +
    preparedFiniteForwardWork A stageCountConstant n x + stageLog + 6

noncomputable def preparedFiniteForwardSourcePrecision
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
    2 * preparedFiniteForwardWork A stageCountConstant n x + 1

theorem preparedFiniteForwardParameter_prefix
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    preparedFiniteForwardParameter A stageCountConstant n x = x +
      preparedFiniteForwardCumulative A stageCountConstant n x +
      preparedFiniteForwardPrefixLog A stageCountConstant n x + n := by
  induction n with
  | zero => simp [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      preparedFiniteForwardParameter_zero]
  | succ n ih =>
    rw [preparedFiniteForwardParameter_succ, ih]
    simp only [preparedFiniteForwardCumulative, preparedFiniteForwardPrefixLog,
      Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem preparedFiniteForward_prefix_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) ∧
    preparedFiniteForwardPrefixLog A stageCountConstant n x ∈
      Set.Icc 0 (preparedFiniteForwardParameter A stageCountConstant n x) := by
  have hc : 0 ≤ preparedFiniteForwardCumulative A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardCap_nonneg A stageCountConstant j hx)
  have hb : 0 ≤ preparedFiniteForwardPrefixLog A stageCountConstant n x :=
    Finset.sum_nonneg (fun j _ => preparedFiniteForwardBranch_nonneg A stageCountConstant j hx)
  have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  exact ⟨⟨hc, by linarith only [heq, hb, hx, hn]⟩,
    ⟨hb, by linarith only [heq, hc, hx, hn]⟩⟩

theorem preparedFiniteForward_model_precision_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
    let sourceU := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog
    0 ≤ u ∧ 0 ≤ sourceU ∧ sourceU = u + 2 * w + 1 ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x + gainLog + w + stageLog + 6 ≤ u ∧
      sourceU + w ≤ 4 * b + 4 * w + 16 := by
  intro b w u sourceU
  have hp := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hbase : x ≤ b := by
    have heq := preparedFiniteForwardParameter_prefix A stageCountConstant n x
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    change x ≤ preparedFiniteForwardParameter A stageCountConstant n x
    linarith only [heq, hp.1.1, hp.2.1, hn]
  have hu : 0 ≤ u := by
    dsimp only [u, preparedFiniteForwardModelPrecision]
    linarith only [hp.2.1, hg.1, hw, hstage.1]
  have hs : sourceU = u + 2 * w + 1 := rfl
  refine ⟨hu, by linarith only [hs, hu, hw], hs, le_rfl, ?_⟩
  have hueq : u = preparedFiniteForwardPrefixLog A stageCountConstant n x +
      gainLog + w + stageLog + 6 := rfl
  have hb : 0 ≤ b := hx.trans hbase
  have hg' : gainLog ≤ b := hg.2.trans hbase
  have ht' : stageLog ≤ b := hstage.2.trans hbase
  linarith only [hs, hueq, hp.2.2, hg', ht', hb]

theorem preparedFiniteForward_phase_cap
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n Cphase : ℕ) {x gainLog stageLog : ℝ}
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hphase : Cphase ≤ A) :
    (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase) ^ Cphase ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  have hp := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hb := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ Cphase := Nat.cast_nonneg _
  rw [preparedFiniteForwardCap_eq]
  apply (pow_le_pow_left₀ (by linarith only [hp.2.1, hw, hC])
    (show preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cphase ≤
      4 * preparedFiniteForwardParameter A stageCountConstant n x +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 16 + A by
      have hC' : (Cphase : ℝ) ≤ A := Nat.cast_le.mpr hphase
      linarith only [hp.2.2.2.2, hC']) Cphase).trans
  exact pow_le_pow_right₀ (by linarith only [hb, hw, hA]) hphase

theorem preparedFiniteForward_branch_count_log
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x d : ℝ}
    (hx : 0 ≤ x) (hd : d ≤ x) :
    d * preparedFiniteForwardCap A stageCountConstant n x +
      (preparedFiniteForwardCount A stageCountConstant n x + 8) ^ 8 +
      (preparedFiniteForwardCount A stageCountConstant n x + stageCountConstant n) ^
        stageCountConstant n ≤ preparedFiniteForwardBranch A stageCountConstant n x := by
  rw [preparedFiniteForwardBranch_eq]
  have h := mul_le_mul_of_nonneg_right hd
    (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)
  linarith only [h]

theorem preparedFiniteForward_model_scalar_bounds
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    0 ≤ w ∧ b ≤ w ∧ (count : ℝ) ≤ Real.exp w ∧ b * count ≤ w := by
  intro b w
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw : 0 ≤ w := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
  have hshift : b ≤ b + A := le_add_of_nonneg_right (Nat.cast_nonneg A)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith only [hb, hAreal]
  have hbw : b ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    have hAone : 1 ≤ A := by omega
    have hpower : b + A ≤ (b + A) ^ A := by
      simpa only [pow_one] using (pow_le_pow_right₀ hbase hAone)
    exact hshift.trans hpower
  have hsquare : b ^ 2 ≤ w := by
    rw [show w = (b + A) ^ A from preparedFiniteForwardWork_eq A stageCountConstant n x]
    exact (pow_le_pow_left₀ hb hshift 2).trans (pow_le_pow_right₀ hbase hA)
  refine ⟨hw, hbw, ?_, ?_⟩
  · have hc : (count : ℝ) ≤ w := hcount.trans (hxb.trans hbw)
    have he := Real.add_one_le_exp w
    linarith only [hc, he]
  · exact (mul_le_mul_of_nonneg_left (hcount.trans hxb) hb).trans
      (by simpa only [pow_two] using hsquare)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedFiniteForwardCumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) (x : ℝ) :
    preparedFiniteForwardCumulative A stageCountConstant (r + 1) x =
      preparedFiniteForwardCumulative A stageCountConstant r x +
        preparedFiniteForwardCap A stageCountConstant r x := by
  simp only [preparedFiniteForwardCumulative, Finset.sum_range_succ]

theorem preparedFiniteForwardCumulative_nonneg
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForward_prefix_bounds A stageCountConstant r hx).1.1

theorem preparedFiniteForwardCumulative_le_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCumulative A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCumulative_monotone
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun r => preparedFiniteForwardCumulative A stageCountConstant r x) := by
  apply monotone_nat_of_le_succ
  intro r
  exact preparedFiniteForwardCumulative_le_succ A stageCountConstant r hx

theorem preparedFiniteForwardCap_le_cumulative_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant r x ≤
      preparedFiniteForwardCumulative A stageCountConstant (r + 1) x := by
  rw [preparedFiniteForwardCumulative_succ]
  exact le_add_of_nonneg_left (preparedFiniteForwardCumulative_nonneg A stageCountConstant r hx)

theorem preparedFiniteForwardCap_le_cumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {j r : ℕ} (hjr : j < r) :
    preparedFiniteForwardCap A stageCountConstant j x ≤
      preparedFiniteForwardCumulative A stageCountConstant r x :=
  (preparedFiniteForwardCap_le_cumulative_succ A stageCountConstant j hx).trans
    (preparedFiniteForwardCumulative_monotone A stageCountConstant hx hjr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_controlled_slice_bounds
    (A Cslice : ℕ) (stageCountConstant : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant n x
    let w := preparedFiniteForwardWork A stageCountConstant n x
    let pSlice := (b + Cslice) ^ Cslice
    0 ≤ pSlice ∧ pSlice ≤ w ∧ pSlice * count ≤ w := by
  intro b w pSlice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hA' : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCnat : Cslice ≤ A := (Nat.le_succ _).trans hC
  have hC' : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr hCnat
  have hbase : 1 ≤ b + A := by linarith only [hb, hA']
  have hbase0 : 0 ≤ b + A := le_trans (by norm_num) hbase
  have hslice0 : 0 ≤ pSlice := pow_nonneg (add_nonneg hb (Nat.cast_nonneg Cslice)) Cslice
  have hpow : pSlice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hC') Cslice
  have hcb : (count : ℝ) ≤ b + A := by
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A stageCountConstant n hx
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    linarith only [hcount, hxb, hA0]
  have hw : w = (b + A) ^ A := preparedFiniteForwardWork_eq A stageCountConstant n x
  refine ⟨hslice0, hpow.trans ?_, ?_⟩
  · rw [hw]
    exact pow_le_pow_right₀ hbase hCnat
  · rw [hw]
    calc
      pSlice * count ≤ (b + A) ^ Cslice * (b + A) :=
        mul_le_mul hpow hcb (Nat.cast_nonneg count) (pow_nonneg hbase0 Cslice)
      _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
      _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedCandidateForwardControlInput (s d : ℕ) (b : ℝ) : ℝ :=
  ((s : ℝ) + 3) * ((d : ℝ) + 1) * (b + 1)

theorem allocatedCandidateForwardControlInput_bounds (s d : ℕ) {b : ℝ}
    (hb : 0 ≤ b) :
    0 ≤ allocatedCandidateForwardControlInput s d b ∧
    b ≤ allocatedCandidateForwardControlInput s d b ∧
    3 * b ≤ allocatedCandidateForwardControlInput s d b := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : 3 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd, mul_nonneg hs hd]
  have hthree : 3 * b ≤ allocatedCandidateForwardControlInput s d b := by
    calc
      3 * b ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  have hbthree : b ≤ 3 * b := by linarith only [hb]
  exact ⟨(mul_nonneg (by norm_num) hb).trans hthree, hbthree.trans hthree, hthree⟩

theorem allocatedCandidateForwardControlInput_denominator_bound
    (s d q : ℕ) {b x cumulative : ℝ}
    (hb : 0 ≤ b) (hxb : x ≤ b) (hcb : cumulative ≤ b)
    (hq : (q : ℝ) ≤ Real.exp x) :
    (q : ℝ) * Real.exp ((s : ℝ) * (d : ℝ) * cumulative) ≤
      Real.exp (allocatedCandidateForwardControlInput s d b) := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : (s : ℝ) * d + 1 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd]
  have hexponent : x + (s : ℝ) * d * cumulative ≤
      allocatedCandidateForwardControlInput s d b := by
    calc
      x + (s : ℝ) * d * cumulative ≤ b + (s : ℝ) * d * b :=
        add_le_add hxb (mul_le_mul_of_nonneg_left hcb (mul_nonneg hs hd))
      _ = ((s : ℝ) * d + 1) * b := by ring
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  calc
    (q : ℝ) * Real.exp ((s : ℝ) * d * cumulative) ≤
        Real.exp x * Real.exp ((s : ℝ) * d * cumulative) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _)
    _ = Real.exp (x + (s : ℝ) * d * cumulative) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem allocatedCandidateForwardControlInput_cost_bound
    (s d : ℕ) {b x cumulative Bbound : ℝ}
    (hxb : x ≤ b) (hcb : cumulative ≤ b) (hd : (d : ℝ) ≤ x)
    (hBbound : Bbound ≤ Real.exp x) :
    (d : ℝ) * Bbound * Real.exp cumulative ≤
      Real.exp (allocatedCandidateForwardControlInput s d b + 2) := by
  have hx : 0 ≤ x := (Nat.cast_nonneg d).trans hd
  have hb : 0 ≤ b := hx.trans hxb
  have hdexp : (d : ℝ) ≤ Real.exp x :=
    hd.trans (by linarith only [Real.add_one_le_exp x])
  have hthree := (allocatedCandidateForwardControlInput_bounds s d hb).2.2
  calc
    (d : ℝ) * Bbound * Real.exp cumulative ≤
        (d : ℝ) * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBbound (Nat.cast_nonneg d)) (Real.exp_nonneg _)
    _ ≤ Real.exp x * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdexp (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (x + x + cumulative) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (allocatedCandidateForwardControlInput s d b + 2) :=
      Real.exp_le_exp.mpr (by linarith only [hxb, hcb, hthree])

theorem allocatedCandidateForwardControlInput_power_bound
    (s d C A : ℕ) {b : ℝ} (hb : 0 ≤ b) (hd : (d : ℝ) ≤ b)
    (hA : 2 ≤ A) (hsA : s + 3 ≤ A) (hCA : 4 * C ≤ A) :
    (allocatedCandidateForwardControlInput s d b + C) ^ C ≤ (b + A) ^ A := by
  let K : ℝ := b + A
  have hKtwo : 2 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hb, hAreal]
  have hK : 0 ≤ K := by linarith only [hKtwo]
  have hsK : (s : ℝ) + 3 ≤ K := by
    have hsreal : (s : ℝ) + 3 ≤ A := by exact_mod_cast hsA
    dsimp only [K]
    linarith only [hb, hsreal]
  have hdK : (d : ℝ) + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hd, hAreal]
  have hbK : b + 1 ≤ K := by
    have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
    dsimp only [K]
    linarith only [hAreal]
  have hinput : allocatedCandidateForwardControlInput s d b ≤ K ^ 3 := by
    unfold allocatedCandidateForwardControlInput
    calc
      _ ≤ (K * K) * K :=
        mul_le_mul (mul_le_mul hsK hdK (by positivity) hK) hbK (by positivity)
          (mul_nonneg hK hK)
      _ = K ^ 3 := by ring
  have hCK : (C : ℝ) ≤ K := by
    have hCnat : C ≤ A := by omega
    have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hCnat
    dsimp only [K]
    linarith only [hb, hCreal]
  have hKcube : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hKtwo] : 1 ≤ K)
      (by norm_num : (1 : ℕ) ≤ 3)
  have hbase : allocatedCandidateForwardControlInput s d b + C ≤ K ^ 4 := by
    calc
      _ ≤ K ^ 3 + K ^ 3 := add_le_add hinput (hCK.trans hKcube)
      _ = 2 * K ^ 3 := by ring
      _ ≤ K * K ^ 3 := mul_le_mul_of_nonneg_right hKtwo (pow_nonneg hK _)
      _ = K ^ 4 := by ring
  calc
    _ ≤ (K ^ 4) ^ C := pow_le_pow_left₀
      (add_nonneg (allocatedCandidateForwardControlInput_bounds s d hb).1 (Nat.cast_nonneg C)) hbase C
    _ = K ^ (4 * C) := (pow_mul _ _ _).symm
    _ ≤ K ^ A := pow_le_pow_right₀ (by linarith only [hKtwo]) hCA
    _ = (b + A) ^ A := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem le_preparedFiniteForwardCumulative
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (depth : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hA : 1 ≤ A) (hdepth : 0 < depth) :
    x ≤ preparedFiniteForwardCumulative A stageCountConstant depth x := by
  have hcap : x ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    rw [preparedFiniteForwardCap_eq, preparedFiniteForwardParameter_zero]
    have hw := preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx
    have hbase : 1 ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    have hshift : x ≤ 4 * x +
        4 * preparedFiniteForwardWork A stageCountConstant 0 x + 16 + A := by
      linarith only [hx, hw, Nat.cast_nonneg (α := ℝ) A]
    exact hshift.trans (by simpa only [pow_one] using pow_le_pow_right₀ hbase hA)
  exact hcap.trans (preparedFiniteForwardCap_le_cumulative A stageCountConstant hx hdepth)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardParameter_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardParameter A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_right (preparedFiniteForwardCap_nonneg A stageCountConstant n hx)

theorem le_preparedFiniteForwardCount
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ preparedFiniteForwardCount A stageCountConstant n x :=
  (le_preparedFiniteForwardParameter A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_le_count A stageCountConstant n hx)

theorem preparedFiniteForwardCap_le_count
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCap A stageCountConstant n x ≤
      preparedFiniteForwardCount A stageCountConstant n x := by
  rw [preparedFiniteForwardCount_eq]
  exact le_add_of_nonneg_left (preparedFiniteForwardParameter_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardCount_le_parameter_succ
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant (n + 1) x := by
  rw [preparedFiniteForwardCount_eq, preparedFiniteForwardParameter_succ]
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  linarith only [hbranch]

theorem preparedFiniteForwardCount_le_parameter
    (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ} (hx : 0 ≤ x)
    {n depth : ℕ} (hn : n < depth) :
    preparedFiniteForwardCount A stageCountConstant n x ≤
      preparedFiniteForwardParameter A stageCountConstant depth x :=
  (preparedFiniteForwardCount_le_parameter_succ A stageCountConstant n hx).trans
    (preparedFiniteForwardParameter_monotone A stageCountConstant hx hn)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardStageBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardStage_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x gainLog stageLog : ℝ, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCumulative A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, hB, hschedule⟩ :=
    exists_preparedFiniteForwardSchedule_budget depth A stageCountConstant
  let Q : Polynomial ℕ := 8 * (Polynomial.X + Polynomial.C B) ^ B + 32
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hstage n hn
  have hbound : 8 * (x + B) ^ B + 32 ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget x hx
  have hT : 0 ≤ (x + B) ^ B := pow_nonneg (add_nonneg hx (Nat.cast_nonneg B)) _
  have hraise : (x + B) ^ B ≤ (x + C) ^ C := by linarith only [hbound, hT]
  obtain ⟨hp, hw, hcap, hcount, hbranch⟩ := hschedule x hx n hn
  have hprefix := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hprecision :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hsource :
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤
        (x + C) ^ C := by
    linarith only [hprecision.2.2.2.2, hp.2, hw.1, hw.2, hbound]
  have hmodel :
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ≤
        preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
    linarith only [hprecision.2.2.1, hw.1]
  exact ⟨⟨hp.1, hp.2.trans hraise⟩, ⟨hw.1, hw.2.trans hraise⟩,
    ⟨hcap.1, hcap.2.trans hraise⟩, ⟨hcount.1, hcount.2.trans hraise⟩,
    ⟨hbranch.1, hbranch.2.trans hraise⟩,
    ⟨hprefix.1.1, hprefix.1.2.trans (hp.2.trans hraise)⟩,
    ⟨hprefix.2.1, hprefix.2.2.trans (hp.2.trans hraise)⟩,
    ⟨hprecision.1, hmodel.trans hsource⟩, ⟨hprecision.2.1, hsource⟩⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDecompositionBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajorDecomposition_budget (d a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := (p + a) ^ a
      let B := P + (P + c) ^ c + (2 * p + 2) ^ d + 1
      P ≤ (p + C) ^ C ∧
        (P + 2) ^ 4 ≤ (p + C) ^ C ∧
        (((d + 1 : ℕ) : ℝ) ^ 2 + 3) * (B + 2) ≤ (p + C) ^ C ∧
        2 * (((d + 1 : ℕ) : ℝ) ^ 2 + 1) * B ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let B : Polynomial ℕ := P + (P + Polynomial.C c) ^ c +
    (2 * Polynomial.X + 2) ^ d + 1
  let Q : Polynomial ℕ := (P + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.C ((d + 1) ^ 2 + 3) * (B + 2)
  let S : Polynomial ℕ := Polynomial.C (2 * ((d + 1) ^ 2 + 1)) * B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + S)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hQ := natPolynomial_eval_nonneg Q hp
  have hR := natPolynomial_eval_nonneg R hp
  have hS := natPolynomial_eval_nonneg S hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      Q.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      R.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  simpa only [P, B, Q, R, S, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hparts

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ShiftedSmoothFiniteGridLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def shiftedSmoothPositiveGrid {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    Finset (I → ℤ) :=
  (rectangularWeightIndices a S 1).filter
    (fun k => 0 < (shiftedSmoothProductPMF a S hS hZ k).toReal)

theorem shiftedSmoothPositiveGrid_zero_off {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : I → ℤ) (hk : k ∉ shiftedSmoothPositiveGrid a S hS hZ) :
    (shiftedSmoothProductPMF a S hS hZ k).toReal = 0 := by
  by_cases hmem : k ∈ rectangularWeightIndices a S 1
  · have hnot : ¬ 0 < (shiftedSmoothProductPMF a S hS hZ k).toReal :=
      fun hpos => hk (Finset.mem_filter.mpr ⟨hmem, hpos⟩)
    exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
  · exact shiftedSmoothProductPMF_toReal_zero_off a S hS hZ k hmem

noncomputable def shiftedSmoothPositiveGridWeights {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (shiftedSmoothPositiveGrid a S hS hZ) :=
  FiniteProbabilityWeights.ofSupportedPMF (shiftedSmoothProductPMF a S hS hZ)
    (shiftedSmoothPositiveGrid a S hS hZ) (shiftedSmoothPositiveGrid_zero_off a S hS hZ)

@[simp] theorem shiftedSmoothPositiveGridWeights_weight {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : shiftedSmoothPositiveGrid a S hS hZ) :
    (shiftedSmoothPositiveGridWeights a S hS hZ).weight k =
      (shiftedSmoothProductPMF a S hS hZ k.val).toReal := rfl

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem rectangularWeightIndices_normalized_bound {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    (k : rectangularWeightIndices a S 1) (i : I) :
    |rectangularLatticePoint a S k.val i| ≤ 1 := by
  have hi := Fintype.mem_piFinset.mp k.property i
  have h := sampledWeightIndices_mem_bound hi
  change |((k.val i : ℝ) - a i) / S i| ≤ 1
  rw [abs_div, abs_of_pos (hS i), div_le_one (hS i)]
  simpa only [mul_one] using h

theorem shiftedSmoothProductPMF_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) (k : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ k).toReal ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  calc
    _ ≤ ∏ i, 2 / S i := Finset.prod_le_prod
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun i _ => shiftedSmoothCoefficientPMF_le (a i) (hlarge i) (k i))
    _ = _ := by simp only [div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Finset.prod_inv_distrib]

theorem shiftedSmoothProductFiniteWeights_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (k : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight k ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ :=
  shiftedSmoothProductPMF_point_le a S hS hZ hlarge k.val

theorem shiftedSmoothProductFiniteWeights_mean_eq_tsum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → ℝ) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).mean (fun k => f k.val) =
      ∑' k, (shiftedSmoothProductPMF a S hS hZ k).toReal * f k := by
  change (∑ k : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ k.val).toReal * f k.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun k => (shiftedSmoothProductPMF a S hS hZ k).toReal * f k)]
  exact (hasSum_sum_of_ne_finset_zero (fun k hk => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ k hk, zero_mul])).tsum_eq.symm

theorem shiftedSmoothProductFiniteWeights_event_eq_map {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (event : (I → ℤ) → Prop) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability (fun k => event k.val) =
      ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide (event k)) true).toReal := by
  rw [FiniteProbabilityWeights.eventProbability,
    shiftedSmoothProductFiniteWeights_mean_eq_tsum a S hS hZ
      (fun k => if event k then 1 else 0), pmf_map_toReal_indicator]
  apply tsum_congr
  intro k
  simp only [decide_eq_true_eq]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedSmoothPolynomialSublevel
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

noncomputable def shiftedSmoothSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * (2 ^ N * multivariateSublevelConstant N d)

noncomputable def shiftedSmoothSublevelThreshold (N d count : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) count (shiftedSmoothSublevelConstant N d)
    ((d + 1 : ℝ) ^ N) η

theorem shiftedSmoothSublevelConstant_nonneg {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 ≤ shiftedSmoothSublevelConstant N d := by
  unfold shiftedSmoothSublevelConstant
  exact mul_nonneg (by positivity)
    (mul_nonneg (by positivity) (multivariateSublevelConstant_pos hN d).le)

theorem shiftedSmoothSublevelThreshold_pos {N : ℕ} (hN : 0 < N) (d count : ℕ)
    {η : ℝ} (hη : 0 < η) : 0 < shiftedSmoothSublevelThreshold N d count η :=
  polynomialSublevelThreshold_pos _ _ (shiftedSmoothSublevelConstant_nonneg hN d)
    (by positivity) hη

theorem shiftedSmoothProduct_polynomial_sublevel {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (K u : ℝ) (hK : 0 ≤ K) (hu : 0 < u)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability
      (fun k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) P| ≤ u) ≤
      shiftedSmoothSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := shiftedPolynomial_grid_sublevel_bound_of_value hN hd
    (shiftedSmoothProductFiniteWeights a S hS hZ) Subtype.val Subtype.val_injective
    a S hS hδ hδ1 hmesh (rectangularWeightIndices_normalized_bound a S hS)
    P hdeg (2 ^ N) K u (by positivity) hK hu
    (fun k => by simpa only [Fintype.card_fin] using
      shiftedSmoothProductFiniteWeights_point_le a S hS hZ hlarge k)
    hLip x₀ hx₀ hval
  simpa only [shiftedSmoothSublevelConstant, mul_assoc] using h

theorem shiftedSmoothProduct_polynomial_family_threshold {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {T : Type*} [Fintype T]
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : T → MvPolynomial (Fin N) ℝ) (hdeg : ∀ t i, (P t).degreeOf i ≤ d)
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t x y, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x (P t) - MvPolynomial.eval y (P t)| ≤ K * ‖x - y‖)
    (x₀ : T → Fin N → ℝ) (hx₀ : ∀ t i, |x₀ t i| ≤ 1)
    (hval : ∀ t, 1 ≤ |MvPolynomial.eval (x₀ t) (P t)|)
    (hsmall : K * δ ≤ shiftedSmoothSublevelThreshold N d (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |MvPolynomial.eval (rectangularLatticePoint a S k) (P t)| ≤
        shiftedSmoothSublevelThreshold N d (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  let κ := shiftedSmoothSublevelThreshold N d (Fintype.card T) η
  let C := shiftedSmoothSublevelConstant N d
  let scale := (d + 1 : ℝ) ^ N
  have hκ : 0 < κ := shiftedSmoothSublevelThreshold_pos hN d _ hη
  have hC : 0 ≤ C := shiftedSmoothSublevelConstant_nonneg hN d
  have hs : 0 ≤ scale := by positivity
  simp only [decide_eq_classical]
  rw [← shiftedSmoothProductFiniteWeights_event_eq_map a S hS hZ]
  apply ((shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability_union_bound _
    (fun t k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) (P t)| ≤ κ)
    (fun _ h => h)).trans
  calc
    _ ≤ ∑ _t : T, C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro t _
      apply (shiftedSmoothProduct_polynomial_sublevel hN hd a S hS hZ hlarge hδ hδ1 hmesh
        (P t) (hdeg t) K κ hK hκ (hLip t) (x₀ t) (hx₀ t) (hval t)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow
      · exact mul_nonneg (add_nonneg hκ.le (mul_nonneg hK hδ)) hs
      · exact mul_le_mul_of_nonneg_right (by dsimp only [κ] at *; linarith) hs
      · positivity
    _ = (Fintype.card T : ℝ) * C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hC hs hη

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothMatrixBlockBudget
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem matrixBlock_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

theorem smoothMatrixBlock_bad_probability {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {T : Type*} [Fintype T] (entry : T → (Fin n × Fin n ↪ Fin N))
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n N * δ ≤
      shiftedSmoothSublevelThreshold N n (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (entry t (i,j)))| ≤
        shiftedSmoothSublevelThreshold N n (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  have h := shiftedSmoothProduct_polynomial_family_threshold hN hn a S hS hZ hlarge
    hδ hδ1 hη hmesh (fun t => embeddedMatrixDeterminantPolynomial (entry t))
    (fun t => embeddedMatrixDeterminantPolynomial_degree (entry t))
    (embeddedMatrixDeterminantLip n N) (embeddedMatrixDeterminantLip_nonneg n N)
    (fun t => embeddedMatrixDeterminantPolynomial_lipschitz (entry t))
    (fun t => embeddedMatrixIdentityPoint (entry t))
    (fun t => embeddedMatrixIdentityPoint_bound (entry t))
    (fun t => by rw [embeddedMatrixDeterminantPolynomial_identity]; norm_num) hsmall
  simpa only [embeddedMatrixDeterminantPolynomial_eval, matrixBlock_decide_eq_classical] using h

end Erdos3

end

section

namespace Erdos3

theorem embeddedMatrixDeterminantLip_le_exp (n N : ℕ) :
    embeddedMatrixDeterminantLip n N ≤
      Real.exp ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) := by
  have hN : (N : ℝ) ≤ Real.exp (N : ℝ) := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    linarith [Real.add_one_le_exp (n : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  unfold embeddedMatrixDeterminantLip
  calc
    _ ≤ Real.exp (N : ℝ) *
        (Real.exp ((n : ℝ) ^ 2) * (Real.exp (n : ℝ) * Real.exp (n : ℝ))) := by
      gcongr
      exact factorial_le_exp_sq n
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

noncomputable def smoothMatrixBlockMesh (n N : ℕ) (κ : ℝ) : ℝ :=
  min 1 (κ / (embeddedMatrixDeterminantLip n N + 1))

theorem smoothMatrixBlockMesh_spec (n N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < smoothMatrixBlockMesh n N κ ∧ smoothMatrixBlockMesh n N κ ≤ 1 ∧
      embeddedMatrixDeterminantLip n N * smoothMatrixBlockMesh n N κ ≤ κ := by
  have hK := embeddedMatrixDeterminantLip_nonneg n N
  have hK1 : 0 < embeddedMatrixDeterminantLip n N + 1 := by positivity
  have hδ : 0 < smoothMatrixBlockMesh n N κ :=
    lt_min (by norm_num) (div_pos hκ hK1)
  have hmul : smoothMatrixBlockMesh n N κ * (embeddedMatrixDeterminantLip n N + 1) ≤ κ :=
    (le_div_iff₀ hK1).mp (min_le_right 1 (κ / (embeddedMatrixDeterminantLip n N + 1)))
  refine ⟨hδ, min_le_left _ _, ?_⟩
  nlinarith

theorem smoothMatrixBlockMesh_width_spec (n N : ℕ) {κ S : ℝ} (hκ : 0 < κ)
    (hS : max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S) :
    0 < S ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ S ∧
      1 / S ≤ smoothMatrixBlockMesh n N κ := by
  have hδ := (smoothMatrixBlockMesh_spec n N hκ).1
  have hi : (smoothMatrixBlockMesh n N κ)⁻¹ ≤ S := (le_max_right _ _).trans hS
  have hS0 : 0 < S := (inv_pos.mpr hδ).trans_le hi
  refine ⟨hS0, (le_max_left _ _).trans hS, ?_⟩
  have h := (inv_le_inv₀ hS0 (inv_pos.mpr hδ)).mpr hi
  simpa only [inv_inv, one_div] using h

theorem smoothMatrixBlockMesh_inv_le_exp_of_lip_bound (n N : ℕ)
    {κ P Klog : ℝ} (hκ : 0 < κ) (hP : 0 ≤ P) (hKlog : 0 ≤ Klog)
    (hκP : κ⁻¹ ≤ Real.exp P)
    (hK : embeddedMatrixDeterminantLip n N ≤ Real.exp Klog) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤ Real.exp (P + Klog + 1) := by
  have hK1 : embeddedMatrixDeterminantLip n N + 1 ≤ Real.exp (Klog + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hKlog hK
  unfold smoothMatrixBlockMesh
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp (by positivity : 0 ≤ P + Klog + 1)
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Klog + 1) * Real.exp P :=
        mul_le_mul hK1 hκP (inv_nonneg.mpr hκ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothMatrixBlockMesh_inv_le_exp (n N : ℕ) {κ P : ℝ}
    (hκ : 0 < κ) (hP : 0 ≤ P) (hκP : κ⁻¹ ≤ Real.exp P) :
    (smoothMatrixBlockMesh n N κ)⁻¹ ≤
      Real.exp (P + ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1) :=
  smoothMatrixBlockMesh_inv_le_exp_of_lip_bound n N hκ hP (by positivity) hκP
    (embeddedMatrixDeterminantLip_le_exp n N)

end Erdos3

end

section

namespace Erdos3
open scoped Classical

noncomputable def smoothMatrixBlockConstantLogBudget (N n : ℕ) : ℝ :=
  5 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ))

noncomputable def smoothMatrixBlockThresholdLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  (N : ℝ) * n + 2 + ((N * n : ℕ) : ℝ) *
    (smoothMatrixBlockConstantLogBudget N n + count + E + 2)

theorem smoothMatrixBlockConstantLogBudget_nonneg (N n : ℕ) :
    0 ≤ smoothMatrixBlockConstantLogBudget N n := by
  unfold smoothMatrixBlockConstantLogBudget
  positivity

theorem smoothMatrixBlockThresholdLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockThresholdLogBudget N n count E := by
  unfold smoothMatrixBlockThresholdLogBudget
  have := smoothMatrixBlockConstantLogBudget_nonneg N n
  positivity

theorem shiftedSmoothSublevelConstant_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    shiftedSmoothSublevelConstant N n ≤ Real.exp (smoothMatrixBlockConstantLogBudget N n) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hmulti := multivariateSublevelConstant_le_exp N n hn
  have hmulti0 := (multivariateSublevelConstant_pos hN n).le
  unfold shiftedSmoothSublevelConstant smoothMatrixBlockConstantLogBudget
  calc
    _ ≤ (Real.exp 1) ^ N * ((Real.exp 1) ^ N *
        Real.exp (3 * (N : ℝ) + (n + 1 : ℝ) + n * (8 + (n + 1 : ℝ)))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem smoothMatrixBlock_scale_le_exp (N n : ℕ) :
    (n + 1 : ℝ) ^ N ≤ Real.exp ((N : ℝ) * n) := by
  have hb : (n + 1 : ℝ) ≤ Real.exp (n : ℝ) := Real.add_one_le_exp _
  calc
    _ ≤ (Real.exp (n : ℝ)) ^ N := pow_le_pow_left₀ (by positivity) hb N
    _ = _ := (Real.exp_nat_mul (n : ℝ) N).symm

theorem smoothMatrixBlock_threshold_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (shiftedSmoothSublevelThreshold N n count η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget N n count E) := by
  exact polynomialSublevelThreshold_inverse_le_exp (N * n) count
    (shiftedSmoothSublevelConstant_nonneg hN n) (by positivity) hη
    (smoothMatrixBlockConstantLogBudget_nonneg N n) (by positivity) hE
    (shiftedSmoothSublevelConstant_le_exp hN hn)
    (smoothMatrixBlock_scale_le_exp N n) hηb

noncomputable def smoothMatrixBlockMeshLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockThresholdLogBudget N n count E +
    ((N : ℝ) + (n : ℝ) ^ 2 + 2 * n) + 1

noncomputable def smoothMatrixBlockWidthLogBudget (N n count : ℕ) (E : ℝ) : ℝ :=
  smoothMatrixBlockMeshLogBudget N n count E + 8 + probabilityProfileLipschitz

theorem smoothMatrixBlockMeshLogBudget_nonneg (N n count : ℕ)
    {E : ℝ} (hE : 0 ≤ E) : 0 ≤ smoothMatrixBlockMeshLogBudget N n count E := by
  unfold smoothMatrixBlockMeshLogBudget
  have := smoothMatrixBlockThresholdLogBudget_nonneg N n count hE
  positivity

theorem smoothMatrixBlock_actual_mesh_inverse_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockMeshLogBudget N n count E) :=
  smoothMatrixBlockMesh_inv_le_exp n N (shiftedSmoothSublevelThreshold_pos hN n count hη)
    (smoothMatrixBlockThresholdLogBudget_nonneg N n count hE)
    (smoothMatrixBlock_threshold_inverse_le_exp hN hn count hη hE hηb)

theorem smoothMatrixBlock_actual_width_le_exp {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (count : ℕ)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    max (8 * (probabilityProfileLipschitz : ℝ))
      (smoothMatrixBlockMesh n N (shiftedSmoothSublevelThreshold N n count η))⁻¹ ≤
      Real.exp (smoothMatrixBlockWidthLogBudget N n count E) := by
  have hB := smoothMatrixBlockMeshLogBudget_nonneg N n count hE
  have hL : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  apply max_le
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    have hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
      linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
    calc
      _ ≤ Real.exp 8 * Real.exp probabilityProfileLipschitz :=
        mul_le_mul h8 hLip hL (Real.exp_pos _).le
      _ = Real.exp (8 + probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold smoothMatrixBlockWidthLogBudget; linarith)
  · apply (smoothMatrixBlock_actual_mesh_inverse_le_exp hN hn count hη hE hηb).trans
    apply Real.exp_le_exp.mpr
    unfold smoothMatrixBlockWidthLogBudget
    linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AlgebraicMajorWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem majorShiftCoordinates_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (j : B) :
    majorShiftCoordinates e j ∈ weightedSupportLE (Sum.elim v w) (w j) := by
  exact (weightedSupportLE _ _).add_mem
    (weightedSupportLE_X (Sum.elim v w) (Sum.inr j))
    (weightedSupportLE_rename_inl_ring v w (he j))

theorem majorShiftSubstitution_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (i : U ⊕ B) :
    majorShiftSubstitution e i ∈ weightedSupportLE (Sum.elim v w) (Sum.elim v w i) := by
  cases i with
  | inl i => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)
  | inr j => exact majorShiftCoordinates_weightedSupportLE v w e he j

theorem majorSlowPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (D0 : MvPolynomial B R) (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) {d : ℕ}
    (hD0 : D0 ∈ weightedSupportLE w d)
    (hE : E ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) :
    majorSlowPolynomial D0 E V e ∈ weightedSupportLE (Sum.elim v w) d := by
  unfold majorSlowPolynomial
  apply (weightedSupportLE _ _).sub_mem
  · apply (weightedSupportLE _ _).add_mem (weightedSupportLE_rename_inr_ring v w hD0)
    exact weightedSupportLE_aeval (Sum.elim v w) (Sum.elim v w)
      (majorShiftSubstitution e) (majorShiftSubstitution_weightedSupportLE v w e he) hE
  · exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates e)
      (majorShiftCoordinates_weightedSupportLE v w e he) hV

theorem majorRationalPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (Q : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (a : B → MvPolynomial U R) {d : ℕ}
    (hQ : Q ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (ha : ∀ j, a j ∈ weightedSupportLE v (w j)) :
    majorRationalPolynomial Q V a ∈ weightedSupportLE (Sum.elim v w) d := by
  apply (weightedSupportLE _ _).add_mem hQ
  exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates (-a))
    (majorShiftCoordinates_weightedSupportLE v w (-a)
      (fun j => (weightedSupportLE v (w j)).neg_mem (ha j))) hV

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in

theorem map_polynomialLinearRestriction_ratCast
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) :=
  map_eval₂ (algebraMap ℚ ℝ) (linearCoordinatePolynomial A) P

omit [Fintype σ] [Fintype τ] in

theorem polynomialDenominator_coefficientGrid (P : MvPolynomial σ ℚ) :
    (fun m => P.coeff m) ∈ denominatorGrid (polynomialDenominator P) := by
  classical
  refine ⟨fun m => if hm : m ∈ P.support then
    clearedArray (fun n : P.support => P.coeff n.val) ⟨m, hm⟩ else 0, ?_⟩
  intro m
  change (polynomialDenominator P : ℚ) * P.coeff m = _
  by_cases hm : m ∈ P.support
  · simp only [dif_pos hm]
    exact (clearedArray_cast (fun n : P.support => P.coeff n.val) ⟨m, hm⟩).symm
  · simp [hm, notMem_support_iff.mp hm]

theorem linearCoordinatePolynomial_realCoefficientGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun i j => A (Pi.single j 1) i))
      (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) := by
  classical
  let M : Matrix σ τ ℚ := fun i j => A (Pi.single j 1) i
  have hc (j : τ) : ((clearedMatrix M i j : ℤ) : ℝ) =
      (matrixDenominator M : ℝ) * (M i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast M) i) j
    change ((clearedMatrix M i j : ℤ) : ℚ) = (matrixDenominator M : ℚ) * M i j at h
    exact_mod_cast h
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨∑ j, C (clearedMatrix M i j) * X j, ?_⟩
  simp only [linearCoordinatePolynomial, ← C_mul', map_sum, map_mul, map_C, map_X,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  simp only [hcast, Int.coe_castRingHom]
  rw [hc, map_mul, mul_assoc]
  simp only [M]
  congr 3
  apply congrArg (fun x : τ → ℚ => (A x i : ℝ))
  ext k
  simp [Pi.single_apply]

theorem polynomialLinearRestriction_denominatorGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    (d : ℕ) (hd : P.totalDegree ≤ d) :
    (fun m => (polynomialLinearRestriction A P).coeff m) ∈
      denominatorGrid (polynomialDenominator P *
        matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [map_polynomialLinearRestriction_ratCast]
  apply realPolynomialCoefficientGrid_substitute
  · apply le_trans (b := P.totalDegree) ?_ hd
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (polynomialDenominator_coefficientGrid P)
  · exact linearCoordinatePolynomial_realCoefficientGrid A

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem rationalPolynomial_realMass_le {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) {K d : ℕ}
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) P) ≤
      ((Fintype.card σ + 1) ^ d * K : ℕ) := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (support_map_subset (algebraMap ℚ ℝ) P)]
  have hc : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d (fun _ hm => (le_totalDegree hm).trans hd)
  calc
    _ ≤ ∑ _m ∈ P.support, (K : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      rw [coeff_map]
      exact (hP m).abs_real_le
    _ = (P.support.card : ℝ) * K := by simp
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right K hc

theorem linearCoordinatePolynomial_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) (i : σ) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) ≤
      (Fintype.card τ * H : ℕ) := by
  classical
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  rw [linearCoordinatePolynomial, map_sum]
  simp only [← C_mul', map_mul, map_C, map_X, hcast]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : τ, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply (realPolynomialMass_C_mul_le _ _).trans
      rw [realPolynomialMass_X, mul_one]
      convert (hA i j).abs_real_le using 1 <;> first | rfl | congr!
    _ = _ := by simp

theorem polynomialLinearRestriction_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have he : map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) := map_eval₂ _ _ _
  rw [he]
  have hd' : (map (algebraMap ℚ ℝ) P).totalDegree ≤ d := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)).trans hd
  have hmass := realPolynomialMass_substitution_le (map (algebraMap ℚ ℝ) P)
    (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
    (M := (Fintype.card τ * H + 1 : ℕ)) (by exact_mod_cast Nat.le_add_left 1 _)
    (fun i => (linearCoordinatePolynomial_realMass_le A hA i).trans
      (by exact_mod_cast Nat.le_succ (Fintype.card τ * H))) hd'
  refine hmass.trans ?_
  simpa only [Nat.cast_mul, Nat.cast_pow] using mul_le_mul_of_nonneg_right
    (rationalPolynomial_realMass_le P hP hd)
    (pow_nonneg (Nat.cast_nonneg (Fintype.card τ * H + 1)) d)

theorem polynomialLinearRestriction_coeff_abs_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) (m : τ →₀ ℕ) :
    |(((polynomialLinearRestriction A P).coeff m : ℚ) : ℝ)| ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have h := (realPolynomialMass_coeff_le
    (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) m).trans
      (polynomialLinearRestriction_realMass_le A P hA hP hd)
  rw [coeff_map] at h
  exact h

theorem rationalHeightLE_of_integral_mul_of_abs_le (q : ℚ) {Q B D : ℕ}
    (hQ : 0 < Q) (hQD : Q ≤ D) (hB : 1 ≤ B)
    (hint : ∃ z : ℤ, (Q : ℚ) * q = z) (habs : |(q : ℝ)| ≤ B) :
    RationalHeightLE q (B * D) := by
  obtain ⟨z, hz⟩ := hint
  have hzR : (Q : ℝ) * (q : ℝ) = z := by exact_mod_cast hz
  have hzbound : z.natAbs ≤ B * D := by
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    rw [← hzR, abs_mul, abs_of_nonneg (Nat.cast_nonneg Q)]
    exact (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg Q)).trans
      (by nlinarith [show (Q : ℝ) ≤ D by exact_mod_cast hQD])
  have he : q = (z : ℚ) / (Q : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hQ.ne' : ((Q : ℤ) : ℚ) ≠ 0)).mpr
    simpa only [Int.cast_natCast, mul_comm] using hz
  rw [he]
  exact rationalHeightLE_fraction z Q (by exact_mod_cast hQ.ne') hzbound
    (by simpa only [Int.natAbs_natCast] using hQD.trans (Nat.le_mul_of_pos_left D hB))

theorem polynomialLinearRestriction_height
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    RationalPolynomialHeightLE (polynomialLinearRestriction A P)
      (linearRestrictionHeight (Fintype.card σ) (Fintype.card τ) d H K) := by
  have hK : 0 < K := hP.one_le
  have hmasspos : 1 ≤ ((Fintype.card σ + 1) ^ d * K) *
      (Fintype.card τ * H + 1) ^ d := by
    change 0 < ((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d
    positivity
  obtain ⟨z, hz⟩ := polynomialLinearRestriction_denominatorGrid A P d hd
  intro m
  exact rationalHeightLE_of_integral_mul_of_abs_le _
    (polynomialLinearRestriction_denominator_pos A P d)
    (polynomialLinearRestriction_denominator_le A P hd hP hA)
    hmasspos ⟨z m, hz m⟩ (polynomialLinearRestriction_coeff_abs_le A P hA hP hd m)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardPolynomialCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForward_polynomial_cap (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      P.eval₂ (Nat.castRingHom ℝ)
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x) ≤
        preparedFiniteForwardCap A stageCountConstant n x := by
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hCA hx hg hs
  have hprec := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  exact (hpoly _ (add_nonneg hprec.2.1 hw)).trans
    (preparedFiniteForward_phase_cap A stageCountConstant n C hx hg hs hCA)

theorem exists_preparedFiniteForward_composed_phase_cap (Cnative Cmajor : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog pMajor : ℝ}, C ≤ A → 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → 0 ≤ pMajor →
      pMajor ≤ (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cnative) ^ Cnative →
      (pMajor + Cmajor) ^ Cmajor ≤ preparedFiniteForwardCap A stageCountConstant n x := by
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C Cnative) ^ Cnative +
    Polynomial.C Cmajor) ^ Cmajor
  obtain ⟨C, hC, hpoly⟩ := exists_preparedFiniteForward_polynomial_cap P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog pMajor hCA hx hg hs hp hbound
  apply le_trans (pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg Cmajor))
    (add_le_add hbound (le_refl (Cmajor : ℝ))) Cmajor)
  simpa [P, Polynomial.eval₂_pow] using hpoly A stageCountConstant n hCA hx hg hs

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialFromRealGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem exists_rationalPolynomial_of_realCoefficientGrid
    {σ : Type*} (P : MvPolynomial σ ℝ) {q : ℕ} (hq : 0 < q)
    (hP : realPolynomialCoefficientGrid q P) :
    ∃ Q : MvPolynomial σ ℚ,
      MvPolynomial.map (algebraMap ℚ ℝ) Q = P ∧
      (fun α => Q.coeff α) ∈ denominatorGrid q ∧ Q.totalDegree = P.totalDegree := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  obtain ⟨z, hz⟩ := hP
  have hrange : P ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨α, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    refine ⟨(z α : ℚ) / (q : ℚ), ?_⟩
    have hα : (z α : ℝ) = (q : ℝ) * P.coeff α := congrFun hz α
    simp only [map_div₀, map_intCast, map_natCast, hα, mul_div_cancel_left₀ _ hq0]
  obtain ⟨Q, hQ⟩ := hrange
  refine ⟨Q, hQ, ?_, ?_⟩
  · apply (realPolynomialCoefficientGrid_ratCast_iff q Q).mp
    rw [hQ]
    exact ⟨z, hz⟩
  · rw [← hQ]
    unfold totalDegree
    rw [MvPolynomial.support_map_of_injective Q (algebraMap ℚ ℝ).injective]

end Erdos3

end

end OAI

end


