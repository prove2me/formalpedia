-- Prove2me | Definitions.Def_OAIErdos3B014
-- name    : OAIErdos3B014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T11:08:43.496026+00:00
-- url     : https://prove2.me/theorems/a229cbc7-79ca-4395-811b-ad5d2d5c74b8
-- title:
--   OpenAI Erdős-3 split, definitions bundle 15 of 88
-- statement:
--   Definitions bundle 15 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B013`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 15 available.
--
--   Modules: `OAI.Erdos3.BasisGradedSubmodule`, `OAI.Erdos3.BasisGradedSubmodule.baseChange`, `OAI.Erdos3.BasisGradedSubmodule.below_mem`, `OAI.Erdos3.BasisGradedSubmodule.coordinate_dilation_mem`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.Param`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.Proper`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.card_carrier_of_proper`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.carrier`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff_abs_le`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff_sub_abs_le_two_mul`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval_eq_eval_minParam_add_sum`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval_predParam_add_eval_unitParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval_unitParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.minParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.minParam_apply`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.predParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.predParam_apply_ne`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.predParam_apply_self`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.sum_predParam_add_one`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.unitParam`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.unitParam_apply_ne`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.unitParam_apply_self`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.zero`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.zero_carrier`, `OAI.Erdos3.BohrProgression.CyclicCenteredGAP.zero_proper`, `OAI.Erdos3.BohrProgression.abs_det_matrixOf_bohrLatticeBasis`, `OAI.Erdos3.BohrProgression.abs_intCast_bohrCertificateCombination_le`, `OAI.Erdos3.BohrProgression.abs_intCast_bohrCertificatePoint_le`, `OAI.Erdos3.BohrProgression.bohrCertificateCoeff`, `OAI.Erdos3.BohrProgression.bohrCertificateCoeff_spec`, `OAI.Erdos3.BohrProgression.bohrCertificateCombination`, `OAI.Erdos3.BohrProgression.bohrCertificateCombination_cast_coordinate`, `OAI.Erdos3.BohrProgression.bohrCertificatePoint`, `OAI.Erdos3.BohrProgression.bohrCertificatePoint_independent`, `OAI.Erdos3.BohrProgression.bohrCertificate_scale_pos`, `OAI.Erdos3.BohrProgression.bohrCyclicProgression`, `OAI.Erdos3.BohrProgression.bohrCyclicProgression_card_lower_bound`, `OAI.Erdos3.BohrProgression.bohrCyclicProgression_carrier_subset`, `OAI.Erdos3.BohrProgression.bohrCyclicProgression_proper`, `OAI.Erdos3.BohrProgression.bohrLatticeBasis`, `OAI.Erdos3.BohrProgression.bohrLatticeBasis_apply`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrix`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrixInt`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrixInt_zero_succ`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrix_succ_succ`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrix_zero_succ`, `OAI.Erdos3.BohrProgression.bohrLatticeMatrix_zero_zero`, `OAI.Erdos3.BohrProgression.bohrLatticePoint`, `OAI.Erdos3.BohrProgression.bohrLatticePoint_cast_coordinate`, `OAI.Erdos3.BohrProgression.bohrLatticePoint_zero`, `OAI.Erdos3.BohrProgression.bohrProgressionRadius`, `OAI.Erdos3.BohrProgression.bohrProgressionRadius_mul_scale_le`, `OAI.Erdos3.BohrProgression.bohrSuccessiveCertificate`, `OAI.Erdos3.BohrProgression.det_bohrLatticeMatrix`, `OAI.Erdos3.BohrProgression.det_bohrLatticeMatrix_ne_zero`, `OAI.Erdos3.BohrProgression.eval_bohrCyclicProgression`, `OAI.Erdos3.BohrProgression.exists_large_proper_progression`, `OAI.Erdos3.BohrProgression.exists_large_proper_progression_all`, `OAI.Erdos3.BohrProgression.exists_proper_progression_of_quartic_bounds`, `OAI.Erdos3.BohrProgression.exists_proper_progression_subset`, `OAI.Erdos3.BohrProgression.indexedCyclicCharacter`, `OAI.Erdos3.BohrProgression.indexedCyclicCharacter_zero`, `OAI.Erdos3.BohrProgression.intCastVec_bohrCertificatePoint`, `OAI.Erdos3.BohrProgression.intCastVec_bohrLatticePoint`, `OAI.Erdos3.BohrProgression.int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt`, `OAI.Erdos3.BohrProgression.inv_scale_le_two_mul_bohrProgressionRadius_add_one`, `OAI.Erdos3.BohrProgression.matrixOf_bohrLatticeBasis`, `OAI.Erdos3.BohrProgression.minkowskiSecondConstant_le_exp`, `OAI.Erdos3.BohrProgression.progression_size_factor_lower_bound`, `OAI.Erdos3.BooleanCubeKernel.exists_integral_vector_mode_witness`, `OAI.Erdos3.BooleanCubeKernel.integerCubeWitnessBound`, `OAI.Erdos3.BooleanCubeKernel.integerCubeWitnessBound_nonneg`, `OAI.Erdos3.BooleanCubeKernel.integer_coefficient_le_mass`, `OAI.Erdos3.C_int_mem_integralRealPolynomialSubring`, `OAI.Erdos3.CellRefinement.replacementIntegral`, `OAI.Erdos3.CircleFourier.character_affine_integer_combination`, `OAI.Erdos3.CircleFourier.exists_real_character_phase`, `OAI.Erdos3.CoefficientFiberControl.recOn`, `OAI.Erdos3.CyclicBohr.Set`, `OAI.Erdos3.CyclicBohr.Set.IsRankRegular`, `OAI.Erdos3.CyclicBohr.Set.add_mem_dilate`, `OAI.Erdos3.CyclicBohr.Set.add_mem_ndilate`, `OAI.Erdos3.CyclicBohr.Set.add_mem_of_mem`, `OAI.Erdos3.CyclicBohr.Set.approximationWidth`, `OAI.Erdos3.CyclicBohr.Set.card_pos`, `OAI.Erdos3.CyclicBohr.Set.carrier`, `OAI.Erdos3.CyclicBohr.Set.carrier_meet_subset_left`, `OAI.Erdos3.CyclicBohr.Set.carrier_meet_subset_right`, `OAI.Erdos3.CyclicBohr.Set.carrier_mono`, `OAI.Erdos3.CyclicBohr.Set.carrier_ndilate_mono`, `OAI.Erdos3.CyclicBohr.Set.carrier_ndilate_whole`, `OAI.Erdos3.CyclicBohr.Set.carrier_nonempty`, `OAI.Erdos3.CyclicBohr.Set.carrier_whole`, `OAI.Erdos3.CyclicBohr.Set.character_neg_index`, `OAI.Erdos3.CyclicBohr.Set.dilate`, `OAI.Erdos3.CyclicBohr.Set.dilate_dilate`, `OAI.Erdos3.CyclicBohr.Set.dilate_mono`, `OAI.Erdos3.CyclicBohr.Set.dilate_one`, `OAI.Erdos3.CyclicBohr.Set.exists_controlled_regular_subdilate`, `OAI.Erdos3.CyclicBohr.Set.exists_rankRegular_ndilate`, `OAI.Erdos3.CyclicBohr.Set.frequencies_dilate`, `OAI.Erdos3.CyclicBohr.Set.frequencies_meet`, `OAI.Erdos3.CyclicBohr.Set.frequencies_ofFrequencies`, `OAI.Erdos3.CyclicBohr.Set.initialSamplingScale`, `OAI.Erdos3.CyclicBohr.Set.instMembershipZMod`, `OAI.Erdos3.CyclicBohr.Set.isRankRegular_ndilate_iff`, `OAI.Erdos3.CyclicBohr.Set.isRankRegular_whole`, `OAI.Erdos3.CyclicBohr.Set.log_card_growth_lt_five_mul_rank`, `OAI.Erdos3.CyclicBohr.Set.lowerApprox`, `OAI.Erdos3.CyclicBohr.Set.meet`, `OAI.Erdos3.CyclicBohr.Set.mem_carrier`, `OAI.Erdos3.CyclicBohr.Set.mem_iff`, `OAI.Erdos3.CyclicBohr.Set.ndilate`, `OAI.Erdos3.CyclicBohr.Set.ndilate_ndilate`, `OAI.Erdos3.CyclicBohr.Set.ndilate_one`, `OAI.Erdos3.CyclicBohr.Set.neg_mem_iff`, `OAI.Erdos3.CyclicBohr.Set.norm_one_sub_character_neg_index`, `OAI.Erdos3.CyclicBohr.Set.norm_one_sub_prod_le_sum`, `OAI.Erdos3.CyclicBohr.Set.normalizedLogCard`, `OAI.Erdos3.CyclicBohr.Set.normalizedLogCard_buffer_growth`, `OAI.Erdos3.CyclicBohr.Set.normalizedLogCard_monotone`, `OAI.Erdos3.CyclicBohr.Set.ofFrequencies`, `OAI.Erdos3.CyclicBohr.Set.radius_dilate`, `OAI.Erdos3.CyclicBohr.Set.radius_meet`, `OAI.Erdos3.CyclicBohr.Set.radius_ndilate`, `OAI.Erdos3.CyclicBohr.Set.radius_ofFrequencies`, `OAI.Erdos3.CyclicBohr.Set.radius_whole`, `OAI.Erdos3.CyclicBohr.Set.rank`, `OAI.Erdos3.CyclicBohr.Set.rank_dilate`, `OAI.Erdos3.CyclicBohr.Set.rank_meet_le`, `OAI.Erdos3.CyclicBohr.Set.rank_ndilate`, `OAI.Erdos3.CyclicBohr.Set.rank_ofFrequencies`, `OAI.Erdos3.CyclicBohr.Set.rank_whole`, `OAI.Erdos3.CyclicBohr.Set.sub_mem_dilate`, `OAI.Erdos3.CyclicBohr.Set.sub_mem_ndilate`, `OAI.Erdos3.CyclicBohr.Set.torusLowerApprox`, `OAI.Erdos3.CyclicBohr.Set.torusUpperApprox`, `OAI.Erdos3.CyclicBohr.Set.uniformMass_translation_le_of_rankRegular`, `OAI.Erdos3.CyclicBohr.Set.uniformMass_translation_le_shell`, `OAI.Erdos3.CyclicBohr.Set.upperApprox`, `OAI.Erdos3.CyclicBohr.Set.whole`, `OAI.Erdos3.CyclicBohr.Set.zero_mem`, `OAI.Erdos3.CyclicBohr.abs_arg_character_le_two_radius`, `OAI.Erdos3.CyclicBohr.abs_arg_sub_lt_half_radius_of_localArgBin_eq`, `OAI.Erdos3.CyclicBohr.abs_localScaledArg_sub_lt_one_of_localArgBin_eq`, `OAI.Erdos3.CyclicBohr.argBin`, `OAI.Erdos3.CyclicBohr.argumentCode`, `OAI.Erdos3.CyclicBohr.card_argumentCodeSpace`, `OAI.Erdos3.CyclicBohr.card_carrier_le_nine_pow_rank_mul_card_half`, `OAI.Erdos3.CyclicBohr.card_le_dyadic_dilate`, `OAI.Erdos3.CyclicBohr.card_localArgumentCodeSpace`, `OAI.Erdos3.CyclicBohr.card_two_le_nine_pow_three_rank_mul_card_quarter`, `OAI.Erdos3.CyclicBohr.character`, `OAI.Erdos3.CyclicBohr.character_add`, `OAI.Erdos3.CyclicBohr.character_add_index`, `OAI.Erdos3.CyclicBohr.character_comm`, `OAI.Erdos3.CyclicBohr.character_eq_one_mul`, `OAI.Erdos3.CyclicBohr.character_zero`, `OAI.Erdos3.CyclicBohr.character_zero_index`, `OAI.Erdos3.CyclicBohr.exists_real_frequency_phase`, `OAI.Erdos3.CyclicBohr.localArgBin`, `OAI.Erdos3.CyclicBohr.localArgumentCode`, `OAI.Erdos3.CyclicBohr.localScaledArg`, `OAI.Erdos3.CyclicBohr.localScaledArg_le_eight`, `OAI.Erdos3.CyclicBohr.localScaledArg_nonneg`, `OAI.Erdos3.CyclicBohr.norm_character`, `OAI.Erdos3.CyclicBohr.norm_one_sub_character_intCast`, `OAI.Erdos3.CyclicBohr.norm_one_sub_character_le_of_mul_eq_intCast`, `OAI.Erdos3.CyclicBohr.norm_one_sub_character_sub`, `OAI.Erdos3.CyclicBohr.norm_one_sub_mul_of_norm_le_one`, `OAI.Erdos3.CyclicBohr.norm_sub_le_abs_arg_sub_of_norm_eq_one`, `OAI.Erdos3.CyclicBohr.relative_card_lower_bound`, `OAI.Erdos3.CyclicBohr.scaledArg`, `OAI.Erdos3.CyclicBohr.scaledArg_le`, `OAI.Erdos3.CyclicBohr.sub_mem_half_dilate_of_localArgumentCode_eq`, `OAI.Erdos3.CyclicCrootSisask.abs_setAverageTranslate_le`, `OAI.Erdos3.CyclicCrootSisask.centeredTranslate`, `OAI.Erdos3.CyclicCrootSisask.exists_local_shift_fiber`, `OAI.Erdos3.CyclicCrootSisask.global_sampleDeviation_input_moment`, `OAI.Erdos3.CyclicCrootSisask.global_sampleDeviation_moment`, `OAI.Erdos3.CyclicCrootSisask.goodSamples`, `OAI.Erdos3.CyclicCrootSisask.goodSamples_give_almost_period`, `OAI.Erdos3.CyclicCrootSisask.markov_card_good`, `OAI.Erdos3.CyclicCrootSisask.mem_goodSamples`, `OAI.Erdos3.CyclicCrootSisask.pointwise_sampleDeviation_moment`, `OAI.Erdos3.CyclicCrootSisask.sampleDeviation`, `OAI.Erdos3.CyclicCrootSisask.sampleDeviation_sub_const_identity`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate`, `OAI.Erdos3.CyclicCrootSisask.sum_centeredTranslate_eq_zero`, `OAI.Erdos3.CyclicCrootSisask.sum_centeredTranslate_pow_le`, `OAI.Erdos3.CyclicCrootSisask.sum_setAverageTranslate_pow_le`, `OAI.Erdos3.FilteredLieTree.eval_mem_weighted_span`, `OAI.Erdos3.FiniteCubeSlice.radius`, `OAI.Erdos3.FiniteCubeSlice.recOn`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_finitePushforward_relativeSlice`, `OAI.Erdos3.FiniteProbabilityWeights.exists_large_correlating_fiber`, `OAI.Erdos3.FiniteProbabilityWeights.fiberComplexMean`, `OAI.Erdos3.FiniteProbabilityWeights.fiberComplexMean_eq_condition`, `OAI.Erdos3.FiniteProbabilityWeights.mass_mul_condition_complexMean`, `OAI.Erdos3.FiniteProbabilityWeights.sum_fiberComplexMean_on`, `OAI.Erdos3.FiniteProbabilityWeights.translated_subset_mixture_compare`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_condition_complexMean`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_finitePushforward_complexMean`, `OAI.Erdos3.FiniteTupleDependsOn`, `OAI.Erdos3.FiniteTupleDependsOn.snoc`, `OAI.Erdos3.FixedDensity.DescendingGrowthHierarchy`, `OAI.Erdos3.FixedDensity.DescendingGrowthHierarchy.antitone`, `OAI.Erdos3.FixedDensity.DescendingGrowthHierarchy.growth_eq_upper`, `OAI.Erdos3.FixedDensity.DescendingGrowthHierarchy.lower_le_growth`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.recOn`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedAllRankTowerHierarchy`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedAllRankTowerHierarchy_last`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedFineLayerMaximum`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedRankTowerHierarchy`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedRankTowerHierarchy_last`, `OAI.Erdos3.FixedDensity.GrowthFunctionOrderedComplexRegularityCertificate.selectedRankTowerHierarchy_zero`, `OAI.Erdos3.FixedDensity.boundedGrowthRegularityOneStepMaximum`, `OAI.Erdos3.FixedDensity.boundedGrowthRegularityOneStepMaximum_monotone`, `OAI.Erdos3.FixedDensity.canonicalDescendingGrowthHierarchy`, `OAI.Erdos3.FixedDensity.canonicalDescendingGrowthHierarchy_last`, `OAI.Erdos3.FixedDensity.canonicalDescendingGrowthHierarchy_zero`, `OAI.Erdos3.FixedDensity.finiteMaximum`, `OAI.Erdos3.FixedDensity.finiteRankGrowthRegularityOneStepMaximum`, `OAI.Erdos3.FixedDensity.finiteRankGrowthRegularityOneStepMaximum_monotone`, `OAI.Erdos3.FixedDensity.growthRegularityComplexity_succ_eq_oneStep`, `OAI.Erdos3.FixedDensity.growthRegularityOneStep`, `OAI.Erdos3.FixedDensity.selectedGrowthCoarseComplexityBound`, `OAI.Erdos3.FixedDensity.selectedGrowthCoarseLayerComplexityBound`, `OAI.Erdos3.FixedDensity.selectedGrowthFineComplexityBound`, `OAI.Erdos3.FixedDensity.selectedGrowthFineLayerComplexityBound`, `OAI.Erdos3.FixedDensity.towerDominatingGrowth`, `OAI.Erdos3.FixedDensity.towerDominatingGrowthIteration`, `OAI.Erdos3.FixedDensity.towerDominatingGrowthIteration_succ`, `OAI.Erdos3.FixedDensity.towerDominatingGrowthIteration_zero`, `OAI.Erdos3.FixedDensity.towerDominatingGrowth_apply`, `OAI.Erdos3.FreimanModel.card_difference_image_of_freiman`, `OAI.Erdos3.FreimanModel.card_fiveTermValues_le`, `OAI.Erdos3.FreimanModel.card_image_eq_of_same_fibers`, `OAI.Erdos3.FreimanModel.card_sub_le_of_fourfold_subset`, `OAI.Erdos3.FreimanModel.exists_dense_cyclic_model`, `OAI.Erdos3.FreimanModel.exists_nonempty_large_fiber`, `OAI.Erdos3.FreimanModel.fiveTermValue`, `OAI.Erdos3.FreimanModel.fiveTermValue_eq_iff`, `OAI.Erdos3.FreimanModel.sub_subset_fiveTermValues`, `OAI.Erdos3.LieTreeOccurrences`, `OAI.Erdos3.LocalConvolution.balancedFunction`, `OAI.Erdos3.LocalConvolution.localMomentExponentFactor`, `OAI.Erdos3.LocalConvolution.localMomentGain`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairFiltration`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairFiltrationLayerEquiv`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairFirst`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairLayer`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairLayer_antitone`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairLayer_terminal`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairLayer_top_relation`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairSecond`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairTop_relation`, `OAI.Erdos3.NilpotentLieFiltration.lieTreeEval_mem_rankLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_dilationPairFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.mem_dilationPairLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_dilationPairSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_eq_weighted_tree_span`, `OAI.Erdos3.PolynomialPatch.coordinateFiber`, `OAI.Erdos3.PolynomialPatch.coordinateFiber_value`, `OAI.Erdos3.PolynomialPatch.exists_coordinate_fiber_score`, `OAI.Erdos3.RelativeChangSanders.card_weightedDissociated_realFinsetIndicator_le`, `OAI.Erdos3.RelativeChangSanders.card_weightedDissociated_relativeLargeSpectrum_le`, `OAI.Erdos3.RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff`, `OAI.Erdos3.RelativeSpectrumBridge.sum_realFinsetIndicator_mul_character_eq_const_mul`, `OAI.Erdos3.RelativeSpectrumBridge.sum_realFinsetIndicator_mul_eq_const_mul_card`, `OAI.Erdos3.ResidueBoxSlice.fiberIntegerPoint`, `OAI.Erdos3.ResidueBoxSlice.fiberInverseParameters`, `OAI.Erdos3.ResidueBoxSlice.fiberInverseParameters_degree`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_integerPoint_value`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_kernel`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_lip`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_point_value`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_value`, `OAI.Erdos3.ResidueBoxSlice.fiberReinsertPatch_weight`, `OAI.Erdos3.ResidueBoxSlice.fullSliceLaw_complexMean`, `OAI.Erdos3.SpatialSiteLabel`, `OAI.Erdos3.SymmetricIntegerInterval`, `OAI.Erdos3.TailReflectionData.correlation`, `OAI.Erdos3.TailReflectionData.correlation_square_le_pair`, `OAI.Erdos3.TailReflectionData.exists_reflected_correlation`, `OAI.Erdos3.TailReflectionData.noConfusion`, `OAI.Erdos3.TailReflectionData.pair`, `OAI.Erdos3.TailReflectionData.reflectedKernel`, `OAI.Erdos3.TailReflectionData.reflectedKernel_cons`, `OAI.Erdos3.VectorPolynomial.BoundedCoefficientExponent`, `OAI.Erdos3.VectorPolynomial.CoefficientArray`, `OAI.Erdos3.VectorPolynomial.CoefficientSlot`, `OAI.Erdos3.VectorPolynomial.Homogeneous`, `OAI.Erdos3.VectorPolynomial.MonomialRowBound`, `OAI.Erdos3.VectorPolynomial.boundedCoefficientExponentFintype`, `OAI.Erdos3.VectorPolynomial.boundedCoefficientExponent_card_le`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_eq_zero_iff`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_single`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional_monomial`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional_rowBound`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional_unit`, `OAI.Erdos3.VectorPolynomial.coefficients_homogeneousPart`, `OAI.Erdos3.VectorPolynomial.coefficients_ofCoordinates_basisFun`, `OAI.Erdos3.VectorPolynomial.coefficients_ofCoordinates_mem_realDenominatorGrid`, `OAI.Erdos3.VectorPolynomial.contractedRow`, `OAI.Erdos3.VectorPolynomial.contractedRow_apply`, `OAI.Erdos3.VectorPolynomial.contractedRow_le_mass`, `OAI.Erdos3.VectorPolynomial.contractedRow_prod_bound`, `OAI.Erdos3.VectorPolynomial.coordinate_homogeneousPart`, `OAI.Erdos3.VectorPolynomial.curried_nonfactor`, `OAI.Erdos3.VectorPolynomial.eq_of_homogeneous_tmul`, `OAI.Erdos3.VectorPolynomial.exists_homogeneous_monomial_nonzero`, `OAI.Erdos3.VectorPolynomial.exists_restricted_coefficient_nonzero`, `OAI.Erdos3.VectorPolynomial.homogeneousPart`, `OAI.Erdos3.VectorPolynomial.homogeneousPart_homogeneous`, `OAI.Erdos3.VectorPolynomial.homogeneousPart_tmul`, `OAI.Erdos3.VectorPolynomial.homogeneous_empty_factorization_iff`, `OAI.Erdos3.VectorPolynomial.homogeneous_support_degree`, `OAI.Erdos3.VectorPolynomial.homogeneous_tmul`, `OAI.Erdos3.VectorPolynomial.siteEvaluation`, `OAI.Erdos3.VectorPolynomial.siteEvaluation_tmul`, `OAI.Erdos3.VectorPolynomial.siteFunctional`, `OAI.Erdos3.VectorPolynomial.siteFunctional_tmul`, `OAI.Erdos3.VectorPolynomial.sub_homogeneousPart_degreeLE`, `OAI.Erdos3.WeightedLoweringAut`, `OAI.Erdos3.WeightedLoweringAut.difference_lower`, `OAI.Erdos3.WeightedLoweringAut.ofHom`, `OAI.Erdos3.WeightedLoweringAut.preserves_degree`, `OAI.Erdos3.X_mem_integralRealPolynomialSubring`, `OAI.Erdos3.add_integerPolynomial_coefficientGrid`, `OAI.Erdos3.affinePairColumnEquiv`, `OAI.Erdos3.affinePairFree`, `OAI.Erdos3.affinePairImage`, `OAI.Erdos3.affinePairMatrix`, `OAI.Erdos3.affinePairPivot`, `OAI.Erdos3.affinePairPivot_det`, `OAI.Erdos3.affinePairRowDensity`, `OAI.Erdos3.affinePairScale`, `OAI.Erdos3.affinePairScale_pos`, `OAI.Erdos3.basisBelowProjection`, `OAI.Erdos3.basisBelowProjection_eq_iff`, `OAI.Erdos3.basisBelowProjection_eq_sum_grades`, `OAI.Erdos3.basisBelowProjection_repr`, `OAI.Erdos3.basisCoordinateProjection`, `OAI.Erdos3.basisCoordinateProjection_abs_repr_le`, `OAI.Erdos3.basisCoordinateProjection_baseChange`, `OAI.Erdos3.basisCoordinateProjection_basis`, `OAI.Erdos3.basisCoordinateProjection_eq_iff`, `OAI.Erdos3.basisCoordinateProjection_eq_self`, `OAI.Erdos3.basisCoordinateProjection_eq_zero_iff`, `OAI.Erdos3.basisCoordinateProjection_idempotent`, `OAI.Erdos3.basisCoordinateProjection_mem_span`, `OAI.Erdos3.basisCoordinateProjection_norm_le`, `OAI.Erdos3.basisCoordinateProjection_real_grid`, `OAI.Erdos3.basisCoordinateProjection_repr`, `OAI.Erdos3.basisGradeProjection`, `OAI.Erdos3.basisGradeProjection_pi_apply`, `OAI.Erdos3.basisGradeProjection_repr`, `OAI.Erdos3.basis_isCompl_span_compl`, `OAI.Erdos3.basis_mem_span_image_iff`, `OAI.Erdos3.bohrSmoothingMeasure`, `OAI.Erdos3.bohrSmoothingMeasure_apply_of_mem`, `OAI.Erdos3.bohrSmoothingMeasure_nonneg`, `OAI.Erdos3.bounded_coefficients_evaluation_error`, `OAI.Erdos3.box_gowers_lower_bound_of_overlaps`, `OAI.Erdos3.box_overlap_side_gt_of_card_gt`, `OAI.Erdos3.bracketMultilinear`, `OAI.Erdos3.canonicalPrincipalExponent_degree`, `OAI.Erdos3.card_centeredIntegerBox`, `OAI.Erdos3.card_dilate_one_add_le_two_mul`, `OAI.Erdos3.card_doubled_centeredIntegerBox_le`, `OAI.Erdos3.card_mul_le_of_kernel_translates`, `OAI.Erdos3.cardinality_ge_overlap_weight`, `OAI.Erdos3.centeredIntegerBox`, `OAI.Erdos3.centeredScalarBlock`, `OAI.Erdos3.centeredScalarBlock_lt`, `OAI.Erdos3.centeredScalarCenter`, `OAI.Erdos3.centeredScalarCenter_offset`, `OAI.Erdos3.coefficientImageMask`, `OAI.Erdos3.coefficientImageMultiplier`, `OAI.Erdos3.coefficientResidueMultiplier`, `OAI.Erdos3.commonCyclicCut_representative`, `OAI.Erdos3.commonCyclicCut_short`, `OAI.Erdos3.commonCyclicCuts`, `OAI.Erdos3.commonCyclicCuts_card_le`, `OAI.Erdos3.commonCyclicCuts_le`, `OAI.Erdos3.constantCoefficientSlot`, `OAI.Erdos3.constantCoefficientSlot_not_principal`, `OAI.Erdos3.convolutionPower_realUniformMass_support`, `OAI.Erdos3.coordinateFiberParameters`, `OAI.Erdos3.coordinateFiberParameters_degree`, `OAI.Erdos3.cubeCarryShift`, `OAI.Erdos3.cubeRepresentativeSum`, `OAI.Erdos3.cubeRepresentativeSum_intCast`, `OAI.Erdos3.cubeRepresentativeSum_le`, `OAI.Erdos3.cubeRepresentativeSum_zmodCast`, `OAI.Erdos3.cyclicCutCell`, `OAI.Erdos3.den_dvd_of_mem_denominatorGrid`, `OAI.Erdos3.den_le_of_mem_denominatorGrid`, `OAI.Erdos3.dense_product_signed_box`, `OAI.Erdos3.exists_affine_cyclic_character_phase`, `OAI.Erdos3.exists_anchored_reflected_family`, `OAI.Erdos3.exists_bounded_ambient_spanning`, `OAI.Erdos3.exists_convex_model_of_weighted_detector`, `OAI.Erdos3.exists_correlating_commonCyclicCut`, `OAI.Erdos3.exists_correlating_integer_product_interval`, `OAI.Erdos3.exists_cube_carry_code`, `OAI.Erdos3.exists_cyclic_cube_product_interval`, `OAI.Erdos3.exists_dense_centered_box_block`, `OAI.Erdos3.exists_dense_proper_coordinate_restriction`, `OAI.Erdos3.exists_dense_real_box_cell`, `OAI.Erdos3.exists_dense_row_phase_alignment`, `OAI.Erdos3.exists_dense_translate`, `OAI.Erdos3.exists_empirical_length`, `OAI.Erdos3.exists_family_reflected_correlation`, `OAI.Erdos3.exists_finite_inner_interval_family`, `OAI.Erdos3.exists_integerBox_coordinate_fiber`, `OAI.Erdos3.exists_intervalCut`, `OAI.Erdos3.exists_linear_lieTree_expansion`, `OAI.Erdos3.exists_many_family_derivative_correlations`, `OAI.Erdos3.exists_mem_cyclicQuarter`, `OAI.Erdos3.exists_mixed_anchor_weights`, `OAI.Erdos3.exists_mixed_reflected_correlation`, `OAI.Erdos3.exists_mixed_reflected_exp_correlation`, `OAI.Erdos3.exists_model_of_marginal_excess`, `OAI.Erdos3.exists_model_with_tail_error`, `OAI.Erdos3.exists_modeling_dual_obstruction`, `OAI.Erdos3.exists_scaledPair_basis_height`, `OAI.Erdos3.exists_supported_correlation_pairs`, `OAI.Erdos3.exists_two_marked_occurrences`, `OAI.Erdos3.exists_weighted_convex_approximation`, `OAI.Erdos3.exists_weighted_model_of_detector`, `OAI.Erdos3.exp_le_gowers_imageExtension`, `OAI.Erdos3.expect_imageExtension_mul`, `OAI.Erdos3.finiteBoxPointsEquiv`, `OAI.Erdos3.finiteBoxPoints_expect`, `OAI.Erdos3.finiteBoxPoints_expect_finset`, `OAI.Erdos3.finiteFactorMultiplicity`, `OAI.Erdos3.finiteLieTrees`, `OAI.Erdos3.finiteLieTrees_card_le`, `OAI.Erdos3.finiteMaskedLpStep`, `OAI.Erdos3.finiteMaskedMixedLp`, `OAI.Erdos3.finiteMaskedWeights`, `OAI.Erdos3.finiteMixedLp`, `OAI.Erdos3.finiteProductCoordinateEquiv`, `OAI.Erdos3.finiteProductIntegral`, `OAI.Erdos3.finiteSectionCount`, `OAI.Erdos3.finiteSectionCount_eq_card`, `OAI.Erdos3.finiteSectionFill`, `OAI.Erdos3.finiteSectionFreeOrder`, `OAI.Erdos3.finiteSectionIntegral`, `OAI.Erdos3.finiteSectionL2Control`, `OAI.Erdos3.finiteSectionL2Norm`, `OAI.Erdos3.finiteSectionWeight`, `OAI.Erdos3.finiteSection_free_card`, `OAI.Erdos3.finiteSiteInnerFamily`, `OAI.Erdos3.finiteSiteInnerFamily_card`, `OAI.Erdos3.finiteSiteInnerFamily_image_mem`, `OAI.Erdos3.finiteSitePreimage`, `OAI.Erdos3.finiteSitePreimage_card`, `OAI.Erdos3.finiteSitePreimage_subset`, `OAI.Erdos3.finiteSlotMask`, `OAI.Erdos3.finiteSplitPoint`, `OAI.Erdos3.finiteSplitPoint_fixed`, `OAI.Erdos3.finiteSplitPoint_linearPart`, `OAI.Erdos3.finiteSplitPoint_restrict`, `OAI.Erdos3.finiteWeightedL2Map`, `OAI.Erdos3.finiteWeightedLieValues`, `OAI.Erdos3.finiteWeightedLieValues_card_le`, `OAI.Erdos3.finiteWeightedLp`, `OAI.Erdos3.fourDiagonalMap`, `OAI.Erdos3.four_annihilator_common_zero`, `OAI.Erdos3.four_annihilator_decomposition`, `OAI.Erdos3.four_refined_annihilator_identity`, `OAI.Erdos3.freeLieTruncation_zero`, `OAI.Erdos3.freeLie_lowerCentralSeries_truncation_zero`, `OAI.Erdos3.fullSmoothPairError`, `OAI.Erdos3.higher_difference_card_le`, `OAI.Erdos3.homogeneous_aeval_scaled`, `OAI.Erdos3.imageExtension_norm_le_one`, `OAI.Erdos3.image_finiteSitePreimage`, `OAI.Erdos3.independentProductPMF_marginal`, `OAI.Erdos3.injOn_shrunk_integer_box_of_distinct_points`, `OAI.Erdos3.injOn_small_integer_box_of_dense_subset`, `OAI.Erdos3.integerCubeProductWithShift`, `OAI.Erdos3.integerSites_card_le`, `OAI.Erdos3.integerSites_card_le_exp`, `OAI.Erdos3.integralRealPolynomialSubring`, `OAI.Erdos3.intervalBoxDifference`, `OAI.Erdos3.intervalBoxDifference_injective`, `OAI.Erdos3.intervalBox_card_ratio`, `OAI.Erdos3.intervalCutUpper`, `OAI.Erdos3.intervalCutUpper_le_cut`, `OAI.Erdos3.intervalCutUpper_le_end`, `OAI.Erdos3.intervalCut_unique`, `OAI.Erdos3.intervalDifference`, `OAI.Erdos3.intervalDifference_injective`, `OAI.Erdos3.kernel_eq_zero_of_dense_integer_box`, `OAI.Erdos3.latticeStarMask`, `OAI.Erdos3.le_intervalCutUpper`, `OAI.Erdos3.lieBCH_pair_coordinate_dist_le`, `OAI.Erdos3.lieBCH_pair_coordinates_bound`, `OAI.Erdos3.lieTreeEval_relabel`, `OAI.Erdos3.lieTreeLength_relabel`, `OAI.Erdos3.lieTreeMarkedCount`, `OAI.Erdos3.lieTreeMarkedCount_eq_card`, `OAI.Erdos3.lieTreeMarkedCount_le_length`, `OAI.Erdos3.lieTreeMarkedCount_leaf`, `OAI.Erdos3.lieTreeMarkedCount_mul`, `OAI.Erdos3.lieTreeMultidegree`, `OAI.Erdos3.lieTreeMultidegree_apply`, `OAI.Erdos3.lieTreeMultidegree_leaf`, `OAI.Erdos3.lieTreeMultidegree_mul`, `OAI.Erdos3.lieTreeOccurrenceLabel`, `OAI.Erdos3.lieTreeOccurrenceMultilinear`, `OAI.Erdos3.lieTreeOccurrenceMultilinear_apply`, `OAI.Erdos3.lieTreeOccurrenceMultilinear_original`, `OAI.Erdos3.lieTreeOccurrenceTree`, `OAI.Erdos3.lieTreeOccurrenceTree_eval`, `OAI.Erdos3.lieTreeOccurrenceTree_length`, `OAI.Erdos3.lieTreeOccurrenceTree_support`, `OAI.Erdos3.lieTreeOccurrenceTree_weight`, `OAI.Erdos3.lieTreeOccurrencesFintype`, `OAI.Erdos3.lieTreeSupport_relabel`, `OAI.Erdos3.lieTreeWeight`, `OAI.Erdos3.lieTreeWeight_eq_sum_occurrences`, `OAI.Erdos3.lieTreeWeight_relabel`, `OAI.Erdos3.lieTree_length_le_weight`, `OAI.Erdos3.liftResidueMatrix`, `OAI.Erdos3.linearFunctional_eq_coordinate_sum`, `OAI.Erdos3.majorRationalPolynomial`, `OAI.Erdos3.majorRationalPolynomial_coefficientGrid`, `OAI.Erdos3.majorRationalPolynomial_denominatorGrid`, `OAI.Erdos3.majorRationalPolynomial_eval₂`, `OAI.Erdos3.majorRationalPolynomial_map`, `OAI.Erdos3.majorShiftCoordinates`, `OAI.Erdos3.majorShiftCoordinates_coefficientGrid`, `OAI.Erdos3.majorShiftCoordinates_eval`, `OAI.Erdos3.majorShiftCoordinates_eval₂`, `OAI.Erdos3.majorShiftCoordinates_map`, `OAI.Erdos3.majorShiftCoordinates_mass_le`, `OAI.Erdos3.majorShiftSubstitution`, `OAI.Erdos3.majorShiftSubstitution_eval`, `OAI.Erdos3.majorShiftSubstitution_eval₂`, `OAI.Erdos3.majorShiftSubstitution_mass_le`, `OAI.Erdos3.majorSlowPolynomial`, `OAI.Erdos3.majorSlowPolynomial_eval`, `OAI.Erdos3.majorSlowPolynomial_mass_le`, `OAI.Erdos3.markedGeneratorGrade`, `OAI.Erdos3.markedTreeGrade_count`, `OAI.Erdos3.markedTreeGrade_length`, `OAI.Erdos3.markedTreeGrade_weight`, `OAI.Erdos3.massCoeff`, `OAI.Erdos3.massCoeff_convolutionPower`, `OAI.Erdos3.massCoeff_massConvolution`, `OAI.Erdos3.massCoeff_realUniformMass`, `OAI.Erdos3.mem_centeredIntegerBox`, `OAI.Erdos3.mem_closure_model_of_weighted_detector`, `OAI.Erdos3.mem_closure_model_set_of_dual_detector`, `OAI.Erdos3.mem_cyclicCutCell`, `OAI.Erdos3.mem_finiteLieTrees_of_length_le`, `OAI.Erdos3.mem_finiteSiteInnerFamily`, `OAI.Erdos3.mem_integralRealPolynomialSubring_iff`, `OAI.Erdos3.mem_principalCoefficientSlots`, `OAI.Erdos3.mem_scaledPairLayer`, `OAI.Erdos3.mixedReflectedCorner`, `OAI.Erdos3.mixedReflectedCorner_independent`, `OAI.Erdos3.mixedReflectedCorner_norm`, `OAI.Erdos3.mixedTailDifference`, `OAI.Erdos3.mixedTailDifference_eq_anchor`, `OAI.Erdos3.mixedTailDifference_map`, `OAI.Erdos3.mixedTailDifference_norm`, `OAI.Erdos3.model_error_norm_le`, `OAI.Erdos3.nearIntegerDensity_interval_differences`, `OAI.Erdos3.norm_expect_imageExtension_mul_le`, `OAI.Erdos3.norm_expect_injective_sub_le`, `OAI.Erdos3.norm_expect_subset_sub_le`, `OAI.Erdos3.norm_finset_expect_le_one`, `OAI.Erdos3.norm_massCoeff_bohrSmoothingMeasure_le`, `OAI.Erdos3.norm_massCoeff_le_sum`, `OAI.Erdos3.norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum`, `OAI.Erdos3.norm_one_sub_le_of_mem_largeSpectrum`, `OAI.Erdos3.norm_one_sub_le_of_mem_largeSpectrum_half`, `OAI.Erdos3.pairDifferenceMod`, `OAI.Erdos3.piFinset_inner_card_loss`, `OAI.Erdos3.piFinset_inner_normalized_loss`, `OAI.Erdos3.polynomialHomDifference`, `OAI.Erdos3.polynomialHomDifference_pow_eq_zero`, `OAI.Erdos3.polynomialOfFiniteCoefficientVector`, `OAI.Erdos3.polynomialOfFiniteCoefficientVector_coeff`, `OAI.Erdos3.polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem`, `OAI.Erdos3.polynomialOfFiniteCoefficientVector_reconstruct`, `OAI.Erdos3.polynomialOfFiniteCoefficientVector_support_subset`, `OAI.Erdos3.polynomial_eq_zero_of_pderiv_closed`, `OAI.Erdos3.polynomial_substitution_cleared_mem`, `OAI.Erdos3.principalCoefficientChoice`, `OAI.Erdos3.principalCoefficientSlot`, `OAI.Erdos3.principalCoefficientSlot_injective`, `OAI.Erdos3.principalCoefficientSlots`, `OAI.Erdos3.principalCoefficientSlots_card`, `OAI.Erdos3.productBlockExponent_degree`, `OAI.Erdos3.product_difference_bias_approximation`, `OAI.Erdos3.quarterLower_mem_commonCyclicCuts`, `OAI.Erdos3.quarterUpper_mem_commonCyclicCuts`, `OAI.Erdos3.realBoxCellCenter`, `OAI.Erdos3.realBoxCellCount`, `OAI.Erdos3.realBoxCellCount_le`, `OAI.Erdos3.realBoxCellCount_pos`, `OAI.Erdos3.realBoxCell_floor_lt`, `OAI.Erdos3.realBoxCell_offset`, `OAI.Erdos3.realFinsetIndicator`, `OAI.Erdos3.realPairEquiv`, `OAI.Erdos3.realPairEquiv_difference`, `OAI.Erdos3.realPairEquiv_first`, `OAI.Erdos3.realPairEquiv_second`, `OAI.Erdos3.realPairEquiv_tmul`, `OAI.Erdos3.realPolynomialCoefficientGrid`, `OAI.Erdos3.realPolynomialCoefficientGrid_X`, `OAI.Erdos3.realPolynomialCoefficientGrid_add`, `OAI.Erdos3.realPolynomialCoefficientGrid_aeval_integral`, `OAI.Erdos3.realPolynomialCoefficientGrid_iff`, `OAI.Erdos3.realPolynomialCoefficientGrid_intCast`, `OAI.Erdos3.realPolynomialCoefficientGrid_mono`, `OAI.Erdos3.realPolynomialCoefficientGrid_neg`, `OAI.Erdos3.realPolynomialCoefficientGrid_ratCast_iff`, `OAI.Erdos3.realPolynomialCoefficientGrid_rename`, `OAI.Erdos3.realPolynomialCoefficientGrid_substitute`, `OAI.Erdos3.realPolynomialCoefficientGrid_substitute_common`, `OAI.Erdos3.realPolynomialCoefficientGrid_weightedHomogeneousComponent`, `OAI.Erdos3.realPolynomialMass_fin_prod_le`, `OAI.Erdos3.rename_mem_integralRealPolynomialSubring`, `OAI.Erdos3.scaledPairAssemble`, `OAI.Erdos3.scaledPairAssemble_decompose`, `OAI.Erdos3.scaledPairDifference`, `OAI.Erdos3.scaledPairDifference_apply`, `OAI.Erdos3.scaledPairDifference_assemble`, `OAI.Erdos3.scaledPairLayer`, `OAI.Erdos3.scaledPairLayerEquiv`, `OAI.Erdos3.scaled_weighted_empirical_seminorm_bound`, `OAI.Erdos3.selectedCoefficientDensity`, `OAI.Erdos3.seminorm_le_mask_add_tail`, `OAI.Erdos3.seminorm_mask_le`, `OAI.Erdos3.seminorm_mask_le_condition`, `OAI.Erdos3.seminorm_sq_le_weighted_square_mean`, `OAI.Erdos3.seminorm_tail_le`, `OAI.Erdos3.shiftedPairLocationKernel`, `OAI.Erdos3.side_gt_of_prod_gt`, `OAI.Erdos3.smoothAffinePairRows`, `OAI.Erdos3.smoothAffineSample`, `OAI.Erdos3.smoothPairCoefficientScale`, `OAI.Erdos3.smoothPairErrorCoefficient`, `OAI.Erdos3.smoothPairErrorLog`, `OAI.Erdos3.smoothPairKernelBaseCap`, `OAI.Erdos3.smoothPairKernelBaseLip`, `OAI.Erdos3.smoothPairKernelCap`, `OAI.Erdos3.smoothPairKernelLip`, `OAI.Erdos3.smoothPairProbabilityCap`, `OAI.Erdos3.smoothPairProbabilityError`, `OAI.Erdos3.smoothPairProductDensity`, `OAI.Erdos3.smoothPairRowErrorLog`, `OAI.Erdos3.smoothPairRowLipschitz`, `OAI.Erdos3.span_weighted_leaves_le`, `OAI.Erdos3.spatialSiteApprox`, `OAI.Erdos3.spatialSiteCoefficient`, `OAI.Erdos3.spatialStarDensity`, `OAI.Erdos3.sub_basisBelowProjection_mem`, `OAI.Erdos3.sub_basisCoordinateProjection_mem`, `OAI.Erdos3.sum_basisGradeProjection_pi`, `OAI.Erdos3.sum_bohrSmoothingMeasure`, `OAI.Erdos3.sum_commonCyclicCut_indicator`, `OAI.Erdos3.sum_cyclicCutCell_indicator`, `OAI.Erdos3.sum_imageExtension_mul`, `OAI.Erdos3.supportedQuotientBasis`, `OAI.Erdos3.supportedQuotientBasis_apply`, `OAI.Erdos3.supportedQuotientBasis_map_span`, `OAI.Erdos3.supportedQuotientBasis_repr_mk`, `OAI.Erdos3.supportedSubmoduleBasis`, `OAI.Erdos3.supportedSubmoduleBasis_coe`, `OAI.Erdos3.supportedSubmoduleBasis_repr`, `OAI.Erdos3.symmetricIntegerInterval_abs_le`, `OAI.Erdos3.symmetricIntegerInterval_card`, `OAI.Erdos3.symmetricIntegerInterval_inhabited`, `OAI.Erdos3.torusChordCutoff`, `OAI.Erdos3.translatedCyclicProduct`, `OAI.Erdos3.translatedCyclicProduct_cut_correlation`, `OAI.Erdos3.translatedCyclicProduct_on_cut`, `OAI.Erdos3.weight_correlating_large_box_overlaps`, `OAI.Erdos3.weight_correlating_large_overlaps`, `OAI.Erdos3.weightedDerivation_apply`, `OAI.Erdos3.weightedDerivation_apply_le`, `OAI.Erdos3.weightedDerivation_bracket`, `OAI.Erdos3.weightedDerivation_monomial`, `OAI.Erdos3.weightedDerivation_monomial_one`, `OAI.Erdos3.weightedDerivation_mul`, `OAI.Erdos3.weightedDerivation_pow`, `OAI.Erdos3.weightedDerivation_pow_eq_zero`, `OAI.Erdos3.weightedEuclideanMap`, `OAI.Erdos3.weightedEuclideanMap_norm_sq`, `OAI.Erdos3.weightedLieTreeGenerators`, `OAI.Erdos3.weightedLieTreeSpan`, `OAI.Erdos3.weightedLieTreeSpan_antitone`, `OAI.Erdos3.weightedLieTreeSpan_eq_finite_span`, `OAI.Erdos3.weightedLieTreeSpan_lie_mem`, `OAI.Erdos3.weightedLieTree_eval_mem_layer`, `OAI.Erdos3.weightedLieUpperGenerators`, `OAI.Erdos3.weightedLieUpperSpan`, `OAI.Erdos3.weightedLieUpperSpan_antitone`, `OAI.Erdos3.weightedLieUpperSpan_le_comap`, `OAI.Erdos3.weightedLieUpperSpan_leaf`, `OAI.Erdos3.weightedLieUpperSpan_lie_mem`, `OAI.Erdos3.weightedLoweringEquiv`, `OAI.Erdos3.weightedLoweringEquiv_mem`, `OAI.Erdos3.weightedLoweringSubgroup`, `OAI.Erdos3.weightedLowering_bijective`, `OAI.Erdos3.weightedLowering_difference`, `OAI.Erdos3.weightedLowering_eq_zero_of_degree`, `OAI.Erdos3.weightedLowering_injective`, `OAI.Erdos3.weightedLowering_monomial`, `OAI.Erdos3.weightedLowering_monomial_one`, `OAI.Erdos3.weightedLowering_mul_bounds`, `OAI.Erdos3.weightedLowering_preimage_degree`, `OAI.Erdos3.weightedLowering_preserves_degree`, `OAI.Erdos3.weightedSupportLT_le`, `OAI.Erdos3.weightedSupportLT_mono`, `OAI.Erdos3.weightedSupportLT_succ_le`, `OAI.Erdos3.weightedSupportLT_zero_eq`, `OAI.Erdos3.wordTruncation_eq_zero_iff`, `OAI.Erdos3.wordTruncation_succ_lie_eq_zero`, `OAI.Erdos3.wordTruncation_succ_mul_eq_zero`, `OAI.Erdos3.wrap_mem_commonCyclicCuts`, `OAI.Erdos3.zero_mem_commonCyclicCuts`, `_private.Fourier.TranslatedBohrDifference.0.OAI.Erdos3.normalizedSpectrum_eq`, `_private.Fourier.TranslatedBohrDifference.0.OAI.Erdos3.normalizedSpectrum_translate`, `_private.Polynomial.PolynomialCoefficientGridDenominator.0.OAI.Erdos3.cleared_substitution_term`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012
import Definitions.Def_OAIErdos3B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TailReflectionInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_family_reflected_correlation
    {T G : Type*} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (F : T → G → G → ℂ) (b₁ b₂ b₃ : T → G → ℂ)
    (hb₁ : ∀ t x, ‖b₁ t x‖ ≤ 1) (hb₂ : ∀ t y, ‖b₂ t y‖ ≤ 1)
    (hb₃ : ∀ t z, ‖b₃ t z‖ ≤ 1) :
    ∃ (z : G) (b : T → G → ℂ), (∀ t y, ‖b t y‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2 ≤
        (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          b t y * star (b t y')).re := by
  let B (z : G) (t : T) (y : G) := b₂ t y * star (b₃ t (z - y))
  let v (y : G) (u : T × G) := F u.1 y u.2 * b₂ u.1 y * b₃ u.1 (u.2 + y)
  have hleft : (𝔼 u : T × G, b₁ u.1 u.2 * (𝔼 y, v y u)) =
      𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y) := by
    simp_rw [expect_prod_split, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    dsimp only [v]
    ring
  have hchange (t : T) : (𝔼 y, 𝔼 y', 𝔼 x,
      v y (t, x) * star (v y' (t, x))) =
      𝔼 z, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z, F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, v, B, h₁, h₂, add_sub_cancel_right,
          star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
          B z t y * star (B z t y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hright : (𝔼 y, 𝔼 y', 𝔼 u : T × G, v y u * star (v y' u)) =
      𝔼 z, 𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y') := by
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 y, 𝔼 t, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 y, 𝔼 y', 𝔼 x, v y (t, x) * star (v y' (t, x)) :=
        Finset.expect_comm _ _ _
      _ = _ := by simp_rw [hchange]; exact Finset.expect_comm _ _ _
  have hcs := finite_family_cauchy_schwarz_re (fun u : T × G => b₁ u.1 u.2)
    v (fun u => hb₁ u.1 u.2)
  simp only [one_pow, one_mul, hleft, hright] at hcs
  rw [expect_re, Fintype.expect_eq_sum_div_card (fun z : G =>
    (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
      B z t y * star (B z t y')).re)] at hcs
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ _z : G,
      ‖𝔼 t, 𝔼 x, 𝔼 y, F t y x * b₁ t x * b₂ t y * b₃ t (x + y)‖ ^ 2) ≤
      ∑ z : G, (𝔼 t, 𝔼 y, 𝔼 y', F t y (z - y - y') * star (F t y' (z - y - y')) *
        B z t y * star (B z t y')).re := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hcs
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro t y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ t y)).trans (hb₃ t _)

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

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

structure TailReflectionData (n : ℕ) (T G : Type*) where
  kernel : T → G → G → (Fin n → G) → ℂ
  signal : T → G → ℂ
  leftWeight : T → G → (Fin n → G) → ℂ
  rightWeight : T → G → (Fin n → G) → ℂ
  tailWeight : T → Fin n → G → G → (Fin n → G) → ℂ
  signal_norm : ∀ t x, ‖signal t x‖ ≤ 1
  left_norm : ∀ t x v, ‖leftWeight t x v‖ ≤ 1
  right_norm : ∀ t x v, ‖rightWeight t x v‖ ≤ 1
  tail_norm : ∀ t i h m v, ‖tailWeight t i h m v‖ ≤ 1
  tail_misses : ∀ t i h m, MissesBoxCoordinate (tailWeight t i h m) i

namespace TailReflectionData

noncomputable def correlation {n : ℕ} {T G : Type*} [Fintype T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData n T G) : ℂ :=
  𝔼 t, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
    D.signal t (m + h + ∑ i, v i) * D.kernel t h m v *
      D.leftWeight t m v * D.rightWeight t h v * ∏ i, D.tailWeight t i h m v

noncomputable def pair {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) : TailReflectionData n (T × (G × G)) G where
  kernel t h m v := D.kernel t.1 h m (Fin.cons t.2.1 v) *
    star (D.kernel t.1 h m (Fin.cons t.2.2 v))
  signal t w := D.signal t.1 (w + t.2.1) * star (D.signal t.1 (w + t.2.2))
  leftWeight t m v := D.leftWeight t.1 m (Fin.cons t.2.1 v) *
    star (D.leftWeight t.1 m (Fin.cons t.2.2 v))
  rightWeight t h v := D.rightWeight t.1 h (Fin.cons t.2.1 v) *
    star (D.rightWeight t.1 h (Fin.cons t.2.2 v))
  tailWeight t i h m v := boxTailTests (fun j => D.tailWeight t.1 j h m) t.2.1 t.2.2 i v
  signal_norm t w := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.signal_norm _ _)).trans (D.signal_norm _ _)
  left_norm t m v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.left_norm _ _ _)).trans (D.left_norm _ _ _)
  right_norm t h v := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (D.right_norm _ _ _)).trans (D.right_norm _ _ _)
  tail_norm t i h m v := boxTailTests_norm (fun j => D.tailWeight t.1 j h m)
    (fun j x => D.tail_norm t.1 j h m x) t.2.1 t.2.2 i v
  tail_misses t i h m := boxTailTests_misses (fun j => D.tailWeight t.1 j h m)
    (fun j => D.tail_misses t.1 j h m) t.2.1 t.2.2 i

noncomputable def reflectedKernel {n : ℕ} {T G : Type*} (D : TailReflectionData n T G)
    (t : T) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => D.kernel t a.1 a.2 x) u v (h, m)

theorem reflectedKernel_cons {n : ℕ} {T G : Type*} [AddCommGroup G]
    (D : TailReflectionData (n + 1) T G) (t : T) (a b : G)
    (u v : Fin n → G) (h m : G) :
    D.reflectedKernel t (Fin.cons a u) (Fin.cons b v) h m =
      D.pair.reflectedKernel (t, (a, b)) u v h m := by
  simp only [reflectedKernel, iteratedBoxDifference, Fin.cons_zero, Fin.tail_cons, pair]

end TailReflectionData

end Erdos3

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

theorem correlation_square_le_pair {n : ℕ} {T G : Type*} [Fintype T] [Nonempty T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData (n + 1) T G) :
    ‖D.correlation‖ ^ 2 ≤ D.pair.correlation.re := by
  let C (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.tailWeight q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1)
  let V (a : G) (q : T × ((Fin n → G) × (G × G))) : ℂ :=
    D.signal q.1 (q.2.2.1 + q.2.2.2 + ∑ i, (Fin.cons a q.2.1) i) *
      D.kernel q.1 q.2.2.2 q.2.2.1 (Fin.cons a q.2.1) *
      D.leftWeight q.1 q.2.2.1 (Fin.cons a q.2.1) *
      D.rightWeight q.1 q.2.2.2 (Fin.cons a q.2.1) *
      ∏ i : Fin n, D.tailWeight q.1 i.succ q.2.2.2 q.2.2.1 (Fin.cons a q.2.1)
  have hleft : (𝔼 q, C q * (𝔼 a, V a q)) = D.correlation := by
    unfold correlation
    simp_rw [expect_dependent_fin_cons, Finset.mul_expect]
    rw [Finset.expect_comm]
    simp_rw [expect_prod_split]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro a _
    apply Finset.expect_congr rfl
    intro v _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [C, V]
    rw [Fin.prod_univ_succ,
      missesBoxCoordinate_head (D.tail_misses t 0 h m) a 0 v]
    ring
  have hright : (𝔼 a, 𝔼 b, 𝔼 q, V a q * star (V b q)) = D.pair.correlation := by
    unfold correlation
    simp_rw [expect_prod_split]
    calc
      _ = 𝔼 a, 𝔼 t, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
      _ = 𝔼 t, 𝔼 a, 𝔼 b, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
          V a (t, (v, (m, h))) * star (V b (t, (v, (m, h)))) :=
        Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro t _
        apply Finset.expect_congr rfl
        intro a _
        apply Finset.expect_congr rfl
        intro b _
        apply Finset.expect_congr rfl
        intro v _
        apply Finset.expect_congr rfl
        intro m _
        apply Finset.expect_congr rfl
        intro h _
        dsimp only [V, pair]
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, boxTailTests,
          star_mul, star_prod, Finset.prod_mul_distrib]
        have ha : m + h + (a + ∑ i, v i) = (m + h + ∑ i, v i) + a := by abel
        have hb : m + h + (b + ∑ i, v i) = (m + h + ∑ i, v i) + b := by abel
        rw [ha, hb]
        ring
  have hcs := finite_family_cauchy_schwarz_re C V
    (fun q => D.tail_norm q.1 0 q.2.2.2 q.2.2.1 (Fin.cons 0 q.2.1))
  simpa only [hleft, hright, one_pow, one_mul] using hcs

end Erdos3.TailReflectionData

end

section

namespace Erdos3.TailReflectionData

open scoped BigOperators Classical

universe u

theorem exists_reflected_correlation (n : ℕ) :
    ∀ {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
      (D : TailReflectionData n T G),
      ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
        (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
        ‖D.correlation‖ ^ (2 ^ (n + 1)) ≤
          (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h')).re := by
  induction n with
  | zero =>
      intro T G _ _ _ _ D
      let e : Fin 0 → G := fun i => Fin.elim0 i
      obtain ⟨z, b, hb, hcorr⟩ := exists_family_reflected_correlation
        (fun t h m => D.kernel t h m e)
        (fun t m => D.leftWeight t m e) (fun t h => D.rightWeight t h e) D.signal
        (fun t m => D.left_norm t m e) (fun t h => D.right_norm t h e) D.signal_norm
      refine ⟨z, (fun t _ _ h => b t h), (fun t _ _ h => hb t h), ?_⟩
      simpa only [correlation, reflectedKernel, iteratedBoxDifference, expect_empty_tuple,
        Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one, one_mul, Nat.zero_add, pow_one,
        e, mul_comm, mul_left_comm, mul_assoc] using hcorr
  | succ n ih =>
      intro T G _ _ _ _ D
      obtain ⟨z, b, hb, hcorr⟩ := ih D.pair
      let B (t : T) (u v : Fin (n + 1) → G) (h : G) :=
        b (t, (u 0, v 0)) (Fin.tail u) (Fin.tail v) h
      refine ⟨z, B, (fun t u v h => hb _ _ _ _), ?_⟩
      have hmean :
          (𝔼 t, 𝔼 u : Fin (n + 1) → G, 𝔼 v : Fin (n + 1) → G, 𝔼 h, 𝔼 h',
            D.reflectedKernel t u v h (z - h - h') *
              star (D.reflectedKernel t u v h' (z - h - h')) *
                B t u v h * star (B t u v h')) =
          𝔼 t : T × (G × G), 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
            D.pair.reflectedKernel t u v h (z - h - h') *
              star (D.pair.reflectedKernel t u v h' (z - h - h')) *
                b t u v h * star (b t u v h') := by
        simp_rw [expect_prod_split]
        apply Finset.expect_congr rfl
        intro t _
        rw [expect_two_dependent_fin_cons]
        simp only [B, Fin.cons_zero, Fin.tail_cons, reflectedKernel_cons]
      rw [hmean]
      calc
        _ = (‖D.correlation‖ ^ 2) ^ (2 ^ (n + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          omega
        _ ≤ ‖D.pair.correlation‖ ^ (2 ^ (n + 1)) :=
          pow_le_pow_left₀ (sq_nonneg _)
            (D.correlation_square_le_pair.trans (Complex.re_le_norm _)) _
        _ ≤ _ := hcorr

end Erdos3.TailReflectionData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReflectedFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

universe u

noncomputable def mixedTailDifference {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → G) (h m : G) : ℂ :=
  iteratedBoxDifference n (fun x (a : G × G) => K a.1 a.2 x) u v (h, m)

theorem exists_mixed_reflected_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖ ^
          (2 ^ (n + 1)) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  let D : TailReflectionData n T G := {
    kernel := K
    signal := f
    leftWeight := fun t m x => A t 0 (Fin.cons 0 (Fin.cons m x))
    rightWeight := fun t h x => A t 1 (Fin.cons h (Fin.cons 0 x))
    tailWeight := fun t i h m x => A t i.succ.succ (Fin.cons h (Fin.cons m x))
    signal_norm := hf
    left_norm := fun t m x => hA t 0 _
    right_norm := fun t h x => hA t 1 _
    tail_norm := fun t i h m x => hA t i.succ.succ _
    tail_misses := by
      intro t i h m x a
      simp only [Fin.cons_update]
      exact hmiss t i.succ.succ _ a }
  have hleft (t : T) (h m : G) (x : Fin n → G) :
      A t 0 (Fin.cons h (Fin.cons m x)) = A t 0 (Fin.cons 0 (Fin.cons m x)) :=
    missesBoxCoordinate_head (hmiss t 0) h 0 (Fin.cons m x)
  have hright (t : T) (h m : G) (x : Fin n → G) :
      A t 1 (Fin.cons h (Fin.cons m x)) = A t 1 (Fin.cons h (Fin.cons 0 x)) := by
    have H := hmiss t 1 (Fin.cons h (Fin.cons m x)) 0
    change A t 1 (Function.update (Fin.cons h (Fin.cons m x))
      (0 : Fin (n + 1)).succ 0) = _ at H
    rw [← Fin.cons_update, Fin.update_cons_zero] at H
    exact H.symm
  have hcorr_eq : D.correlation =
      𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x)) := by
    unfold TailReflectionData.correlation
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro m _
    apply Finset.expect_congr rfl
    intro h _
    dsimp only [D]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ = _ * (A t 0 (Fin.cons h (Fin.cons m x)) *
      (A t 1 (Fin.cons h (Fin.cons m x)) *
        ∏ i : Fin n, A t i.succ.succ (Fin.cons h (Fin.cons m x))))
    simp only [hleft, hright]
    ring
  obtain ⟨z, b, hb, hcorr⟩ := TailReflectionData.exists_reflected_correlation n D
  refine ⟨z, b, hb, ?_⟩
  simpa only [hcorr_eq, TailReflectionData.reflectedKernel, mixedTailDifference, D] using hcorr

theorem exists_mixed_reflected_exp_correlation (n : ℕ)
    {T G : Type u} [Fintype T] [Nonempty T] [AddCommGroup G] [Fintype G]
    (K : T → G → G → (Fin n → G) → ℂ) (f : T → G → ℂ)
    (A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ)
    (hf : ∀ t x, ‖f t x‖ ≤ 1) (hA : ∀ t i x, ‖A t i x‖ ≤ 1)
    (hmiss : ∀ t i, MissesBoxCoordinate (A t i) i) {p : ℝ}
    (hcorr : Real.exp (-p) ≤
      ‖𝔼 t, 𝔼 x : Fin n → G, 𝔼 m, 𝔼 h,
        f t (m + h + ∑ i, x i) * K t h m x * ∏ i, A t i (Fin.cons h (Fin.cons m x))‖) :
    ∃ (z : G) (b : T → (Fin n → G) → (Fin n → G) → G → ℂ),
      (∀ t u v h, ‖b t u v h‖ ≤ 1) ∧
      Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) ≤
        (𝔼 t, 𝔼 u : Fin n → G, 𝔼 v : Fin n → G, 𝔼 h, 𝔼 h',
          mixedTailDifference (K t) u v h (z - h - h') *
            star (mixedTailDifference (K t) u v h' (z - h - h')) *
              b t u v h * star (b t u v h')).re := by
  obtain ⟨z, b, hb, hbound⟩ := exists_mixed_reflected_correlation n K f A hf hA hmiss
  refine ⟨z, b, hb, ?_⟩
  have hpower : Real.exp (-((2 ^ (n + 1) : ℕ) : ℝ) * p) =
      Real.exp (-p) ^ (2 ^ (n + 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpower]
  exact (pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedTailDifference_eq_anchor {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (u a : Fin n → G) (h m : G) :
    mixedTailDifference K u a h m =
      K h m u * boxCornerAnchor (fun x => K h m x) a u := by
  rw [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct, boxCornerProduct_eq_mul_anchor]

theorem mixedTailDifference_norm {n : ℕ} {G : Type*}
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (u a : Fin n → G) (h m : G) : ‖mixedTailDifference K u a h m‖ ≤ 1 := by
  rw [mixedTailDifference_eq_anchor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hK h m u)).trans
    (boxCornerAnchor_norm_le_one (fun x => K h m x) (hK h m) a u)

theorem mixedTailDifference_map {n : ℕ} {X G : Type*} (φ : X → G)
    (K : G → G → (Fin n → G) → ℂ) (u v : Fin n → X) (h m : X) :
    mixedTailDifference (fun h m x => K (φ h) (φ m) (fun i => φ (x i))) u v h m =
      mixedTailDifference K (fun i => φ (u i)) (fun i => φ (v i)) (φ h) (φ m) := by
  simp only [mixedTailDifference, iteratedBoxDifference_eq_cornerProduct]
  exact boxCornerProduct_map φ (fun x => K (φ h) (φ m) x) u v

noncomputable def mixedReflectedCorner {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (x : Fin (n + 2) → G) : ℂ :=
  conjugationPower (booleanWeight ω)
      (K (x 0) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)) *
    star (conjugationPower (booleanWeight ω)
      (K (x 1) (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))

theorem mixedReflectedCorner_norm {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (ω : Fin n → Bool) (x : Fin (n + 2) → G) :
    ‖mixedReflectedCorner K c a ω x‖ ≤ 1 := by
  have hc (h m : G) (v : Fin n → G) :
      ‖conjugationPower (booleanWeight ω) (K h m v)‖ ≤ 1 := by
    rw [conjugationPower_eq_if_mod]
    split_ifs <;> simpa only [norm_star] using hK h m v
  rw [mixedReflectedCorner, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc _ _ _)).trans (hc _ _ _)

theorem mixedReflectedCorner_independent {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (c : G) (a : Fin n → G) (ω : Fin n → Bool)
    (j : Fin n) (hj : ω j = true) (x y : Fin (n + 2) → G)
    (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedReflectedCorner K c a ω x = mixedReflectedCorner K c a ω y := by
  have h0 : x 0 = y 0 := hxy 0 (Fin.succ_ne_zero j.succ).symm
  have hne : j.succ.succ ≠ (1 : Fin (n + 2)) := by
    intro heq
    exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
  have h1 : x 1 = y 1 := hxy 1 hne.symm
  have hcorner : boxCorner (fun i => x i.succ.succ) a ω =
      boxCorner (fun i => y i.succ.succ) a ω := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [boxCorner, hj]
    · have hk : k.succ.succ ≠ j.succ.succ := by
        intro heq
        exact hkj (Fin.succ_injective n (Fin.succ_injective (n + 1) heq))
      simp only [boxCorner, hxy k.succ.succ hk]
  simp only [mixedReflectedCorner, h0, h1, hcorner]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_mixed_anchor_weights {n : ℕ} {G : Type*} [AddCommGroup G]
    (K : G → G → (Fin n → G) → ℂ) (hK : ∀ h m x, ‖K h m x‖ ≤ 1)
    (c : G) (a : Fin n → G) (b d : (Fin n → G) → G → ℂ)
    (hb : ∀ u h, ‖b u h‖ ≤ 1) (hd : ∀ u h, ‖d u h‖ ≤ 1) :
    ∃ A : Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, (mixedTailDifference K (fun i => x i.succ.succ) a (x 0) (c - x 0 - x 1) *
          star (mixedTailDifference K (fun i => x i.succ.succ) a (x 1) (c - x 0 - x 1)) *
          b (fun i => x i.succ.succ) (x 0) * d (fun i => x i.succ.succ) (x 1)) =
        (K (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) *
          star (K (x 1) (c - x 0 - x 1) (fun i => x i.succ.succ))) * ∏ i, A i x := by
  let S : Finset (Fin n → Bool) := Finset.univ.erase (fun _ => false)
  let F (ω : S) (x : Fin (n + 2) → G) := mixedReflectedCorner K c a ω.val x
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := fun ω x => mixedReflectedCorner_norm K hK c a ω.val x
  have hFind : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    have hne : ω.val ≠ fun _ => false := (Finset.mem_erase.mp ω.property).1
    obtain ⟨i, hi⟩ := exists_true_of_ne_false hne
    exact ⟨i.succ.succ, mixedReflectedCorner_independent K c a ω.val i hi⟩
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  have hFprod (x : Fin (n + 2) → G) : (∏ ω : S, F ω x) =
      boxCornerAnchor (fun v => K (x 0) (c - x 0 - x 1) v) a (fun i => x i.succ.succ) *
        star (boxCornerAnchor (fun v => K (x 1) (c - x 0 - x 1) v) a (fun i => x i.succ.succ)) := by
    simp only [F, mixedReflectedCorner, Finset.prod_mul_distrib, ← star_prod]
    have he (h : G) :
        (∏ ω : S, conjugationPower (booleanWeight ω.val)
          (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω.val))) =
          boxCornerAnchor (fun v => K h (c - x 0 - x 1) v) a (fun i => x i.succ.succ) :=
      Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (K h (c - x 0 - x 1) (boxCorner (fun i => x i.succ.succ) a ω)))
    rw [he, he]
  let H (i : Fin (n + 2)) (x : Fin (n + 2) → G) : ℂ :=
    Fin.cases (d (fun j => x j.succ.succ) (x 1))
      (Fin.cases (b (fun j => x j.succ.succ) (x 0)) (fun _ => 1)) i
  have hH : ∀ i x, ‖H i x‖ ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x
      exact hd _ _
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        exact hb _ _
      · intro x
        change ‖(1 : ℂ)‖ ≤ 1
        norm_num
  have hHind : ∀ i x y, (∀ k, k ≠ i → x k = y k) → H i x = H i y := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change d (fun j => x j.succ.succ) (x 1) = d (fun j => y j.succ.succ) (y 1)
      rw [ht, hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1)))]
    · refine Fin.cases ?_ (fun j => ?_) i
      · intro x y hxy
        have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
          intro heq
          exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
        have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
          funext (fun j => hxy j.succ.succ (hne j))
        change b (fun j => x j.succ.succ) (x 0) = b (fun j => y j.succ.succ) (y 0)
        rw [ht, hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm]
      · intro x y _
        rfl
  have hHprod (x : Fin (n + 2) → G) : (∏ i, H i x) =
      d (fun j => x j.succ.succ) (x 1) * b (fun j => x j.succ.succ) (x 0) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    change _ * (_ * (∏ _j : Fin n, (1 : ℂ))) = _
    simp only [Finset.prod_const_one, mul_one]
    rfl
  refine ⟨(fun i x => H i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH i x)).trans (hD i x)
  · intro i x y hxy
    change H i x * D i x = H i y * D i y
    rw [hHind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hHprod, hDprod, hFprod]
    simp only [mixedTailDifference_eq_anchor, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_anchored_reflected_family {n : ℕ} {T X G : Type*}
    [Fintype T] [Nonempty T] [Fintype X] [Nonempty X] [AddCommGroup G]
    (φ : X → G) (ψ : G → X) (hψ : ∀ x, ψ (φ x) = x)
    (K : T → G → G → (Fin n → G) → ℂ) (hK : ∀ t h m u, ‖K t h m u‖ ≤ 1)
    (c : G) (B C : T → (Fin n → X) → (Fin n → X) → G → ℂ)
    (hB : ∀ t u v h, ‖B t u v h‖ ≤ 1) (hC : ∀ t u v h, ‖C t u v h‖ ≤ 1)
    {δ : ℝ} (hcorr : δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 v : Fin n → X, 𝔼 x, 𝔼 y,
      mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
        star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
          (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)‖) :
    ∃ A : T → Fin (n + 2) → (Fin (n + 2) → G) → ℂ,
      (∀ t i x, ‖A t i x‖ ≤ 1) ∧
      (∀ t i x y, (∀ k, k ≠ i → x k = y k) → A t i x = A t i y) ∧
      δ ≤ ‖𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))‖ := by
  let F (t : T) (u v : Fin n → X) := 𝔼 x : X, 𝔼 y : X,
    mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ x) (c - φ x - φ y) *
      star (mixedTailDifference (K t) (fun i => φ (u i)) (fun i => φ (v i)) (φ y)
        (c - φ x - φ y)) * B t u v (φ x) * C t u v (φ y)
  have hcomm : (𝔼 t, 𝔼 u, 𝔼 v, F t u v) = 𝔼 v, 𝔼 t, 𝔼 u, F t u v := by
    calc
      _ = 𝔼 t, 𝔼 v, 𝔼 u, F t u v :=
        Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
      _ = _ := Finset.expect_comm _ _ _
  change δ ≤ ‖𝔼 t, 𝔼 u, 𝔼 v, F t u v‖ at hcorr
  rw [hcomm] at hcorr
  have hmean : δ ≤ 𝔼 v, ‖𝔼 t, 𝔼 u, F t u v‖ :=
    hcorr.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hweights (t : T) := exists_mixed_anchor_weights (K t) (hK t) c (fun i => φ (a i))
    (fun u h => B t (fun i => ψ (u i)) a h) (fun u h => C t (fun i => ψ (u i)) a h)
    (fun u h => hB t _ a h) (fun u h => hC t _ a h)
  choose A hA hAind hpoint using hweights
  refine ⟨A, hA, hAind, ?_⟩
  have heq : (𝔼 t, 𝔼 u, F t u a) =
      𝔼 t, 𝔼 u : Fin n → X, 𝔼 x, 𝔼 y,
        (K t (φ x) (c - φ x - φ y) (fun i => φ (u i)) *
          star (K t (φ y) (c - φ x - φ y) (fun i => φ (u i)))) *
            ∏ i, A t i (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j)))) := by
    apply Finset.expect_congr rfl
    intro t _
    apply Finset.expect_congr rfl
    intro u _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    have H := hpoint t (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))))
    have h1 : (Fin.cons (φ x) (Fin.cons (φ y) (fun j => φ (u j))) :
        Fin (n + 2) → G) 1 = φ y := rfl
    simpa only [Fin.cons_zero, Fin.cons_succ, h1, hψ] using H
  rw [← heq]
  exact ha

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem bounded_coefficients_evaluation_error {J : Type*} [Fintype J]
    (P Q : MvPolynomial J ℝ) {s : ℕ} (hP : P.totalDegree ≤ s) (hQ : Q.totalDegree ≤ s)
    {η B : ℝ} (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hcoeff : ∀ e : BoundedIntegerExponent J s, |P.coeff e.val - Q.coeff e.val| ≤ η)
    (x : J → ℝ) (hx : ∀ j, |x j| ≤ B) :
    |aeval x P - aeval x Q| ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η * B ^ s := by
  have hdeg : (P - Q).totalDegree ≤ s := (totalDegree_sub P Q).trans (max_le hP hQ)
  have hmass : realPolynomialMass (P - Q) ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η := by
    calc
      _ ≤ ∑ _e ∈ (P - Q).support, η := by
        apply Finset.sum_le_sum
        intro e he
        simpa only [coeff_sub] using hcoeff ⟨e, (le_totalDegree he).trans hdeg⟩
      _ = ((P - Q).support.card : ℝ) * η := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (polynomial_support_card_le _ hdeg)) hη
  rw [← map_sub]
  exact (abs_aeval_le_mass_box (P - Q) x hB hx hdeg).trans
    (mul_le_mul_of_nonneg_right hmass (pow_nonneg (zero_le_one.trans hB) s))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

def Homogeneous (h : ℕ) (p : VectorPolynomial σ R W) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree ≠ h → coefficients p d = 0

theorem homogeneous_tmul {P : MvPolynomial σ R} {h : ℕ} (hP : P.IsHomogeneous h) (w : W) :
    Homogeneous h (P ⊗ₜ[R] w) := by
  intro d hd
  rw [coefficients_tmul, hP.coeff_eq_zero hd, zero_smul]

theorem homogeneous_support_degree {p : VectorPolynomial σ R W} {h : ℕ}
    (hp : Homogeneous h p) {d : σ →₀ ℕ} (hd : d ∈ (coefficients p).support) : d.degree = h := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hd) (hp d hn)

theorem eq_of_homogeneous_tmul (f g : VectorPolynomial σ R W →ₗ[R] Z) (h : ℕ)
    (he : ∀ (P : MvPolynomial σ R), P.IsHomogeneous h → ∀ w, f (P ⊗ₜ[R] w) = g (P ⊗ₜ[R] w))
    {p : VectorPolynomial σ R W} (hp : Homogeneous h p) : f p = g p := by
  have hexp := sum_monomial_coefficients p
  conv_lhs => rw [← hexp]
  conv_rhs => rw [← hexp]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact he (MvPolynomial.monomial d 1)
    (MvPolynomial.isHomogeneous_monomial 1 (homogeneous_support_degree hp hd)) (coefficients p d)

noncomputable def siteEvaluation {ι : Type*} (x : ι → σ → R) :
    VectorPolynomial σ R W →ₗ[R] (ι → W) := LinearMap.pi (fun i => eval (x i))

theorem siteEvaluation_tmul {ι : Type*} (x : ι → σ → R) (P : MvPolynomial σ R) (w : W) :
    siteEvaluation x (P ⊗ₜ[R] w) = fun i => MvPolynomial.eval (x i) P • w := rfl

noncomputable def siteFunctional {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) : (ι → W) →ₗ[R] R :=
  ∑ i, (L (Pi.single i 1)).comp (LinearMap.proj i)

theorem siteFunctional_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (W →ₗ[R] R)) (z : ι → R) (w : W) :
    siteFunctional L (fun i => z i • w) = L z w := by
  have hz : z = ∑ i, z i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hz]
  simp only [siteFunctional, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem curried_nonfactor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → σ → R) (Λ : VectorPolynomial σ R W →ₗ[R] R) (h : ℕ)
    (hn : ¬ ∃ M : (ι → W) →ₗ[R] R, ∀ p, Homogeneous h p → Λ p = M (siteEvaluation x p)) :
    ¬ ∃ L : (ι → R) →ₗ[R] (W →ₗ[R] R),
      ∀ P, P.IsHomogeneous h → TensorProduct.curry Λ P = L (fun i => MvPolynomial.eval (x i) P) := by
  rintro ⟨L, hL⟩
  apply hn
  refine ⟨siteFunctional L, ?_⟩
  intro p hp
  apply eq_of_homogeneous_tmul Λ ((siteFunctional L).comp (siteEvaluation x)) h _ hp
  intro P hP w
  have he := congrArg (fun F : W →ₗ[R] R => F w) (hL P hP)
  rw [TensorProduct.curry_apply] at he
  change Λ (P ⊗ₜ[R] w) = siteFunctional L (siteEvaluation x (P ⊗ₜ[R] w))
  rw [siteEvaluation_tmul, siteFunctional_tmul]
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

noncomputable def homogeneousPart (h : ℕ) :
    VectorPolynomial I R W →ₗ[R] VectorPolynomial I R W :=
  (MvPolynomial.homogeneousComponent h).rTensor W

theorem homogeneousPart_tmul (h : ℕ) (P : MvPolynomial I R) (w : W) :
    homogeneousPart h (P ⊗ₜ[R] w) = MvPolynomial.homogeneousComponent h P ⊗ₜ[R] w := rfl

theorem coefficients_homogeneousPart (h : ℕ) (p : VectorPolynomial I R W) (d : I →₀ ℕ) :
    coefficients (homogeneousPart h p) d = if d.degree = h then coefficients p d else 0 := by
  classical
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul P w =>
    rw [homogeneousPart_tmul, coefficients_tmul, MvPolynomial.coeff_homogeneousComponent,
      coefficients_tmul]
    split <;> simp_all
  | add p q hp hq =>
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split <;> simp

theorem homogeneousPart_homogeneous (h : ℕ) (p : VectorPolynomial I R W) :
    Homogeneous h (homogeneousPart h p) := by
  intro d hd
  simp only [coefficients_homogeneousPart, if_neg hd]

theorem sub_homogeneousPart_degreeLE {n : ℕ} {p : VectorPolynomial I R W}
    (hp : DegreeLE (1 : I → ℕ) (n + 1) p) :
    DegreeLE (1 : I → ℕ) n (p - homogeneousPart (n + 1) p) := by
  intro d hd
  have hd' : n < d.degree := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  simp only [map_sub, Finsupp.sub_apply, coefficients_homogeneousPart]
  by_cases he : d.degree = n + 1
  · simp only [if_pos he, sub_self]
  · have hh : n + 1 < Finsupp.weight (1 : I → ℕ) d := by
      have hh' : n + 1 < d.degree := by omega
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh'
    simp only [if_neg he, hp d hh, sub_zero]

theorem coordinate_homogeneousPart (f : W →+ S) (h : ℕ) (p : VectorPolynomial I R W) :
    coordinate f (homogeneousPart h p) = MvPolynomial.homogeneousComponent h (coordinate f p) := by
  classical
  ext d
  simp only [coeff_coordinate, coefficients_homogeneousPart, MvPolynomial.coeff_homogeneousComponent]
  split <;> simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

theorem independentProductPMF_marginal {I J X : Type*} [Fintype I] [Fintype J]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : I → PMF X) (e : J → I) (he : Function.Injective e) :
    (independentProductPMF p).map (fun (x : I → X) (j : J) => x (e j)) =
      independentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : I → X) j => x (e j)) _ (by fun_prop)]
  simp only [independentProductPMF, Measure.toPMF_toMeasure]
  exact (finiteProductMarginal_measurePreserving (fun i => (p i).toMeasure) e he).map_eq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

theorem linearFunctional_eq_coordinate_sum {J R : Type*} [Fintype J] [CommRing R]
    (L : (J → R) →ₗ[R] R) (w : J → R) :
    L w = ∑ j, L (Pi.single j 1) * w j := by
  have hw : w = ∑ j, w j • Pi.single j (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem realPolynomialMass_fin_prod_le {σ : Type*} {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) {B : ℝ}
    (hP : ∀ i, realPolynomialMass (P i) ≤ B) :
    realPolynomialMass (∏ i, P i) ≤ B ^ h := by
  apply (realPolynomialMass_prod_le Finset.univ P).trans
  calc
    _ ≤ ∏ _i : Fin h, B := Finset.prod_le_prod
      (fun i _ => realPolynomialMass_nonneg (P i)) (fun i _ => hP i)
    _ = B ^ h := by simp

namespace VectorPolynomial

noncomputable def contractedRow {σ J R : Type*} [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) : J → R :=
  fun j => Λ (P ⊗ₜ[R] Pi.single j 1)

theorem contractedRow_apply {σ J R : Type*} [Fintype J] [CommRing R]
    (Λ : VectorPolynomial σ R (J → R) →ₗ[R] R) (P : MvPolynomial σ R) (w : J → R) :
    ∑ j, contractedRow Λ P j * w j = Λ (P ⊗ₜ[R] w) :=
  (linearFunctional_eq_coordinate_sum (TensorProduct.curry Λ P) w).symm

def MonomialRowBound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ) (C : ℝ) : Prop :=
  ∀ (d : σ →₀ ℕ), d.degree = h → ∀ j, |Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)| ≤ C

theorem contractedRow_le_mass {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ} (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ P j| ≤ C * realPolynomialMass P :=
  polynomialFunctional_homogeneous_le_mass ((TensorProduct.curry Λ).flip (Pi.single j 1))
    hP (fun d hd => hΛ d hd j)

theorem contractedRow_prod_bound {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ) {h : ℕ}
    (P : Fin h → MvPolynomial σ ℝ) (hP : ∀ i, (P i).IsHomogeneous 1)
    {B C : ℝ} (hmass : ∀ i, realPolynomialMass (P i) ≤ B)
    (hC : 0 ≤ C) (hΛ : MonomialRowBound Λ h C) (j : J) :
    |contractedRow Λ (∏ i, P i) j| ≤ C * B ^ h := by
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => hP i)
  exact (contractedRow_le_mass Λ hp hΛ j).trans
    (mul_le_mul_of_nonneg_left (realPolynomialMass_fin_prod_le P hmass) hC)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientFunctional {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) : VectorPolynomial σ R (J → R) →ₗ[R] R :=
  (Finsupp.lsum R (fun d => ∑ j, frequency d j • LinearMap.proj j)).comp coefficients.toLinearMap

theorem coefficientFunctional_monomial {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (w : J → R) :
    coefficientFunctional frequency (monomial d w) = ∑ j, frequency d j * w j := by
  simp only [coefficientFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coefficients_monomial, Finsupp.lsum_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem coefficientFunctional_unit {σ J R : Type*} [Fintype J] [CommRing R]
    (frequency : (σ →₀ ℕ) → J → R) (d : σ →₀ ℕ) (j : J) :
    coefficientFunctional frequency (MvPolynomial.monomial d 1 ⊗ₜ[R] Pi.single j 1) = frequency d j := by
  change coefficientFunctional frequency (monomial d (Pi.single j 1)) = _
  rw [coefficientFunctional_monomial]
  simp [Pi.single_apply]

theorem coefficientFunctional_rowBound {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℝ) {h : ℕ} {C : ℝ}
    (hfrequency : ∀ d, d.degree = h → ∀ j, |frequency d j| ≤ C) :
    MonomialRowBound (coefficientFunctional frequency) h C := by
  intro d hd j
  rw [coefficientFunctional_unit]
  exact hfrequency d hd j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

abbrev BoundedCoefficientExponent (K : Type*) (h : ℕ) :=
  {d : K →₀ ℕ // d.degree ≤ h}

noncomputable instance boundedCoefficientExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedCoefficientExponent K h) := (Finsupp.finite_of_degree_le h).fintype

abbrev CoefficientSlot (K : Type*) (m : ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1)

abbrev CoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ s : CoefficientSlot K m, U s.1

noncomputable def coefficientArrayFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ where
  toFun x := ∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

theorem coefficientArrayFunctional_single {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (s : CoefficientSlot K m) (w : U s.1) :
    coefficientArrayFunctional U frequency (Pi.single s w) =
      ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a := by
  classical
  change (∑ t : CoefficientSlot K m, ∑ a, (frequency t.1 t.2.val a : ℝ) *
    ((Pi.single s w : CoefficientArray (K := K) U) t).val a) = _
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Pi.single_eq_of_ne hts]
  · simp

theorem coefficientArrayFunctional_eq_zero_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔
      ∀ (s : CoefficientSlot K m) (w : U s.1), ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a = 0 := by
  constructor
  · intro hz s w
    have he := DFunLike.congr_fun hz (Pi.single s w)
    simpa only [coefficientArrayFunctional_single, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    change (∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = 0
    exact Finset.sum_eq_zero (fun s _ => hz s (x s))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_homogeneous_monomial_nonzero {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧ L p ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W, L (monomial d w) ≠ 0 := by
  obtain ⟨p, hp, hLp⟩ := hnonzero
  by_contra hn
  push Not at hn
  apply hLp
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  exact hn d (homogeneous_support_degree hp hd) (coefficients p d)

theorem homogeneous_empty_factorization_iff {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) (site : Empty → K → ℝ) :
    (∃ M : (Empty → W) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous h p → L p = M (siteEvaluation site p)) ↔
      ∀ p, Homogeneous h p → L p = 0 := by
  constructor
  · rintro ⟨M, hM⟩ p hp
    have he := hM p hp
    rwa [Subsingleton.elim (siteEvaluation site p) 0, map_zero] at he
  · intro hz
    exact ⟨0, fun p hp => by simpa using hz p hp⟩

theorem exists_restricted_coefficient_nonzero {K J : Type*} [Fintype J]
    (W : Submodule ℝ (J → ℝ)) (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧
      coefficientFunctional (fun d j => (frequency d j : ℝ)) (map W.subtype p) ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W,
      (∑ j, (frequency d j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨d, hd, w, hw⟩ := exists_homogeneous_monomial_nonzero
    ((coefficientFunctional (fun d j => (frequency d j : ℝ))).comp (map W.subtype)) hnonzero
  refine ⟨d, hd, w, ?_⟩
  simpa only [LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
    coefficientFunctional_monomial] using hw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedCoefficientExponent_card_le {K : Type*} [Fintype K] (h : ℕ) :
    Fintype.card (BoundedCoefficientExponent K h) ≤
      (h + 1) * (Fintype.card K + 1) ^ h := by
  classical
  let code : BoundedCoefficientExponent K h → (Σ n : Fin (h + 1), Fin n.val → K) := fun d =>
    ⟨⟨d.val.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le d.property⟩, d.val.toMultiset.toList.get⟩
  have hinj : Function.Injective code := by
    intro d e he
    have hl := congrArg (fun z : Σ n : Fin (h + 1), Fin n.val → K => List.ofFn z.2) he
    change List.ofFn d.val.toMultiset.toList.get = List.ofFn e.val.toMultiset.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    have hm := congrArg (fun l : List K => (l : Multiset K)) hl
    rw [Multiset.coe_toList, Multiset.coe_toList] at hm
    apply Subtype.ext
    ext k
    have hk := congrArg (fun l : Multiset K => l.count k) hm
    simpa only [Finsupp.count_toMultiset] using hk
  have hc := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (h + 1), Fintype.card K ^ n.val := hc
    _ ≤ ∑ _n : Fin (h + 1), (Fintype.card K + 1) ^ h := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

def integerCubeWitnessBound (q : ℕ) (H D : ℝ) : ℝ :=
  integerFormMassBound q H D ((q.factorial : ℝ) * D ^ q)
    ((q : ℝ) * (((q.factorial : ℝ) * D ^ (q - 1)) * (1 + H)))

theorem integerCubeWitnessBound_nonneg (q : ℕ) {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) :
    0 ≤ integerCubeWitnessBound q H D := by
  unfold integerCubeWitnessBound integerFormMassBound
  positivity

theorem integer_coefficient_le_mass {σ : Type*} (P : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    |((P.coeff d : ℤ) : ℝ)| ≤ realPolynomialMass (map (Int.castRingHom ℝ) P) := by
  simpa only [coeff_map, Int.coe_castRingHom] using
    realPolynomialMass_coeff_le (map (Int.castRingHom ℝ) P) d

theorem exists_integral_vector_mode_witness {α K W : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup W] [Module ℝ W]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (hnonfactor : ¬ ∃ M : (Finset α → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p → Λ p = M (VectorPolynomial.siteEvaluation
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerCubeWitnessBound (Fintype.card α) H D) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      ∃ w : W, Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) ≠ 0 := by
  have hn := VectorPolynomial.curried_nonfactor
    (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) Λ h hnonfactor
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_bounded_integer_vanishing_product
    root difference selection hdet hH hD hroot hdiff (TensorProduct.curry Λ) h hn
  refine ⟨forms, hlen, hforms, hz, ?_⟩
  by_contra hnone
  apply hΛ
  ext w
  change Λ ((map (Int.castRingHom ℝ) forms.prod) ⊗ₜ[ℝ] w) = 0
  by_contra hw
  exact hnone ⟨w, hw⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem productBlockExponent_degree {K : Type*} {h : ℕ} (principal : Fin h → K) :
    (productBlockExponent principal).degree = h := by
  simp [productBlockExponent, map_sum, Finsupp.degree_single]

theorem canonicalPrincipalExponent_degree {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    (canonicalPrincipalExponent (G := G) h d b).degree = h d :=
  productBlockExponent_degree _

def constantCoefficientSlot (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

noncomputable def principalCoefficientSlot {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  ⟨canonicalPrincipalExponent h d b, (canonicalPrincipalExponent_degree h d b).le⟩

theorem principalCoefficientSlot_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientSlot (G := G) (B := B) h d) := by
  intro b b' he
  exact canonicalPrincipalExponent_injective h d hd (congrArg Subtype.val he)

noncomputable def principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] :
    Finset (BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) := by
  classical
  exact Finset.univ.image (principalCoefficientSlot h d)

theorem mem_principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (e) :
    e ∈ principalCoefficientSlots (G := G) (B := B) h d ↔
      ∃ b, principalCoefficientSlot h d b = e := by
  classical
  simp [principalCoefficientSlots]

theorem principalCoefficientSlots_card {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    (principalCoefficientSlots (G := G) (B := B) h d).card = Fintype.card (B d) := by
  classical
  exact (Finset.card_image_of_injective _ (principalCoefficientSlot_injective h d hd)).trans
    (Finset.card_univ)

theorem constantCoefficientSlot_not_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    constantCoefficientSlot (SamplerTupleIndex G B h) (h d) ∉ principalCoefficientSlots h d := by
  intro he
  obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d _).mp he
  exact canonicalPrincipalExponent_ne_zero h d hd b (congrArg Subtype.val hb)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

noncomputable def principalCoefficientChoice {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) :
    Option (B d) → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)
  | none => constantCoefficientSlot _ _
  | some b => principalCoefficientSlot h d b

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

def affinePairMatrix {J : Type*} (t u : J → ℤ) : Matrix (Fin 2) (Option J) ℤ :=
  fun i c => match c with
    | none => 1
    | some j => ![t j, u j] i

def affinePairImage {J : Type*} [Fintype J] (t u : J → ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  (affinePairMatrix t u).mulVecLin.range

end Erdos3

namespace Erdos3

open scoped Matrix

def pairDifferenceMod (m : ℕ) : (Fin 2 → ℤ) →+ ZMod m where
  toFun v := ((v 1 - v 0 : ℤ) : ZMod m)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, Int.cast_sub, Int.cast_add]; ring

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix Classical

def affinePairPivot {J : Type*} (t u : J → ℤ) (k : J) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, t k; 1, u k]

def affinePairFree {J : Type*} (t u : J → ℤ) (k : J) :
    Matrix (Fin 2) {j : J // j ≠ k} ℤ := fun i j => ![t j.val, u j.val] i

def affinePairColumnEquiv {J : Type*} [DecidableEq J] (k : J) :
    (Fin 2 ⊕ {j : J // j ≠ k}) ≃ Option J where
  toFun c := match c with
    | Sum.inl i => if i = 0 then none else some k
    | Sum.inr j => some j.val
  invFun c := match c with
    | none => Sum.inl 0
    | some j => if h : j = k then Sum.inl 1 else Sum.inr ⟨j, h⟩
  left_inv c := by
    rcases c with i | j
    · fin_cases i <;> simp
    · simp [j.property]
  right_inv c := by
    cases c with
    | none => rfl
    | some j => by_cases h : j = k <;> simp [h]

theorem affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J) :
    (affinePairPivot t u k).det = u k - t k := by
  simp [affinePairPivot, Matrix.det_fin_two]

end Erdos3

namespace Erdos3

open scoped Classical

noncomputable def latticeStarMask {I : Type*}
    (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ) (a : (Unit ⊕ I) → ZMod m) : ℂ := by
  classical
  exact if spatialUnstar a ∈ residueLatticeImage L m then (L.toAddSubgroup.index : ℂ) else 0

end Erdos3

namespace Erdos3

open scoped BigOperators

noncomputable def liftResidueMatrix {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) : Matrix I N ℤ :=
  fun i n => (ZMod.intCast_surjective (r i n)).choose

end Erdos3

namespace Erdos3

open scoped Matrix

noncomputable def affinePairScale (H L : ℝ) : Fin 2 → ℝ := ![H, H / L]

theorem affinePairScale_pos {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ i, 0 < affinePairScale H L i := by
  intro i
  fin_cases i
  · exact hH
  · exact div_pos hH hL

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def affinePairRowDensity {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0) (H L : ℝ) (hH : 0 < H) (hL : 0 < L)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
  normalizedFiberDensity (affinePairPivot t u k) (by rwa [affinePairPivot_det])
    (affinePairFree t u k) (affinePairScale H L) (fun _ => H) (fun _ => H / L)
    (affinePairScale_pos hH hL) (fun _ => hH) f

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

noncomputable def smoothPairRowLipschitz {J : Type*} [Fintype J] [DecidableEq J] (k : J) : ℝ≥0 :=
  ((Fintype.card {j : J // j ≠ k} + 2 : ℕ) : ℝ≥0) * probabilityProfileLipschitz

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def coefficientImageMask {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then
    (A.mulVecLin.range.toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

noncomputable def selectedCoefficientDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  normalizedFiberDensity (A.submatrix id s) hA (remainingMatrixColumns A s)
    (fun i => S (s i)) P (fun j => S j.val) (fun i => hS (s i)) hP (selectedCoefficientProfile s f)

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

noncomputable def coefficientImageMultiplier {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then (A.mulVecLin.range.toAddSubgroup.index : ℝ) else 0

noncomputable def coefficientResidueMultiplier {I J N : Type*} [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) {m : ℕ} (r : Matrix I N (ZMod m)) (v : I → ℤ) : ℝ :=
  coefficientImageMultiplier (Matrix.fromCols A (liftResidueMatrix r)) v

open MeasureTheory
open scoped BigOperators NNReal

structure CoefficientFiberControl {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (H L : ℝ) (h : ℕ) (C U G : ℝ) : Prop where
  det_ne_zero : (A.submatrix id s).det ≠ 0
  scale_lower : ∀ j, H / L ^ h ≤ S j
  integer_entry_bound : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h
  normalized_entry_bound : ∀ i j, |normalizedIntegerColumns A S (fun _ => H) i j| ≤ C
  inverse_bound : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
    (fun i => S (s i)) (fun _ => H))).inverse‖ ≤ U
  index_bound : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G

end Erdos3

namespace Erdos3

open scoped Matrix

variable {I I' J : Type*} [Fintype J]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallDifferenceGrowth
namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem higher_difference_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (hA : A.Nonempty) {K : ℝ}
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (m n : ℕ) :
    ((m • A - n • A).card : ℝ) ≤ K ^ (m + n) * A.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA A m n
  have hreal : ((m • A - n • A).card : ℝ) ≤
      (((A - A).card : ℝ) / A.card) ^ (m + n) * A.card := by
    have hc := (NNRat.cast_le (K := ℝ)).mpr h
    simpa only [NNRat.cast_natCast, NNRat.cast_mul, NNRat.cast_pow,
      NNRat.cast_div] using hc
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((A - A).card : ℝ) / A.card ≤ K :=
    (div_le_iff₀ hcard).mpr hsmall
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio _) hcard.le)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCyclicFreimanModel
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model (A : Finset ℤ) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card)
    (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (A' : Finset ℤ) (B : Finset (ZMod N)) (f : ℤ → ZMod N),
      0 < N ∧ A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
      B.Nonempty ∧ B = A'.image f ∧ B.card = A'.card ∧
      IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hN : 0 < 2 * D.card := Nat.mul_pos (by decide) hD.card_pos
  obtain ⟨A', B, f, hA'ne, hA'sub, hsize, hB, hf⟩ :=
    exists_large_cyclic_freiman_model A s hA hs
  have hBcard : B.card = A'.card := by
    rw [hB]
    exact Finset.card_image_of_injOn hf.bijOn.injOn
  have hBne : B.Nonempty := Finset.card_pos.mp (hBcard ▸ hA'ne.card_pos)
  have hDsize : (D.card : ℝ) ≤ K ^ (2 * s) * A.card := by
    simpa only [D, two_mul] using Erdos3.higher_difference_card_le A hA hsmall s s
  have hNsize : ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    push_cast
    calc
      2 * (D.card : ℝ) ≤ 2 * (K ^ (2 * s) * A.card) :=
        mul_le_mul_of_nonneg_left hDsize (by norm_num)
      _ = _ := by ring
  have hsizeR : (A.card : ℝ) ≤ (2 * (s : ℝ)) * B.card := by
    rw [hBcard]
    exact_mod_cast hsize
  have hmodelSize : ((2 * D.card : ℕ) : ℝ) ≤
      (4 * (s : ℝ) * K ^ (2 * s)) * B.card := by
    calc
      ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := hNsize
      _ ≤ 2 * K ^ (2 * s) * ((2 * (s : ℝ)) * B.card) :=
        mul_le_mul_of_nonneg_left hsizeR (by positivity)
      _ = _ := by ring
  have hdensity : (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤
      (B.card : ℝ) / (2 * D.card : ℕ) := by
    apply (le_div_iff₀ (by exact_mod_cast hN)).mpr
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hmodelSize
  exact ⟨2 * D.card, A', B, f, hN, hA'ne, hA'sub, hsize, hBne, hB,
    hBcard, hf, hNsize, hdensity⟩

end Erdos3.FreimanModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseTranslate
namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem exists_dense_translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A P : Finset G) (hA : A.Nonempty) {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q)
    (hbound : ((A - P).card : ℝ) ≤ q) (hsize : δ * q ≤ (P.card : ℝ)) :
    ∃ t ∈ A - P, ∃ F ⊆ A, F.Nonempty ∧ δ * A.card ≤ (F.card : ℝ) ∧
      ∀ a ∈ F, a - t ∈ P := by
  classical
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hPpos : (0 : ℝ) < P.card := (mul_pos hδ hq).trans_le hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpos)
  have hD : (A - P).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨p, hp⟩ := hP
    exact ⟨a - p, Finset.mem_sub.mpr ⟨a, ha, p, hp, rfl⟩⟩
  have hcount : (A - P).card • (δ * (A.card : ℝ)) ≤ ((A ×ˢ P).card : ℝ) := by
    rw [nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ q * (δ * A.card) := mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = (A.card : ℝ) * (δ * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg A.card)
  obtain ⟨t, ht, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := A ×ˢ P) (t := A - P) (f := fun x => x.1 - x.2)
    (fun x hx => Finset.mem_sub.mpr
      ⟨x.1, (Finset.mem_product.mp hx).1, x.2, (Finset.mem_product.mp hx).2, rfl⟩)
    hD hcount
  let T := (A ×ˢ P).filter fun x => x.1 - x.2 = t
  let F := T.image Prod.fst
  have hinj : Set.InjOn (Prod.fst : G × G → G) (T : Set (G × G)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    apply Prod.ext hxy
    have h := hx'.trans hy'.symm
    rw [hxy] at h
    exact sub_right_inj.mp h
  have hcard : F.card = T.card := Finset.card_image_of_injOn hinj
  have hFlarge : δ * A.card ≤ (F.card : ℝ) := by rw [hcard]; exact hlarge
  have hFpos : (0 : ℝ) < F.card := (mul_pos hδ hApos).trans_le hFlarge
  refine ⟨t, ht, F, ?_, Finset.card_pos.mp (by exact_mod_cast hFpos), hFlarge, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
    have hx' := Finset.mem_filter.mp hx
    have heq : a - t = x.2 := by rw [← hxa, ← hx'.2]; abel
    rw [heq]
    exact (Finset.mem_product.mp hx'.1).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DilationPairCoordinates
namespace OAI

section

namespace Erdos3

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

def scaledPairDifference (q : ℚ) : (L × L) →ₗ[ℚ] L :=
  LinearMap.fst ℚ L L - q • LinearMap.snd ℚ L L

@[simp] theorem scaledPairDifference_apply (q : ℚ) (x : L × L) :
    scaledPairDifference q x = x.1 - q • x.2 := rfl

def scaledPairAssemble (q : ℚ) (u v : L) : L × L := (u + q • v, v)

@[simp] theorem scaledPairDifference_assemble (q : ℚ) (u v : L) :
    scaledPairDifference q (scaledPairAssemble q u v) = u := by
  simp [scaledPairAssemble]

theorem scaledPairAssemble_decompose (q : ℚ) (x : L × L) :
    scaledPairAssemble q (scaledPairDifference q x) x.2 = x := by
  apply Prod.ext <;> simp [scaledPairAssemble]

def scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ P ∧ x.2 ∈ P ∧ scaledPairDifference q x ∈ Q}
  zero_mem' := ⟨P.zero_mem, P.zero_mem, by simp⟩
  add_mem' hx hy := ⟨P.add_mem hx.1 hy.1, P.add_mem hx.2.1 hy.2.1,
    by simpa only [map_add] using Q.add_mem hx.2.2 hy.2.2⟩
  smul_mem' a x hx := ⟨P.smul_mem a hx.1, P.smul_mem a hx.2.1,
    by simpa only [map_smul] using Q.smul_mem a hx.2.2⟩

@[simp] theorem mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) (x : L × L) :
    x ∈ scaledPairLayer P Q q ↔ x.1 ∈ P ∧ x.2 ∈ P ∧ x.1 - q • x.2 ∈ Q := Iff.rfl

def scaledPairLayerEquiv (P Q : Submodule ℚ L) (hQP : Q ≤ P) (q : ℚ) :
    (Q × P) ≃ₗ[ℚ] scaledPairLayer P Q q where
  toFun x := ⟨scaledPairAssemble q x.1 x.2,
    ⟨P.add_mem (hQP x.1.property) (P.smul_mem q x.2.property), x.2.property,
      by
        rw [scaledPairDifference_assemble]
        exact x.1.property⟩⟩
  invFun x := (⟨scaledPairDifference q x.val, x.property.2.2⟩, ⟨x.val.2, x.property.2.1⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (scaledPairDifference_assemble q (x.1 : L) (x.2 : L))
    · rfl
  right_inv x := Subtype.ext (scaledPairAssemble_decompose q x.val)
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [scaledPairAssemble, Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
      abel
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · change a • (x.1 : L) + q • (a • (x.2 : L)) = a • ((x.1 : L) + q • (x.2 : L))
      rw [smul_add, smul_comm q a]
    · rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n)

@[simp] theorem mem_dilationPairLayer (q : ℚ) (n : ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q n ↔
      x.1 ∈ F.layer n ∧ x.2 ∈ F.layer n ∧ x.1 - q ^ n • x.2 ∈ F.layer (n + 1) := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro i j hij x hx
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hx
  refine ⟨F.antitone hij hx.1, F.antitone hij hx.2.1, ?_⟩
  change x.1 - q ^ i • x.2 ∈ F.layer (i + 1)
  have hdiff : x.1 - q ^ i • x.2 = (x.1 - q ^ j • x.2) + (q ^ j - q ^ i) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.layer (i + 1)).add_mem
    (F.antitone (Nat.add_le_add_right hij 1) hx.2.2)
    ((F.layer (i + 1)).smul_mem _ (F.antitone (Nat.succ_le_of_lt hlt) hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q i) (hy : y ∈ F.dilationPairLayer q j) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ i • x.2, y.1⁆ + q ^ i • ⁅x.2, y.1 - q ^ j • y.2⁆ := by
    simp only [sub_lie, lie_sub, smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [scaledPairDifference_apply, Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    ((F.layer (i + j + 1)).smul_mem _
      (by simpa only [scaledPairDifference_apply, Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2))

theorem dilationPairLayer_terminal (q : ℚ) : F.dilationPairLayer q (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q s) : x.1 = q ^ s • x.2 := by
  have h : x.1 - q ^ s • x.2 ∈ F.layer (s + 1) := hx.2.2
  rw [F.terminal, Submodule.mem_bot, sub_eq_zero] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairSubalgebra (q : ℚ) : LieSubalgebra ℚ (L × L) :=
  { F.dilationPairLayer q 1 with
    lie_mem' := fun hx hy => F.dilationPairLayer_antitone q (by decide : 1 ≤ 1 + 1)
      (F.dilationPairLayer_lie_mem q hx hy) }

@[simp] theorem mem_dilationPairSubalgebra (q : ℚ) (x : L × L) :
    x ∈ F.dilationPairSubalgebra q ↔ x.1 - q • x.2 ∈ F.layer 2 := by
  change x ∈ F.dilationPairLayer q 1 ↔ _
  simp only [mem_dilationPairLayer, F.one_eq_top, Submodule.mem_top, pow_one, true_and]

def dilationPairFiltration (q : ℚ) : NilpotentLieFiltration (F.dilationPairSubalgebra q) s where
  layer n := (F.dilationPairLayer q n).comap (F.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q (s + 1) := hx
    simpa only [F.dilationPairLayer_terminal, Submodule.mem_bot] using h

@[simp] theorem mem_dilationPairFiltration_layer (q : ℚ) (n : ℕ)
    (x : F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).layer n ↔ x.val ∈ F.dilationPairLayer q n := Iff.rfl

def dilationPairFirst (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp (F.dilationPairSubalgebra q).incl

def dilationPairSecond (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp (F.dilationPairSubalgebra q).incl

theorem dilationPairTop_relation (q : ℚ) {x : F.dilationPairSubalgebra q}
    (hx : x ∈ (F.dilationPairFiltration q).layer s) :
    F.dilationPairFirst q x = q ^ s • F.dilationPairSecond q x :=
  F.dilationPairLayer_top_relation q hx

def dilationPairFiltrationLayerEquiv (q : ℚ) (n : ℕ) (hn : 1 ≤ n) :
    (F.dilationPairFiltration q).layer n ≃ₗ[ℚ] F.dilationPairLayer q n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.dilationPairLayer_antitone q hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FamilyDerivativeCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_many_family_derivative_correlations {I G : Type*}
    [Fintype I] [Nonempty I] [AddCommGroup G] [Fintype G]
    (f g : I → G → ℂ) (H : Finset I)
    (hf : ∀ i n, ‖f i n‖ ≤ 1) (hg : ∀ i n, ‖g i n‖ ≤ 1)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hdense : α * Fintype.card I ≤ (H.card : ℝ))
    (hcorr : ∀ i ∈ H, δ ≤ ‖finiteCorrelation Finset.univ (f i) (g i)‖) :
    ∃ Q : Finset (I × G), Q.Nonempty ∧
      α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 ∈ H ∧ α * δ ^ 2 / 2 ≤
        ‖finiteCorrelation Finset.univ
          (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ := by
  classical
  let value (t : I × G) := if t.1 ∈ H then
    ‖finiteCorrelation Finset.univ
      (multiplicativeDerivative (f t.1) t.2) (multiplicativeDerivative (g t.1) t.2)‖ else 0
  have hrow (i : I) : (if i ∈ H then δ ^ 2 else 0) ≤ 𝔼 k : G, value (i, k) := by
    by_cases hi : i ∈ H
    · simp only [value, hi, ite_true]
      exact (pow_le_pow_left₀ hδ.le (hcorr i hi) 2).trans
        (correlation_sq_le_expect_norm_derivative (f i) (g i))
    · simp only [value, hi, ite_false, Fintype.expect_const, le_refl]
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) =
      (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : α * δ ^ 2 ≤ 𝔼 t : I × G, value t := by
    calc
      _ ≤ (H.card : ℝ) * δ ^ 2 / Fintype.card I := by
        apply (le_div_iff₀ hcard).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (sq_nonneg δ)]
      _ = (𝔼 i : I, if i ∈ H then δ ^ 2 else 0) := hindicator.symm
      _ ≤ 𝔼 i : I, 𝔼 k : G, value (i, k) := Finset.expect_le_expect (fun i _ => hrow i)
      _ = _ := by rw [← Finset.expect_product, Finset.univ_product_univ]
  have hcap (t : I × G) : value t ≤ 1 := by
    by_cases ht : t.1 ∈ H
    · simp only [value, ht, ite_true]
      simpa only [one_pow] using norm_derivativeCorrelation_le (f t.1) (g t.1) (hf t.1) (hg t.1) t.2
    · simp only [value, ht, ite_false, zero_le_one]
  obtain ⟨Q, hQsize, hQcorr⟩ :=
    exists_dense_level_set value (by positivity : 0 ≤ α * δ ^ 2) hcap hmean
  have hsize : α * δ ^ 2 / 2 * Fintype.card I * Fintype.card G ≤ (Q.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using hQsize
  have hI : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < α * δ ^ 2 / 2 * (Fintype.card I : ℝ) * Fintype.card G) hsize
  refine ⟨Q, hQ, hsize, ?_⟩
  intro t ht
  have hm : t.1 ∈ H := by
    by_contra hn
    have hpos : 0 < value t := lt_of_lt_of_le (by positivity) (hQcorr t ht)
    simp only [value, hn, ite_false, lt_self_iff_false] at hpos
  exact ⟨hm, by simpa only [value, hm, ite_true] using hQcorr t ht⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

noncomputable def finiteProductIntegral (w : I → X → ℝ) (f : (I → X) → ℝ) : ℝ :=
  ∑ v, (∏ i, w i (v i)) * f v

end Erdos3

end

section

namespace Erdos3

variable {I X : Type*}

def finiteSplitPoint (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) : I → X :=
  fun i => if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩

theorem finiteSplitPoint_fixed (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) (i : {i // p i}) :
    finiteSplitPoint p u v i = u i := by
  simp only [finiteSplitPoint, dif_pos i.property]

theorem finiteSplitPoint_restrict (p : I → Prop) [DecidablePred p] (x : I → X) :
    finiteSplitPoint p (fun i => x i) (fun i => x i) = x := by
  funext i
  by_cases hi : p i <;> simp only [finiteSplitPoint, hi, dite_true, dite_false]

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

variable {I J X : Type*}

def finiteProductCoordinateEquiv (e : I ≃ J) : (I → X) ≃ (J → X) where
  toFun v j := v (e.symm j)
  invFun v i := v (e i)
  left_inv v := by funext i; simp
  right_inv v := by funext j; simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {X : Type*} {keep : X → Prop} {N : {x // keep x} → ℕ} {q s d : ℕ}

noncomputable def fiberInverseParameters (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X k.val - C (S.start k : ℝ))

theorem fiberInverseParameters_degree (S : ResidueBoxSlice N q) (k : {x // keep x}) :
    S.fiberInverseParameters k ∈ weightedSupportLE (fun _ : X => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _
    ((weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

noncomputable def fiberReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : PolynomialPatch X s d :=
  Q.reparam S.fiberInverseParameters S.fiberInverseParameters_degree

@[simp] theorem fiberReinsertPatch_kernel (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel = Q.kernel := rfl

@[simp] theorem fiberReinsertPatch_weight (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).weight = Q.weight := rfl

@[simp] theorem fiberReinsertPatch_lip (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) : (S.fiberReinsertPatch Q).kernel.lip = Q.kernel.lip := rfl

theorem fiberReinsertPatch_value (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (x : X → ℝ) :
    (S.fiberReinsertPatch Q).value x =
      Q.value (fun k => (x k.val - (S.start k : ℝ)) / (q : ℝ)) := by
  rw [fiberReinsertPatch, PolynomialPatch.reparam_value]
  congr 1
  funext k
  simp only [fiberInverseParameters, map_smul, map_sub, aeval_X, aeval_C,
    smul_eq_mul, div_eq_mul_inv, mul_comm, Algebra.algebraMap_self, RingHom.id_apply]

def fiberIntegerPoint [DecidablePred keep] (S : ResidueBoxSlice N q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) : X → ℤ :=
  finiteSplitPoint keep (fun k => ((S.point u k).val : ℤ)) fixed

theorem fiberReinsertPatch_point_value [DecidablePred keep] (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value
      (fun k => ((finiteSplitPoint keep (fun i => ((S.point u i).val : ℤ)) fixed k : ℤ) : ℝ)) =
        Q.value (fun k => ((u k).val : ℝ)) := by
  rw [fiberReinsertPatch_value]
  congr 1
  funext k
  rw [finiteSplitPoint_fixed]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp
  ring

@[simp] theorem fiberReinsertPatch_integerPoint_value [DecidablePred keep]
    (S : ResidueBoxSlice N q) (Q : PolynomialPatch {x // keep x} s d) (hq : 0 < q)
    (fixed : {x // ¬keep x} → ℤ) (u : ∀ k, Fin (S.length k)) :
    (S.fiberReinsertPatch Q).value (fun k => (S.fiberIntegerPoint fixed u k : ℝ)) =
      Q.value (fun k => ((u k).val : ℝ)) :=
  S.fiberReinsertPatch_point_value Q hq fixed u

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedLp (w : X → ℝ) (p : ℝ) (f : X → ℝ) : ℝ :=
  (∑ x, w x * |f x| ^ p) ^ (1 / p)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMixedLp w p n
      (fun v => finiteWeightedLp (w n) (p n) (fun a => f (Fin.snoc v a)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteSectionIntegral (w : ℕ → X → ℝ) :
    (n : ℕ) → (Fin n → Bool) → ((Fin n → X) → ℝ) → (Fin n → X) → ℝ
  | 0, _, f, _ => f (fun i => Fin.elim0 i)
  | n + 1, s, f, z =>
      if s (Fin.last n) then
        finiteSectionIntegral w n (Fin.init s)
          (fun v => f (Fin.snoc v (z (Fin.last n)))) (Fin.init z)
      else
        finiteSectionIntegral w n (Fin.init s)
          (fun v => ∑ a, w n a * f (Fin.snoc v a)) (Fin.init z)

noncomputable def finiteSectionL2Norm (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) : ℝ :=
  Real.sqrt (finiteSectionIntegral w n s (fun v => f v ^ 2) z)

def finiteSectionCount {n : ℕ} (s : Fin n → Bool) : ℕ :=
  ∑ i, if s i then 1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedL2Map (w : X → ℝ) : (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ X where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (w x) * f x)
  map_add' f g := by
    ext x
    change Real.sqrt (w x) * (f x + g x) = Real.sqrt (w x) * f x + Real.sqrt (w x) * g x
    ring
  map_smul' c f := by
    ext x
    change Real.sqrt (w x) * (c * f x) = c * (Real.sqrt (w x) * f x)
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedLpStep (w : X → ℝ) (p : ℝ) (b : Bool) (x₀ : X)
    (n : ℕ) (f : (Fin (n + 1) → X) → ℝ) (v : Fin n → X) : ℝ :=
  if b then finiteWeightedLp w p (fun a => f (Fin.snoc v a)) else f (Fin.snoc v x₀)

noncomputable def finiteMaskedMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (s : ℕ → Bool) (x₀ : X) : (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMaskedMixedLp w p s x₀ n (finiteMaskedLpStep (w n) (p n) (s n) x₀ n f)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

def finiteSectionL2Control (w : ℕ → X → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → (ℕ → ℝ) → Prop
  | 0, f, E => |f (fun i => Fin.elim0 i)| ≤ E 0
  | n + 1, f, E =>
      (∀ a, finiteSectionL2Control w n (fun v => f (Fin.snoc v a))
        (fun j => E (j + 1))) ∧
      finiteSectionL2Control w n
        (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a))) E

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionCount_eq_card (n : ℕ) (s : Fin n → Bool) :
    finiteSectionCount s = Fintype.card {i : Fin n // s i = true} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem finiteSection_free_card (n : ℕ) (s : Fin n → Bool) :
    Fintype.card {i : Fin n // s i ≠ true} = n - finiteSectionCount s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, finiteSectionCount_eq_card]

noncomputable def finiteSectionFreeOrder (n : ℕ) (s : Fin n → Bool) :
    Fin (n - finiteSectionCount s) ≃o {i : Fin n // s i ≠ true} :=
  Fintype.orderIsoFinOfCardEq _ (finiteSection_free_card n s)

noncomputable def finiteSectionFill {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) : Fin n → X :=
  finiteSplitPoint (fun i => s i = true) (fun i => z i)
    (fun i => v ((finiteSectionFreeOrder n s).symm i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteSectionWeight (w : X → ℝ) (b : Bool) (z x : X) : ℝ := by
  classical
  exact if b then (if x = z then 1 else 0) else w x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

def FiniteTupleDependsOn (s : ℕ → Bool) (n : ℕ) (f : (Fin n → X) → ℝ) : Prop :=
  ∀ v u, (∀ i : Fin n, s i = true → v i = u i) → f v = f u

theorem FiniteTupleDependsOn.snoc {s : ℕ → Bool} {n : ℕ}
    {f : (Fin (n + 1) → X) → ℝ} (hf : FiniteTupleDependsOn s (n + 1) f)
    {v u : Fin n → X} {a b : X}
    (hvu : ∀ i : Fin n, s i = true → v i = u i) (hab : s n = true → a = b) :
    f (Fin.snoc v a) = f (Fin.snoc u b) := by
  apply hf
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hs
    simpa only [Fin.snoc_last] using hab hs
  · intro hs
    simpa only [Fin.snoc_castSucc] using hvu j hs

end Erdos3

end

section

namespace Erdos3

variable {n k : ℕ}

noncomputable def finiteSlotMask (a : Fin k → Fin n) (i : ℕ) : Bool := by
  classical
  exact decide (∃ j, (a j).val = i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedWeights (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) : X → ℝ :=
  finiteSectionWeight (w i) (!(s i)) x₀

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

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

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

def finiteFactorMultiplicity (b : J → Bool) : ℕ :=
  (Finset.univ.filter (fun j => b j = true)).card

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X] [Nonempty X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J B X : Type*} [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_expect_le_one {X : Type*} (A : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) : ‖𝔼 x ∈ A, f x‖ ≤ 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  · exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hA hf)

theorem norm_expect_subset_sub_le {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℂ) (hf : ∀ x ∈ B, ‖f x‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have hB : B.Nonempty := hA.mono hAB
  have hB0 : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have hBR : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hmean := norm_finset_expect_le_one A f (fun x hx => hf x (hAB hx))
  have hsum : (∑ x ∈ B \ A, f x) + ∑ x ∈ A, f x = ∑ x ∈ B, f x :=
    Finset.sum_sdiff hAB
  have hc : ((B \ A).card : ℂ) + (A.card : ℂ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  have heq : (𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x =
      (∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)) / (B.card : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [sub_div, mul_div_assoc, Finset.expect_eq_sum_div_card B]
    have hAeq := Finset.card_mul_expect A f
    field_simp
    linear_combination hAeq + hsum - (𝔼 a ∈ A, f a) * hc
  have hnorm : ‖∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)‖ ≤
      2 * ((B \ A).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ B \ A, ‖(𝔼 a ∈ A, f a) - f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ B \ A, (2 : ℝ) := Finset.sum_le_sum (fun x hx =>
        (norm_sub_le _ _).trans (by linarith [hf x (Finset.mem_sdiff.mp hx).1]))
      _ = _ := by simp [mul_comm]
  rw [heq, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hnorm hBR.le).trans_eq
  have hcR : ((B \ A).card : ℝ) + (A.card : ℝ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  field_simp
  nlinarith

theorem norm_expect_injective_sub_le {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f (g x)) - 𝔼 y ∈ B, f y‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have h := norm_expect_subset_sub_le (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

namespace FiniteProbabilityWeights

theorem translated_subset_mixture_compare {X Y Z : Type*} [Fintype Z] [DecidableEq Y]
    (p : FiniteProbabilityWeights Z) (A : Finset X) (B : Finset Y) (hA : A.Nonempty)
    (g : Z → X → Y) (hg : ∀ z, Set.InjOn (g z) A)
    (hB : ∀ z x, x ∈ A → g z x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, p.complexMean (fun z => f (g z x))) - 𝔼 y ∈ B, f y‖ ≤
      2 * (1 - (A.card : ℝ) / B.card) := by
  rw [← p.complexMean_finset_expect]
  have hc : p.complexMean (fun _ => 𝔼 y ∈ B, f y) = 𝔼 y ∈ B, f y := by
    simp only [complexMean, ← Finset.sum_mul, ← Complex.ofReal_sum, p.total,
      Complex.ofReal_one, one_mul]
  rw [← hc]
  exact (p.norm_complexMean_sub_le _ _ (fun _ => 2 * (1 - (A.card : ℝ) / B.card))
    (fun z _ => norm_expect_injective_sub_le A B hA (g z) (hg z) (hB z) f hf)).trans_eq
    (p.mean_const _)

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) : Finset T := Finset.univ.filter (fun t => e t ∈ A)

theorem image_finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) (hA : A ⊆ Finset.univ.image e) :
    (finiteSitePreimage e A).image e = A := by
  ext x
  simp only [Finset.mem_image, finiteSitePreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (hA hx)
    exact ⟨t, hx, rfl⟩

theorem finiteSitePreimage_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X)
    (hA : A ⊆ Finset.univ.image e) : (finiteSitePreimage e A).card = A.card := by
  have h := congrArg Finset.card (image_finiteSitePreimage e A hA)
  simpa only [Finset.card_image_of_injective _ he] using h

theorem finiteSitePreimage_subset {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X) (S : Finset T)
    (hA : A ⊆ S.image e) : finiteSitePreimage e A ⊆ S := by
  intro t ht
  have het : e t ∈ A := (Finset.mem_filter.mp ht).2
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp (hA het)
  exact he hst ▸ hs

noncomputable def finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : Finset (Finset T) :=
  (D.filter (fun A => A ⊆ Finset.univ.image e)).image (finiteSitePreimage e)

theorem finiteSiteInnerFamily_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : (finiteSiteInnerFamily e D).card ≤ D.card :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _)

theorem mem_finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset X}
    (hAD : A ∈ D) (hA : A ⊆ Finset.univ.image e) :
    finiteSitePreimage e A ∈ finiteSiteInnerFamily e D :=
  Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAD, hA⟩, rfl⟩

theorem finiteSiteInnerFamily_image_mem {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset T}
    (hA : A ∈ finiteSiteInnerFamily e D) : A.image e ∈ D := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  rw [image_finiteSitePreimage e B (Finset.mem_filter.mp hB).2]
  exact (Finset.mem_filter.mp hB).1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_inner_interval_family {p : ℝ} (hp : 0 ≤ p) (N : ℕ) :
    ∃ C : Finset (Finset ℤ), (C.card : ℝ) ≤ Real.exp (4 * p + 18) ∧
      (∀ S ∈ C, ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ)) ∧
      ∀ a len : ℕ, a + len ≤ N → 0 < len → Real.exp (-p) * N ≤ (len : ℝ) →
        ∃ S ∈ C, S.Nonempty ∧ S ⊆ Finset.Ico (a : ℤ) (a + len) ∧
          (len : ℝ) ≤ 2 * S.card ∧
          2 * (1 - (S.card : ℝ) / len) ≤ Real.exp (-p) := by
  classical
  by_cases hN : Real.exp (2 * p + 8) ≤ (N : ℝ)
  · obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
    let C := (Finset.univ : Finset (Fin (N / L + 2) × Fin (N / L + 2))).image
      (fun c => Finset.Ico (L * c.1.val : ℤ) (L * c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have hc : C.card ≤ (N / L + 2) * (N / L + 2) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N / L + 2 : ℕ) * (N / L + 2 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
          mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (4 * p + 10) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨L * c.1.val, L * c.2.val, by simp only [Nat.cast_mul]⟩
    · intro a len hend hlen hdense
      have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hsmall : 4 * (L : ℝ) ≤ Real.exp (-p) * len := by
        calc
          _ ≤ Real.exp (-(2 * p)) * N := hscale
          _ = Real.exp (-p) * (Real.exp (-p) * N) := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      have hsN : 4 * L ≤ len := by
        exact_mod_cast hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
      obtain ⟨hstart, hstop, hne, _, hhalf, hloss⟩ := integer_grid_interval_geometry a len hL hsN
      let S := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
      have hcard : S.card = integerGridEnd (a + len) L - integerGridStart a L := by
        simp only [S, Int.card_Ico]
        rw [← Int.natCast_sub hne.le, Int.toNat_natCast]
      have hadiv : a / L ≤ N / L := Nat.div_le_div_right (by omega)
      have hbdiv : (a + len) / L ≤ N / L := Nat.div_le_div_right hend
      refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a / L + 1, by omega⟩, ⟨(a + len) / L, by omega⟩), Finset.mem_univ _, by
            simp only [S, integerGridStart, integerGridEnd, Nat.cast_mul]⟩
      · apply Finset.card_pos.mp
        rw [hcard]
        exact Nat.sub_pos_of_lt hne
      · intro x hx
        simp only [S, Finset.mem_Ico] at hx ⊢
        constructor <;> omega
      · rw [hcard]
        exact_mod_cast hhalf
      · have hlossR : (len : ℝ) ≤ S.card + 2 * L := by rw [hcard]; exact_mod_cast hloss
        have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen
        have he : 2 * (1 - (S.card : ℝ) / len) = 2 * ((len : ℝ) - S.card) / len := by
          field_simp
        rw [he]
        apply (div_le_iff₀ hlenR).mpr
        linarith
  · let C := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).image
      (fun c => Finset.Ico (c.1.val : ℤ) (c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have h1 : (1 : ℝ) ≤ Real.exp (2 * p + 8) := Real.one_le_exp (by positivity)
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hNp : (N + 1 : ℕ) ≤ Real.exp (2 * p + 9) := by
        have hs : (N : ℝ) + 1 ≤ 2 * Real.exp (2 * p + 8) := by linarith
        calc
          ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_cast
          _ ≤ 2 * Real.exp (2 * p + 8) := hs
          _ ≤ Real.exp 1 * Real.exp (2 * p + 8) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have hc : C.card ≤ (N + 1) * (N + 1) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N + 1 : ℕ) * (N + 1 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 9) * Real.exp (2 * p + 9) :=
          mul_le_mul hNp hNp (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨c.1.val, c.2.val, rfl⟩
    · intro a len hend hlen _
      have hcard : (Finset.Ico (a : ℤ) (a + len)).card = len := by simp
      refine ⟨Finset.Ico (a : ℤ) (a + len), ?_, ?_, Finset.Subset.refl _, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a, by omega⟩, ⟨a + len, by omega⟩), Finset.mem_univ _, by simp⟩
      · exact Finset.card_pos.mp (by simpa only [hcard] using hlen)
      · rw [hcard]
        nlinarith [Nat.cast_nonneg (α := ℝ) len]
      · rw [hcard, div_self (by exact_mod_cast hlen.ne' : (len : ℝ) ≠ 0)]
        simpa using Real.exp_nonneg (-p)

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

theorem piFinset_inner_card_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) :
    1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ∑ i, (1 - ((A i).card : ℝ) / (B i).card) := by
  let r : I → ℝ := fun i => ((A i).card : ℝ) / (B i).card
  have hr (i : I) : r i ∈ Set.Icc (0 : ℝ) 1 := by
    have hpos : (0 : ℝ) < (B i).card := by exact_mod_cast (hB i).card_pos
    refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, ?_⟩
    exact (div_le_one hpos).mpr (by exact_mod_cast Finset.card_le_card (hsub i))
  have hprod := one_sub_sum_le_positive_prod Finset.univ r (fun i => 1 - r i)
    (fun i _ => (hr i).1) (fun i _ => ⟨by linarith [(hr i).2], by linarith [(hr i).1]⟩)
    (fun i _ => by linarith)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ i, r i := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he]
  change 1 - ∏ i, r i ≤ ∑ i, (1 - r i)
  linarith

theorem piFinset_inner_normalized_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) (ε : I → ℝ)
    (hloss : ∀ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) ≤ ε i) :
    2 * (1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card) ≤ ∑ i, ε i := by
  calc
    _ ≤ 2 * ∑ i, (1 - ((A i).card : ℝ) / (B i).card) :=
      mul_le_mul_of_nonneg_left (piFinset_inner_card_loss A B hB hsub) (by norm_num)
    _ = ∑ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hloss i)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DenseRealBoxCell
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem card_image_eq_of_same_fibers {α β γ : Type*} [Nonempty α]
    [DecidableEq β] [DecidableEq γ] (A : Finset α) (f : α → β) (g : α → γ)
    (hrel : ∀ x ∈ A, ∀ y ∈ A, f x = f y ↔ g x = g y) :
    (A.image f).card = (A.image g).card := by
  classical
  let r := Function.invFunOn f (A : Set α)
  have hr {y : β} (hy : y ∈ A.image f) : r y ∈ A ∧ f (r y) = y :=
    Function.invFunOn_pos (Finset.mem_image.mp hy)
  have hinj : Set.InjOn (g ∘ r) (A.image f : Set β) := by
    intro y hy z hz h
    have he := (hrel (r y) (hr hy).1 (r z) (hr hz).1).mpr h
    simpa only [(hr hy).2, (hr hz).2] using he
  have himage : (A.image f).image (g ∘ r) = A.image g := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨r y, (hr hy).1, rfl⟩
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hfx : f x ∈ A.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨f x, hfx,
        (hrel (r (f x)) (hr hfx).1 x hx).mp (hr hfx).2⟩
  rw [← himage, Finset.card_image_of_injOn hinj]

theorem card_difference_image_of_freiman {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H)
    (hf : IsAddFreimanIso 2 (A : Set G) (A.image f : Set H) f) :
    ((A.image f - A.image f).card : ℕ) = (A - A).card := by
  have hrel : ∀ x ∈ A ×ˢ A, ∀ y ∈ A ×ˢ A,
      x.1 - x.2 = y.1 - y.2 ↔ f x.1 - f x.2 = f y.1 - f y.2 := by
    intro x hx y hy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    rw [sub_eq_sub_iff_add_eq_add, sub_eq_sub_iff_add_eq_add]
    exact (hf.add_eq_add hx1 hy2 hy1 hx2).symm
  have hcard := card_image_eq_of_same_fibers (A ×ˢ A)
    (fun x => x.1 - x.2) (fun x => f x.1 - f x.2) hrel
  have hout : (A ×ˢ A).image (fun x => f x.1 - f x.2) = A.image f - A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      exact Finset.mem_sub.mpr ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · intro hz
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩,
        by change f x - f y = z; rw [hxu, hyv]; exact huv⟩
  simpa only [hout, Finset.image_sub_product] using hcard.symm

theorem exists_nonempty_large_fiber {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (A : Finset α) (hA : A.Nonempty) (f : α → β) :
    ∃ b : β, (A.filter fun x => f x = b).Nonempty ∧
      A.card ≤ Fintype.card β * (A.filter fun x => f x = b).card := by
  classical
  let k := Fintype.card β
  have hk : 0 < k := Fintype.card_pos
  let n := (A.card - 1) / k
  have hApos := hA.card_pos
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨b, _, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _)
      (by simpa only [Finset.card_univ] using hkn)
  refine ⟨b, Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard), ?_⟩
  have hceil : A.card - 1 < k * (n + 1) := Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤ k * (A.filter fun x => f x = b).card :=
    Nat.mul_le_mul_left k (by omega)
  change A.card ≤ k * (A.filter fun x => f x = b).card
  omega

end Erdos3.FreimanModel

end

section

namespace Erdos3

noncomputable def realBoxCellCount (C : ℝ) (q : ℕ) : ℕ := ⌊2 * q * C⌋₊ + 1

theorem realBoxCellCount_pos (C : ℝ) (q : ℕ) : 0 < realBoxCellCount C q := by
  unfold realBoxCellCount
  omega

theorem realBoxCellCount_le {C : ℝ} (hC : 0 ≤ C) (q : ℕ) :
    (realBoxCellCount C q : ℝ) ≤ 2 * q * C + 1 := by
  unfold realBoxCellCount
  push_cast
  exact add_le_add (Nat.floor_le (by positivity)) (le_refl 1)

theorem realBoxCell_floor_lt {C : ℝ} (q : ℕ) (y : ℝ) (hy : |y| ≤ C) :
    ⌊(q : ℝ) * (y + C)⌋₊ < realBoxCellCount C q := by
  have hupper : (q : ℝ) * (y + C) ≤ 2 * q * C := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 (Nat.cast_nonneg (α := ℝ) q)
    nlinarith
  exact Nat.lt_succ_of_le (Nat.floor_mono hupper)

noncomputable def realBoxCellCenter (C : ℝ) (q n : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) / q - C

theorem realBoxCell_offset {C : ℝ} (q : ℕ) (hq : 0 < q) (y : ℝ) (hy : |y| ≤ C) :
    |y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊| ≤ (1 / 2 : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnonneg : 0 ≤ (q : ℝ) * (y + C) := by
    exact mul_nonneg hqR.le (by linarith [(abs_le.mp hy).1])
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((q : ℝ) * (y + C))
  have he : (q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊) =
      (q : ℝ) * (y + C) - (⌊(q : ℝ) * (y + C)⌋₊ + (1 / 2 : ℝ)) := by
    unfold realBoxCellCenter
    field_simp
    ring
  apply (le_div_iff₀ hqR).mpr
  calc
    _ = |(q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊)| := by
      rw [abs_mul, abs_of_pos hqR]
      ring
    _ ≤ _ := by rw [he]; apply abs_le.mpr; constructor <;> linarith

theorem exists_dense_real_box_cell {ι α : Type} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (y : α → ι → ℝ)
    {C : ℝ} (hbound : ∀ a ∈ S, ∀ i, |y a i| ≤ C)
    (q : ℕ) (hq : 0 < q) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ realBoxCellCount C q ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℝ, (∀ i, |c i| ≤ C + (1 / 2 : ℝ) / q) ∧
        ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
  classical
  let m := realBoxCellCount C q
  have hm : 0 < m := realBoxCellCount_pos C q
  let : NeZero m := ⟨hm.ne'⟩
  let label (a : α) (i : ι) : Fin m :=
    ⟨⌊(q : ℝ) * (y a i + C)⌋₊ % m, Nat.mod_lt _ hm⟩
  obtain ⟨b, hT, hcard⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter (fun a => label a = b)
  let c : ι → ℝ := fun i => realBoxCellCenter C q (b i).val
  have hclose : ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
    intro a ha i
    have haS := (Finset.mem_filter.mp ha).1
    have he := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    change ⌊(q : ℝ) * (y a i + C)⌋₊ % m = (b i).val at he
    rw [Nat.mod_eq_of_lt (realBoxCell_floor_lt q (y a i) (hbound a haS i))] at he
    dsimp only [c]
    rw [← he]
    exact realBoxCell_offset q hq (y a i) (hbound a haS i)
  refine ⟨T, Finset.filter_subset _ _, hT, ?_, c, ?_, hclose⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · obtain ⟨a, ha⟩ := hT
    intro i
    calc
      |c i| = |y a i - (y a i - c i)| := by congr 1; ring
      _ ≤ |y a i| + |y a i - c i| := abs_sub _ _
      _ ≤ C + (1 / 2 : ℝ) / q := add_le_add
        (hbound a (Finset.mem_filter.mp ha).1 i) (hclose a ha i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreimanFivefoldCardinality
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def fiveTermValue (x : Fin 5 → G) : G := x 0 + x 1 + x 2 - x 3 - x 4

theorem fiveTermValue_eq_iff {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso 5 A B f) {x y : Fin 5 → G}
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A) :
    fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) ↔ fiveTermValue x = fiveTermValue y := by
  let s : Multiset G := x 0 ::ₘ x 1 ::ₘ x 2 ::ₘ y 3 ::ₘ y 4 ::ₘ 0
  let t : Multiset G := y 0 ::ₘ y 1 ::ₘ y 2 ::ₘ x 3 ::ₘ x 4 ::ₘ 0
  have hsA : ∀ ⦃a⦄, a ∈ s → a ∈ A := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hx 0, hx 1, hx 2, hy 3, hy 4]
  have htA : ∀ ⦃a⦄, a ∈ t → a ∈ A := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hy 0, hy 1, hy 2, hx 3, hx 4]
  have hrel := hf.map_sum_eq_map_sum hsA htA (by simp [s]) (by simp [t])
  simp only [fiveTermValue, Function.comp_apply, sub_sub, sub_eq_sub_iff_add_eq_add, add_assoc]
  simpa [s, t, add_assoc] using hrel

theorem card_fiveTermValues_le [DecidableEq G] [DecidableEq H] [Fintype H]
    (A : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) :
    ((Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue).card ≤ Fintype.card H := by
  classical
  let U := Fintype.piFinset fun _ : Fin 5 => A
  have hrel : ∀ x ∈ U, ∀ y ∈ U,
      fiveTermValue x = fiveTermValue y ↔
        fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) := by
    intro x hx y hy
    exact (fiveTermValue_eq_iff hf (Fintype.mem_piFinset.mp hx)
      (Fintype.mem_piFinset.mp hy)).symm
  have hcard := card_image_eq_of_same_fibers U fiveTermValue (fun x => fiveTermValue (f ∘ x)) hrel
  change (U.image fiveTermValue).card ≤ _
  rw [hcard]
  exact Finset.card_le_univ _

theorem sub_subset_fiveTermValues [DecidableEq G] (A P : Finset G)
    (hP : P ⊆ 2 • A - 2 • A) :
    A - P ⊆ (Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue := by
  classical
  intro z hz
  obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨q, hq, hval⟩ := mem_two_nsmul_sub_two_nsmul_iff.mp (hP hp)
  let x : Fin 5 → G := ![a, q.neg₁, q.neg₂, q.pos₁, q.pos₂]
  have hx : x ∈ Fintype.piFinset (fun _ : Fin 5 => A) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hq.2.2.1
    · exact hq.2.2.2
    · exact hq.1
    · exact hq.2.1
  refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
  rw [← hval]
  change a + q.neg₁ + q.neg₂ - q.pos₁ - q.pos₂ = a - (q.pos₁ + q.pos₂ - q.neg₁ - q.neg₂)
  abel

theorem card_sub_le_of_fourfold_subset [DecidableEq G] [DecidableEq H] [Fintype H]
    (A P : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) (hP : P ⊆ 2 • A - 2 • A) :
    (A - P).card ≤ Fintype.card H :=
  (Finset.card_le_card (sub_subset_fiveTermValues A P hP)).trans (card_fiveTermValues_le A f hf)

end Erdos3.FreimanModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousScaledSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem homogeneous_aeval_scaled {I J R : Type*} [CommRing R]
    (P : MvPolynomial I R) {h : ℕ} (hP : P.IsHomogeneous h)
    (w : I → R) (Q : MvPolynomial J R) :
    aeval (fun i => C (w i) * Q) P = C (eval w P) * Q ^ h := by
  have hm (a : I →₀ ℕ) (ha : a ∈ P.support) :
      aeval (fun i => C (w i) * Q) (monomial a (P.coeff a)) =
        C (eval w (monomial a (P.coeff a))) * Q ^ h := by
    have hd : (∑ i ∈ a.support, a i) = h := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
        hP (mem_support_iff.mp ha)
    rw [aeval_monomial, eval_monomial]
    simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, hd, map_mul, mul_assoc]
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageExtensionInverseBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem imageExtension_norm_le_one (φ : A →+ B) (Q : Finset A) (f : A → ℂ)
    (hφ : Set.InjOn φ (Q : Set A)) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (y : B) :
    ‖imageExtension φ Q f y‖ ≤ 1 := by
  classical
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply hφ f hx]
    exact hf x hx
  · rw [imageExtension_eq_zero f (by
      rintro ⟨x, hx, hxy⟩
      exact hy (Finset.mem_image.mpr ⟨x, hx, hxy⟩))]
    simp

theorem sum_imageExtension_mul (φ : A →+ B) (Q : Finset A) (f : A → ℂ) (g : B → ℂ) :
    (∑ y : B, imageExtension φ Q f y * g y) = ∑ x ∈ Q, f x * g (φ x) := by
  classical
  simp only [imageExtension, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem expect_imageExtension_mul (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (f : A → ℂ) (g : B → ℂ) :
    (𝔼 y : B, imageExtension φ Q f y * g y) =
      ((Q.card : ℂ) / Fintype.card B) * (𝔼 x ∈ Q, f x * g (φ x)) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, sum_imageExtension_mul, Finset.expect_eq_sum_div_card]
  have hq : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.card_pos.ne'
  field_simp

theorem norm_expect_imageExtension_mul_le (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (hφ : Set.InjOn φ (Q : Set A)) (f : A → ℂ) (g : B → ℂ) :
    ‖𝔼 y : B, imageExtension φ Q f y * g y‖ ≤ ‖𝔼 x ∈ Q, f x * g (φ x)‖ := by
  classical
  rw [expect_imageExtension_mul φ Q hQ, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hc : Q.card ≤ Fintype.card B := by
    have h := (Q.image φ).card_le_univ
    rwa [Finset.card_image_of_injOn hφ] at h
  have hratio : (Q.card : ℝ) / Fintype.card B ≤ 1 :=
    (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card B)).mpr (by exact_mod_cast hc)
  exact mul_le_of_le_one_left (norm_nonneg _) hratio

theorem exp_le_gowers_imageExtension (j : ℕ) (φ : A →+ B) (Q : Finset A)
    (hφ : ReflectsPairSums φ (Q : Set A)) (f : A → ℂ) {p q : ℝ}
    (hQ : Real.exp (-q) ≤ (Q.card : ℝ) / Fintype.card B)
    (hf : Real.exp (-p) ≤ finiteSupportGowersNorm (j + 1) Q f) :
    Real.exp (-(p + q)) ≤ gowersNorm (j + 1) (imageExtension φ Q f) := by
  classical
  have hm := norm_expect_le_gowersNorm j (restrictTo (Q.image φ) (fun _ => (1 : ℂ)))
  rw [norm_expect_restrict_one, Finset.card_image_of_injOn hφ.injOn] at hm
  have hd := hQ.trans hm
  have hdpos := lt_of_lt_of_le (Real.exp_pos (-q)) hd
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm, restrictTo_imageExtension] at hf
  have hprod := (le_div_iff₀ hdpos).mp hf
  calc
    _ = Real.exp (-p) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-p) * gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ))) :=
      mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)
    _ ≤ _ := hprod

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeWeight (w : I → ℕ) : FreeMagma I → ℕ
  | .of i => w i
  | .mul a b => lieTreeWeight w a + lieTreeWeight w b

theorem lieTree_length_le_weight (w : I → ℕ) (hw : ∀ i, 0 < w i) (a : FreeMagma I) :
    a.length ≤ lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => exact hw i
  | mul a b ha hb => exact Nat.add_le_add ha hb

def weightedLieTreeGenerators (v : I → L) (w : I → ℕ) (d r : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, lieTreeWeight w a = d ∧ r ≤ a.length ∧ lieTreeEval v a = x}

def weightedLieTreeSpan (v : I → L) (w : I → ℕ) (d r : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieTreeGenerators v w d r)

theorem weightedLieTreeSpan_antitone (v : I → L) (w : I → ℕ) (d : ℕ) :
    Antitone (weightedLieTreeSpan v w d) := by
  intro r t hrt
  apply Submodule.span_mono
  rintro x ⟨a, ha, ht, hx⟩
  exact ⟨a, ha, hrt.trans ht, hx⟩

theorem weightedLieTreeSpan_lie_mem (v : I → L) (w : I → ℕ) {d e r t : ℕ} {x y : L}
    (hx : x ∈ weightedLieTreeSpan v w d r) (hy : y ∈ weightedLieTreeSpan v w e t) :
    ⁅x, y⁆ ∈ weightedLieTreeSpan v w (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hi, rfl⟩ := hx
    obtain ⟨b, hb, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, congrArg₂ (· + ·) ha hb, Nat.add_le_add hi hj, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem span_weighted_leaves_le (v : I → L) (w : I → ℕ) (d : ℕ) :
    Submodule.span ℚ (v '' {i | w i = d}) ≤ weightedLieTreeSpan v w d 1 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  exact Submodule.subset_span ⟨.of i, hi, le_rfl, rfl⟩

theorem FilteredLieTree.eval_mem_weighted_span {s : ℕ} {F : NilpotentLieFiltration L s}
    (v : I → L) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d}))
    {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ weightedLieTreeSpan v w d r := by
  induction a with
  | leaf hd x hx => exact span_weighted_leaves_le v w _ (hspan _ hd hx)
  | bracket a b ha hb => exact weightedLieTreeSpan_lie_mem v w ha hb

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem lieTreeEval_mem_rankLayer (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.rankLayer (lieTreeWeight w a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact F.tree_eval_mem_rankLayer (.leaf (hw i) (v i) (hv i)) le_rfl
  | mul a b ha hb => exact F.rankLayer_lie_mem ha hb

theorem rankLayer_eq_weighted_tree_span (v : I → L) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i))
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d})) (d r : ℕ) :
    F.rankLayer d r = F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro x ⟨k, hrk, a, rfl⟩
    have h := weightedLieTreeSpan_antitone v w d hrk (a.eval_mem_weighted_span v w hspan)
    exact (show weightedLieTreeSpan v w d r ≤ F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r from
      le_sup_right) h
  · apply sup_le (F.layer_succ_le_rankLayer d r)
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, hr, rfl⟩
    have h := F.lieTreeEval_mem_rankLayer v w hw hv a
    rw [ha] at h
    exact F.rankLayer_rank_antitone d hr h

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

variable (I : Type*) [Fintype I]

noncomputable def finiteLieTrees : ℕ → Finset (FreeMagma I)
  | 0 => ∅
  | n + 1 => by
    classical
    exact (Finset.univ.image FreeMagma.of) ∪
      (((finiteLieTrees n).product (finiteLieTrees n)).image (fun z => z.1 * z.2))

theorem mem_finiteLieTrees_of_length_le (a : FreeMagma I) {n : ℕ} (hn : a.length ≤ n) :
    a ∈ finiteLieTrees I n := by
  classical
  induction a using FreeMagma.rec generalizing n with
  | of i =>
    cases n with
    | zero => simp only [FreeMagma.length] at hn; omega
    | succ n =>
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  | mul a b ha hb =>
    have hapos := a.length_pos
    have hbpos := b.length_pos
    change a.length + b.length ≤ n at hn
    cases n with
    | zero => omega
    | succ n =>
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_product.mpr ⟨ha (n := n) (by omega), hb (n := n) (by omega)⟩, rfl⟩

theorem finiteLieTrees_card_le (n : ℕ) :
    (finiteLieTrees I n).card ≤ (Fintype.card I + 2) ^ (3 ^ n) := by
  classical
  induction n with
  | zero => simp only [finiteLieTrees, Finset.card_empty, Nat.zero_le]
  | succ n ih =>
    let B := (Fintype.card I + 2) ^ (3 ^ n)
    have hB : Fintype.card I + 2 ≤ B := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (show 0 < Fintype.card I + 2 by omega)
        (show 1 ≤ 3 ^ n from pow_pos (show 0 < (3 : ℕ) by norm_num) n)
    have hm : Fintype.card I ≤ B ^ 2 := by
      have h := Nat.le_mul_of_pos_right B (show 0 < B by omega)
      nlinarith
    have hrec : (finiteLieTrees I (n + 1)).card ≤
        Fintype.card I + (finiteLieTrees I n).card ^ 2 := by
      apply (Finset.card_union_le _ _).trans
      have h1 := Finset.card_image_le (s := (Finset.univ : Finset I)) (f := FreeMagma.of)
      have h2 : (((finiteLieTrees I n).product (finiteLieTrees I n)).image
          (fun z => z.1 * z.2)).card ≤ (finiteLieTrees I n).card * (finiteLieTrees I n).card := by
        exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
      simp only [Finset.card_univ] at h1
      simpa only [pow_two] using Nat.add_le_add h1 h2
    calc
      _ ≤ Fintype.card I + B ^ 2 := hrec.trans (Nat.add_le_add_left (Nat.pow_le_pow_left ih 2) _)
      _ ≤ B ^ 2 + B ^ 2 := Nat.add_le_add_right hm _
      _ = 2 * B ^ 2 := by omega
      _ ≤ B * B ^ 2 := Nat.mul_le_mul_right (B ^ 2) (show 2 ≤ B by omega)
      _ = B ^ 3 := by ring
      _ = _ := by dsimp [B]; rw [show 3 ^ (n + 1) = 3 ^ n * 3 from pow_succ 3 n, pow_mul]

variable {I} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteWeightedLieValues (v : I → L) (w : I → ℕ) (d r : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I d).filter (fun a => lieTreeWeight w a = d ∧ r ≤ a.length)).image
    (lieTreeEval v)

theorem weightedLieTreeSpan_eq_finite_span (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (d r : ℕ) : weightedLieTreeSpan v w d r =
      Submodule.span ℚ (finiteWeightedLieValues v w d r : Set L) := by
  classical
  unfold weightedLieTreeSpan
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, hr, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨?_, ha, hr⟩, rfl⟩
    apply mem_finiteLieTrees_of_length_le
    exact (lieTree_length_le_weight w hw a).trans_eq ha
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hd, hr⟩ := Finset.mem_filter.mp ha
    exact ⟨a, hd, hr, rfl⟩

omit [LieAlgebra ℚ L] in
theorem finiteWeightedLieValues_card_le (v : I → L) (w : I → ℕ) (d r : ℕ) :
    (finiteWeightedLieValues v w d r).card ≤ (Fintype.card I + 2) ^ (3 ^ d) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (finiteLieTrees_card_le I d)

end Erdos3

end

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeEval_relabel (v : J → L) (f : I → J) (a : FreeMagma I) :
    lieTreeEval v (FreeMagma.map f a) = lieTreeEval (v ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v (FreeMagma.map f a), lieTreeEval v (FreeMagma.map f b)⁆ = _
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeWeight_relabel (w : J → ℕ) (f : I → J) (a : FreeMagma I) :
    lieTreeWeight w (FreeMagma.map f a) = lieTreeWeight (w ∘ f) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight w (FreeMagma.map f a) + lieTreeWeight w (FreeMagma.map f b) = _
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeLength_relabel (f : I → J) (a : FreeMagma I) :
    (FreeMagma.map f a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map f a).length + (FreeMagma.map f b).length = _
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeSupport_relabel (f : I → J) (a : FreeMagma I) :
    lieTreeSupport (FreeMagma.map f a) = f '' lieTreeSupport a := by
  induction a using FreeMagma.rec with
  | of i => simp only [FreeMagma.map_of, lieTreeSupport, Set.image_singleton]
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map f a) ∪ lieTreeSupport (FreeMagma.map f b) = _
    rw [ha, hb, ← Set.image_union]
    rfl

abbrev LieTreeOccurrences : FreeMagma I → Type
  | .of _ => Unit
  | .mul a b => LieTreeOccurrences a ⊕ LieTreeOccurrences b

instance lieTreeOccurrencesFintype (a : FreeMagma I) : Fintype (LieTreeOccurrences a) := by
  induction a using FreeMagma.rec with
  | of i => exact inferInstanceAs (Fintype Unit)
  | mul a b ha hb =>
    let := ha
    let := hb
    exact inferInstanceAs (Fintype (LieTreeOccurrences a ⊕ LieTreeOccurrences b))

def lieTreeOccurrenceLabel : (a : FreeMagma I) → LieTreeOccurrences a → I
  | .of i => fun _ => i
  | .mul a b => Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b)

def lieTreeOccurrenceTree : (a : FreeMagma I) → FreeMagma (LieTreeOccurrences a)
  | .of _ => .of ()
  | .mul a b => .mul (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a))
    (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))

theorem lieTreeOccurrenceTree_eval (v : I → L) (a : FreeMagma I) :
    lieTreeEval (v ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeEval v a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆ = _
    rw [lieTreeEval_relabel, lieTreeEval_relabel]
    exact congrArg₂ (fun x y : L => ⁅x, y⁆) ha hb

theorem lieTreeOccurrenceTree_weight (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight (w ∘ lieTreeOccurrenceLabel a) (lieTreeOccurrenceTree a) = lieTreeWeight w a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change lieTreeWeight _ (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) +
      lieTreeWeight _ (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeWeight_relabel, lieTreeWeight_relabel]
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeOccurrenceTree_length (a : FreeMagma I) :
    (lieTreeOccurrenceTree a).length = a.length := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)).length +
      (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)).length = _
    rw [lieTreeLength_relabel, lieTreeLength_relabel]
    exact congrArg₂ (· + ·) ha hb

theorem lieTreeOccurrenceTree_support (a : FreeMagma I) :
    lieTreeSupport (lieTreeOccurrenceTree a) = Set.univ := by
  induction a using FreeMagma.rec with
  | of i =>
    ext j
    cases j
    exact iff_of_true rfl trivial
  | mul a b ha hb =>
    change lieTreeSupport (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)) ∪
      lieTreeSupport (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b)) = _
    rw [lieTreeSupport_relabel, lieTreeSupport_relabel, ha, hb]
    ext j
    constructor
    · intro _; trivial
    · intro _
      cases j with
      | inl j => exact Or.inl ⟨j, Set.mem_univ _, rfl⟩
      | inr j => exact Or.inr ⟨j, Set.mem_univ _, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def bracketMultilinear
    (f : MultilinearMap R (fun _ : I => L) L)
    (g : MultilinearMap R (fun _ : J => L) L) :
    MultilinearMap R (fun _ : I ⊕ J => L) L :=
  MultilinearMap.uncurrySum
    { toFun := fun m =>
        ({ toFun := fun y => ⁅f m, y⁆
           map_add' := fun y z => lie_add (f m) y z
           map_smul' := fun c y => lie_smul c (f m) y } : L →ₗ[R] L).compMultilinearMap g
      map_update_add' m i x y := by
        ext v
        change ⁅f (Function.update m i (x + y)), g v⁆ =
          ⁅f (Function.update m i x), g v⁆ + ⁅f (Function.update m i y), g v⁆
        rw [f.map_update_add, add_lie]
      map_update_smul' m i c x := by
        ext v
        change ⁅f (Function.update m i (c • x)), g v⁆ = c • ⁅f (Function.update m i x), g v⁆
        rw [f.map_update_smul, smul_lie] }

noncomputable def lieTreeOccurrenceMultilinear :
    (a : FreeMagma I) → MultilinearMap R (fun _ : LieTreeOccurrences a => L) L
  | .of _ => MultilinearMap.ofSubsingleton R L L () LinearMap.id
  | .mul a b => bracketMultilinear (lieTreeOccurrenceMultilinear a) (lieTreeOccurrenceMultilinear b)

theorem lieTreeOccurrenceMultilinear_apply (a : FreeMagma I) :
    ∀ v : LieTreeOccurrences a → L,
      lieTreeOccurrenceMultilinear (R := R) a v = lieTreeEval v (lieTreeOccurrenceTree a) := by
  induction a using FreeMagma.rec with
  | of i => intro v; rfl
  | mul a b ha hb =>
    intro v
    change ⁅lieTreeOccurrenceMultilinear a (v ∘ Sum.inl),
      lieTreeOccurrenceMultilinear b (v ∘ Sum.inr)⁆ = _
    rw [ha, hb]
    change _ = ⁅lieTreeEval v (FreeMagma.map Sum.inl (lieTreeOccurrenceTree a)),
      lieTreeEval v (FreeMagma.map Sum.inr (lieTreeOccurrenceTree b))⁆
    rw [lieTreeEval_relabel, lieTreeEval_relabel]

theorem lieTreeOccurrenceMultilinear_original (v : I → L) (a : FreeMagma I) :
    lieTreeOccurrenceMultilinear (R := R) a (v ∘ lieTreeOccurrenceLabel a) = lieTreeEval v a :=
  (lieTreeOccurrenceMultilinear_apply a _).trans (lieTreeOccurrenceTree_eval v a)

theorem exists_linear_lieTree_expansion {E : Type*} [AddCommGroup E] [Module R E]
    (η : L →ₗ[R] E) (C D : I → Submodule R L) (hDC : ∀ i, D i ≤ C i)
    (a : FreeMagma I) (x : I → L) (hx : ∀ i, x i ∈ C i)
    (hvanish : ∀ v : LieTreeOccurrences a → L,
      (∀ i, v i ∈ C (lieTreeOccurrenceLabel a i)) → ∀ i j, i ≠ j →
        v i ∈ D (lieTreeOccurrenceLabel a i) → v j ∈ D (lieTreeOccurrenceLabel a j) →
        η (lieTreeEval v (lieTreeOccurrenceTree a)) = 0) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      η (lieTreeEval (fun i => x i + (y i : L)) a) = η (lieTreeEval x a) + A y := by
  classical
  let f := η.compMultilinearMap (lieTreeOccurrenceMultilinear (R := R) a)
  obtain ⟨A, hA⟩ := exists_linear_expansion_of_two_vanish f
    (C ∘ lieTreeOccurrenceLabel a) (D ∘ lieTreeOccurrenceLabel a)
    (fun i => hDC (lieTreeOccurrenceLabel a i))
    (fun v hv i j hij hi hj => by
      change η (lieTreeOccurrenceMultilinear a v) = 0
      rw [lieTreeOccurrenceMultilinear_apply]
      exact hvanish v hv i j hij hi hj)
    (x ∘ lieTreeOccurrenceLabel a) (fun i => hx (lieTreeOccurrenceLabel a i))
  let diagonal : (∀ i, D i) →ₗ[R] (∀ j : LieTreeOccurrences a, D (lieTreeOccurrenceLabel a j)) :=
    LinearMap.pi (fun j => LinearMap.proj (lieTreeOccurrenceLabel a j))
  refine ⟨A.comp diagonal, ?_⟩
  intro y
  have h := hA (diagonal y)
  change η (lieTreeOccurrenceMultilinear a ((fun i => x i + (y i : L)) ∘
      lieTreeOccurrenceLabel a)) =
    η (lieTreeOccurrenceMultilinear a (x ∘ lieTreeOccurrenceLabel a)) + A (diagonal y) at h
  simpa only [lieTreeOccurrenceMultilinear_original, LinearMap.comp_apply] using h

end Erdos3

end

section

namespace Erdos3

variable {I : Type*}

def lieTreeMarkedCount (marked : I → Bool) (a : FreeMagma I) : ℕ :=
  lieTreeWeight (fun i => if marked i then 1 else 0) a

@[simp] theorem lieTreeMarkedCount_leaf (marked : I → Bool) (i : I) :
    lieTreeMarkedCount marked (.of i) = if marked i then 1 else 0 := rfl

@[simp] theorem lieTreeMarkedCount_mul (marked : I → Bool) (a b : FreeMagma I) :
    lieTreeMarkedCount marked (a * b) =
      lieTreeMarkedCount marked a + lieTreeMarkedCount marked b := rfl

theorem lieTreeMarkedCount_le_length (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a ≤ a.length := by
  induction a using FreeMagma.rec with
  | of i => simp only [lieTreeMarkedCount_leaf, FreeMagma.length]; split <;> omega
  | mul a b ha hb => exact Nat.add_le_add ha hb

theorem lieTreeWeight_eq_sum_occurrences (w : I → ℕ) (a : FreeMagma I) :
    lieTreeWeight w a = ∑ i : LieTreeOccurrences a, w (lieTreeOccurrenceLabel a i) := by
  induction a using FreeMagma.rec with
  | of i => simp [lieTreeWeight, LieTreeOccurrences, lieTreeOccurrenceLabel]
  | mul a b ha hb =>
    change lieTreeWeight w a + lieTreeWeight w b =
      ∑ i : LieTreeOccurrences a ⊕ LieTreeOccurrences b,
        w (Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b) i)
    rw [Fintype.sum_sum_type, ha, hb]
    rfl

theorem lieTreeMarkedCount_eq_card (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMarkedCount marked a =
      (Finset.univ.filter (fun i : LieTreeOccurrences a => marked (lieTreeOccurrenceLabel a i))).card := by
  classical
  rw [lieTreeMarkedCount, lieTreeWeight_eq_sum_occurrences]
  simp only [Finset.card_filter]

theorem exists_two_marked_occurrences (marked : I → Bool) (a : FreeMagma I)
    (ha : 2 ≤ lieTreeMarkedCount marked a) :
    ∃ i j : LieTreeOccurrences a, i ≠ j ∧
      marked (lieTreeOccurrenceLabel a i) = true ∧
      marked (lieTreeOccurrenceLabel a j) = true := by
  classical
  rw [lieTreeMarkedCount_eq_card] at ha
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < _ from ha)
  exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

variable {I σ : Type*}

noncomputable def lieTreeMultidegree (g : I → σ →₀ ℕ) : FreeMagma I → σ →₀ ℕ
  | .of i => g i
  | .mul a b => lieTreeMultidegree g a + lieTreeMultidegree g b

@[simp] theorem lieTreeMultidegree_leaf (g : I → σ →₀ ℕ) (i : I) :
    lieTreeMultidegree g (.of i) = g i := rfl

@[simp] theorem lieTreeMultidegree_mul (g : I → σ →₀ ℕ) (a b : FreeMagma I) :
    lieTreeMultidegree g (a * b) = lieTreeMultidegree g a + lieTreeMultidegree g b := rfl

theorem lieTreeMultidegree_apply (g : I → σ →₀ ℕ) (a : FreeMagma I) (j : σ) :
    lieTreeMultidegree g a j = lieTreeWeight (fun i => g i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

noncomputable def markedGeneratorGrade (w : I → ℕ) (marked : I → Bool) (i : I) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (w i) + Finsupp.single 1 (if marked i then 1 else 0) + Finsupp.single 2 1

theorem markedTreeGrade_weight (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 0 = lieTreeWeight w a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade]

theorem markedTreeGrade_count (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 1 = lieTreeMarkedCount marked a := by
  rw [lieTreeMultidegree_apply]
  simp [markedGeneratorGrade, lieTreeMarkedCount]

theorem markedTreeGrade_length (w : I → ℕ) (marked : I → Bool) (a : FreeMagma I) :
    lieTreeMultidegree (markedGeneratorGrade w marked) a 2 = a.length := by
  induction a using FreeMagma.rec with
  | of i => simp [markedGeneratorGrade, FreeMagma.length]
  | mul a b ha hb => exact congrArg₂ (· + ·) ha hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RelativeSpectrumDimension
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable def realFinsetIndicator {G : Type*} (A : Finset G) (x : G) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

namespace RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in

theorem sum_realFinsetIndicator_mul_eq_const_mul_card
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) :
    ∑ x : G, realFinsetIndicator X x * w x = c * X.card := by
  classical
  calc
    ∑ x : G, realFinsetIndicator X x * w x = ∑ x ∈ X, c := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = c * X.card := by simp [mul_comm]

theorem sum_realFinsetIndicator_mul_character_eq_const_mul
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (psi : AddChar G ℂ) :
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
      (c : ℂ) * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (c : ℂ) * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = (c : ℂ) * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem mem_relativeLargeSpectrum_of_eq_const_iff
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (hc : 0 < c)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum w (realFinsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw]
  rw [sum_realFinsetIndicator_mul_character_eq_const_mul hXB hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  constructor
  · intro h
    have hh : c * (eta * (X.card : ℝ)) ≤
        c * ‖Chang.spectrumSum X psi‖ := by
      calc
        c * (eta * (X.card : ℝ)) = eta * (c * (X.card : ℝ)) := by ring
        _ ≤ c * ‖Chang.spectrumSum X psi‖ := h
    nlinarith
  · intro h
    calc
      eta * (c * (X.card : ℝ)) = c * (eta * (X.card : ℝ)) := by ring
      _ ≤ c * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h hc.le

end RelativeSpectrumBridge
end Erdos3

end

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem card_weightedDissociated_relativeLargeSpectrum_le
    (mu f : G → ℝ) (K eta : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (heta : 0 < eta)
    (hDelta : IsWeightedDissociated mu K Delta)
    (hsub : Delta ⊆ relativeLargeSpectrum mu f eta)
    (hmass : 0 < ∑ x : G, f x * mu x) :
    (Delta.card : ℝ) ≤
      2 * (K + log ((∑ x : G, f x * mu x)⁻¹)) / eta ^ 2 := by
  let a : ℝ := ∑ x : G, f x * mu x
  have ha : 0 < a := by simpa [a] using hmass
  let spec : AddChar G ℂ → ℂ := fun psi ↦
    ∑ x : G, (f x * mu x : ℝ) * psi x
  choose u hu huspec using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spec psi)
  let c : AddChar G ℂ → ℂ := fun psi ↦ (eta : ℂ) * u psi
  let P : G → ℝ := fun x ↦ (∑ psi ∈ Delta, c psi * psi x).re
  have hc_norm (psi : AddChar G ℂ) : ‖c psi‖ ^ 2 = eta ^ 2 := by
    simp [c, hu, abs_of_pos heta]
  have hc_sq : ∑ psi ∈ Delta, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm]
    simp
    ring
  have hcomplex :
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
    calc
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
          ∑ psi ∈ Delta,
            c psi * ∑ x : G, ((f x * mu x : ℝ) : ℂ) * psi x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro psi hpsi
        apply sum_congr rfl
        intro x hx
        ring
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spec psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        dsimp [c, spec]
        rw [mul_assoc, ← huspec]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
        rw [Finset.mul_sum]
  have hmeanP :
      ∑ x : G, f x * mu x * P x =
        eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
    have hre := congrArg Complex.re hcomplex
    calc
      ∑ x : G, f x * mu x * P x =
          (∑ x : G, ((f x * mu x : ℝ) : ℂ) *
            (∑ psi ∈ Delta, c psi * psi x)).re := by
        simp [P, Complex.re_sum, Complex.mul_re]
      _ = ((eta : ℂ) *
          ∑ psi ∈ Delta, (‖spec psi‖ : ℂ)).re := hre
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by simp
  have hmean_lower :
      eta ^ 2 * a * Delta.card ≤ ∑ x : G, f x * mu x * P x := by
    rw [hmeanP]
    calc
      eta ^ 2 * a * (Delta.card : ℝ) =
          ∑ psi ∈ Delta, eta * (eta * a) := by
        simp
        ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spec psi‖ := by
        gcongr with psi hpsi
        have hs := mem_relativeLargeSpectrum.mp (hsub hpsi)
        simpa [a, spec] using hs
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
        rw [Finset.mul_sum]
  let w : G → ℝ := fun x ↦ f x * mu x / a
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (mul_nonneg (hf0 x) (hmu x)) ha.le
  have hw_sum : ∑ x : G, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    dsimp [a]
    exact div_self ha.ne'
  have hmean_w : eta ^ 2 * Delta.card ≤ ∑ x : G, w x * P x := by
    calc
      eta ^ 2 * (Delta.card : ℝ) ≤
          (∑ x : G, f x * mu x * P x) / a := by
        rw [le_div_iff₀ ha]
        calc
          eta ^ 2 * (Delta.card : ℝ) * a =
              eta ^ 2 * a * (Delta.card : ℝ) := by ring
          _ ≤ _ := hmean_lower
      _ = ∑ x : G, w x * P x := by
        dsimp [w]
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro x hx
        ring
  have hJensen :
      exp (eta ^ 2 * Delta.card) ≤
        ∑ x : G, w x * exp (P x) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (∑ x : G, w x * P x) := by
        exact Real.exp_le_exp.mpr hmean_w
      _ ≤ _ := exp_weightedAverage_le_weightedAverage_exp w hw0 hw_sum P
  have hweighted_le :
      ∑ x : G, w x * exp (P x) ≤
        a⁻¹ * ∑ x : G, mu x * exp (P x) := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x hx
    rw [div_eq_inv_mul]
    calc
      a⁻¹ * (f x * mu x) * exp (P x) ≤
          a⁻¹ * (1 * mu x) * exp (P x) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact mul_le_mul_of_nonneg_right (hf1 x) (hmu x)
      _ = a⁻¹ * (mu x * exp (P x)) := by ring
  have hRudin :
      ∑ x : G, mu x * exp (P x) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    have hr := weighted_rudin_exp_ineq mu K Delta hmu hDelta c
    simpa [P, hc_sq] using hr
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2) :=
    hJensen.trans (hweighted_le.trans
      (mul_le_mul_of_nonneg_left hRudin (inv_nonneg.mpr ha.le)))
  have hmul :
      a * exp (eta ^ 2 * Delta.card) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    calc
      a * exp (eta ^ 2 * Delta.card) ≤
          a * (a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2)) := by
        gcongr
      _ = exp (K + eta ^ 2 * Delta.card / 2) := by
        field_simp
  have hlinear :
      log a + eta ^ 2 * Delta.card ≤
        K + eta ^ 2 * Delta.card / 2 := by
    rw [← exp_log ha, ← exp_add] at hmul
    exact Real.exp_le_exp.mp hmul
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  rw [log_inv]
  nlinarith

theorem card_weightedDissociated_realFinsetIndicator_le
    (B X : Finset G) (hXB : X ⊆ B) (hX : X.Nonempty)
    (w : G → ℝ) (c R eta : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∈ B, w x = c)
    (hc : 0 < c) (hR : (c * X.card)⁻¹ ≤ R)
    (heta : 0 < eta) (Delta : Finset (AddChar G ℂ))
    (hDelta : IsWeightedDissociated w 1 Delta)
    (hsub : Delta ⊆ Chang.largeSpectrum X eta) :
    (Delta.card : ℝ) ≤ 2 * (1 + log R) / eta ^ 2 := by
  classical
  have hmass_eq :
      ∑ x : G, realFinsetIndicator X x * w x = c * X.card :=
    RelativeSpectrumBridge.sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw
  have hmass : 0 < ∑ x : G, realFinsetIndicator X x * w x := by
    rw [hmass_eq]
    have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have hsub' : Delta ⊆
      relativeLargeSpectrum w (realFinsetIndicator X) eta := by
    intro psi hpsi
    exact (RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
      hXB hw hc eta psi).2 (hsub hpsi)
  have hdim := card_weightedDissociated_relativeLargeSpectrum_le
    w (realFinsetIndicator X) 1 eta Delta hw0
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    heta hDelta hsub' hmass
  have hmassInv :
      ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ R := by
    simpa [hmass_eq] using hR
  have hlog :
      log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ log R :=
    Real.log_le_log (inv_pos.mpr hmass) hmassInv
  calc
    (Delta.card : ℝ) ≤
        2 * (1 + log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹)) /
          eta ^ 2 := by simpa using hdim
    _ ≤ 2 * (1 + log R) / eta ^ 2 := by
      gcongr

end Erdos3.RelativeChangSanders

end

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

noncomputable def balancedFunction (L : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  f x - realFinsetIndicator L x

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def localMomentExponentFactor (delta : ℝ) : ℕ :=
  momentAmplificationFactor (delta ^ 2 / 8)

noncomputable def localMomentGain (delta : ℝ) : ℝ :=
  momentAmplificationGain (delta ^ 2 / 8) / 2

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementIntegral (D Q C : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, 𝔼 x ∈ D, 𝔼 t ∈ C, f x * g (z + t) * a (x + (z + t))

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalShiftFiber
namespace OAI

section

namespace Erdos3

open _root_.Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

section LargeShifts

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {A S : Finset G} {r : ℕ}

end LargeShifts

noncomputable def setAverageTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) : ℝ :=
  (∑ a ∈ A, f (x - a)) / A.card

noncomputable def centeredTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x a : ZMod N) : ℝ :=
  f (x - a) - setAverageTranslate A f x

noncomputable def sampleDeviation
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (x : ZMod N) : ℝ :=
  ∑ i, centeredTranslate A f x (a i)

omit [NeZero N] in
lemma sum_centeredTranslate_eq_zero
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ) (x : ZMod N) :
    ∑ a ∈ A, centeredTranslate A f x a = 0 := by
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  unfold centeredTranslate setAverageTranslate
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

omit [NeZero N] in

theorem pointwise_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) (x : ZMod N) :
    ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  let g : ZMod N → ℝ := centeredTranslate A f x
  have hg : ∀ i, ∑ a ∈ A ^^ k, g (a i) = 0 := by
    intro i
    rw [Fintype.sum_piFinset_apply]
    rw [show ∑ b ∈ A, g b = 0 by
      simpa [g] using sum_centeredTranslate_eq_zero hA f x]
    simp
  have h := Erdos3.CyclicMZ.RCLike.marcinkiewicz_zygmund
    (A := A) (n := k) hm g hg
  simpa only [Real.norm_eq_abs, sampleDeviation, g] using h

theorem global_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  rw [Finset.sum_comm]
  calc
    ∑ x : ZMod N, ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
        ∑ x : ZMod N, (8 * m) ^ m * k ^ (m - 1) *
          ∑ a ∈ A ^^ k, ∑ i,
            |centeredTranslate A f x (a i)| ^ (2 * m) := by
      exact Finset.sum_le_sum fun x _ ↦ pointwise_sampleDeviation_moment hA f hm x
    _ = (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

omit [NeZero N] in

lemma abs_setAverageTranslate_le
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (_ : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x : ZMod N) :
    |setAverageTranslate A f x| ≤ M := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hsum : ∑ a ∈ A, |f (x - a)| ≤ ∑ _a ∈ A, M := by
    exact Finset.sum_le_sum fun a _ ↦ hf (x - a)
  unfold setAverageTranslate
  calc
    |(∑ a ∈ A, f (x - a)) / (A.card : ℝ)| =
        |∑ a ∈ A, f (x - a)| / (A.card : ℝ) := by
      rw [abs_div, abs_of_pos hcard]
    _ ≤ (∑ a ∈ A, |f (x - a)|) / (A.card : ℝ) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ _a ∈ A, M) / (A.card : ℝ) := by gcongr
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

lemma markov_card_good
    {ι : Type*} {S : Finset ι} {g : ι → ℝ} {c ε : ℝ}
    (hc : 0 < c) (hg : ∀ a ∈ S, 0 ≤ g a)
    (h : ∑ a ∈ S, g a ≤ ε * c * S.card) :
    (1 - ε) * S.card ≤ (S.filter fun a ↦ g a ≤ c).card := by
  classical
  have hbad := h.trans'
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun a ↦ ¬g a ≤ c) S) fun i hi _ ↦ hg i hi)
  have hcount :=
    (Finset.card_nsmul_le_sum (S.filter fun a ↦ ¬g a ≤ c) g c
      (by simp +contextual [le_of_lt])).trans hbad
  rw [nsmul_eq_mul, mul_right_comm] at hcount
  have hcount' := le_of_mul_le_mul_right hcount hc
  rw [Finset.filter_not, Finset.cast_card_sdiff (Finset.filter_subset _ _)] at hcount'
  linarith

noncomputable def goodSamples
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (k m : ℕ) (C : ℝ) :
    Finset (Fin k → ZMod N) :=
  (A ^^ k).filter fun a ↦
    (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C

lemma mem_goodSamples
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} :
    a ∈ goodSamples A f k m C ↔
      a ∈ A ^^ k ∧
        (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C := by
  simp [goodSamples]

omit [NeZero N] in
lemma sampleDeviation_sub_const_identity
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (t x : ZMod N) :
    sampleDeviation A f (a - fun _ ↦ t) x -
        sampleDeviation A f a (x + t) =
      (k : ℝ) *
        (setAverageTranslate A f (x + t) - setAverageTranslate A f x) := by
  unfold sampleDeviation centeredTranslate
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have harg (i : Fin k) : x - (a i - t) = x + t - a i := by abel
  simp_rw [harg]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

theorem goodSamples_give_almost_period
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m C)
    (hat : (a - fun _ ↦ t) ∈ goodSamples A f k m C) :
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      2 ^ (2 * m) * C := by
  have haMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 ha |>.2
  have hatMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 hat |>.2
  have hshift :
      (∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) =
        ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) := by
    exact Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ ↦ rfl
  by_cases hm : m = 0
  · subst m
    simpa using haMoment
  have hpne : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm
  calc
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) =
      ∑ x : ZMod N,
        ((k : ℝ) ^ (2 * m) *
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) := by
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod N,
        |sampleDeviation A f (a - fun _ ↦ t) x -
          sampleDeviation A f a (x + t)| ^ (2 * m) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← mul_pow]
      have hkabs : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
      rw [← hkabs, ← abs_mul, ← sampleDeviation_sub_const_identity]
    _ ≤ ∑ x : ZMod N, 2 ^ (2 * m - 1) *
        (|sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m) +
          |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc
        |sampleDeviation A f (a - fun _ ↦ t) x -
            sampleDeviation A f a (x + t)| ^ (2 * m) ≤
          (|sampleDeviation A f (a - fun _ ↦ t) x| +
            |sampleDeviation A f a (x + t)|) ^ (2 * m) := by
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub _ _)
            _
        _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) _
    _ = 2 ^ (2 * m - 1) *
        ((∑ x : ZMod N,
            |sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m)) +
          ∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 ^ (2 * m - 1) * (C + C) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hatMoment (by rwa [hshift])
      · positivity
    _ = 2 ^ (2 * m) * C := by
      conv_rhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_add, pow_one]
      ring

end CyclicCrootSisask
end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

theorem exists_local_shift_fiber {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) {k : ℕ}
    (L : Finset (Fin k → G)) (hL : L.Nonempty) (hLA : L ⊆ A ^^ k) :
    ∃ (x : Fin k → G) (T : Finset G), T ⊆ S ∧ T.Nonempty ∧
      ((L.card : ℝ) * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card ∧
      ∀ t ∈ T, (x - fun _ => t) ∈ L := by
  classical
  let P := L ×ˢ S
  let X := (A + S) ^^ k
  let φ : ((Fin k → G) × G) → (Fin k → G) := fun z => z.1 + fun _ => z.2
  have hX : X.Nonempty := (hA.add hS).piFinset_const
  have hmap : ∀ z ∈ P, φ z ∈ X := by
    rintro ⟨a, t⟩ hat
    obtain ⟨ha, ht⟩ := Finset.mem_product.mp hat
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.add_mem_add (Fintype.mem_piFinset.mp (hLA ha) i) ht
  have hXcard : (X.card : ℝ) = ((A + S).card : ℝ) ^ k := by
    simp [X]
  have hXne : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_ne_zero
  have hpigeon : ∃ x ∈ X, ((L.card : ℝ) * S.card) / X.card ≤
      ∑ z ∈ P with φ z = x, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap hX
    simp only [nsmul_eq_mul, sum_const, P, card_product, Nat.cast_mul]
    rw [mul_comm (X.card : ℝ), div_mul_cancel₀ _ hXne, mul_one]
  obtain ⟨x, _hx, hx⟩ := hpigeon
  let Q := P.filter (fun z => φ z = x)
  let T := Q.image Prod.snd
  have hQcard : (Q.card : ℝ) = ∑ z ∈ P with φ z = x, (1 : ℝ) := by simp [Q]
  have hinj : _root_.Set.InjOn Prod.snd (Q : _root_.Set ((Fin k → G) × G)) := by
    rintro ⟨a, s⟩ has ⟨b, t⟩ hbt hst
    have hab : a + (fun _ => s) = b + fun _ => t :=
      (Finset.mem_filter.mp has).2.trans (Finset.mem_filter.mp hbt).2.symm
    cases hst
    apply Prod.ext
    · funext i
      exact add_right_cancel (congrFun hab i)
    · rfl
  have hTcard : T.card = Q.card := Finset.card_image_iff.mpr hinj
  have hQpos : (0 : ℝ) < Q.card := by
    have hratio : 0 < ((L.card : ℝ) * S.card) / X.card := by
      apply div_pos
      · exact mul_pos (by exact_mod_cast hL.card_pos) (by exact_mod_cast hS.card_pos)
      · exact_mod_cast hX.card_pos
    exact hratio.trans_le (by simpa only [← hQcard] using hx)
  have hT : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    exact_mod_cast hQpos
  refine ⟨x, T, ?_, hT, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
  · rw [← hXcard, hTcard, hQcard]
    exact hx
  · intro t ht
    obtain ⟨⟨a, s⟩, has, hst⟩ := Finset.mem_image.mp ht
    have hax := (Finset.mem_filter.mp has).2
    have ha := (Finset.mem_product.mp (Finset.mem_filter.mp has).1).1
    have heq : (x - fun _ => t) = a := by
      funext i
      have h := congrFun hax i
      change a i + s = x i at h
      change s = t at hst
      simp only [Pi.sub_apply]
      rw [← h, hst, add_sub_cancel_right]
    rw [heq]
    exact ha

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IntervalBoxDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SymmetricIntegerInterval (N : ℕ) :=
  ↥(Finset.Icc (-(N : ℤ)) (N : ℤ))

instance symmetricIntegerInterval_inhabited (N : ℕ) : Inhabited (SymmetricIntegerInterval N) :=
  ⟨⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩

theorem symmetricIntegerInterval_card (N : ℕ) :
    Fintype.card (SymmetricIntegerInterval N) = 2*N+1 := by
  simpa only [Fintype.card_coe] using symmetricInterval_card N

theorem symmetricIntegerInterval_abs_le (N : ℕ) (x : SymmetricIntegerInterval N) :
    |(x : ℤ)| ≤ (N : ℤ) :=
  abs_le.mpr (Finset.mem_Icc.mp x.property)

theorem dense_product_signed_box (e : ℕ) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  apply dense_product_approximation_density e (X := fun i => SymmetricIntegerInterval (N i))
    (fun _ x => (x : ℤ))
    (fun _ => Subtype.val_injective) N hη hη1 hN
  · intro i
    rw [symmetricIntegerInterval_card]
    omega
  · exact fun i => symmetricIntegerInterval_abs_le (N i)
  · exact hε
  · exact hsmall
  · exact hdensity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def intervalDifference (N : ℕ) (y x : Fin N) : SymmetricIntegerInterval N :=
  ⟨(x.val : ℤ)-y.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem intervalDifference_injective (N : ℕ) (y : Fin N) :
    Function.Injective (intervalDifference N y) := by
  intro x x' h
  have he := congrArg Subtype.val h
  dsimp [intervalDifference] at he
  apply Fin.ext
  omega

def intervalBoxDifference {ι : Type*} (N : ι → ℕ)
    (y x : ∀ i, Fin (N i)) : ∀ i, SymmetricIntegerInterval (N i) :=
  fun i => intervalDifference (N i) (y i) (x i)

theorem intervalBoxDifference_injective {ι : Type*} (N : ι → ℕ)
    (y : ∀ i, Fin (N i)) : Function.Injective (intervalBoxDifference N y) := by
  intro x x' h
  funext i
  exact intervalDifference_injective (N i) (y i) (congrFun h i)

theorem intervalBox_card_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) :
    (1 : ℝ)/3^Fintype.card ι ≤
      (Fintype.card (∀ i, Fin (N i)) : ℝ) /
        Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
  have hden : (0 : ℝ) < Fintype.card (∀ i, SymmetricIntegerInterval (N i)) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_div_iff₀ (by positivity) hden).mpr
  simp only [Fintype.card_pi, Fintype.card_fin, symmetricIntegerInterval_card,
    Nat.cast_prod, one_mul]
  calc
    (∏ i, ((2*N i+1 : ℕ) : ℝ)) ≤ ∏ i, (N i : ℝ)*3 := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        have hi : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
        push_cast
        linarith
    _ = (∏ i, (N i : ℝ))*3^Fintype.card ι := by
      rw [Finset.prod_mul_distrib]
      simp

theorem nearIntegerDensity_interval_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i)
    (a : (∀ i, SymmetricIntegerInterval (N i)) → ℝ) (ε : ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hdensity : η ≤ 𝔼 y : ∀ i, Fin (N i),
      nearIntegerDensity (fun x => a (intervalBoxDifference N y x)) ε) :
    η/3^Fintype.card ι ≤ nearIntegerDensity a ε := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hd := nearIntegerDensity_fiber_injections a ε (intervalBoxDifference N)
    (intervalBoxDifference_injective N) hdensity
  have hr := mul_le_mul_of_nonneg_left (intervalBox_card_ratio N hN) hη
  apply (le_trans ?_ hd)
  simpa only [← mul_div_assoc, mul_one] using hr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductDifferenceBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem product_difference_bias_approximation (e : ℕ) (N : Fin e → ℕ) (M : ℕ)
    (hM : 0 < M) {a θ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e (a/(2*3^e)) ≤ N i)
    (hMlarge : denseProductDensityBudget e (a/(2*3^e)) ≤ (M : ℝ)*a)
    (hbias : a ≤ 𝔼 y : (∀ i : Fin e, Fin (N i)), 𝔼 x : (∀ i : Fin e, Fin (N i)),
      ‖geometricCharacterMean M
        ((θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ))) : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e (a/(2*3^e)) ∧
      NearInteger
        (denseProductDensityBudget e (a/(2*3^e))/((M : ℝ)*a*∏ i, (N i : ℝ)))
        ((q : ℝ)*θ) := by
  let η := a/(2*3^e)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have hp : (1 : ℝ) ≤ 3^e := one_le_pow₀ (by norm_num)
    apply (div_le_one (by positivity : (0 : ℝ) < 2*3^e)).mpr
    linarith
  have hNp : ∀ i, 0 < N i := by
    intro i
    have h := (denseProductDensityBudget_pos e hη).trans_le (hN i)
    exact_mod_cast h
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hNp i⟩⟩
  let f := fun (y x : ∀ i, Fin (N i)) =>
    θ * (∏ i : Fin e, (((x i).val : ℝ)-((y i).val : ℝ)))
  have hsplit : (𝔼 p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)),
      ‖geometricCharacterMean M (f p.1 p.2 : CircleFourier.Circle)‖) =
      𝔼 y, 𝔼 x, ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖ := by
    simpa using (Finset.expect_product' Finset.univ Finset.univ
      (fun y x => ‖geometricCharacterMean M (f y x : CircleFourier.Circle)‖))
  have hpair := nearIntegerDensity_of_geometric_mean
    (fun p : (∀ i, Fin (N i)) × (∀ i, Fin (N i)) => f p.1 p.2) hM ha
    (hbias.trans_eq hsplit.symm)
  rw [nearIntegerDensity_product f] at hpair
  have hdiff : a/2/3^e ≤ nearIntegerDensity
      (fun x : ∀ i, SymmetricIntegerInterval (N i) => θ * ∏ i, ((x i : ℤ) : ℝ))
      (1/((M : ℝ)*a)) := by
    simpa only [Fintype.card_fin] using nearIntegerDensity_interval_differences N hNp
      (fun x => θ * ∏ i, ((x i : ℤ) : ℝ)) (1/((M : ℝ)*a)) (by positivity : 0 ≤ a/2)
      (by simpa only [f, intervalBoxDifference, intervalDifference, Int.cast_sub,
        Int.cast_natCast] using hpair)
  have hsmall : 1/((M : ℝ)*a) ≤ 1/denseProductDensityBudget e η :=
    one_div_le_one_div_of_le (denseProductDensityBudget_pos e hη) hMlarge
  obtain ⟨q, hq, hqB, hnear⟩ := dense_product_signed_box e N hη hη1 hN
    (by positivity : 0 ≤ 1/((M : ℝ)*a)) hsmall
    (by simpa only [η, div_div] using hdiff)
  refine ⟨q, hq, hqB, ?_⟩
  convert hnear using 1
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def integralRealPolynomialSubring (σ : Type*) : Subring (MvPolynomial σ ℝ) :=
  (MvPolynomial.map (Int.castRingHom ℝ)).range

def realPolynomialCoefficientGrid (q : ℕ) (P : MvPolynomial σ ℝ) : Prop :=
  (fun m => P.coeff m) ∈ realDenominatorGrid q

theorem mem_integralRealPolynomialSubring_iff (P : MvPolynomial σ ℝ) :
    P ∈ integralRealPolynomialSubring σ ↔
      ∀ m, ∃ z : ℤ, (z : ℝ) = P.coeff m := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    exact ⟨Q.coeff m, by simp [coeff_map]⟩
  · intro h
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h m

theorem C_int_mem_integralRealPolynomialSubring (z : ℤ) :
    C (z : ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨C z, by simp⟩

theorem X_mem_integralRealPolynomialSubring (i : σ) :
    (X i : MvPolynomial σ ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨X i, by simp⟩

theorem rename_mem_integralRealPolynomialSubring {τ : Type*} (f : σ → τ)
    {P : MvPolynomial σ ℝ} (hP : P ∈ integralRealPolynomialSubring σ) :
    rename f P ∈ integralRealPolynomialSubring τ := by
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

theorem realPolynomialCoefficientGrid_iff (q : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialCoefficientGrid q P ↔
      C (q : ℝ) * P ∈ integralRealPolynomialSubring σ := by
  rw [mem_integralRealPolynomialSubring_iff]
  simp only [coeff_C_mul]
  constructor
  · rintro ⟨z, hz⟩ m
    exact ⟨z m, congrFun hz m⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

theorem realPolynomialCoefficientGrid_add {q : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid q Q) :
    realPolynomialCoefficientGrid q (P + Q) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_add]
  exact (integralRealPolynomialSubring σ).add_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
    ((realPolynomialCoefficientGrid_iff q Q).mp hQ)

theorem realPolynomialCoefficientGrid_neg {q : ℕ} {P : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) : realPolynomialCoefficientGrid q (-P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_neg]
  exact (integralRealPolynomialSubring σ).neg_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_X (q : ℕ) (i : σ) :
    realPolynomialCoefficientGrid q (X i) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  exact (integralRealPolynomialSubring σ).mul_mem
    ⟨C (q : ℤ), by simp⟩
    (X_mem_integralRealPolynomialSubring i)

theorem realPolynomialCoefficientGrid_rename {τ : Type*} (f : σ → τ)
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (rename f P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simpa using rename_mem_integralRealPolynomialSubring f
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_mono {q r : ℕ} (hqr : q ∣ r)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid r P := by
  obtain ⟨k, rfl⟩ := hqr
  apply (realPolynomialCoefficientGrid_iff (q * k) _).mpr
  have hk : C (k : ℝ) ∈ integralRealPolynomialSubring σ := ⟨C (k : ℤ), by simp⟩
  have h := (integralRealPolynomialSubring σ).mul_mem
    hk
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
  simpa [Nat.cast_mul, map_mul, mul_assoc, mul_left_comm] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

noncomputable def majorShiftCoordinates (e : B → MvPolynomial U R) :
    B → MvPolynomial (U ⊕ B) R :=
  fun b => X (Sum.inr b) + rename Sum.inl (e b)

noncomputable def majorShiftSubstitution (e : B → MvPolynomial U R) :
    U ⊕ B → MvPolynomial (U ⊕ B) R :=
  Sum.elim (fun u => X (Sum.inl u)) (majorShiftCoordinates e)

noncomputable def majorSlowPolynomial (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) : MvPolynomial (U ⊕ B) R :=
  rename Sum.inr D0 + eval₂Hom C (majorShiftSubstitution e) E -
    eval₂Hom C (majorShiftCoordinates e) V

noncomputable def majorRationalPolynomial (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    MvPolynomial (U ⊕ B) R :=
  Q + eval₂Hom C (majorShiftCoordinates (-a)) V

theorem majorShiftCoordinates_map {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R) (j : B) :
    map φ (majorShiftCoordinates e j) =
      majorShiftCoordinates (fun i => map φ (e i)) j := by
  simp [majorShiftCoordinates, map_rename]

theorem majorRationalPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    map φ (majorRationalPolynomial Q V a) =
      majorRationalPolynomial (map φ Q) (map φ V) (fun i => map φ (a i)) := by
  unfold majorRationalPolynomial
  rw [map_add, map_eval₂Hom]
  simp only [coe_eval₂Hom, eval₂_map_comp_C, majorShiftCoordinates_map,
    Pi.neg_apply, map_neg]
  rfl

@[simp] theorem majorShiftCoordinates_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : B) :
    eval₂ φ (Sum.elim u b) (majorShiftCoordinates e j) =
      b j + eval₂ φ u (e j) := by
  simp [majorShiftCoordinates, eval₂_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : U ⊕ B) :
    eval₂ φ (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval₂ φ u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

theorem majorRationalPolynomial_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R)
    (u : U → T) (b : B → T) :
    eval₂ φ (Sum.elim u b) (majorRationalPolynomial Q V a) =
      eval₂ φ (Sum.elim u b) Q + eval₂ φ (fun i => b i - eval₂ φ u (a i)) V := by
  simp only [majorRationalPolynomial, eval₂_add, coe_eval₂Hom, ← eval₂_assoc,
    majorShiftCoordinates_eval₂, Pi.neg_apply, eval₂_neg, sub_eq_add_neg]

@[simp] theorem majorShiftCoordinates_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : B) :
    eval (Sum.elim u b) (majorShiftCoordinates e j) = b j + eval u (e j) := by
  simp [majorShiftCoordinates, eval_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : U ⊕ B) :
    eval (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

theorem majorSlowPolynomial_eval (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) (u : U → R) (b : B → R) :
    eval (Sum.elim u b) (majorSlowPolynomial D0 E V e) =
      eval b D0 + eval (Sum.elim u (fun i => b i + eval u (e i))) E -
        eval (fun i => b i + eval u (e i)) V := by
  unfold majorSlowPolynomial
  simp only [map_sub, map_add, eval_rename]
  congr 1
  · congr 1
    change eval (Sum.elim u b) (eval₂ C (majorShiftSubstitution e) E) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftSubstitution_eval]
  · change eval (Sum.elim u b) (eval₂ C (majorShiftCoordinates e) V) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftCoordinates_eval]

theorem majorShiftCoordinates_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (he : ∀ i, realPolynomialMass (e i) ≤ M) (j : B) :
    realPolynomialMass (majorShiftCoordinates e j) ≤ 1 + M := by
  apply (realPolynomialMass_add_le _ _).trans
  exact add_le_add (realPolynomialMass_X _).le
    ((realPolynomialMass_rename_le (e j) Sum.inl).trans (he j))

theorem majorShiftSubstitution_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ i, realPolynomialMass (e i) ≤ M)
    (j : U ⊕ B) :
    realPolynomialMass (majorShiftSubstitution e j) ≤ 1 + M := by
  cases j with
  | inl i =>
    change realPolynomialMass (X (Sum.inl i) : MvPolynomial (U ⊕ B) ℝ) ≤ _
    rw [realPolynomialMass_X]
    exact le_add_of_nonneg_right hM
  | inr i => exact majorShiftCoordinates_mass_le e he i

theorem majorSlowPolynomial_mass_le (D0 : MvPolynomial B ℝ)
    (E : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (e : B → MvPolynomial U ℝ) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ i, realPolynomialMass (e i) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D0 E V e) ≤
      realPolynomialMass D0 +
        (realPolynomialMass E + realPolynomialMass V) * (1 + M) ^ d := by
  have hE' := realPolynomialMass_substitution_le E (majorShiftSubstitution e)
    (show 1 ≤ 1 + M by linarith) (majorShiftSubstitution_mass_le e hM he) hE
  have hV' := realPolynomialMass_substitution_le V (majorShiftCoordinates e)
    (show 1 ≤ 1 + M by linarith) (majorShiftCoordinates_mass_le e he) hV
  unfold majorSlowPolynomial
  exact (realPolynomialMass_sub_le _ _).trans
    (((add_le_add ((realPolynomialMass_add_le _ _).trans
      (add_le_add (realPolynomialMass_rename_le D0 Sum.inr) hE')) hV')).trans
      (by ring_nf; rfl))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {σ J R : Type*} [Fintype J] [CommRing R] [Module R ℝ]

@[simp] theorem coefficients_ofCoordinates_basisFun
    (Q : J → MvPolynomial σ ℝ) (α : σ →₀ ℕ) (j : J) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j =
      (Q j).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := R) (Pi.basisFun ℝ J) Q j)
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Module.Basis.coord_apply, Pi.basisFun_repr] using h

theorem coefficients_ofCoordinates_mem_realDenominatorGrid
    (Q : J → MvPolynomial σ ℝ) (q : ℕ)
    (hQ : ∀ j, realPolynomialCoefficientGrid q (Q j)) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α ∈
      realDenominatorGrid q := by
  classical
  choose z hz using hQ
  refine ⟨fun j => z j α, funext fun j => ?_⟩
  change (z j α : ℝ) = (q : ℝ) *
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j
  rw [coefficients_ofCoordinates_basisFun]
  exact congrFun (hz j) α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {U B R : Type*} [CommRing R]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem cleared_substitution_term
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (m : σ →₀ ℕ) (hm : m.sum (fun _ n => n) ≤ d) :
    C ((qV * qA ^ d : ℕ) : ℝ) *
        (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) =
      C ((qV : ℝ) * V.coeff m) * C ((qA : ℝ) ^ (d - m.sum (fun _ n => n))) *
        ∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i := by
  classical
  rw [show (∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i) =
      C (qA : ℝ) ^ m.sum (fun _ n => n) * ∏ i ∈ m.support, A i ^ m i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl]
  simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  calc
    _ = (C (qV : ℝ) * C (V.coeff m)) * C (qA : ℝ) ^ d *
        (∏ i ∈ m.support, A i ^ m i) := by ring
    _ = _ := by
      rw [show C (qA : ℝ) ^ d =
        C (qA : ℝ) ^ (d - m.sum (fun _ n => n)) * C (qA : ℝ) ^ m.sum (fun _ n => n) by
        rw [← pow_add, Nat.sub_add_cancel hm]]
      ring

theorem polynomial_substitution_cleared_mem
    (S : Subring (MvPolynomial τ ℝ))
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : ∀ m ∈ V.support, C ((qV : ℝ) * V.coeff m) ∈ S)
    (hA : ∀ i, C (qA : ℝ) * A i ∈ S)
    (hqA : C (qA : ℝ) ∈ S) :
    C ((qV * qA ^ d : ℕ) : ℝ) * aeval A V ∈ S := by
  classical
  rw [aeval_def, eval₂_eq, Finset.mul_sum]
  apply S.sum_mem
  intro m hm
  change C ((qV * qA ^ d : ℕ) : ℝ) *
    (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) ∈ S
  rw [cleared_substitution_term V A qV qA d m ((le_totalDegree hm).trans hdegree)]
  apply S.mul_mem
  · apply S.mul_mem (hV m hm)
    simpa only [map_pow] using S.pow_mem hqA (d - m.sum (fun _ n => n))
  · exact S.prod_mem fun i _ => S.pow_mem (hA i) (m i)

theorem realPolynomialCoefficientGrid_substitute
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid qV V)
    (hA : ∀ i, realPolynomialCoefficientGrid qA (A i)) :
    realPolynomialCoefficientGrid (qV * qA ^ d) (aeval A V) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  apply polynomial_substitution_cleared_mem (integralRealPolynomialSubring τ)
    V A qV qA d hdegree
  · obtain ⟨z, hz⟩ := hV
    intro m _
    have hm : (z m : ℝ) = (qV : ℝ) * V.coeff m := congrFun hz m
    rw [← hm]
    exact C_int_mem_integralRealPolynomialSubring (z m)
  · exact fun i => (realPolynomialCoefficientGrid_iff _ _).mp (hA i)
  · exact ⟨C (qA : ℤ), by simp⟩

theorem realPolynomialCoefficientGrid_substitute_common
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (q d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid q V)
    (hA : ∀ i, realPolynomialCoefficientGrid q (A i)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (aeval A V) := by
  simpa only [pow_succ'] using
    realPolynomialCoefficientGrid_substitute V A q q d hdegree hV hA

theorem majorShiftCoordinates_coefficientGrid {U B : Type*}
    (a : B → MvPolynomial U ℝ) (q : ℕ)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) (b : B) :
    realPolynomialCoefficientGrid q (majorShiftCoordinates a b) := by
  exact realPolynomialCoefficientGrid_add (realPolynomialCoefficientGrid_X q _)
    (realPolynomialCoefficientGrid_rename Sum.inl (ha b))

theorem majorRationalPolynomial_coefficientGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (a : B → MvPolynomial U ℝ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : realPolynomialCoefficientGrid q Q)
    (hV : realPolynomialCoefficientGrid q V)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (majorRationalPolynomial Q V a) := by
  apply realPolynomialCoefficientGrid_add
  · exact realPolynomialCoefficientGrid_mono (dvd_pow_self q (by omega)) hQ
  · exact realPolynomialCoefficientGrid_substitute_common V
      (majorShiftCoordinates (-a)) q d hdegree hV
      (majorShiftCoordinates_coefficientGrid (-a) q
        (fun b => realPolynomialCoefficientGrid_neg (ha b)))

theorem realPolynomialCoefficientGrid_ratCast_iff
    (q : ℕ) (P : MvPolynomial σ ℚ) :
    realPolynomialCoefficientGrid q (map (algebraMap ℚ ℝ) P) ↔
      (fun m => P.coeff m) ∈ denominatorGrid q := by
  simp only [realPolynomialCoefficientGrid, coeff_map]
  exact real_cast_mem_denominatorGrid_iff q (fun m => P.coeff m)

theorem majorRationalPolynomial_denominatorGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℚ) (V : MvPolynomial B ℚ)
    (a : B → MvPolynomial U ℚ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : (fun m => Q.coeff m) ∈ denominatorGrid q)
    (hV : (fun m => V.coeff m) ∈ denominatorGrid q)
    (ha : ∀ b, (fun m => (a b).coeff m) ∈ denominatorGrid q) :
    (fun m => (majorRationalPolynomial Q V a).coeff m) ∈ denominatorGrid (q ^ (d + 1)) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [majorRationalPolynomial_map]
  apply majorRationalPolynomial_coefficientGrid
  · apply le_trans (b := V.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) V hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hQ
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hV
  · exact fun b => (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr (ha b)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialCoefficientGrid_aeval_integral
    (P : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ) (q : ℕ)
    (hP : realPolynomialCoefficientGrid q P)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    realPolynomialCoefficientGrid q (aeval A P) := by
  simpa only [one_pow, mul_one] using
    realPolynomialCoefficientGrid_substitute P A q 1 P.totalDegree le_rfl hP hA

theorem realPolynomialCoefficientGrid_intCast (P : MvPolynomial σ ℤ) :
    realPolynomialCoefficientGrid 1 (map (Int.castRingHom ℝ) P) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  simpa only [Nat.cast_one, map_one, one_mul] using
    (show map (Int.castRingHom ℝ) P ∈ integralRealPolynomialSubring σ from ⟨P, rfl⟩)

theorem realPolynomialCoefficientGrid_weightedHomogeneousComponent
    {M : Type*} [AddCommMonoid M] (w : σ → M) (d : M)
    (q : ℕ) (P : MvPolynomial σ ℝ) (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (weightedHomogeneousComponent w d P) := by
  classical
  obtain ⟨z, hz⟩ := hP
  refine ⟨fun m => if Finsupp.weight w m = d then z m else 0, funext (fun m => ?_)⟩
  change ((if Finsupp.weight w m = d then z m else 0 : ℤ) : ℝ) =
    (q : ℝ) * (weightedHomogeneousComponent w d P).coeff m
  by_cases hm : Finsupp.weight w m = d
  · have hzm : (z m : ℝ) = (q : ℝ) * P.coeff m := congrFun hz m
    simpa [coeff_weightedHomogeneousComponent, hm] using hzm
  · simp [coeff_weightedHomogeneousComponent, hm]

end Erdos3

end

section

namespace Erdos3

theorem den_dvd_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ∣ q := by
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff q hq x).mp hx
  rw [hz i]
  have h := Rat.den_dvd (z i) (q : ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

theorem den_le_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ≤ q :=
  Nat.le_of_dvd hq (den_dvd_of_mem_denominatorGrid hq hx i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringGroup
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLT_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLT w e :=
  fun _ ha => lt_of_lt_of_le (hp ha) hde

theorem weightedSupportLT_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLE w d :=
  fun _ ha => le_of_lt (show _ < d from hp ha)

theorem weightedSupportLT_succ_le {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w (d + 1)) : p ∈ weightedSupportLE w d :=
  fun _ ha => Nat.lt_succ_iff.mp (hp ha)

theorem weightedSupportLT_zero_eq {w : σ → ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w 0) : p = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro a
  by_contra ha
  exact Nat.not_lt_zero _ (hp (MvPolynomial.mem_support_iff.mpr ha))

theorem weightedLowering_preserves_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p ∈ weightedSupportLE w d := by
  rw [MvPolynomial.aeval_unique F]
  apply weightedSupportLE_aeval w w _ _ hp
  intro i
  simpa only [sub_add_cancel, Function.comp_apply] using (weightedSupportLE w (w i)).add_mem
    (weightedSupportLT_le (hF i)) (weightedSupportLE_X w i)

theorem weightedLowering_mul_bounds (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (hFp : F p ∈ weightedSupportLE w d) (hFq : F q ∈ weightedSupportLE w e)
    (hdp : F p - p ∈ weightedSupportLT w d)
    (hdq : F q - q ∈ weightedSupportLT w e) :
    F (p * q) ∈ weightedSupportLE w (d + e) ∧
      F (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul hFp hFq, ?_⟩
  rw [map_mul, show F p * F q - p * q = (F p - p) * F q + p * (F q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp hFq)
    (weightedSupportLE_mul_LT hp hdq)

theorem weightedLowering_monomial_one (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - monomial a 1 ∈ weightedSupportLT w (Finsupp.weight w a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - 1 ∈ _
        rw [map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) hp (weightedLowering_preserves_degree w F hF hp)
          (weightedLowering_preserves_degree w F hF (weightedSupportLE_X w i)) ih (hF i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh.2
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedLowering_mul_bounds w F (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a)
        hp (weightedLowering_preserves_degree w F hF hp)
        (weightedLowering_preserves_degree w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh.2

theorem weightedLowering_monomial (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - monomial a r ∈ weightedSupportLT w (Finsupp.weight w a) := by
  have hc : F (C r) = C r := F.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, map_mul, hc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedLowering_monomial_one w F hF a)

theorem weightedLowering_difference (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    F p - p ∈ weightedSupportLT w d := by
  classical
  change (F.toLinearMap - (LinearMap.id : Module.End R (MvPolynomial σ R))) p ∈
    weightedSupportLT w d
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w d).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha) (weightedLowering_monomial w F hF a (p.coeff a))

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialHomDifference
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) : Module.End R (MvPolynomial σ R) :=
  F.toLinearMap - LinearMap.id

theorem polynomialHomDifference_pow_eq_zero (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    (polynomialHomDifference F ^ (d + 1)) p = 0 := by
  induction d generalizing p with
  | zero =>
      rw [pow_one]
      exact weightedSupportLT_zero_eq (weightedLowering_difference w F hF hp)
  | succ d ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (weightedSupportLT_succ_le (weightedLowering_difference w F hF hp))

theorem weightedLowering_eq_zero_of_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) (hz : F p = 0) :
    p = 0 := by
  induction d generalizing p with
  | zero =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      exact neg_eq_zero.mp (weightedSupportLT_zero_eq h)
  | succ d ih =>
      have h := weightedLowering_difference w F hF hp
      rw [hz, zero_sub] at h
      have hlow : p ∈ weightedSupportLT w (d + 1) := by
        simpa only [neg_neg] using (weightedSupportLT w (d + 1)).neg_mem h
      exact ih (weightedSupportLT_succ_le hlow) hz

theorem weightedLowering_injective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Injective F := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply weightedLowering_eq_zero_of_degree w F hF
    ((mem_weightedSupportLE_iff w ((p - q).weightedTotalDegree w) (p - q)).mpr le_rfl)
  rw [map_sub, hpq, sub_self]

theorem weightedLowering_preimage_degree (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i))
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    ∃ q, q ∈ weightedSupportLE w d ∧ F q = p := by
  induction d generalizing p with
  | zero =>
      exact ⟨p, hp, sub_eq_zero.mp (weightedSupportLT_zero_eq
        (weightedLowering_difference w F hF hp))⟩
  | succ d ih =>
      have hdiff := weightedSupportLT_succ_le (weightedLowering_difference w F hF hp)
      obtain ⟨q, hq, heq⟩ := ih hdiff
      refine ⟨p - q, (weightedSupportLE w (d + 1)).sub_mem hp
        (weightedSupportLE_mono (Nat.le_succ d) hq), ?_⟩
      rw [map_sub, heq]
      abel

theorem weightedLowering_bijective (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : Function.Bijective F := by
  refine ⟨weightedLowering_injective w F hF, ?_⟩
  intro p
  obtain ⟨q, _, hq⟩ := weightedLowering_preimage_degree w F hF
    ((mem_weightedSupportLE_iff w (p.weightedTotalDegree w) p).mpr le_rfl)
  exact ⟨q, hq⟩

noncomputable def weightedLoweringEquiv (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofBijective F (weightedLowering_bijective w F hF)

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

def weightedLoweringSubgroup (w : σ → ℕ) :
    Subgroup (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) where
  carrier := {e | ∀ i, e (X i) - X i ∈ weightedSupportLT w (w i)}
  one_mem' := by
    intro i
    change X i - X i ∈ weightedSupportLT w (w i)
    rw [sub_self]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro e f he hf i
    have hp := weightedLowering_preserves_degree w f.toAlgHom hf (weightedSupportLE_X w i)
    have h := weightedLowering_difference w e.toAlgHom he hp
    change e (f (X i)) - f (X i) ∈ weightedSupportLT w (w i) at h
    change e (f (X i)) - X i ∈ weightedSupportLT w (w i)
    simpa only [sub_add_sub_cancel] using (weightedSupportLT w (w i)).add_mem h (hf i)
  inv_mem' := by
    intro e he i
    obtain ⟨q, hq, hqe⟩ := weightedLowering_preimage_degree w e.toAlgHom he
      (weightedSupportLE_X w i)
    change e q = X i at hqe
    have heq : e.symm (X i) = q := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hqe.symm
    change e.symm (X i) - X i ∈ weightedSupportLT w (w i)
    rw [heq]
    have h := weightedLowering_difference w e.toAlgHom he hq
    change e q - q ∈ weightedSupportLT w (w i) at h
    rw [hqe] at h
    simpa only [neg_sub] using (weightedSupportLT w (w i)).neg_mem h

abbrev WeightedLoweringAut (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(weightedLoweringSubgroup (R := R) w)

theorem weightedLoweringEquiv_mem (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) :
    weightedLoweringEquiv w F hF ∈ weightedLoweringSubgroup w := hF

noncomputable def WeightedLoweringAut.ofHom (w : σ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hF : ∀ i, F (X i) - X i ∈ weightedSupportLT w (w i)) : WeightedLoweringAut w R :=
  ⟨weightedLoweringEquiv w F hF, weightedLoweringEquiv_mem w F hF⟩

theorem WeightedLoweringAut.preserves_degree {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p ∈ weightedSupportLE w d :=
  weightedLowering_preserves_degree w e.val.toAlgHom e.property hp

theorem WeightedLoweringAut.difference_lower {w : σ → ℕ} (e : WeightedLoweringAut w R)
    {d : ℕ} {p : MvPolynomial σ R} (hp : p ∈ weightedSupportLE w d) :
    e.val p - p ∈ weightedSupportLT w d :=
  weightedLowering_difference w e.val.toAlgHom e.property hp

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedDerivationDrop
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedDerivation_mul (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (P Q : MvPolynomial σ R) (d e k : ℕ)
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportLE w e)
    (hDP : D P ∈ weightedSupportDrop w d k) (hDQ : D Q ∈ weightedSupportDrop w e k) :
    D (P * Q) ∈ weightedSupportDrop w (d + e) k := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  apply (weightedSupportDrop w (d + e) k).add_mem (weightedSupportLE_mul_drop hP hDQ)
  simpa only [Nat.add_comm e d] using weightedSupportLE_mul_drop hQ hDP

theorem weightedDerivation_monomial_one (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) :
    D (monomial a 1) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      D (monomial (Finsupp.single i n) 1) ∈ weightedSupportDrop w (n * w i) k := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change D 1 ∈ _
        rw [D.map_one_eq_zero]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) k hp (weightedSupportLE_X w i) ih (hD i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change D 1 ∈ weightedSupportDrop w 0 k
      rw [D.map_one_eq_zero]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a) k hp hq
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

theorem weightedDerivation_monomial (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) (c : R) :
    D (monomial a c) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  have hm : C c * monomial a (1 : R) = monomial a c := by
    change monomial 0 c * monomial a 1 = monomial a c
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, D.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]
  simpa only [zero_add] using weightedSupportLE_mul_drop (weightedSupportLE_C w 0 c)
    (weightedDerivation_monomial_one w D k hD a)

theorem weightedDerivation_apply (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) :
    D P ∈ weightedSupportDrop w n (r + k) := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportDrop w n (r + k)).sum_mem
  intro a ha
  have hm := weightedDerivation_monomial w D k hD a (P.coeff a)
  intro b hb
  have h1 : Finsupp.weight w b + k ≤ Finsupp.weight w a := hm hb
  have h2 : Finsupp.weight w a + r ≤ n := hP ha
  change Finsupp.weight w b + (r + k) ≤ n
  omega

theorem weightedDerivation_apply_le (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    D P ∈ weightedSupportDrop w n k := by
  rw [← weightedSupportDrop_zero] at hP
  simpa only [Nat.zero_add] using weightedDerivation_apply w D k hD hP

theorem weightedDerivation_bracket (w : σ → ℕ)
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (a b : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) a)
    (hE : ∀ i, E (X i) ∈ weightedSupportDrop w (w i) b) (i : σ) :
    ⁅D, E⁆ (X i) ∈ weightedSupportDrop w (w i) (a + b) := by
  rw [Derivation.commutator_apply]
  apply (weightedSupportDrop w (w i) (a + b)).sub_mem
  · simpa only [Nat.add_comm b a] using weightedDerivation_apply w D a hD (hE i)
  · exact weightedDerivation_apply w E b hE (hD i)

theorem weightedDerivation_pow (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) (m : ℕ) :
    (D.toLinearMap ^ m) P ∈ weightedSupportDrop w n (r + m * k) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.zero_mul, Nat.add_zero] using hP
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      change D ((D.toLinearMap ^ m) P) ∈ weightedSupportDrop w n (r + (m + 1) * k)
      simpa only [Nat.succ_mul, Nat.add_assoc] using weightedDerivation_apply w D k hD ih

theorem weightedDerivation_pow_eq_zero (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) 1)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    (D.toLinearMap ^ (n + 1)) P = 0 := by
  rw [← weightedSupportDrop_zero] at hP
  have h := weightedDerivation_pow w D 1 hD hP (n + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_self n) h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeSeparation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomial_eq_zero_of_pderiv_closed
    (S : Set (MvPolynomial σ ℚ))
    (hderiv : ∀ p ∈ S, ∀ i, pderiv i p ∈ S)
    (hconstant : ∀ p ∈ S, p.coeff 0 = 0) : ∀ p ∈ S, p = 0 := by
  classical
  have hcoeff : ∀ α : σ →₀ ℕ, ∀ p ∈ S, p.coeff α = 0 := by
    intro α
    induction α using Finsupp.induction with
    | zero => exact hconstant
    | @single_add i n α hi hn ih =>
      have hsteps : ∀ m : ℕ, ∀ p ∈ S, p.coeff (Finsupp.single i m + α) = 0 := by
        intro m
        induction m with
        | zero => simpa using ih
        | succ m ihm =>
          intro p hp
          have h := ihm (pderiv i p) (hderiv p hp i)
          rw [coeff_pderiv] at h
          have hindex : Finsupp.single i (m + 1) + α =
              (Finsupp.single i m + α) + Finsupp.single i 1 := by
            rw [Finsupp.single_add]
            abel
          rw [hindex]
          apply (mul_eq_zero.mp h).resolve_right
          exact_mod_cast Nat.succ_ne_zero ((Finsupp.single i m + α) i)
      exact hsteps n
  intro p hp
  ext α
  simpa only [MvPolynomial.coeff_zero] using hcoeff α p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def supportedSubmoduleBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis S K P := by
  let c := Basis.span (b.linearIndependent.comp (fun i : S => (i : ι)) Subtype.val_injective)
  have he : Submodule.span K (Set.range (fun i : S => b i)) = P := by
    rw [hP]
    congr 1
    ext x
    simp
  exact c.map (LinearEquiv.ofEq _ _ he)

@[simp] theorem supportedSubmoduleBasis_coe (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : S) :
    (supportedSubmoduleBasis b P S hP i : V) = b i := by
  simp [supportedSubmoduleBasis, Basis.map_apply]

theorem supportedSubmoduleBasis_repr (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : P) (i : S) :
    (supportedSubmoduleBasis b P S hP).repr x i = b.repr (x : V) i := by
  classical
  let c := supportedSubmoduleBasis b P S hP
  have he : c.coord i = (b.coord i).comp P.subtype := by
    apply c.ext
    intro j
    simp [c, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change c.coord i x = b.coord i (x : V)
  rw [he]
  rfl

theorem basis_mem_span_image_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    x ∈ Submodule.span K (b '' S) ↔ ∀ i, i ∉ S → b.repr x i = 0 := by
  classical
  rw [b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (Finsupp.mem_support_iff.mpr hne))
  · intro h i hi
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hi) (h i hnot)

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisCoordinateProjection (b : Basis ι K V) (S : Set ι) : V →ₗ[K] V := by
  classical
  exact
    { toFun := fun x => b.repr.symm ((b.repr x).filter (· ∈ S))
      map_add' := fun x y => by simp only [map_add, Finsupp.filter_add]
      map_smul' := fun c x => by simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

theorem basisCoordinateProjection_repr (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (x : V) (i : ι) :
    b.repr (basisCoordinateProjection b S x) i = if i ∈ S then b.repr x i else 0 := by
  classical
  by_cases hi : i ∈ S <;>
    simp [basisCoordinateProjection, hi]

theorem basisCoordinateProjection_mem_span (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x ∈ Submodule.span K (b '' S) := by
  classical
  apply (basis_mem_span_image_iff b S _).mpr
  intro i hi
  simp only [basisCoordinateProjection_repr, hi, ↓reduceIte]

theorem basisCoordinateProjection_eq_self (b : Basis ι K V) (S : Set ι) (x : V)
    (hx : x ∈ Submodule.span K (b '' S)) : basisCoordinateProjection b S x = x := by
  classical
  apply b.repr.injective
  ext i
  rw [basisCoordinateProjection_repr]
  split_ifs with hi
  · rfl
  · exact ((basis_mem_span_image_iff b S x).mp hx i hi).symm

theorem basisCoordinateProjection_basis (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (i : ι) :
    basisCoordinateProjection b S (b i) = if i ∈ S then b i else 0 := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact basisCoordinateProjection_eq_self b S (b i) (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply b.repr.injective
    ext j
    classical
    by_cases hj : j ∈ S <;> by_cases hij : i = j <;>
      simp_all [basisCoordinateProjection_repr]

theorem basisCoordinateProjection_idempotent (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S (basisCoordinateProjection b S x) = basisCoordinateProjection b S x :=
  basisCoordinateProjection_eq_self b S _ (basisCoordinateProjection_mem_span b S x)

theorem basisCoordinateProjection_eq_zero_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S x = 0 ↔ x ∈ Submodule.span K (b '' Sᶜ) := by
  classical
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have hiS : i ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hi
    have h := congrArg (fun v => b.repr v i) hx
    simpa only [basisCoordinateProjection_repr, hiS, ↓reduceIte, map_zero, Finsupp.zero_apply] using h
  · intro hx
    apply b.repr.injective
    ext i
    simp only [basisCoordinateProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hi
    · exact hx i (by simpa only [Set.mem_compl_iff, not_not] using hi)
    · rfl

theorem sub_basisCoordinateProjection_mem (b : Basis ι K V) (S : Set ι) (x : V) :
    x - basisCoordinateProjection b S x ∈ Submodule.span K (b '' Sᶜ) := by
  apply (basisCoordinateProjection_eq_zero_iff b S _).mp
  rw [map_sub, basisCoordinateProjection_idempotent, sub_self]

theorem basisCoordinateProjection_eq_iff (b : Basis ι K V) (S : Set ι) (x y : V) :
    basisCoordinateProjection b S x = basisCoordinateProjection b S y ↔
      x - y ∈ Submodule.span K (b '' Sᶜ) := by
  rw [← basisCoordinateProjection_eq_zero_iff, map_sub, sub_eq_zero]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basis_isCompl_span_compl (b : Basis ι K V) (S : Set ι) :
    IsCompl (Submodule.span K (b '' S)) (Submodule.span K (b '' Sᶜ)) := by
  apply b.linearIndependent.isCompl_span_image
  · exact b.span_eq
  · exact isCompl_compl

noncomputable def supportedQuotientBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis {i // i ∉ S} K (V ⧸ P) :=
  (supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl).map
    (P.quotientEquivOfIsCompl (Submodule.span K (b '' Sᶜ))
      (by rw [hP]; exact basis_isCompl_span_compl b S)).symm

@[simp] theorem supportedQuotientBasis_apply (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : {i // i ∉ S}) :
    supportedQuotientBasis b P S hP i = P.mkQ (b i) := by
  change P.mkQ ((supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl) i : V) = _
  exact congrArg P.mkQ (supportedSubmoduleBasis_coe b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl i)

theorem supportedQuotientBasis_repr_mk (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : V) (i : {i // i ∉ S}) :
    (supportedQuotientBasis b P S hP).repr (P.mkQ x) i = b.repr x i := by
  classical
  have hker : P ≤ LinearMap.ker (b.coord i) := by
    intro y hy
    rw [hP, basis_mem_span_image_iff] at hy
    exact hy i i.property
  let f := P.liftQ (b.coord i) hker
  have hf : (supportedQuotientBasis b P S hP).coord i = f := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change (supportedQuotientBasis b P S hP).repr (supportedQuotientBasis b P S hP j) i = _
    rw [Basis.repr_self]
    simp [f, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change (supportedQuotientBasis b P S hP).coord i (P.mkQ x) = _
  rw [hf]
  rfl

theorem supportedQuotientBasis_map_span (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (T : Set ι) :
    (Submodule.span K (b '' T)).map P.mkQ = Submodule.span K
      (supportedQuotientBasis b P S hP '' {i : {i // i ∉ S} | (i : ι) ∈ T}) := by
  rw [Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    by_cases hs : i ∈ S
    · have hz : P.mkQ (b i) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (by
        rw [hP]
        exact Submodule.subset_span ⟨i, hs, rfl⟩)
      change P.mkQ (b i) ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    · have h := Submodule.subset_span (R := K)
        (show supportedQuotientBasis b P S hP ⟨i, hs⟩ ∈
          supportedQuotientBasis b P S hP '' {j : {i // i ∉ S} | (j : ι) ∈ T} from
            ⟨⟨i, hs⟩, hi, rfl⟩)
      simpa only [supportedQuotientBasis_apply] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    rw [supportedQuotientBasis_apply]
    exact Submodule.subset_span ⟨i.val, hi, rfl⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisGradeProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i = j}

noncomputable def basisBelowProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i < j}

@[simp] theorem basisGradeProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisGradeProjection b w j x) i = if w i = j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i = j} x i

@[simp] theorem basisBelowProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisBelowProjection b w j x) i = if w i < j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i < j} x i

theorem basisBelowProjection_eq_sum_grades (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    basisBelowProjection b w j x = ∑ k ∈ Finset.range j, basisGradeProjection b w k x := by
  apply b.repr.injective
  ext i
  simp [basisBelowProjection_repr, basisGradeProjection_repr]

def BasisGradedSubmodule (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V) : Prop :=
  ∀ j x, x ∈ U → basisGradeProjection b w j x ∈ U

theorem BasisGradedSubmodule.below_mem (b : Basis ι K V) (w : ι → ℕ) (U : Submodule K V)
    (hU : BasisGradedSubmodule b w U) (j : ℕ) (x : V) (hx : x ∈ U) :
    basisBelowProjection b w j x ∈ U := by
  rw [basisBelowProjection_eq_sum_grades]
  exact Submodule.sum_mem U (fun k _ => hU k x hx)

theorem sub_basisBelowProjection_mem (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    x - basisBelowProjection b w j x ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    sub_basisCoordinateProjection_mem b {i | w i < j} x

theorem basisBelowProjection_eq_iff (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x y : V) :
    basisBelowProjection b w j x = basisBelowProjection b w j y ↔
      x - y ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    basisCoordinateProjection_eq_iff b {i | w i < j} x y

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem basisGradeProjection_pi_apply (w : σ → ℕ) (j : ℕ)
    (x : σ → ℚ) (i : σ) :
    basisGradeProjection (Pi.basisFun ℚ σ) w j x i =
      if w i = j then x i else 0 := by
  simpa only [Pi.basisFun_repr] using
    basisGradeProjection_repr (Pi.basisFun ℚ σ) w j x i

theorem sum_basisGradeProjection_pi (w : σ → ℕ) (x : σ → ℚ) :
    ∑ j ∈ Finset.univ.image w, basisGradeProjection (Pi.basisFun ℚ σ) w j x = x := by
  classical
  funext i
  simp only [Finset.sum_apply, basisGradeProjection_pi_apply]
  simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

noncomputable def character (r : ZMod N) : AddChar (ZMod N) ℂ :=
  AddChar.zmodAddEquiv r

@[simp] lemma character_zero (r : ZMod N) : character r 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp] lemma character_add (r x y : ZMod N) :
    character r (x + y) = character r x * character r y := by
  exact AddChar.map_add_eq_mul _ _ _

@[simp] lemma norm_character (r x : ZMod N) : ‖character r x‖ = 1 := by
  simp [character]

lemma character_comm (r x : ZMod N) : character r x = character x r := by
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (↑(AddChar.zmod N (r : ZMod N) (x : ZMod N)) : ℂ) =
    ↑(AddChar.zmod N (x : ZMod N) (r : ZMod N))
  rw [AddChar.zmod_intCast, AddChar.zmod_intCast]
  congr 1
  ring_nf
  rfl

@[simp] lemma character_zero_index (x : ZMod N) : character 0 x = 1 := by
  rw [character_comm, character_zero]

@[simp] lemma character_add_index (r s x : ZMod N) :
    character (r + s) x = character r x * character s x := by
  rw [character_comm, character_add, character_comm x r, character_comm x s]

lemma norm_one_sub_mul_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - a * b‖ ≤ ‖1 - a‖ + ‖1 - b‖ := by
  calc
    ‖1 - a * b‖ = ‖(1 - a) + a * (1 - b)‖ := by ring_nf
    _ ≤ ‖1 - a‖ + ‖a * (1 - b)‖ := norm_add_le _ _
    _ ≤ ‖1 - a‖ + ‖1 - b‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)

structure Set (N : ℕ) [NeZero N] where
  frequencies : Finset (ZMod N)
  radius : ℝ
  radius_nonneg : 0 ≤ radius

namespace Set

noncomputable def carrier (B : Set N) : Finset (ZMod N) :=
  Finset.univ.filter fun x ↦
    ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius

instance : Membership (ZMod N) (Set N) := ⟨fun B x ↦ x ∈ B.carrier⟩

@[simp] lemma mem_carrier {B : Set N} {x : ZMod N} :
    x ∈ B.carrier ↔
      ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius := by
  simp [carrier]

lemma mem_iff {B : Set N} {x : ZMod N} :
    x ∈ B ↔ ∀ r ∈ B.frequencies, ‖1 - character r x‖ ≤ B.radius :=
  mem_carrier

def rank (B : Set N) : ℕ := B.frequencies.card

def dilate (ρ : ℝ) (B : Set N) : Set N where
  frequencies := B.frequencies
  radius := |ρ| * B.radius
  radius_nonneg := mul_nonneg (abs_nonneg _) B.radius_nonneg

def ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set N where
  frequencies := Γ
  radius := ρ
  radius_nonneg := hρ

def meet (B C : Set N) : Set N where
  frequencies := B.frequencies ∪ C.frequencies
  radius := min B.radius C.radius
  radius_nonneg := le_min B.radius_nonneg C.radius_nonneg

@[simp] lemma frequencies_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).frequencies = Γ := rfl

@[simp] lemma radius_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).radius = ρ := rfl

@[simp] lemma rank_ofFrequencies (Γ : Finset (ZMod N)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ofFrequencies Γ ρ hρ).rank = Γ.card := rfl

@[simp] lemma frequencies_meet (B C : Set N) :
    (B.meet C).frequencies = B.frequencies ∪ C.frequencies := rfl

@[simp] lemma radius_meet (B C : Set N) :
    (B.meet C).radius = min B.radius C.radius := rfl

lemma rank_meet_le (B C : Set N) : (B.meet C).rank ≤ B.rank + C.rank := by
  exact Finset.card_union_le _ _

@[simp] lemma frequencies_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).frequencies = B.frequencies := rfl

@[simp] lemma radius_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).radius = |ρ| * B.radius := rfl

@[simp] lemma rank_dilate (ρ : ℝ) (B : Set N) :
    (B.dilate ρ).rank = B.rank := rfl

@[simp] lemma zero_mem (B : Set N) : (0 : ZMod N) ∈ B := by
  rw [mem_iff]
  intro r hr
  simp [B.radius_nonneg]

lemma carrier_nonempty (B : Set N) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem⟩

lemma card_pos (B : Set N) : 0 < B.carrier.card :=
  Finset.card_pos.mpr B.carrier_nonempty

lemma neg_mem_iff (B : Set N) (x : ZMod N) : -x ∈ B ↔ x ∈ B := by
  rw [mem_iff, mem_iff]
  have hnorm (z : ℂ) : ‖1 - (starRingEnd ℂ) z‖ = ‖1 - z‖ := by
    simpa using (RCLike.norm_conj (1 - z))
  constructor
  · intro h r hr
    have hr' := h r hr
    rw [AddChar.map_neg_eq_conj, hnorm] at hr'
    exact hr'
  · intro h r hr
    rw [AddChar.map_neg_eq_conj, hnorm]
    exact h r hr

lemma add_mem_of_mem {B₁ B₂ B₃ : Set N}
    (hfreq₁ : B₃.frequencies ⊆ B₁.frequencies)
    (hfreq₂ : B₃.frequencies ⊆ B₂.frequencies)
    (hradius : B₁.radius + B₂.radius ≤ B₃.radius)
    {x y : ZMod N} (hx : x ∈ B₁) (hy : y ∈ B₂) : x + y ∈ B₃ := by
  rw [mem_iff] at hx hy ⊢
  intro r hr
  calc
    ‖1 - character r (x + y)‖ =
        ‖1 - character r x * character r y‖ := by rw [character_add]
    _ ≤ ‖1 - character r x‖ + ‖1 - character r y‖ :=
      norm_one_sub_mul_of_norm_le_one (by rw [norm_character])
    _ ≤ B₁.radius + B₂.radius := add_le_add (hx r (hfreq₁ hr)) (hy r (hfreq₂ hr))
    _ ≤ B₃.radius := hradius

lemma add_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x + y ∈ B.dilate (ρ + σ) := by
  apply add_mem_of_mem (B₁ := B.dilate ρ) (B₂ := B.dilate σ)
      (B₃ := B.dilate (ρ + σ))
  · simp
  · simp
  · simp [abs_of_nonneg hρ, abs_of_nonneg hσ, abs_of_nonneg (add_nonneg hρ hσ), add_mul]
  · exact hx
  · exact hy

lemma sub_mem_dilate {B : Set N} {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    {x y : ZMod N} (hx : x ∈ B.dilate ρ) (hy : y ∈ B.dilate σ) :
    x - y ∈ B.dilate (ρ + σ) := by
  rw [sub_eq_add_neg]
  apply add_mem_dilate hρ hσ hx
  exact (B.dilate σ).neg_mem_iff y |>.2 hy

lemma carrier_mono {B₁ B₂ : Set N} (hfreq : B₂.frequencies ⊆ B₁.frequencies)
    (hradius : B₁.radius ≤ B₂.radius) : B₁.carrier ⊆ B₂.carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro r hr
  exact (hx r (hfreq hr)).trans hradius

lemma carrier_meet_subset_left (B C : Set N) : (B.meet C).carrier ⊆ B.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_left
  · exact min_le_left _ _

lemma carrier_meet_subset_right (B C : Set N) : (B.meet C).carrier ⊆ C.carrier := by
  apply carrier_mono
  · exact Finset.subset_union_right
  · exact min_le_right _ _

lemma dilate_mono (B : Set N) {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) :
    (B.dilate ρ).carrier ⊆ (B.dilate σ).carrier := by
  apply carrier_mono
  · simp
  · have hσ : 0 ≤ σ := hρ.trans hρσ
    simp only [radius_dilate, ge_iff_le]
    rw [abs_of_nonneg hρ, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_right hρσ B.radius_nonneg

@[simp] lemma dilate_one (B : Set N) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : Set N) (s t : ℝ) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, abs_mul, mul_assoc]

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma norm_sub_le_abs_arg_sub_of_norm_eq_one {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ≤ |z.arg - w.arg| := by
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    calc
      Complex.exp (z.arg * Complex.I) =
          ‖z‖ * Complex.exp (z.arg * Complex.I) := by simp [hz]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  have hwexp : Complex.exp (w.arg * Complex.I) = w := by
    calc
      Complex.exp (w.arg * Complex.I) =
          ‖w‖ * Complex.exp (w.arg * Complex.I) := by simp [hw]
      _ = w := Complex.norm_mul_exp_arg_mul_I w
  calc
    ‖z - w‖ =
        ‖Complex.exp (z.arg * Complex.I) - Complex.exp (w.arg * Complex.I)‖ := by
      rw [hzexp, hwexp]
    _ =
        ‖Complex.exp (w.arg * Complex.I) *
          (Complex.exp ((z.arg - w.arg) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    _ = ‖Complex.exp ((z.arg - w.arg) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ |z.arg - w.arg| := by
      simpa [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.arg - w.arg))

noncomputable def scaledArg (m : ℕ) (z : ℂ) : ℝ :=
  (z.arg + Real.pi) * m / (2 * Real.pi)

lemma scaledArg_le (m : ℕ) (z : ℂ) : scaledArg m z ≤ m := by
  unfold scaledArg
  have hz : z.arg + Real.pi ≤ 2 * Real.pi := by
    linarith [Complex.arg_le_pi z]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi]
  nlinarith

noncomputable def argBin (m : ℕ) (z : ℂ) : Fin (m + 1) :=
  ⟨⌊scaledArg m z⌋₊, by
    rw [Nat.floor_lt' (Nat.add_one_ne_zero m)]
    exact (scaledArg_le m z).trans_lt (by exact_mod_cast Nat.lt_succ_self m)⟩

noncomputable def argumentCode (B : Set N) (m : ℕ) (x : ZMod N) :
    (r : ↥B.frequencies) → Fin (m + 1) :=
  fun r ↦ argBin m (character r.1 x)

@[simp] lemma card_argumentCodeSpace (B : Set N) (m : ℕ) :
    Fintype.card ((r : ↥B.frequencies) → Fin (m + 1)) =
      (m + 1) ^ B.rank := by
  simp [Set.rank]

lemma norm_one_sub_character_sub (r x y : ZMod N) :
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ := by
  have hy : character r y ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_character]; norm_num)
  rw [AddChar.map_sub_eq_div, one_sub_div hy, norm_div, norm_character]
  simp [norm_sub_rev]

lemma abs_arg_character_le_two_radius (B : Set N) {x r : ZMod N}
    (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    |(character r x).arg| ≤ 2 * B.radius := by
  have hnorm := Set.mem_iff.mp hx r hr
  have hangle := Complex.angle_le_mul_norm_sub
    (norm_character r x) (by norm_num : ‖(1 : ℂ)‖ = 1)
  calc
    |(character r x).arg| = InnerProductGeometry.angle (character r x) 1 :=
      (Complex.angle_one_right (norm_ne_zero_iff.mp (by
        rw [norm_character]
        norm_num))).symm
    _ ≤ Real.pi / 2 * ‖character r x - 1‖ := hangle
    _ = Real.pi / 2 * ‖1 - character r x‖ := by rw [norm_sub_rev]
    _ ≤ Real.pi / 2 * B.radius :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 * B.radius := by
      apply mul_le_mul_of_nonneg_right _ B.radius_nonneg
      linarith [Real.pi_lt_four]

noncomputable def localScaledArg (B : Set N) (z : ℂ) : ℝ :=
  2 * (z.arg + 2 * B.radius) / B.radius

lemma localScaledArg_nonneg (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    0 ≤ localScaledArg B (character r x) := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  have hsum : 0 ≤ (character r x).arg + 2 * B.radius := by linarith [harg.1]
  exact div_nonneg (mul_nonneg (by norm_num) hsum) hB.le

lemma localScaledArg_le_eight (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    localScaledArg B (character r x) ≤ 8 := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  rw [div_le_iff₀ hB]
  linarith

noncomputable def localArgBin (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) (r : ↥B.frequencies) : Fin 9 :=
  ⟨⌊localScaledArg B (character r.1 x.1)⌋₊, by
    rw [Nat.floor_lt' (by norm_num : (9 : ℕ) ≠ 0)]
    exact (localScaledArg_le_eight B hB x.2 r.2).trans_lt (by norm_num)⟩

noncomputable def localArgumentCode (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) : (r : ↥B.frequencies) → Fin 9 :=
  fun r ↦ localArgBin B hB x r

@[simp] lemma card_localArgumentCodeSpace (B : Set N) :
    Fintype.card ((r : ↥B.frequencies) → Fin 9) = 9 ^ B.rank := by
  simp [Set.rank]

lemma abs_localScaledArg_sub_lt_one_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |localScaledArg B (character r.1 x.1) -
      localScaledArg B (character r.1 y.1)| < 1 := by
  have hfloor :
      ⌊localScaledArg B (character r.1 x.1)⌋₊ =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ := by
    exact_mod_cast hfloor
  have hxlow :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 x.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB x.2 r.2)
  have hylow :
      (⌊localScaledArg B (character r.1 y.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 y.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB y.2 r.2)
  have hxup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 x.1))
  have hyup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 y.1))
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_half_radius_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |(character r.1 x.1).arg - (character r.1 y.1).arg| < B.radius / 2 := by
  have h := abs_localScaledArg_sub_lt_one_of_localArgBin_eq B hB hbin
  have hscale :
      |localScaledArg B (character r.1 x.1) -
        localScaledArg B (character r.1 y.1)| =
      2 * |(character r.1 x.1).arg - (character r.1 y.1).arg| / B.radius := by
    have heq :
        localScaledArg B (character r.1 x.1) -
          localScaledArg B (character r.1 y.1) =
        2 * ((character r.1 x.1).arg - (character r.1 y.1).arg) /
          B.radius := by
      unfold localScaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [hscale] at h
  rw [div_lt_iff₀ hB] at h
  linarith

lemma sub_mem_half_dilate_of_localArgumentCode_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    (hcode : localArgumentCode B hB x = localArgumentCode B hB y) :
    x.1 - y.1 ∈ B.dilate (1 / 2 : ℝ) := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : localArgBin B hB x ⟨r, hr⟩ =
      localArgBin B hB y ⟨r, hr⟩ := congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x.1 - y.1)‖ =
        ‖character r x.1 - character r y.1‖ :=
      norm_one_sub_character_sub r x.1 y.1
    _ ≤ |(character r x.1).arg - (character r y.1).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one
        (norm_character r x.1) (norm_character r y.1)
    _ ≤ B.radius / 2 :=
      (abs_arg_sub_lt_half_radius_of_localArgBin_eq B hB hbin).le
    _ = (B.dilate (1 / 2 : ℝ)).radius := by
      simp [div_eq_mul_inv, mul_comm]

theorem card_carrier_le_nine_pow_rank_mul_card_half
    (B : Set N) (hB : 0 < B.radius) :
    B.carrier.card ≤ 9 ^ B.rank * (B.dilate (1 / 2 : ℝ)).carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin 9
  let code : ↥B.carrier → Q := localArgumentCode B hB
  have hQ : Fintype.card Q = 9 ^ B.rank := by
    simpa [Q] using card_localArgumentCodeSpace B
  have hmain : Fintype.card ↥B.carrier ≤
      Fintype.card Q * (B.dilate (1 / 2 : ℝ)).carrier.card := by
    by_contra hbound
    rw [not_le] at hbound
    obtain ⟨q, hq⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hbound
    let S : Finset ↥B.carrier := Finset.univ.filter fun x ↦ code x = q
    have hScard : (B.dilate (1 / 2 : ℝ)).carrier.card < S.card := by
      simpa [S] using hq
    have hSnonempty : S.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hScard)
    obtain ⟨x₀, hx₀⟩ := hSnonempty
    let e : ↥B.carrier ↪ ZMod N :=
      ⟨fun x ↦ x.1 - x₀.1, by
        intro x y hxy
        apply Subtype.ext
        exact (Equiv.subRight x₀.1).injective hxy⟩
    have hmap : S.map e ⊆ (B.dilate (1 / 2 : ℝ)).carrier := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      have hcodex : code x = q := by simpa [S] using hxS
      have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
      exact sub_mem_half_dilate_of_localArgumentCode_eq B hB
        (hcodex.trans hcodex₀.symm)
    have hle : S.card ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := by
      calc
        S.card = (S.map e).card := (Finset.card_map e).symm
        _ ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := Finset.card_le_card hmap
    omega
  rw [hQ] at hmain
  have hcardcoe : Fintype.card ↥B.carrier = B.carrier.card :=
    Fintype.card_coe B.carrier
  rw [hcardcoe] at hmain
  exact hmain

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

lemma norm_one_sub_prod_le_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (norm_one_sub_mul_of_norm_le_one (hf a (by simp))).trans
        (add_le_add le_rfl (ih fun i hi ↦ hf i (by simp [hi])))

@[simp] lemma character_neg_index (r x : ZMod N) :
    character (-r) x = (starRingEnd ℂ) (character r x) := by
  rw [character_comm, AddChar.map_neg_eq_conj, character_comm]

@[simp]
lemma norm_one_sub_character_neg_index (r x : ZMod N) :
    ‖1 - character (-r) x‖ = ‖1 - character r x‖ := by
  rw [character_neg_index]
  simpa using (RCLike.norm_conj (1 - character r x))

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

lemma character_eq_one_mul {N : ℕ} [NeZero N] (r x : ZMod N) :
    character r x = character 1 (r * x) := by
  change (↑(AddChar.zmod N r x) : ℂ) = ↑(AddChar.zmod N 1 (r * x))
  simp [AddChar.zmod]

lemma norm_one_sub_character_intCast {N : ℕ} [NeZero N] (t : ℤ) :
    ‖1 - character 1 (t : ZMod N)‖ ≤ 8 * |(t : ℝ)| / N := by
  change ‖1 - (↑(AddChar.zmod N 1 (t : ZMod N)) : ℂ)‖ ≤ _
  rw [show (1 : ZMod N) = ((1 : ℤ) : ZMod N) by simp]
  rw [AddChar.zmod_intCast, Circle.coe_exp, norm_sub_rev]
  simp only [Int.cast_one, one_mul]
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hnorm : ‖Complex.exp ((2 * Real.pi * ((t : ℝ) / N) : ℝ) *
      Complex.I) - 1‖ ≤ |2 * Real.pi * ((t : ℝ) / N)| := by
    simpa only [mul_comm, Real.norm_eq_abs]
      using (Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * ((t : ℝ) / N)))
  refine hnorm.trans ?_
  rw [← mul_div_assoc, abs_div, abs_mul, abs_mul, abs_of_pos hN,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  linarith [Real.pi_le_four]

lemma norm_one_sub_character_le_of_mul_eq_intCast {N : ℕ} [NeZero N]
    (r x : ZMod N) (t : ℤ) (h : r * x = (t : ZMod N)) :
    ‖1 - character r x‖ ≤ 8 * |(t : ℝ)| / N := by
  rw [character_eq_one_mul, h]
  exact norm_one_sub_character_intCast t

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem card_two_le_nine_pow_three_rank_mul_card_quarter (B : Set N) (hB : 0 < B.radius) :
    (B.dilate 2).carrier.card ≤ 9 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate 2)
    (show 0 < (B.dilate 2).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hB)
  have h₁ := card_carrier_le_nine_pow_rank_mul_card_half B hB
  have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate (1 / 2))
    (show 0 < (B.dilate (1 / 2)).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hB)
  simp only [Set.rank_dilate, Set.dilate_dilate] at h₂ hh
  norm_num at h₂ hh
  calc
    _ ≤ 9 ^ B.rank * B.carrier.card := h₂
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := Nat.mul_le_mul_left _ h₁
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem card_le_dyadic_dilate (B : Set N) (hB : 0 < B.radius) (k : ℕ) :
    B.carrier.card ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (B.dilate ((1 / 2 : ℝ) ^ k)).radius := by
      simp only [Set.radius_dilate, abs_of_nonneg (pow_nonneg (by norm_num) _)]
      positivity
    have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate ((1 / 2 : ℝ) ^ k)) hpos
    have heq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ, mul_comm]
    simp only [Set.rank_dilate, Set.dilate_dilate, heq] at hh
    calc
      _ ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := ih
      _ ≤ 9 ^ (k * B.rank) *
          (9 ^ B.rank * (B.dilate ((1 / 2 : ℝ) ^ (k + 1))).carrier.card) := Nat.mul_le_mul_left _ hh
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul, pow_add, mul_assoc]

theorem relative_card_lower_bound (B : Set N) (hB : 0 < B.radius)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (r / 2) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ (B.dilate r).carrier.card := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let k := n + 1
  have hk : (1 / 2 : ℝ) ^ k ≤ r := hn.le
  have hhalf : r / 2 ≤ (1 / 2 : ℝ) ^ k := by
    dsimp [k]
    rw [pow_succ]
    nlinarith
  have hd := card_le_dyadic_dilate B hB k
  have hdR : (B.carrier.card : ℝ) ≤
      (9 : ℝ) ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by exact_mod_cast hd
  have hcoef : ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * 9 ^ (k * B.rank) ≤ 1 := by
    calc
      _ = ((1 / 2 : ℝ) ^ 4) ^ (k * B.rank) * 9 ^ (k * B.rank) := by
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = ((1 / 2 : ℝ) ^ 4 * 9) ^ (k * B.rank) := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * B.carrier.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (Nat.cast_nonneg _)
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) *
        (9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card) :=
      mul_le_mul_of_nonneg_left hdR (by positivity)
    _ ≤ 1 * ((B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ ≤ (B.dilate r).carrier.card := by
      rw [one_mul]
      exact_mod_cast Finset.card_le_card (B.dilate_mono (pow_nonneg (by norm_num) _) hk)

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr.Set

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuarticBohrProgression
namespace OAI

section

open scoped BigOperators Matrix Pointwise

namespace Erdos3.BohrProgression

open Erdos3.BohrLattice.BoxCertificate
open Erdos3.BohrLattice.MinkowskiSecondBox

noncomputable section

noncomputable def indexedCyclicCharacter {N : ℕ}
    (Gamma : Finset (ZMod N)) : Fin (Gamma.card + 1) → ZMod N :=
  Fin.cases 1 fun i => (Gamma.equivFin.symm i : Gamma)

@[simp] lemma indexedCyclicCharacter_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) : indexedCyclicCharacter Gamma 0 = 1 := rfl

def bohrLatticeMatrixInt {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℤ :=
  fun i j => if j = 0 then ((indexedCyclicCharacter Gamma i).val : ℤ)
    else if i = j then (N : ℤ) else 0

def bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
  (bohrLatticeMatrixInt Gamma).map (Int.castRingHom ℝ)

@[simp] lemma bohrLatticeMatrixInt_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixInt Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixInt, (Fin.succ_ne_zero j).symm]

@[simp] lemma bohrLatticeMatrix_zero_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    bohrLatticeMatrix Gamma 0 0 = 1 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1)]

@[simp] lemma bohrLatticeMatrix_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrix]

@[simp] lemma bohrLatticeMatrix_succ_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (i j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma i.succ j.succ =
      if i = j then (N : ℝ) else 0 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, Fin.succ_inj]

lemma det_bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det = (N : ℝ) ^ Gamma.card := by
  have hminor :
      (bohrLatticeMatrix Gamma).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.diagonal (fun _ : Fin Gamma.card => (N : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_apply]
    simp [Matrix.submatrix]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bohrLatticeMatrix_zero_zero Gamma hN, bohrLatticeMatrix_zero_succ]
  rw [hminor]
  rw [Matrix.det_diagonal]
  simp

lemma det_bohrLatticeMatrix_ne_zero {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det ≠ 0 := by
  rw [det_bohrLatticeMatrix Gamma hN]
  positivity

noncomputable def bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Module.Basis (Fin (Gamma.card + 1)) ℝ
      (Fin (Gamma.card + 1) → ℝ) :=
  matrixBasis (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN)

@[simp] lemma bohrLatticeBasis_apply {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (j i : Fin (Gamma.card + 1)) :
    bohrLatticeBasis Gamma hN j i = bohrLatticeMatrix Gamma i j := by
  exact congrFun (matrixBasis_apply (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN) j) i

def bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  Matrix.mulVec (bohrLatticeMatrixInt Gamma) z

lemma intCastVec_bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) :
    intCastVec (bohrLatticePoint Gamma z) =
      Matrix.mulVec (bohrLatticeMatrix Gamma) (intCastVec z) := by
  funext i
  simp [bohrLatticePoint, bohrLatticeMatrix, Matrix.mulVec, dotProduct,
    intCastVec]

lemma bohrLatticePoint_zero {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (z : Fin (Gamma.card + 1) → ℤ) :
    bohrLatticePoint Gamma z 0 = z 0 := by
  simp [bohrLatticePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1),
    (fun x : Fin Gamma.card => (Fin.succ_ne_zero x).symm)]

lemma bohrLatticePoint_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (z : Fin (Gamma.card + 1) → ℤ)
    (hN : 1 < N)
    (i : Fin (Gamma.card + 1)) :
    (bohrLatticePoint Gamma z i : ZMod N) =
      (bohrLatticePoint Gamma z 0 : ZMod N) *
        indexedCyclicCharacter Gamma i := by
  rw [bohrLatticePoint_zero Gamma hN]
  simp only [bohrLatticePoint, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixInt]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [mul_comm]

structure CyclicCenteredGAP (N : ℕ) where
  rank : ℕ
  step : Fin rank → ZMod N
  radius : Fin rank → ℕ

namespace CyclicCenteredGAP

abbrev Param {N : ℕ} (Q : CyclicCenteredGAP N) :=
  (i : Fin Q.rank) → Fin (2 * Q.radius i + 1)

def coeff {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) : ℤ := (x i : ℤ) - Q.radius i

def eval {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param) : ZMod N :=
  ∑ i, (Q.coeff x i : ZMod N) * Q.step i

noncomputable def carrier {N : ℕ} (Q : CyclicCenteredGAP N) : Finset (ZMod N) :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper {N : ℕ} (Q : CyclicCenteredGAP N) : Prop :=
  Function.Injective Q.eval

lemma card_carrier_of_proper {N : ℕ} (Q : CyclicCenteredGAP N)
    (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (2 * Q.radius i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

lemma coeff_abs_le {N : ℕ} (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i| ≤ (Q.radius i : ℤ) := by
  change |(x i : ℤ) - Q.radius i| ≤ (Q.radius i : ℤ)
  rw [abs_le]
  have hi := (x i).isLt
  change (x i : ℕ) < 2 * Q.radius i + 1 at hi
  constructor <;> omega

lemma coeff_sub_abs_le_two_mul {N : ℕ} (Q : CyclicCenteredGAP N)
    (x y : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i - Q.coeff y i| ≤ (2 * Q.radius i : ℕ) := by
  calc
    |Q.coeff x i - Q.coeff y i| ≤
        |Q.coeff x i| + |Q.coeff y i| := abs_sub _ _
    _ ≤ (Q.radius i : ℤ) + Q.radius i :=
      add_le_add (Q.coeff_abs_le x i) (Q.coeff_abs_le y i)
    _ = (2 * Q.radius i : ℕ) := by push_cast; ring

end CyclicCenteredGAP

noncomputable def bohrSuccessiveCertificate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range (bohrLatticeBasis Gamma hN))).toAddSubgroup
      (fun _ => R)
      (minkowskiSecondConstant (Gamma.card + 1) *
        |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
          (∏ _i : Fin (Gamma.card + 1), R)⁻¹) :=
  Classical.choice
    (realBox_has_minkowskiSecondCertificate
      (bohrLatticeBasis Gamma hN) (fun _ => R) (fun _ => hR))

noncomputable def bohrCertificateCoeff {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  Classical.choose
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

lemma bohrCertificateCoeff_spec {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    ∑ j, bohrCertificateCoeff Gamma hN R hR i j •
        bohrLatticeBasis Gamma hN j =
      (bohrSuccessiveCertificate Gamma hN R hR).point i :=
  Classical.choose_spec
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

noncomputable def bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  bohrLatticePoint Gamma (bohrCertificateCoeff Gamma hN R hR i)

lemma intCastVec_bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    intCastVec (bohrCertificatePoint Gamma hN R hR i) =
      (bohrSuccessiveCertificate Gamma hN R hR).point i := by
  rw [bohrCertificatePoint, intCastVec_bohrLatticePoint]
  rw [← bohrCertificateCoeff_spec Gamma hN R hR i]
  funext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bohrLatticeBasis_apply]
  simp [intCastVec, mul_comm]

lemma bohrCertificatePoint_independent {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    LinearIndependent ℝ (fun i =>
      intCastVec (bohrCertificatePoint Gamma hN R hR i)) := by
  simpa only [intCastVec_bohrCertificatePoint] using
    (bohrSuccessiveCertificate Gamma hN R hR).independent

lemma bohrCertificate_scale_pos {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hs := C.scale_nonneg i
  refine hs.lt_of_ne ?_
  intro hz
  have hpzero : C.point i = 0 := by
    have hm := C.mem_scaledBox i
    rw [← hz, zero_smul] at hm
    ext j
    have hlo := hm.1 j
    have hhi := hm.2 j
    simp only [Pi.zero_apply, neg_zero] at hlo hhi
    exact le_antisymm hhi hlo
  exact C.independent.ne_zero i hpzero

noncomputable def bohrProgressionRadius {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : ℕ :=
  ⌊((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹⌋₊

noncomputable def bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    CyclicCenteredGAP N where
  rank := Gamma.card + 1
  step i := (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N)
  radius := bohrProgressionRadius Gamma hN R hR

lemma bohrProgressionRadius_mul_scale_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (bohrProgressionRadius Gamma hN R hR i : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i ≤
      1 / (4 * (Gamma.card + 1) : ℝ) := by
  let s := (bohrSuccessiveCertificate Gamma hN R hR).scale i
  have hs : 0 < s := bohrCertificate_scale_pos Gamma hN R hR i
  have hm : (0 : ℝ) < 4 * (Gamma.card + 1) := by positivity
  have hfloor :
      (bohrProgressionRadius Gamma hN R hR i : ℝ) ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ := by
    apply Nat.floor_le
    positivity
  calc
    (bohrProgressionRadius Gamma hN R hR i : ℝ) * s ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ * s :=
      mul_le_mul_of_nonneg_right hfloor hs.le
    _ = 1 / (4 * (Gamma.card + 1) : ℝ) := by
      field_simp

lemma abs_intCast_bohrCertificatePoint_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i j : Fin (Gamma.card + 1)) :
    |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      (bohrSuccessiveCertificate Gamma hN R hR).scale i * R := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hm := C.mem_scaledBox i
  have hlo := hm.1 j
  have hhi := hm.2 j
  rw [← intCastVec_bohrCertificatePoint Gamma hN R hR i] at hlo hhi
  change -(C.scale i * R) ≤
      (bohrCertificatePoint Gamma hN R hR i j : ℝ) at hlo
  change (bohrCertificatePoint Gamma hN R hR i j : ℝ) ≤
      C.scale i * R at hhi
  exact (abs_le.mpr ⟨hlo, hhi⟩)

def bohrCertificateCombination {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  fun j => ∑ i, u i * bohrCertificatePoint Gamma hN R hR i j

lemma bohrCertificateCombination_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) (j : Fin (Gamma.card + 1)) :
    (bohrCertificateCombination Gamma hN R hR u j : ZMod N) =
      (bohrCertificateCombination Gamma hN R hR u 0 : ZMod N) *
        indexedCyclicCharacter Gamma j := by
  simp only [bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := bohrLatticePoint_cast_coordinate Gamma
    (bohrCertificateCoeff Gamma hN R hR i) hN j
  change (bohrCertificatePoint Gamma hN R hR i j : ZMod N) =
    (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N) *
      indexedCyclicCharacter Gamma j at hp
  rw [hp]
  ring

lemma abs_intCast_bohrCertificateCombination_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (a : ℕ) (u : Fin (Gamma.card + 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (a * bohrProgressionRadius Gamma hN R hR i : ℕ))
    (j : Fin (Gamma.card + 1)) :
    |(bohrCertificateCombination Gamma hN R hR u j : ℝ)| ≤
      (a : ℝ) * R / 4 := by
  let m := Gamma.card + 1
  have hm : (0 : ℝ) < m := by positivity
  have hR0 : 0 ≤ R := hR.le
  have hterm (i : Fin m) :
      |(u i : ℝ) *
          (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        (a : ℝ) * R / (4 * m : ℝ) := by
    rw [abs_mul]
    have huR : |(u i : ℝ)| ≤
        (a : ℝ) * bohrProgressionRadius Gamma hN R hR i := by
      rw [← Int.cast_abs]
      exact_mod_cast hu i
    calc
      |(u i : ℝ)| *
          |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        ((a : ℝ) * bohrProgressionRadius Gamma hN R hR i) *
          ((bohrSuccessiveCertificate Gamma hN R hR).scale i * R) := by
            gcongr
            exact abs_intCast_bohrCertificatePoint_le Gamma hN R hR i j
      _ = (a : ℝ) *
          ((bohrProgressionRadius Gamma hN R hR i : ℝ) *
            (bohrSuccessiveCertificate Gamma hN R hR).scale i) * R := by ring
      _ ≤ (a : ℝ) * (1 / (4 * m : ℝ)) * R := by
        gcongr
        simpa [m, Nat.cast_add, Nat.cast_one] using
          bohrProgressionRadius_mul_scale_le Gamma hN R hR i
      _ = (a : ℝ) * R / (4 * m : ℝ) := by ring
  have hcast : (bohrCertificateCombination Gamma hN R hR u j : ℝ) =
      ∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ) := by
    simp [bohrCertificateCombination]
  rw [hcast]
  calc
    |∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      ∑ i, |(u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ((a : ℝ) * R / (4 * m : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = (a : ℝ) * R / 4 := by
      simp [m]
      field_simp

lemma eval_bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (x : (bohrCyclicProgression Gamma hN R hR).Param) :
    (bohrCyclicProgression Gamma hN R hR).eval x =
      (bohrCertificateCombination Gamma hN R hR
        ((bohrCyclicProgression Gamma hN R hR).coeff x) 0 : ZMod N) := by
  simp only [CyclicCenteredGAP.eval, bohrCyclicProgression,
    bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt {N : ℕ} [NeZero N]
    {t : ℤ} (ht0 : (t : ZMod N) = 0) (htN : |(t : ℝ)| < N) : t = 0 := by
  have hdvd : (N : ℤ) ∣ t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd t N).mp ht0
  have habs : (t.natAbs : ℝ) = |(t : ℝ)| := by
    calc
      (t.natAbs : ℝ) = (((t.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|t| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(t : ℝ)| := Int.cast_abs
  have hnat : t.natAbs < N := by
    exact_mod_cast (habs.trans_lt htN)
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simpa using hnat

theorem bohrCyclicProgression_proper {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    (bohrCyclicProgression Gamma hN R hR).Proper := by
  let Q := bohrCyclicProgression Gamma hN R hR
  intro x y hxy
  let u : Fin (Gamma.card + 1) → ℤ := fun i => Q.coeff x i - Q.coeff y i
  let v := bohrCertificateCombination Gamma hN R hR u
  have hu (i : Fin (Gamma.card + 1)) :
      |u i| ≤ (2 * bohrProgressionRadius Gamma hN R hR i : ℕ) := by
    exact CyclicCenteredGAP.coeff_sub_abs_le_two_mul Q x y i
  have hv0cast : (v 0 : ZMod N) = 0 := by
    have hx := eval_bohrCyclicProgression Gamma hN R hR x
    have hy := eval_bohrCyclicProgression Gamma hN R hR y
    have hvsub : (v 0 : ZMod N) =
        (bohrCyclicProgression Gamma hN R hR).eval x -
          (bohrCyclicProgression Gamma hN R hR).eval y := by
      rw [hx, hy]
      simp only [v, u, bohrCertificateCombination, Int.cast_sum, Int.cast_mul,
        Int.cast_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hvsub, hxy, sub_self]
  have hvcast (j : Fin (Gamma.card + 1)) : (v j : ZMod N) = 0 := by
    rw [bohrCertificateCombination_cast_coordinate Gamma hN R hR u j,
      hv0cast, zero_mul]
  have hvabs (j : Fin (Gamma.card + 1)) : |(v j : ℝ)| ≤ R / 2 := by
    convert abs_intCast_bohrCertificateCombination_le Gamma hN R hR 2 u hu j
      using 1; norm_num; ring
  have hvzero : v = 0 := by
    funext j
    apply int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt (hvcast j)
    exact (hvabs j).trans_lt (by linarith)
  have hsum : ∑ i, (u i : ℝ) •
      intCastVec (bohrCertificatePoint Gamma hN R hR i) = 0 := by
    funext j
    have hj := congrFun hvzero j
    have hjR : (v j : ℝ) = 0 := by exact_mod_cast hj
    simpa [v, bohrCertificateCombination, intCastVec] using hjR
  have huR : ∀ i, (u i : ℝ) = 0 :=
    (Fintype.linearIndependent_iff.mp
      (bohrCertificatePoint_independent Gamma hN R hR)) _ hsum
  have hu0 : u = 0 := by
    funext i
    change u i = 0
    exact_mod_cast huR i
  funext i
  apply Fin.ext
  have hi0 : u i = 0 := by
    change u i = (0 : Fin (Gamma.card + 1) → ℤ) i
    exact congrFun hu0 i
  have hi : (x i : ℤ) = (y i : ℤ) := by
    dsimp only [u, Q] at hi0
    simp only [CyclicCenteredGAP.coeff] at hi0
    omega
  exact_mod_cast hi

lemma matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Matrix.of (bohrLatticeBasis Gamma hN) =
      (bohrLatticeMatrix Gamma)ᵀ := by
  ext i j
  rw [Matrix.of_apply, Matrix.transpose_apply]
  exact bohrLatticeBasis_apply Gamma hN i j

lemma abs_det_matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| =
      (N : ℝ) ^ Gamma.card := by
  rw [matrixOf_bohrLatticeBasis Gamma hN,
    Matrix.det_transpose, det_bohrLatticeMatrix Gamma hN, abs_of_nonneg]
  positivity

lemma inv_scale_le_two_mul_bohrProgressionRadius_add_one
    {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (((4 * (Gamma.card + 1) : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) ≤
      2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 := by
  have hlt := Nat.lt_floor_add_one
    (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹)
  change (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) <
    (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 at hlt
  have hradius : 0 ≤ (bohrProgressionRadius Gamma hN R hR i : ℝ) := by
    positivity
  linarith

theorem bohrCyclicProgression_card_lower_bound {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) ≤
      ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
  let c : ℝ := 4 * (Gamma.card + 1)
  let B : ℝ := minkowskiSecondConstant (Gamma.card + 1) *
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
      (∏ _i : Fin (Gamma.card + 1), R)⁻¹
  have hc : 0 < c := by positivity
  have hscale (i : Fin (Gamma.card + 1)) :
      0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact bohrCertificate_scale_pos Gamma hN R hR i
  have hprodscale : 0 <
      ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact Finset.prod_pos fun i _ => hscale i
  have hB : 0 < B := by
    simp only [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    unfold minkowskiSecondConstant
    positivity
  have hcertificate :
      (∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i) ≤ B := by
    exact (bohrSuccessiveCertificate Gamma hN R hR).product_le
  have hreciprocal : (c ^ (Gamma.card + 1) * B)⁻¹ ≤
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
    apply (inv_le_inv₀ (mul_pos (pow_pos hc _) hB)
      (mul_pos (pow_pos hc _) hprodscale)).2
    exact mul_le_mul_of_nonneg_left hcertificate (pow_nonneg hc.le _)
  have hproduct :
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ ≤
      ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
    calc
      (c ^ (Gamma.card + 1) *
          ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ =
          (∏ i : Fin (Gamma.card + 1),
            c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            congr 1
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin (Gamma.card + 1),
          (c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            rw [Finset.prod_inv_distrib]
      _ ≤ ∏ i : Fin (Gamma.card + 1),
          (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact inv_nonneg.mpr (mul_nonneg hc.le
                ((bohrSuccessiveCertificate Gamma hN R hR).scale_nonneg i))
            · intro i hi
              simpa [c] using
                inv_scale_le_two_mul_bohrProgressionRadius_add_one
                  Gamma hN R hR i
  have hcard := CyclicCenteredGAP.card_carrier_of_proper
    (bohrCyclicProgression Gamma hN R hR)
    (bohrCyclicProgression_proper Gamma hN R hR hsmall)
  have hBform : B = minkowskiSecondConstant (Gamma.card + 1) *
      (N : ℝ) ^ Gamma.card * (R ^ (Gamma.card + 1))⁻¹ := by
    simp [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const]
  calc
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) =
        (c ^ (Gamma.card + 1) * B)⁻¹ := by
      rw [hBform]
    _ ≤ (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ :=
      hreciprocal
    _ ≤ ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := hproduct
    _ = ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
      rw [hcard]
      norm_cast

end

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open scoped BigOperators
open BohrLattice.MinkowskiSecondBox

theorem bohrCyclicProgression_carrier_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : 2 * R ≤ B.radius * N) :
    (bohrCyclicProgression B.frequencies hN R hR).carrier ⊆ B.carrier := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
  rw [CyclicBohr.Set.mem_carrier]
  intro k hk
  let Γ := B.frequencies
  let i : Fin Γ.card := Γ.equivFin ⟨k, hk⟩
  let u : Fin (Γ.card + 1) → ℤ :=
    (bohrCyclicProgression Γ hN R hR).coeff x
  let v := bohrCertificateCombination Γ hN R hR u
  have hu (j : Fin (Γ.card + 1)) :
      |u j| ≤ (bohrProgressionRadius Γ hN R hR j : ℕ) :=
    CyclicCenteredGAP.coeff_abs_le (bohrCyclicProgression Γ hN R hR) x j
  have heval : (bohrCyclicProgression Γ hN R hR).eval x = (v 0 : ZMod N) :=
    eval_bohrCyclicProgression Γ hN R hR x
  have hchar : indexedCyclicCharacter Γ i.succ = k := by
    change ((Γ.equivFin.symm i : Γ) : ZMod N) = k
    simp [i]
  have hvchar : k * (bohrCyclicProgression Γ hN R hR).eval x =
      (v i.succ : ZMod N) := by
    rw [bohrCertificateCombination_cast_coordinate Γ hN R hR u i.succ,
      hchar, heval, mul_comm]
  have hvabs : |(v i.succ : ℝ)| ≤ R / 4 := by
    simpa using abs_intCast_bohrCertificateCombination_le Γ hN R hR 1 u
      (by simpa using hu) i.succ
  refine (CyclicBohr.norm_one_sub_character_le_of_mul_eq_intCast
    k _ (v i.succ) hvchar).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply (div_le_iff₀ hNpos).2
  nlinarith

theorem exists_proper_progression_subset {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1) ≤ (Q.carrier.card : ℝ) := by
  let R := B.radius * N / 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : R < 2 * N := by dsimp [R]; nlinarith
  refine ⟨bohrCyclicProgression B.frequencies hN R hR, rfl,
    bohrCyclicProgression_proper B.frequencies hN R hR hsmall,
    bohrCyclicProgression_carrier_subset B hN R hR (by dsimp [R]; linarith), ?_⟩
  have hcard := bohrCyclicProgression_card_lower_bound B.frequencies hN R hR hsmall
  have hn : (0 : ℝ) < B.rank + 1 := by positivity
  have hc : 0 < minkowskiSecondConstant (B.rank + 1) := by
    unfold minkowskiSecondConstant
    positivity
  have heq :
      (N : ℝ) * (B.radius / (8 * (B.rank + 1))) ^ (B.rank + 1) /
          minkowskiSecondConstant (B.rank + 1) =
        (((4 * (B.rank + 1) : ℝ) ^ (B.rank + 1)) *
          (minkowskiSecondConstant (B.rank + 1) * (N : ℝ) ^ B.rank *
            (R ^ (B.rank + 1))⁻¹))⁻¹ := by
    dsimp [R]
    simp only [div_pow, mul_pow, pow_succ, mul_inv_rev, inv_inv]
    field_simp
    rw [show (8 : ℝ) ^ B.rank = (2 : ℝ) ^ B.rank * 4 ^ B.rank by
      rw [← mul_pow]; norm_num]
    ring
  rw [heq]
  exact hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

open BohrLattice.MinkowskiSecondBox

lemma minkowskiSecondConstant_le_exp (m : ℕ) :
    minkowskiSecondConstant m ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
  have hidx : m * (m - 1) / 2 ≤ m * m :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left m (Nat.sub_le m 1))
  have hcast : ((m * (m - 1) / 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast hidx
  calc
    minkowskiSecondConstant m = (2 : ℝ) ^ (m * (m - 1) / 2) := rfl
    _ ≤ Real.exp 2 ^ (m * (m - 1) / 2) := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = Real.exp (((m * (m - 1) / 2 : ℕ) : ℝ) * 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 * (m : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      linarith

lemma progression_size_factor_lower_bound (m : ℕ) (hm : 0 < m)
    {w δ : ℝ} (hδ : Real.exp (-w) ≤ δ) :
    Real.exp (-((m : ℝ) * w + 10 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m / minkowskiSecondConstant m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 8 * m := by positivity
  have hrecip : Real.exp (-(8 * m : ℝ)) ≤ (8 * m : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) hden).2
    linarith [Real.add_one_le_exp (8 * m : ℝ)]
  have hbase : Real.exp (-(w + 8 * m)) ≤ δ / (8 * m) := by
    calc
      Real.exp (-(w + 8 * m)) = Real.exp (-w) * Real.exp (-(8 * m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ δ * (8 * m : ℝ)⁻¹ :=
        mul_le_mul hδ hrecip (Real.exp_pos _).le ((Real.exp_pos _).le.trans hδ)
      _ = δ / (8 * m) := by rw [div_eq_mul_inv]
  have hpower : Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) ≤
      (δ / (8 * m)) ^ m := by
    calc
      _ = Real.exp (-(w + 8 * m)) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hbase _
  have hc : 0 < minkowskiSecondConstant m := by
    unfold minkowskiSecondConstant
    positivity
  have hinv : Real.exp (-(2 * (m : ℝ) ^ 2)) ≤ (minkowskiSecondConstant m)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hc).2 (minkowskiSecondConstant_le_exp m)
  calc
    _ = Real.exp (-((m : ℝ) * w + 8 * (m : ℝ) ^ 2)) *
        Real.exp (-(2 * (m : ℝ) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (δ / (8 * m)) ^ m * (minkowskiSecondConstant m)⁻¹ :=
      mul_le_mul hpower hinv (Real.exp_pos _).le ((Real.exp_pos _).le.trans hpower)
    _ = _ := by simp only [div_eq_mul_inv]

theorem exists_large_proper_progression {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hN : 1 < N) {w : ℝ} (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank = B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_proper_progression_subset B hB hB1 hN
  refine ⟨Q, hr, hQ, hsub, ?_⟩
  have hfactor := progression_size_factor_lower_bound (B.rank + 1) (by omega) hwidth
  push_cast at hfactor
  calc
    _ ≤ ((B.radius / (8 * ((B.rank : ℝ) + 1))) ^ (B.rank + 1) /
        minkowskiSecondConstant (B.rank + 1)) * N :=
      mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg N)
    _ = _ := by ring
    _ ≤ _ := hcard

end Erdos3.BohrProgression

end

section

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

def zero (N : ℕ) : CyclicCenteredGAP N where
  rank := 0
  step := Fin.elim0
  radius := Fin.elim0

lemma zero_proper (N : ℕ) : (zero N).Proper := by
  intro x y _
  funext i
  exact Fin.elim0 i

@[simp] lemma zero_carrier (N : ℕ) : (zero N).carrier = {0} := by
  have heval : (zero N).eval = fun _ => 0 := by
    funext x
    unfold eval
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
  rw [carrier, heval]
  exact Finset.image_const ⟨(fun i => Fin.elim0 i), Finset.mem_univ _⟩ 0

end CyclicCenteredGAP

theorem exists_large_proper_progression_all {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank ≤ B.rank + 1 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2)) * N ≤
        (Q.carrier.card : ℝ) := by
  by_cases hN : 1 < N
  · obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression B hB hB1 hN hwidth
    exact ⟨Q, hr.le, hQ, hsub, hcard⟩
  · have hNeq : N = 1 := by have := NeZero.pos N; omega
    subst N
    refine ⟨CyclicCenteredGAP.zero 1, by simp [CyclicCenteredGAP.zero],
      CyclicCenteredGAP.zero_proper 1, ?_, ?_⟩
    · intro x hx
      rw [CyclicCenteredGAP.zero_carrier, Finset.mem_singleton] at hx
      subst x
      exact B.zero_mem
    · simp only [CyclicCenteredGAP.zero_carrier, Finset.card_singleton, Nat.cast_one,
        mul_one]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ ((B.rank : ℝ) + 1) * w + 10 * ((B.rank : ℝ) + 1) ^ 2 := by positivity
      linarith

theorem exists_proper_progression_of_quartic_bounds {N : ℕ} [NeZero N]
    (B : CyclicBohr.Set N) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hB : 0 < B.radius) (hB1 : B.radius ≤ 1)
    (hrank : (B.rank : ℝ) ≤ 1 + C * (p + 1) ^ 4)
    (hwidth : Real.exp (-(C * (p + 1))) ≤ B.radius) :
    ∃ Q : CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + C * (p + 1) ^ 4 ∧ Q.Proper ∧ Q.carrier ⊆ B.carrier ∧
      Real.exp (-(11 * (C + 2) ^ 2 * (p + 1) ^ 8)) * N ≤ (Q.carrier.card : ℝ) := by
  obtain ⟨Q, hr, hQ, hsub, hcard⟩ := exists_large_proper_progression_all B hB hB1
    (by positivity : 0 ≤ C * (p + 1)) hwidth
  have hrR : (Q.rank : ℝ) ≤ B.rank + 1 := by exact_mod_cast hr
  refine ⟨Q, by linarith, hQ, hsub, ?_⟩
  let u := p + 1
  let m := (B.rank : ℝ) + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have huu4 : u ≤ u ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hu (by decide : 1 ≤ (4 : ℕ))
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ (C + 2) * u ^ 4 := by dsimp [m]; nlinarith
  have hw : C * u ≤ (C + 2) * u ^ 4 := by nlinarith
  have hprod : m * (C * u) ≤ ((C + 2) * u ^ 4) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hm hw (by positivity : 0 ≤ C * u)
      (by positivity : 0 ≤ (C + 2) * u ^ 4)
  have hsquare : m ^ 2 ≤ ((C + 2) * u ^ 4) ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have hcost : m * (C * u) + 10 * m ^ 2 ≤ 11 * (C + 2) ^ 2 * u ^ 8 := by
    calc
      _ ≤ 11 * ((C + 2) * u ^ 4) ^ 2 := by linarith
      _ = _ := by ring
  apply le_trans (b := Real.exp (-(m * (C * u) + 10 * m ^ 2)) * N) ?_ hcard
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.BohrProgression

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def smoothAffineSample {K I : Type*} [Fintype K] (t : K → ℤ)
    (z : Option K × I → ℤ) : I → ℤ :=
  fun i => z (none, i) + ∑ k, t k * z (some k, i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

def smoothAffinePairRows {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) : I → Fin 2 → ℤ :=
  fun i => affinePairMatrix t u *ᵥ independentArrayRows z i

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateFiberPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxPointsEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) : (∀ i, S i) ≃ Fintype.piFinset S where
  toFun x := ⟨fun i => (x i).val, Fintype.mem_piFinset.mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, Fintype.mem_piFinset.mp x.property i⟩
  left_inv x := by funext i; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem finiteBoxPoints_expect {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x : Fintype.piFinset S, f x.val) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) :=
  (Fintype.expect_equiv (finiteBoxPointsEquiv S)
    (fun x => f (fun i => (x i).val)) (fun x => f x.val) (fun _ => rfl)).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def coordinateFiberParameters (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : MvPolynomial {i // keep i} ℝ :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩ : ℝ)

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberParameters_degree (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : coordinateFiberParameters keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [coordinateFiberParameters, dif_pos hi]
    exact weightedSupportLE_X _ _
  · simp only [coordinateFiberParameters, dif_neg hi]
    exact weightedSupportLE_C _ _ _

noncomputable def PolynomialPatch.coordinateFiber {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialPatch {i // keep i} s d :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

theorem PolynomialPatch.coordinateFiber_value {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) (x : {i // keep i} → ℤ) :
    (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) =
      A.value (fun i => ((finiteSplitPoint keep x fixed i : ℤ) : ℝ)) := by
  let _ : Fintype I := inferInstance
  let _ : DecidableEq I := inferInstance
  rw [coordinateFiber, reparam_value]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

theorem finiteBoxPoints_expect_finset (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x ∈ Fintype.piFinset S, f x) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) := by
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ, Finset.sum_coe_sort,
    Fintype.card_coe] using finiteBoxPoints_expect S f

theorem exists_integerBox_coordinate_fiber (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (keep : I → Prop) (f : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, f x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i), f (finiteSplitPoint keep x fixed) := by
  let X := fun i => Finset.Ico (0 : ℤ) (N i)
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => X i)
  have hn (i : I) : Nonempty (X i) :=
    ⟨⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hN i⟩⟩⟩
  let : ∀ i, Nonempty (X i) := hn
  have hsplit : (𝔼 x : (∀ i, X i), f (fun i => (x i).val)) =
      𝔼 v : (∀ i : {i // ¬keep i}, X i),
        𝔼 u : (∀ i : {i // keep i}, X i),
          f (finiteSplitPoint keep (fun i => (u i).val) (fun i => (v i).val)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, X i) × (∀ i : {i // ¬keep i}, X i),
          f (finiteSplitPoint keep (fun i => (uv.1 i).val) (fun i => (uv.2 i).val)) := by
        apply Fintype.expect_equiv e
        intro x
        change f (fun i => (x i).val) =
          f (finiteSplitPoint keep (fun i => (x i.val).val) (fun i => (x i.val).val))
        exact congrArg f (finiteSplitPoint_restrict keep (fun i => (x i).val)).symm
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  have hfull : a ≤ 𝔼 x : (∀ i, X i), f (fun i => (x i).val) := by
    rw [← finiteBoxPoints_expect_finset X f]
    exact hmean
  rw [hsplit] at hfull
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hfull
  refine ⟨fun i => (v i).val, fun i => Finset.mem_Ico.mp (v i).property, ?_⟩
  rw [← finiteBoxPoints_expect_finset (fun i : {i // keep i} => X i)
    (fun x => f (finiteSplitPoint keep x (fun i => (v i).val)))] at hv
  exact hv

theorem PolynomialPatch.exists_coordinate_fiber_score {s d : ℕ} (A : PolynomialPatch I s d)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (keep : I → Prop)
    (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, score x * A.value (fun i => (x i : ℝ))) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i),
        score (finiteSplitPoint keep x fixed) *
          (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) := by
  obtain ⟨fixed, hfixed, hscore⟩ := exists_integerBox_coordinate_fiber N hN keep
    (fun x => score x * A.value (fun i => (x i : ℝ))) hmean
  exact ⟨fixed, hfixed, by simpa only [coordinateFiber_value] using hscore⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoordinateProjectionBounds
namespace OAI

section

namespace Erdos3

open Module

theorem basisCoordinateProjection_abs_repr_le {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) (i : ι) :
    |b.repr (basisCoordinateProjection b S x) i| ≤ |b.repr x i| := by
  classical
  rw [basisCoordinateProjection_repr]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (b.repr x i)

theorem basisCoordinateProjection_norm_le {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) :
    ‖b.equivFun (basisCoordinateProjection b S x)‖ ≤ ‖b.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (basisCoordinateProjection_abs_repr_le b S x i).trans (norm_le_pi_norm (b.equivFun x) i)

theorem basisCoordinateProjection_real_grid {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (l : ℕ) (x : V) (hx : (fun i => b.repr x i) ∈ realDenominatorGrid l) :
    (fun i => b.repr (basisCoordinateProjection b S x) i) ∈ realDenominatorGrid l := by
  classical
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if i ∈ S then z i else 0, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * b.repr x i at hi
  change ((if i ∈ S then z i else 0 : ℤ) : ℝ) = (l : ℝ) * b.repr (basisCoordinateProjection b S x) i
  rw [basisCoordinateProjection_repr]
  by_cases h : i ∈ S <;> simp only [h, ↓reduceIte, Int.cast_zero, mul_zero]
  exact hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionCubeEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

structure FiniteCubeSlice (q : ℕ) where
  length : ℕ
  root : ℤ
  modulus : Option (Fin q) → ℕ
  residue : ∀ i, ZMod (modulus i)

namespace FiniteCubeSlice

def radius {q : ℕ} (s : FiniteCubeSlice q) : ℕ := s.root.natAbs + s.length

end FiniteCubeSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace FiniteCubeSlice

end FiniteCubeSlice

namespace FiniteCoefficientSlice

end FiniteCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace RetainedCubeSlice

variable {q M : ℕ}
  {B T η : ℝ≥0}

end RetainedCubeSlice

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

namespace SmoothCubeSlice

variable {q M : ℕ}
  {B T : ℝ≥0}

end SmoothCubeSlice

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

noncomputable def centeredIntegerBox (R : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(R i : ℤ)) (R i : ℤ))

@[simp] theorem mem_centeredIntegerBox (R : ι → ℕ) (x : ι → ℤ) :
    x ∈ centeredIntegerBox R ↔ ∀ i, |x i| ≤ (R i : ℤ) := by
  simp only [centeredIntegerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

@[simp] theorem card_centeredIntegerBox (R : ι → ℕ) :
    (centeredIntegerBox R).card = ∏ i, (2 * R i + 1) := by
  rw [centeredIntegerBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  omega

theorem card_doubled_centeredIntegerBox_le (R : ι → ℕ) :
    (centeredIntegerBox (fun i => 2 * R i)).card ≤
      2 ^ Fintype.card ι * (centeredIntegerBox R).card := by
  rw [card_centeredIntegerBox, card_centeredIntegerBox]
  calc
    (∏ i, (2 * (2 * R i) + 1)) ≤ ∏ i, (2 * (2 * R i + 1)) := by
      gcongr with i
      omega
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

omit [Fintype ι] [DecidableEq ι] in
theorem card_mul_le_of_kernel_translates (φ : (ι → ℤ) →+ G)
    (S X : Finset (ι → ℤ)) (k : ℕ) (v : ι → ℤ) (hv : v ≠ 0)
    (hker : φ v = 0) (hinj : Set.InjOn φ (S : Set _))
    (hsub : ∀ x ∈ S, ∀ j < k, x + j • v ∈ X) : S.card * k ≤ X.card := by
  classical
  rw [← Finset.card_range k, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : (ι → ℤ) × ℕ => z.1 + z.2 • v)
  · intro z hz
    exact hsub z.1 (Finset.mem_product.mp hz).1 z.2
      (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  · intro x hx y hy hxy
    change x.1 + x.2 • v = y.1 + y.2 • v at hxy
    have hφ : φ x.1 = φ y.1 := by
      have h := congrArg φ hxy
      simpa only [map_add, map_nsmul, hker, nsmul_zero, add_zero] using h
    have hbase : x.1 = y.1 := hinj (Finset.mem_product.mp hx).1
      (Finset.mem_product.mp hy).1 hφ
    apply Prod.ext hbase
    have hmul : x.2 • v = y.2 • v := by
      rw [hbase] at hxy
      exact add_left_cancel hxy
    have hnonzero : ¬ ∀ i, v i = 0 := fun h => hv (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnonzero
    have hiEq := congrFun hmul i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hiEq
    exact_mod_cast mul_right_cancel₀ hi hiEq

theorem kernel_eq_zero_of_dense_integer_box (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (v : ι → ℤ) (hker : φ v = 0) (hshort : ∀ i, (k : ℤ) * |v i| ≤ (R i : ℤ)) :
    v = 0 := by
  by_contra hv
  apply (not_le_of_gt hlarge)
  apply card_mul_le_of_kernel_translates φ S (centeredIntegerBox (fun i => 2 * R i)) k v hv hker hinj
  intro x hx j hj
  apply (mem_centeredIntegerBox _ _).mpr
  intro i
  have hxi := (mem_centeredIntegerBox R x).mp (hS hx) i
  have hjk : (j : ℤ) ≤ k := by exact_mod_cast hj.le
  have hbound : |x i + (j : ℤ) * v i| ≤ 2 * (R i : ℤ) := by
    calc
      _ ≤ |x i| + |(j : ℤ) * v i| := abs_add_le _ _
      _ = |x i| + (j : ℤ) * |v i| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg j)]
      _ ≤ (R i : ℤ) + (k : ℤ) * |v i| :=
        add_le_add hxi (mul_le_mul_of_nonneg_right hjk (abs_nonneg _))
      _ ≤ 2 * (R i : ℤ) := by linarith only [hshort i]
  change |x i + j • v i| ≤ ((2 * R i : ℕ) : ℤ)
  simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem injOn_small_integer_box_of_dense_subset (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R r : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (hscale : ∀ i, 2 * k * r i ≤ R i) :
    Set.InjOn φ (centeredIntegerBox r : Set _) := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply kernel_eq_zero_of_dense_integer_box φ S R k hS hinj hlarge (x - y)
  · rw [map_sub, hxy, sub_self]
  · intro i
    have hx' := (mem_centeredIntegerBox r x).mp hx i
    have hy' := (mem_centeredIntegerBox r y).mp hy i
    have hscale' : 2 * (k : ℤ) * (r i : ℤ) ≤ R i := by exact_mod_cast hscale i
    calc
      (k : ℤ) * |(x - y) i| ≤ (k : ℤ) * (|x i| + |y i|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Int.natCast_nonneg k)
      _ ≤ (k : ℤ) * ((r i : ℤ) + (r i : ℤ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hx' hy') (Int.natCast_nonneg k)
      _ = 2 * (k : ℤ) * (r i : ℤ) := by ring
      _ ≤ (R i : ℤ) := hscale'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerSites_card_le {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) (R : ℕ)
    (hbound : ∀ s k, |site s k| ≤ (R : ℤ)) :
    Fintype.card S ≤ (2*R+1)^Fintype.card K := by
  classical
  let f : S → ↥(centeredIntegerBox (fun _ : K => R)) :=
    fun s => ⟨site s, (mem_centeredIntegerBox _ _).mpr (hbound s)⟩
  have hf : Function.Injective f := fun s t h => hsite (congrArg Subtype.val h)
  simpa only [Fintype.card_coe, card_centeredIntegerBox, Finset.prod_const,
    Finset.card_univ] using Fintype.card_le_of_injective f hf

theorem integerSites_card_le_exp {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P) :
    (Fintype.card S : ℝ) ≤ Real.exp (P*(P+5)) := by
  have hcard := integerSites_card_le site hsite ⌈Real.exp P⌉₊ (fun s k => by
    exact_mod_cast (hbound s k).trans (Nat.le_ceil (Real.exp P)))
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h5 : (5 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
  have hbase : (2*⌈Real.exp P⌉₊+1 : ℝ) ≤ Real.exp (P+5) := by
    calc
      _ ≤ 5*Real.exp P := by linarith
      _ ≤ Real.exp P*Real.exp 5 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add P 5).symm
  calc
    _ ≤ ((2*⌈Real.exp P⌉₊+1 : ℕ) : ℝ)^Fintype.card K := by exact_mod_cast hcard
    _ ≤ (Real.exp (P+5))^Fintype.card K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa only [Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hbase) _
    _ = Real.exp ((Fintype.card K : ℝ)*(P+5)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK (by linarith))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem injOn_shrunk_integer_box_of_distinct_points
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (hrepr : ∀ h ∈ J, ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = a + η x) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) := by
  intro k
  classical
  have hall (h : {h // h ∈ J}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h.val = a + η x :=
    hrepr h.val h.property
  choose x hx heq using hall
  have hηx : Function.Injective (η ∘ x) := by
    intro h h' hh
    apply Subtype.ext
    rw [heq h, heq h']
    exact congrArg (fun z => a + z) hh
  have hxinj : Function.Injective x := by
    intro h h' hh
    exact hηx (congrArg η hh)
  let S := Finset.univ.image x
  have hS : S ⊆ centeredIntegerBox R := by
    intro z hz
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_centeredIntegerBox R (x h)).mpr (hx h)
  have hScard : S.card = J.card := by
    rw [show S.card = (Finset.univ.image x).card from rfl,
      Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_coe]
  have hinj : Set.InjOn η (S : Set _) := by
    intro z hz w hw hzw
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hw
    exact congrArg x (hηx hzw)
  apply injOn_small_integer_box_of_dense_subset η S R (fun i => R i / (2 * k)) k hS hinj
  · apply (card_doubled_centeredIntegerBox_le R).trans_lt
    rw [card_centeredIntegerBox, Fintype.card_fin, hScard]
    exact Nat.lt_mul_div_succ (2 ^ r * ∏ i, (2 * R i + 1)) hJ.card_pos
  · intro i
    exact Nat.mul_div_le (R i) (2 * k)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem exists_modeling_dual_obstruction (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E) (hb : b ∉ closure (R • convexHull ℝ S + X.closedBall 0 tau)) :
    ∃ f : E →L[ℂ] ℂ, 1 < (f b).re ∧
      (∀ v, tau * ‖f v‖ ≤ X v) ∧ (∀ Q ∈ S, R * ‖f Q‖ < 1) := by
  let A : Set E := R • convexHull ℝ S + X.closedBall 0 tau
  have hconv : Convex ℝ A :=
    ((convex_convexHull ℝ S).smul R).add (X.convex_closedBall 0 tau)
  have hzS : (0 : E) ∈ convexHull ℝ S := subset_convexHull ℝ S (hS.zero_mem hSn)
  have hzR : (0 : E) ∈ R • convexHull ℝ S := by
    simpa only [smul_zero] using Set.smul_mem_smul_set (a := R) hzS
  have hzBall : (0 : E) ∈ X.closedBall 0 tau := X.mem_closedBall_self htau.le
  have hz : (0 : E) ∈ A := by
    simpa only [add_zero] using Set.add_mem_add hzR hzBall
  obtain ⟨g, u, hgu, hub⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconv.closure isClosed_closure hb
  have hu : 0 < u := by simpa only [map_zero, Complex.zero_re] using hgu 0 (subset_closure hz)
  let f : E →L[ℂ] ℂ := (u⁻¹ : ℝ) • g
  have hf (v : E) : (f v).re = (g v).re / u := by
    change (u⁻¹ • g v).re = _
    rw [Complex.smul_re, smul_eq_mul]
    ring
  have hfb : 1 < (f b).re := by
    rw [hf]
    exact (lt_div_iff₀ hu).mpr (by simpa using hub)
  have hfa : ∀ v ∈ A, (f v).re < 1 := by
    intro v hv
    rw [hf]
    exact (div_lt_iff₀ hu).mpr (by simpa using hgu v (subset_closure hv))
  have hballRe : ∀ v ∈ X.closedBall 0 tau, (f v).re < 1 := by
    intro v hv
    apply hfa
    simpa only [zero_add] using Set.add_mem_add hzR hv
  have hballNorm := norm_lt_of_re_lt_on_balanced f.toLinearMap
    (X.balanced_closedBall_zero tau) hballRe
  have hdual : ∀ v, tau * ‖f v‖ ≤ X v :=
    seminorm_dual_bound_of_ball X f.toLinearMap htau
      (fun v hv => hballNorm v (X.mem_closedBall_zero.mpr hv))
  have hstructRe : ∀ Q ∈ S, (((R : ℝ) • f) Q).re < 1 := by
    intro Q hQ
    have hRQ : R • Q ∈ R • convexHull ℝ S :=
      Set.smul_mem_smul_set (subset_convexHull ℝ S hQ)
    have hQA : R • Q ∈ A := by
      simpa only [add_zero] using Set.add_mem_add hRQ hzBall
    simpa only [smul_apply, ContinuousLinearMap.map_smul_of_tower] using hfa _ hQA
  have hstruct := norm_lt_of_re_lt_on_balanced ((R : ℝ) • f).toLinearMap hS hstructRe
  refine ⟨f, hfb, hdual, ?_⟩
  intro Q hQ
  have h := hstruct Q hQ
  change ‖R • f Q‖ < 1 at h
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR] using h

theorem mem_closure_model_set_of_dual_detector (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E)
    (hdetect : ∀ f : E →L[ℂ] ℂ, 1 < (f b).re → (∀ v, tau * ‖f v‖ ≤ X v) →
      ∃ Q ∈ S, 1 ≤ R * ‖f Q‖) :
    b ∈ closure (R • convexHull ℝ S + X.closedBall 0 tau) := by
  by_contra hb
  obtain ⟨f, hfb, hdual, hsmall⟩ := exists_modeling_dual_obstruction X hS hSn hR htau b hb
  obtain ⟨Q, hQ, hlarge⟩ := hdetect f hfb hdual
  exact (hsmall Q hQ).not_ge hlarge

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def weightedEuclideanMap (p : FiniteProbabilityWeights Ω) :
    (Ω → ℂ) →ₗ[ℝ] EuclideanSpace ℂ Ω :=
  (WithLp.linearEquiv 2 ℝ (Ω → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun x => Real.sqrt (p.weight x) • LinearMap.proj x)

theorem weightedEuclideanMap_norm_sq (p : FiniteProbabilityWeights Ω) (v : Ω → ℂ) :
    ‖weightedEuclideanMap p v‖ ^ 2 = p.mean (fun x => ‖v x‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖Real.sqrt (p.weight x) • v x‖ ^ 2 = p.weight x * ‖v x‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (p.nonneg x)]

theorem exists_weighted_convex_approximation (p : FiniteProbabilityWeights Ω)
    {S : Set (Ω → ℂ)} {z : Ω → ℂ} (hz : z ∈ convexHull ℝ S)
    (hS : ∀ q ∈ S, ∀ x, ‖q x‖ ≤ 1) (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → (Ω → ℂ), (∀ i, q i ∈ S) ∧
      p.mean (fun x => ‖((n : ℝ)⁻¹ • (∑ i, q i) - z) x‖ ^ 2) ≤ 1 / (n : ℝ) := by
  classical
  let e := weightedEuclideanMap p
  have hz' : e z ∈ convexHull ℝ (e '' S) := by
    rw [← e.image_convexHull S]
    exact ⟨z, hz, rfl⟩
  have hS' : ∀ v ∈ e '' S, ‖v‖ ≤ 1 := by
    rintro v ⟨q, hq, rfl⟩
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖weightedEuclideanMap p q‖ ^ 2 ≤ 1 ^ 2
    rw [weightedEuclideanMap_norm_sq, one_pow]
    exact (p.mean_mono (fun x => by
      nlinarith [hS q hq x, norm_nonneg (q x)])).trans_eq (p.mean_const 1)
  obtain ⟨v, hv, hsq⟩ := exists_convex_empirical_average hz' hS' n hn
  have hpre : ∀ i, ∃ q ∈ S, e q = v i := hv
  choose q hq heq using hpre
  have hid : e ((n : ℝ)⁻¹ • (∑ i, q i) - z) =
      (n : ℝ)⁻¹ • (∑ i, v i) - e z := by
    simp only [map_sub, map_smul, map_sum, heq]
  rw [← hid, one_pow] at hsq
  exact ⟨q, hq, (weightedEuclideanMap_norm_sq p _).ge.trans hsq⟩

theorem seminorm_sq_le_weighted_square_mean (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K : ℝ}
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖)) (v : Ω → ℂ) :
    (X v) ^ 2 ≤ K ^ 2 * p.mean (fun x => ‖v x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (apply_nonneg X v) (hX v) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (p.mean_square_le (fun x => ‖v x‖)) (sq_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_empirical_length {R K tau : ℝ} (htau : 0 < tau) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 1 + R ^ 2 * K ^ 2 / tau ^ 2 ∧
      Real.sqrt (R ^ 2 * K ^ 2 / n) < tau := by
  let t := R ^ 2 * K ^ 2 / tau ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlen : (n : ℝ) ≤ 1 + t := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le ht]
  have hlt : t < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hprod : R ^ 2 * K ^ 2 < tau ^ 2 * n := by
    have h := (div_lt_iff₀ (pow_pos htau 2)).mp hlt
    simpa only [mul_comm] using h
  have hsmall : R ^ 2 * K ^ 2 / n < tau ^ 2 := (div_lt_iff₀ hnR).mpr hprod
  have hsquare := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  refine ⟨n, hn, hlen, ?_⟩
  nlinarith [Real.sqrt_nonneg (R ^ 2 * K ^ 2 / n)]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

variable [DecidableEq Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem mem_closure_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    b ∈ closure ((2 / beta : ℝ) • convexHull ℝ S + X.closedBall 0 tau) := by
  apply mem_closure_model_set_of_dual_detector X hS hSn (by positivity) htau b
  intro f hfb hdual
  have hzero := modeling_dual_zero_weight p X f.toLinearMap htau hX hdual
  have hcap := weightedDualVector_cap p X f.toLinearMap hK htau hX hdual
  have hlarge := weightedDualVector_detectable p X f.toLinearMap b hM htau hb hfb hdual hzero
  obtain ⟨Q, hQ, hcor⟩ := hdetect (weightedDualVector p f.toLinearMap) hcap hlarge.le
  rw [p.norm_correlation_symm, ← functional_eq_weighted_inner p f.toLinearMap hzero] at hcor
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcor (show 0 ≤ 2 / beta by positivity)
  rw [div_mul_cancel₀ 2 hbeta.ne'] at h
  exact (by norm_num : (1 : ℝ) ≤ 2).trans h

theorem exists_convex_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau eta : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ z ∈ convexHull ℝ S, X (b - (2 / beta : ℝ) • z) ≤ tau + eta := by
  have hc := mem_closure_model_of_weighted_detector p X hS hSn hK hM hbeta htau hX hdetect b hb
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (eta / (K + 1)) (by positivity)
  obtain ⟨v, hv, e, he, hve⟩ := Set.mem_add.mp hy
  obtain ⟨z, hz, hzv⟩ := Set.mem_smul_set.mp hv
  have hxe : X e ≤ tau := X.mem_closedBall_zero.mp he
  have hnorm : ‖b - y‖ < eta / (K + 1) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : K * ‖b - y‖ ≤ eta := by
    have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hnorm
    nlinarith [norm_nonneg (b - y)]
  have hmean : p.mean (fun x => ‖(b - y) x‖) ≤ ‖b - y‖ :=
    (p.mean_mono (fun x => norm_le_pi_norm (b - y) x)).trans_eq (p.mean_const ‖b - y‖)
  have hxy : X (b - y) ≤ eta := (hX (b - y)).trans
    ((mul_le_mul_of_nonneg_left hmean hK).trans hsmall)
  refine ⟨z, hz, ?_⟩
  have hid : b - (2 / beta : ℝ) • z = (b - y) + e := by
    rw [← hve, ← hzv]
    abel
  rw [hid]
  exact (map_add_le_add X _ _).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem scaled_weighted_empirical_seminorm_bound (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (v : Ω → ℂ) (n : ℕ) (hn : 0 < n)
    (hv : p.mean (fun x => ‖v x‖ ^ 2) ≤ 1 / (n : ℝ)) :
    X (R • v) ≤ Real.sqrt (R ^ 2 * K ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := (seminorm_sq_le_weighted_square_mean p X hX v).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg K))
  have hsmul : X (R • v) = R * X v := by
    change (X.restrictScalars ℝ) (R • v) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg hR]
    rfl
  have hscaled : (X (R • v)) ^ 2 ≤ R ^ 2 * K ^ 2 / n := by
    rw [hsmul, mul_pow]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using h
  have hroot := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  exact (sq_le_sq₀ (apply_nonneg X _) (Real.sqrt_nonneg _)).mp (hscaled.trans_eq hroot.symm)

variable [DecidableEq Ω]

theorem exists_weighted_model_of_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let R := 2 / beta
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨n, hn, hlen, hsmall⟩ := exists_empirical_length (R := R) (K := K) htau
  let s := Real.sqrt (R ^ 2 * K ^ 2 / n)
  have hs : s < tau := hsmall
  let eta := (tau - s) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨z, hz, hmodel⟩ := exists_convex_model_of_weighted_detector p X hS hSn
    hK hM hbeta htau heta hX hdetect b hb
  obtain ⟨Q, hQ, happrox⟩ := exists_weighted_convex_approximation p hz hSbound n hn
  let avg := (n : ℝ)⁻¹ • (∑ i, Q i)
  have hnoise : X (R • (avg - z)) ≤ s :=
    scaled_weighted_empirical_seminorm_bound p X hR.le hX (avg - z) n hn happrox
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun _ => R / n
  have hstruct : (∑ i, c i • Q i) = R • avg := by
    calc
      _ = (R / (n : ℝ)) • (∑ i, Q i) := by rw [Finset.smul_sum]
      _ = _ := by dsimp only [avg]; rw [smul_smul]; congr 1
  have hcost : (∑ i, |c i|) = R := by
    simp only [c, abs_of_nonneg (div_nonneg hR.le hnR.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨n, hn, Q, c, b - ∑ i, c i • Q i, hQ, ?_, hcost.le, ?_, ?_⟩
  · abel
  · rw [hstruct]
    have hid : b - R • avg = (b - R • z) - R • (avg - z) := by
      rw [smul_sub]
      abel
    rw [hid]
    have h := map_sub_le_add X (b - R • z) (R • (avg - z))
    change X (b - R • z) ≤ tau + eta at hmodel
    dsimp only [eta] at hmodel
    linarith
  · have heq : R ^ 2 * K ^ 2 / tau ^ 2 = 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
      dsimp only [R]
      field_simp
      ring
    simpa only [heq] using hlen

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem seminorm_mask_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (_hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
  have hmean : p.mean (fun x => m x * ‖finiteMask G v x‖) ≤
      C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simpa only [finiteMask_apply, hx, ite_true] using
        mul_le_mul_of_nonneg_right (hgood x hx) (norm_nonneg (v x))
    · simp [hx]
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_mask_le_condition (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (hG : 0 < p.mass G) (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * (p.condition G hG).mean (fun x => ‖v x‖) := by
  have h := seminorm_mask_le p G X m hC hC₀ hX hgood v
  rw [← p.mass_mul_condition_mean G hG] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hC₀)
  exact mul_le_of_le_one_left ((p.condition G hG).mean_nonneg (fun x => norm_nonneg _))
    (p.mass_le_one G)

theorem seminorm_tail_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X (v - finiteMask G v) ≤ C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  have hmean : p.mean (fun x => m x * ‖(v - finiteMask G v) x‖) ≤
      B * p.mean (fun x => if x ∈ G then 0 else m x) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simp [hx]
    · simpa only [Pi.sub_apply, finiteMask_apply, hx, ite_false, sub_zero, mul_comm B]
        using mul_le_mul_of_nonneg_left (hv x) (hm x)
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_le_mask_add_tail (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X v ≤ X (finiteMask G v) +
      C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  calc
    X v = X (finiteMask G v + (v - finiteMask G v)) := by congr 1; abel
    _ ≤ X (finiteMask G v) + X (v - finiteMask G v) := map_add_le_add X _ _
    _ ≤ _ := add_le_add le_rfl (seminorm_tail_le p G X m hC hm hX v hv)

omit [Fintype Ω] [DecidableEq Ω] in

theorem model_error_norm_le {ι : Type*} [Fintype ι]
    {b e : Ω → ℂ} {Q : ι → (Ω → ℂ)} {c : ι → ℝ} {M R : ℝ}
    (hb : ∀ x, ‖b x‖ ≤ M) (hQ : ∀ i x, ‖Q i x‖ ≤ 1)
    (hdecomp : b = (∑ i, c i • Q i) + e) (hc : (∑ i, |c i|) ≤ R) :
    ∀ x, ‖e x‖ ≤ M + R := by
  intro x
  have hsum : ‖(∑ i, c i • Q i) x‖ ≤ R := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => ?_)).trans hc
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hQ i x)
  have he : e x = b x - (∑ i, c i • Q i) x := by
    have h := congrFun hdecomp x
    simp only [Pi.add_apply] at h
    exact eq_sub_of_add_eq' h.symm
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (hb x) hsum)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_model_with_tail_error (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {C C₀ M beta tau : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hm : ∀ x, 0 ≤ m x) (hgood : ∀ x ∈ G, m x ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ C * C₀ / tau) →
      tau / M ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2 * tau + C * (M + 2 / beta) *
        p.mean (fun x => if x ∈ G then 0 else m x) ∧
      (n : ℝ) ≤ 1 + 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  have hK : 0 ≤ C * C₀ := mul_nonneg hC hC₀
  have hR : 0 ≤ 2 / beta := by positivity
  have htail : 0 ≤ p.mean (fun x => if x ∈ G then 0 else m x) :=
    p.mean_nonneg (fun x => by split_ifs; exact le_rfl; exact hm x)
  by_cases hG : 0 < p.mass G
  · let XG := X.comp (finiteMask G)
    have hXG (v : Ω → ℂ) : XG v ≤
        (C * C₀) * (p.condition G hG).mean (fun x => ‖v x‖) :=
      seminorm_mask_le_condition p G hG X m hC hC₀ hX hgood v
    have hdetG (psi : Ω → ℂ) (hpsi : ∀ x, ‖psi x‖ ≤ C * C₀ / tau)
        (hlarge : tau / M ^ 2 ≤ XG psi) :
        ∃ Q ∈ S, beta ≤ ‖(p.condition G hG).correlation psi Q‖ := by
      have hmask : ∀ x, ‖finiteMask G psi x‖ ≤ C * C₀ / tau := by
        intro x
        by_cases hx : x ∈ G
        · simpa [hx] using hpsi x
        · simpa [hx] using div_nonneg hK htau.le
      obtain ⟨Q, hQ, hcorr⟩ := hdetect (finiteMask G psi) hmask hlarge
      refine ⟨Q, hQ, hcorr.trans ?_⟩
      rw [p.norm_correlation_mask G hG]
      exact mul_le_of_le_one_left (norm_nonneg _) (p.mass_le_one G)
    obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
      exists_weighted_model_of_detector (p.condition G hG) XG hS hSn hSbound
        hK hM hbeta htau hXG hdetG b hb
    refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
    have herror := model_error_norm_le hb (fun i => hSbound (Q i) (hQ i)) hdecomp hc
    have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX e herror
    exact hglobal.trans (add_le_add he le_rfl)
  · have hmass : p.mass G = 0 := le_antisymm (le_of_not_gt hG) (p.mass_nonneg G)
    obtain ⟨Q₀, hQ₀⟩ := hSn
    refine ⟨1, by decide, fun _ => Q₀, fun _ => 0, b, fun _ => hQ₀, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hR
    · have hmask : X (finiteMask G b) ≤ 0 := by
        have h := seminorm_mask_le p G X m hC hC₀ hX hgood b
        simpa [p.mean_mask_zero G hmass] using h
      have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX b hb
      have hmono : C * M * p.mean (fun x => if x ∈ G then 0 else m x) ≤
          C * (M + 2 / beta) * p.mean (fun x => if x ∈ G then 0 else m x) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) hC) htail
      linarith
    · have hnonneg : 0 ≤ 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by positivity
      simpa using (le_add_of_nonneg_right hnonneg : (1 : ℝ) ≤ 1 + _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_model_of_marginal_excess {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * q.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (hexcess : p.excessMass q C ≤ ε)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2*tau + 2*K*(B + 2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2*C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2*C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2*ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact FiniteProbabilityWeights.mass_above_double_cap_le_of_excess p q hexcess
  have hbound (v : Ω → ℂ) : X v ≤ K * p.mean (fun x => p.relativeDensity q x * ‖v x‖) := by
    rw [p.mean_relativeDensity q hp]
    exact hX v
  obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
    exists_model_with_tail_error p G X (p.relativeDensity q) hS hSn hSbound hK
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hB hbeta htau
      (p.relativeDensity_nonneg q) (fun x hx => (Finset.mem_filter.mp hx).2)
      hbound hdetect b hb
  refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
  have hscale : 0 ≤ K*(B + 2/beta) := by positivity
  have hsmall := mul_le_mul_of_nonneg_left htail hscale
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

def intervalCutUpper (S : Finset ℕ) (N a : ℕ) : ℕ :=
  (insert N (S.filter (a < ·))).min' (Finset.insert_nonempty _ _)

theorem intervalCutUpper_le_end (S : Finset ℕ) (N a : ℕ) :
    intervalCutUpper S N a ≤ N :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem intervalCutUpper_le_cut (S : Finset ℕ) (N : ℕ) {a b : ℕ}
    (hb : b ∈ S) (hab : a < b) : intervalCutUpper S N a ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hb, hab⟩))

theorem le_intervalCutUpper (S : Finset ℕ) (N : ℕ) {a : ℕ} (ha : a ≤ N) :
    a ≤ intervalCutUpper S N a := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ha
  · exact (Finset.mem_filter.mp hb).2.le

theorem exists_intervalCut (S : Finset ℕ) (N : ℕ) (hzero : 0 ∈ S)
    {x : ℕ} (hx : x < N) :
    ∃ a ∈ S, a ≤ x ∧ x < intervalCutUpper S N a := by
  let A := S.filter (· ≤ x)
  have hA : A.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hzero, Nat.zero_le _⟩⟩
  let a := A.max' hA
  have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
  refine ⟨a, ha.1, ha.2, ?_⟩
  apply (Finset.lt_min'_iff _ _).mpr
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hx
  · obtain ⟨hbS, hab⟩ := Finset.mem_filter.mp hb
    by_contra hxb
    have hbA : b ∈ A := Finset.mem_filter.mpr ⟨hbS, by omega⟩
    have hba : b ≤ a := Finset.le_max' A b hbA
    omega

theorem intervalCut_unique (S : Finset ℕ) (N : ℕ) {a b x : ℕ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hax : a ≤ x) (hxa : x < intervalCutUpper S N a)
    (hbx : b ≤ x) (hxb : x < intervalCutUpper S N b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · have hh := intervalCutUpper_le_cut S N hb hab
    omega
  · exact hab
  · have hh := intervalCutUpper_le_cut S N ha hba
    omega

def cyclicCutCell (S : Finset ℕ) (N a : ℕ) : Finset (ZMod N) :=
  cyclicInterval (a : ZMod N) (intervalCutUpper S N a - a)

theorem mem_cyclicCutCell {N : ℕ} [NeZero N] (S : Finset ℕ) {a : ℕ} (ha : a ≤ N)
    (x : ZMod N) : x ∈ cyclicCutCell S N a ↔ a ≤ x.val ∧ x.val < intervalCutUpper S N a :=
  mem_cyclicInterval_representatives a _ (le_intervalCutUpper S N ha)
    (intervalCutUpper_le_end S N a) x

theorem sum_cyclicCutCell_indicator {N : ℕ} [NeZero N] (S : Finset ℕ)
    (hzero : 0 ∈ S) (hbound : ∀ a ∈ S, a ≤ N) (x : ZMod N) :
    (∑ a : S, finiteIndicator (cyclicCutCell S N a) x) = 1 := by
  obtain ⟨a, ha, hax, hxa⟩ := exists_intervalCut S N hzero x.val_lt
  have hmem : x ∈ cyclicCutCell S N a := (mem_cyclicCutCell S (hbound a ha) x).mpr ⟨hax, hxa⟩
  rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
  · simp only [finiteIndicator, hmem, ite_true]
  · intro b _ hba
    have hnot : x ∉ cyclicCutCell S N b := by
      intro hx
      have hb := (mem_cyclicCutCell S (hbound b b.property) x).mp hx
      have he := intervalCut_unique S N b.property ha hb.1 hb.2 hax hxa
      exact hba (Subtype.ext he)
    simp only [finiteIndicator, hnot, ite_false]
  · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def cubeRepresentativeSum {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) : ℕ :=
  ∑ i, if ω i then (k i).val else 0

theorem cubeRepresentativeSum_intCast {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ℤ) = cubeShift (fun i => ((k i).val : ℤ)) ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem cubeRepresentativeSum_zmodCast {d N : ℕ} [NeZero N] (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ZMod N) = cubeShift k ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem cubeRepresentativeSum_le {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) (ω : Fin d → Bool) : cubeRepresentativeSum k ω ≤ d * N := by
  calc
    _ ≤ ∑ _i : Fin d, N := Finset.sum_le_sum (fun i _ => by
      split_ifs <;> [exact (k i).val_lt.le; exact Nat.zero_le _])
    _ = _ := by simp

def cubeCarryShift (d N : ℕ) (b : (Fin d → Bool) → Fin (d + 1)) : (Fin d → Bool) → ℤ :=
  fun ω => -((b ω).val : ℤ) * N

theorem exists_cube_carry_code {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) {a : ℕ} (ha : a < N) :
    ∃ b : (Fin d → Bool) → Fin (d + 1), ∀ ω,
      cyclicTranslationOffset (cubeShift k ω) a =
        cubeShift (fun i => ((k i).val : ℤ)) ω + cubeCarryShift d N b ω := by
  let b (ω : Fin d → Bool) : Fin (d + 1) :=
    ⟨(a + cubeRepresentativeSum k ω) / N, (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by
      have hs := cubeRepresentativeSum_le k ω
      nlinarith)⟩
  refine ⟨b, ?_⟩
  intro ω
  have ha' : (a : ZMod N).val = a := by simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have hadd := cyclic_representative_add (cubeShift k ω) (a : ZMod N)
  rw [ha'] at hadd
  have hcast : ((a + cubeRepresentativeSum k ω : ℕ) : ZMod N) = cubeShift k ω + (a : ZMod N) := by
    rw [Nat.cast_add, cubeRepresentativeSum_zmodCast, add_comm]
  have hval := congrArg (fun x : ZMod N => (x.val : ℤ)) hcast
  rw [ZMod.val_natCast] at hval
  have hdiv := Nat.mod_add_div (a + cubeRepresentativeSum k ω) N
  have hdiv' := congrArg (fun x : ℕ => (x : ℤ)) hdiv
  simp only [Nat.cast_add, Nat.cast_mul] at hdiv'
  rw [hval, hadd] at hdiv'
  rw [← cubeRepresentativeSum_intCast]
  change (cubeShift k ω).val - (if N - (cubeShift k ω).val ≤ a then (N : ℤ) else 0) =
    (cubeRepresentativeSum k ω : ℤ) + -(((a + cubeRepresentativeSum k ω) / N : ℕ) : ℤ) * N
  nlinarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ}

def commonCyclicCuts (h : ι → ZMod N) : Finset ℕ :=
  (Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)) ∪
    (Finset.univ.image (fun i => N - (h i).val))

theorem quarterLower_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterLower N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem quarterUpper_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterUpper N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

theorem wrap_mem_commonCyclicCuts (h : ι → ZMod N) (i : ι) :
    N - (h i).val ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, rfl⟩

theorem zero_mem_commonCyclicCuts (h : ι → ZMod N) : 0 ∈ commonCyclicCuts h := by
  simpa only [quarterLower, Fin.val_zero, zero_mul, Nat.zero_div] using
    quarterLower_mem_commonCyclicCuts h 0

theorem commonCyclicCuts_le (h : ι → ZMod N) {a : ℕ} (ha : a ∈ commonCyclicCuts h) : a ≤ N := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ha
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact (quarter_bounds N i).1.trans (quarter_bounds N i).2
  · exact (quarter_bounds N i).2
  · exact Nat.sub_le _ _

theorem commonCyclicCuts_card_le (h : ι → ZMod N) :
    (commonCyclicCuts h).card ≤ Fintype.card ι + 8 := by
  have hL := Finset.card_image_le (s := Finset.univ) (f := quarterLower N)
  have hU := Finset.card_image_le (s := Finset.univ) (f := quarterUpper N)
  have hW := Finset.card_image_le (s := Finset.univ) (f := fun i => N - (h i).val)
  have hLU := Finset.card_union_le (Finset.univ.image (quarterLower N)) (Finset.univ.image (quarterUpper N))
  have hAll := Finset.card_union_le
    ((Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)))
    (Finset.univ.image (fun i => N - (h i).val))
  simp only [Finset.card_univ, Fintype.card_fin] at hL hU hW
  unfold commonCyclicCuts
  omega

theorem exists_mem_cyclicQuarter [NeZero N] (x : ZMod N) : ∃ i, x ∈ cyclicQuarter N i := by
  by_contra hn
  push Not at hn
  have hz (i : Fin 4) : finiteIndicator (cyclicQuarter N i) x = 0 := by
    simp only [finiteIndicator, hn i, ite_false]
  have hs := sum_cyclicQuarter_indicator x
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

theorem commonCyclicCut_short [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) :
    2 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N ∧
    3 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N := by
  have haN := commonCyclicCuts_le h ha
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  by_cases he : a = N
  · have hN := NeZero.pos N
    constructor <;> omega
  · have haN' : a < N := by omega
    obtain ⟨i, hi⟩ := exists_mem_cyclicQuarter (a : ZMod N)
    rw [mem_cyclicQuarter, ZMod.val_natCast_of_lt haN'] at hi
    have hub := intervalCutUpper_le_cut (commonCyclicCuts h) N
      (quarterUpper_mem_commonCyclicCuts h i) hi.2
    have h2 := quarter_short N (NeZero.pos N) i
    have h3 := quarter_diameter_lt_third N (NeZero.pos N) i
    constructor <;> omega

theorem sum_commonCyclicCut_indicator [NeZero N] (h : ι → ZMod N) (x : ZMod N) :
    (∑ a : commonCyclicCuts h, finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = 1 :=
  sum_cyclicCutCell_indicator _ (zero_mem_commonCyclicCuts h)
    (fun _ ha => commonCyclicCuts_le h ha) x

theorem commonCyclicCut_representative [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) (i : ι) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    (((h i + x).val : ℕ) : ℤ) = (x.val : ℤ) + cyclicTranslationOffset (h i) a := by
  have hxi := (mem_cyclicCutCell _ (commonCyclicCuts_le h ha) x).mp hx
  have hw : (N - (h i).val ≤ x.val) ↔ (N - (h i).val ≤ a) := by
    constructor
    · intro hwx
      by_contra hwa
      have hu := intervalCutUpper_le_cut (commonCyclicCuts h) N
        (wrap_mem_commonCyclicCuts h i) (by omega : a < N - (h i).val)
      omega
    · intro hwa
      omega
  rw [cyclic_representative_add, cyclicTranslationOffset]
  simp only [hw]
  ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem exists_correlating_commonCyclicCut {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f u : ZMod N → ℂ) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f u‖) :
    ∃ a : commonCyclicCuts h, (cyclicCutCell (commonCyclicCuts h) N a).Nonempty ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f u‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤
        ((cyclicCutCell (commonCyclicCuts h) N a).card : ℝ) / N := by
  have hsum (x : ZMod N) :
      (∑ a : commonCyclicCuts h, u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = u x := by
    rw [← Finset.mul_sum, sum_commonCyclicCut_indicator, mul_one]
  have hcard : (Fintype.card (commonCyclicCuts h) : ℝ) ≤ (Fintype.card ι : ℝ) + 8 := by
    rw [Fintype.card_coe]
    exact_mod_cast commonCyclicCuts_card_le h
  obtain ⟨a, ha⟩ := exists_correlating_summand Finset.univ_nonempty f u
    (fun a : commonCyclicCuts h => fun x => u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x)
    hρ (by positivity : (0 : ℝ) < (Fintype.card ι : ℝ) + 8) hcard (fun x _ => hf x)
    (fun x _ => by rw [hsum, sub_self, norm_zero]; positivity) hc
  have hh := retained_restricted_correlation (cyclicCutCell (commonCyclicCuts h) N a) f u
    (ρ := ρ / (2 * ((Fintype.card ι : ℝ) + 8))) (by positivity) hB
    (fun x _ => hf x) (fun x _ => hu x) ha
  refine ⟨a, hh.1, hh.2.1, ?_⟩
  simpa only [div_div, ZMod.card] using hh.2.2

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

noncomputable def translatedCyclicProduct (h : ι → ZMod N) (u : ι → ℤ → ℂ) (x : ZMod N) : ℂ :=
  ∏ i, u i ((h i + x).val : ℤ)

theorem translatedCyclicProduct_on_cut (h : ι → ZMod N) (u : ι → ℤ → ℂ) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    translatedCyclicProduct h u x = ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a) := by
  unfold translatedCyclicProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [commonCyclicCut_representative h ha i hx]

theorem translatedCyclicProduct_cut_correlation (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {a : ℕ} (ha : a ∈ commonCyclicCuts h) :
    finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f (translatedCyclicProduct h u) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + (intervalCutUpper (commonCyclicCuts h) N a - a : ℕ)))
        (fun x => f (x : ZMod N)) (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a)) := by
  have haN := commonCyclicCuts_le h ha
  have hupper := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hle := le_intervalCutUpper (commonCyclicCuts h) N haN
  calc
    _ = finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f
        (fun x => ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a)) := by
      unfold finiteCorrelation
      apply Finset.expect_congr rfl
      intro x hx
      rw [translatedCyclicProduct_on_cut h u ha hx]
    _ = _ := cyclicInterval_representative_correlation (N := N) a
      (intervalCutUpper (commonCyclicCuts h) N a - a) (by omega)
      (commonCyclicCut_short h ha).1 f (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))

theorem exists_correlating_integer_product_interval (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖translatedCyclicProduct h u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct h u)‖) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤ (len : ℝ) / N := by
  obtain ⟨a, ha, hcorr, hvol⟩ := exists_correlating_commonCyclicCut h f
    (translatedCyclicProduct h u) hρ hB hf hu hc
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hlen : intervalCutUpper (commonCyclicCuts h) N a - a.val ≤ N := by omega
  have hcard : (cyclicCutCell (commonCyclicCuts h) N a).card =
      intervalCutUpper (commonCyclicCuts h) N a - a.val := cyclicInterval_card _ hlen
  refine ⟨a, ?_, ?_, (commonCyclicCut_short h a.property).1, ?_, ?_⟩
  · rw [← hcard]
    exact ha.card_pos
  · have haN := commonCyclicCuts_le h a.property
    have hal := le_intervalCutUpper (commonCyclicCuts h) N haN
    omega
  · rwa [translatedCyclicProduct_cut_correlation h u f a.property] at hcorr
  · rwa [hcard] at hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerCubeProductWithShift {d : ℕ} (R : ℤ → ℂ) (k : Fin d → ℤ)
    (c : (Fin d → Bool) → ℤ) (n : ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (R (n + cubeShift k ω + c ω))

theorem exists_cyclic_cube_product_interval {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (k : Fin d → ZMod N)
    {ρ : ℝ} (hρ : 0 < ρ) (hf : ∀ x, ‖f x‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k))‖) :
    ∃ (b : (Fin d → Bool) → Fin (d + 1)) (a len : ℕ),
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun n => f (n : ZMod N))
          (integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b))‖ ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤ (len : ℝ) / N := by
  classical
  let shifts (ω : Fin d → Bool) := cubeShift k ω
  let u (ω : Fin d → Bool) (n : ℤ) := conjugationPower (booleanWeight ω) (R n)
  have heval (n : ZMod N) : translatedCyclicProduct shifts u n =
      cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k) n := by
    rw [cubeProduct_eq_boolean_product]
    unfold translatedCyclicProduct
    apply Finset.prod_congr rfl
    intro ω _
    simp only [shifts, u, add_comm]
  have hcap (n : ZMod N) : ‖translatedCyclicProduct shifts u n‖ ≤ 1 := by
    rw [heval]
    exact cubeProduct_norm_le_one _ (fun x => hR x.val) _ n
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hend, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  obtain ⟨b, hb⟩ := exists_cube_carry_code k haN
  have hprod (n : ℤ) : (∏ ω, u ω (n + cyclicTranslationOffset (shifts ω) a.val)) =
      integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b) n := by
    unfold integerCubeProductWithShift
    apply Finset.prod_congr rfl
    intro ω _
    simp only [u, shifts, hb, add_assoc]
  refine ⟨b, a.val, len, hlen, hend, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisProjectionRealification
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

theorem basisCoordinateProjection_baseChange (b : Basis ι ℚ V) (S : Set ι) :
    (basisCoordinateProjection b S).baseChange ℝ = basisCoordinateProjection (b.baseChange ℝ) S := by
  classical
  apply (b.baseChange ℝ).ext
  intro i
  rw [basisCoordinateProjection_basis, Basis.baseChange_apply, LinearMap.baseChange_tmul,
    basisCoordinateProjection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

theorem BasisGradedSubmodule.baseChange (b : Basis ι ℚ V) (w : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b w U) : BasisGradedSubmodule (b.baseChange ℝ) w (U.baseChange ℝ) := by
  intro j x hx
  have hstable : U.baseChange ℝ ≤ (U.baseChange ℝ).comap (basisGradeProjection (b.baseChange ℝ) w j) := by
    conv_lhs => rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change basisCoordinateProjection (b.baseChange ℝ) {i | w i = j} ((1 : ℝ) ⊗ₜ[ℚ] u) ∈ U.baseChange ℝ
    rw [← basisCoordinateProjection_baseChange, LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hU j u hu)
  exact hstable hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieUpperGenerators (v : I → L) (w : I → ℕ) (d : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ lieTreeEval v a = x}

def weightedLieUpperSpan (v : I → L) (w : I → ℕ) (d : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieUpperGenerators v w d)

theorem weightedLieUpperSpan_antitone (v : I → L) (w : I → ℕ) :
    Antitone (weightedLieUpperSpan v w) := by
  intro d e hde
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hde.trans ha, rfl⟩

theorem weightedLieUpperSpan_lie_mem (v : I → L) (w : I → ℕ) {d e : ℕ} {x y : L}
    (hx : x ∈ weightedLieUpperSpan v w d) (hy : y ∈ weightedLieUpperSpan v w e) :
    ⁅x, y⁆ ∈ weightedLieUpperSpan v w (d + e) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem weightedLieUpperSpan_leaf (v : I → L) (w : I → ℕ) (i : I) :
    v i ∈ weightedLieUpperSpan v w (w i) :=
  Submodule.subset_span ⟨.of i, le_rfl, rfl⟩

theorem weightedLieTree_eval_mem_layer {s : ℕ} (F : NilpotentLieFiltration M s)
    (v : I → M) (w : I → ℕ) (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight w a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem weightedLieUpperSpan_le_comap {s : ℕ} (F : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, φ (v i) ∈ F.layer (w i)) (d : ℕ) :
    weightedLieUpperSpan v w d ≤ (F.layer d).comap φ.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ F.layer d
  rw [map_lieTreeEval]
  exact F.antitone ha (weightedLieTree_eval_mem_layer F (fun i => φ (v i)) w hv a)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WordTruncationBracket
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_eq_zero_iff (s : ℕ) (p : WordPolynomial X) :
    wordTruncation s p = 0 ↔ ∀ w, w.length ≤ s → p.coeff w = 0 := by
  simpa using wordTruncation_eq_iff s p 0

theorem wordTruncation_succ_mul_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (h : wordTruncation s p = 0 ∨ wordTruncation s q = 0) :
    wordTruncation (s + 1) (p * q) = 0 := by
  classical
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hne : u * v ≠ w := by
    intro he
    have hlen : u.length + v.length ≤ s + 1 := by
      simpa only [← he, FreeSemigroup.length_mul] using hw
    have hu0 : 0 < u.length := by change 0 < u.tail.length + 1; omega
    have hv0 : 0 < v.length := by change 0 < v.tail.length + 1; omega
    rcases h with hp | hq
    · exact (Finsupp.mem_support_iff.mp hu)
        ((wordTruncation_eq_zero_iff s p).mp hp u (by omega))
    · exact (Finsupp.mem_support_iff.mp hv)
        ((wordTruncation_eq_zero_iff s q).mp hq v (by omega))
  simp only [hne, ite_false]

theorem wordTruncation_succ_lie_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (hq : wordTruncation s q = 0) : wordTruncation (s + 1) ⁅p, q⁆ = 0 := by
  rw [wordPolynomial_lie, map_sub, wordTruncation_succ_mul_eq_zero s p q (Or.inr hq),
    wordTruncation_succ_mul_eq_zero s q p (Or.inl hq), sub_self]

theorem freeLieTruncation_zero (p : FreeLieAlgebra ℚ X) : freeLieTruncation 0 p = 0 := by
  apply freeLieWordExpansion_injective
  rw [freeLieTruncation_expansion, map_zero]
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  have : 0 < w.length := by change 0 < w.tail.length + 1; omega
  omega

theorem freeLie_lowerCentralSeries_truncation_zero (s : ℕ) (p : FreeLieAlgebra ℚ X)
    (hp : p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s) :
    freeLieTruncation s p = 0 := by
  induction s generalizing p with
  | zero => exact freeLieTruncation_zero p
  | succ s ih =>
    have hsub : (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) (s + 1)).toSubmodule ≤
        LinearMap.ker (freeLieTruncation (X := X) (s + 1)) := by
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
      apply Submodule.span_le.mpr
      rintro z ⟨x, y, rfl⟩
      change freeLieTruncation (s + 1) ⁅x.val, y.val⁆ = 0
      apply freeLieWordExpansion_injective
      rw [freeLieTruncation_expansion, map_zero, LieHom.map_lie]
      apply wordTruncation_succ_lie_eq_zero
      rw [← freeLieTruncation_expansion, ih y.val y.property, map_zero]
    exact hsub hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
namespace OAI

section

namespace Erdos3.CircleFourier

theorem exists_real_character_phase {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ r : ℝ, character (r : Circle) = z := by
  let c : _root_.Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  rw [AddCircle.homeomorphCircle_apply] at ht
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨r, congrArg (fun c : _root_.Circle => (c : ℂ)) ht⟩

end Erdos3.CircleFourier

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem exists_real_frequency_phase (r : ZMod N) :
    ∃ theta : ℝ, ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x := by
  obtain ⟨theta, htheta⟩ := CircleFourier.exists_real_character_phase (norm_character r 1)
  refine ⟨theta, ?_⟩
  intro x
  have hphase : (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) =
      x.val • (theta : CircleFourier.Circle) := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := x.val) (x := theta))
  rw [hphase, CircleFourier.character_nsmul, htheta]
  calc
    _ = character r (x.val • (1 : ZMod N)) := (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = character r x := by simp

end Erdos3.CyclicBohr

end

section

namespace Erdos3

open scoped BigOperators

theorem CircleFourier.character_affine_integer_combination
    {I : Type*} [Fintype I] (a t : ℝ) (b : I → ℝ) (x : I → ℤ) :
    character ((t * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : Circle) =
      character ((t * a : ℝ) : Circle) *
        ∏ i, character ((t * b i : ℝ) : Circle) ^ (x i) := by
  classical
  have hcoe (v : I → ℝ) : ((∑ i, v i : ℝ) : Circle) = ∑ i, (v i : Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) v Finset.univ
  rw [mul_add, Finset.mul_sum, AddCircle.coe_add, character_add, hcoe, character_fintype_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← character_zsmul, ← AddCircle.coe_zsmul]
  congr 1
  congr 1
  simp only [zsmul_eq_mul]
  ring

theorem exists_affine_cyclic_character_phase {I : Type*} [Fintype I]
    {N : ℕ} [NeZero N] (ξ : (I → ℤ) →+ ZMod N) (ξ₀ : ZMod N) :
    ∃ (a : ℝ) (b : I → ℝ), ∀ (x : I → ℤ) (n : ZMod N),
      CircleFourier.character
        (((n.val : ℝ) * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : CircleFourier.Circle) =
          AddChar.zmodAddEquiv (ξ₀ + ξ x) n := by
  classical
  obtain ⟨a, ha⟩ := CyclicBohr.exists_real_frequency_phase ξ₀
  choose b hb using fun i => CyclicBohr.exists_real_frequency_phase (ξ (Pi.single i 1))
  simp only [CyclicBohr.character] at ha hb
  refine ⟨a, b, ?_⟩
  intro x n
  have hx : ξ x = ∑ i, (x i) • ξ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    simp only [map_zsmul]
  rw [CircleFourier.character_affine_integer_combination, ha n, hx]
  simp only [map_add, map_sum, map_zsmul, AddChar.add_apply, AddChar.sum_apply,
    AddChar.zsmul_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hb i n]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def ndilate (B : Set N) (t : ℝ≥0) : Set N := B.dilate t

@[simp] theorem radius_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).radius = t * B.radius := by simp [ndilate]

@[simp] theorem rank_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).rank = B.rank := rfl

@[simp] theorem ndilate_one (B : Set N) : B.ndilate 1 = B := by simp [ndilate]

@[simp] theorem ndilate_ndilate (B : Set N) (s t : ℝ≥0) :
    (B.ndilate s).ndilate t = B.ndilate (t * s) := by simp [ndilate]

theorem carrier_ndilate_mono {B : Set N} {s t : ℝ≥0} (hst : s ≤ t) :
    (B.ndilate s).carrier ⊆ (B.ndilate t).carrier :=
  B.dilate_mono s.coe_nonneg (by exact_mod_cast hst)

def IsRankRegular (B : Set N) : Prop :=
  let d : ℕ := 2 * max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.ndilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.ndilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

theorem isRankRegular_ndilate_iff (B : Set N) (rho : ℝ≥0) :
    (B.ndilate rho).IsRankRegular ↔
      let d : ℕ := 2 * max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) ≤
              ((B.ndilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.ndilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

theorem log_card_growth_lt_five_mul_rank (B : Set N) (hB : 0 < B.radius) :
    Real.log ((B.ndilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.ndilate (1 / 4)).carrier.card : ℝ) <
      5 * (2 * max B.rank 1 : ℕ) := by
  classical
  let d : ℕ := 2 * max B.rank 1
  have hcard : (B.ndilate (5 / 4)).carrier.card ≤
      9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card := by
    calc
      (B.ndilate (5 / 4)).carrier.card ≤ (B.ndilate 2).carrier.card :=
        Finset.card_le_card (carrier_ndilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card :=
        by simpa [ndilate] using card_two_le_nine_pow_three_rank_mul_card_quarter B hB
  have hsmall_pos : (0 : ℝ) < (B.ndilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.ndilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.ndilate (5 / 4)).carrier.card : ℝ) ≤
        ((9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hlog9 : Real.log (9 : ℝ) < 10 / 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by norm_num : (9 : ℝ) ≤ 2 ^ 4)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (9 : ℝ) < 5 * d := by
    have hpos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hrank : (B.rank : ℝ) ≤ (max B.rank 1 : ℕ) := by exact_mod_cast le_max_left B.rank 1
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 9 ≤ 3 * (max B.rank 1 : ℕ) * Real.log 9 := by gcongr
      _ < 3 * (max B.rank 1 : ℕ) * (10 / 3) := by gcongr
      _ = 5 * d := by dsimp [d]; push_cast; ring
  dsimp [d] at hmain ⊢
  linarith

noncomputable def normalizedLogCard (B : Set N) (s : ℝ) : ℝ :=
  Real.log ((B.ndilate s.toNNReal).carrier.card : ℝ) /
    (2 * max B.rank 1 : ℕ)

theorem normalizedLogCard_monotone (B : Set N) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.ndilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_ndilate_mono (B := B) (Real.toNNReal_mono hst))

theorem normalizedLogCard_buffer_growth (B : Set N) (hB : 0 < B.radius) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  classical
  have h := log_card_growth_lt_five_mul_rank B hB
  have hd : (0 : ℝ) < (2 * max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

theorem exists_rankRegular_ndilate (B : Set N) (hB : 0 < B.radius) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.ndilate rho).IsRankRegular := by
  classical
  let d : ℕ := 2 * max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B hB)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_ndilate_iff]
  dsimp only [rank_ndilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.ndilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.ndilate splus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.ndilate rho).carrier.card : ℝ) -
          Real.log ((B.ndilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.ndilate sminus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.ndilate rho).carrier.card : ℝ) ≤
      ((B.ndilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
        exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.ndilate sminus).carrier.card := by
        exact_mod_cast (B.ndilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.ndilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.ndilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
      exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.ndilate splus).carrier.card := by
      exact_mod_cast (B.ndilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def torusChordCutoff (a : ℝ) (h : ℝ≥0) (v : ι → CircleFourier.Circle) : ℝ :=
  chordBoxCutoff a h (fun i => CircleFourier.character (v i))

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationWidth (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  rho * ⟨B.radius, B.radius_nonneg⟩

noncomputable def upperApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff B.radius (B.approximationWidth rho) (fun r : B.frequencies => character r x)

noncomputable def lowerApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)
    (fun r : B.frequencies => character r x)

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem add_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x + y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using add_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem sub_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x - y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using sub_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem uniformMass_translation_le_shell (B : Set N) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1) {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      (((B.ndilate (1 + kappa)).carrier.card : ℝ) - (B.ndilate (1 - kappa)).carrier.card) /
        B.carrier.card := by
  apply Erdos3.uniformMass_translation_le_shell
  · intro x hx
    constructor
    · have h := carrier_ndilate_mono (B := B) (show 1 - kappa ≤ 1 from tsub_le_self) hx
      simpa only [ndilate_one] using h
    · have h := sub_mem_ndilate (B := B) hx ht
      simpa only [tsub_add_cancel_of_le hkappa, ndilate_one, mem_iff, mem_carrier] using h
  · intro x hx
    rcases hx with hx | hx
    · have h := carrier_ndilate_mono (B := B) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
      apply h
      simpa only [ndilate_one] using hx
    · have h := add_mem_ndilate (B := B) (r := 1) (s := kappa)
        (x := x - t) (y := t) (by simpa only [ndilate_one, mem_iff, mem_carrier] using hx) ht
      simpa only [sub_add_cancel, mem_iff, mem_carrier] using h

theorem uniformMass_translation_le_of_rankRegular {B : Set N} (hreg : B.IsRankRegular)
    {kappa : ℝ≥0} (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      400 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
    · positivity
  have hcards := hreg kappa hkappa
  have hcenter : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  apply (uniformMass_translation_le_shell B hkappa_one ht).trans
  rw [div_le_iff₀ hcenter]
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

def whole : Set N := ofFrequencies {0} 1 (by norm_num)

@[simp] theorem rank_whole : (whole : Set N).rank = 1 := by simp [whole]

@[simp] theorem radius_whole : (whole : Set N).radius = 1 := rfl

@[simp] theorem carrier_whole : (whole : Set N).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [whole, mem_carrier, ofFrequencies]

theorem exists_controlled_regular_subdilate (B : Set N) (hB : 0 < B.radius)
    (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (r : ℝ) * B.radius / 2 ≤ C.radius ∧ C.radius ≤ r * B.radius ∧
      C.carrier ⊆ (B.ndilate r).carrier ∧
      ((r : ℝ) / 4) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ C.carrier.card := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hB0 : 0 < (B.ndilate r).radius := by
    rw [radius_ndilate]
    exact mul_pos hrR hB
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_ndilate (B.ndilate r) hB0
  let C := (B.ndilate r).ndilate rho
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have hC : C.radius = (rho : ℝ) * ((r : ℝ) * B.radius) := by simp only [C, radius_ndilate]
  refine ⟨C, rfl, hreg, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · have h := carrier_ndilate_mono (B := B.ndilate r) hrho1
    simpa only [ndilate_one] using h
  · have hprod : 0 < (rho : ℝ) * r := mul_pos (by linarith) hrR
    have hprod1 : (rho : ℝ) * r ≤ 1 := by nlinarith
    have hvol := relative_card_lower_bound B hB hprod hprod1
    have hlower : (r : ℝ) / 4 ≤ ((rho : ℝ) * r) / 2 := by nlinarith
    have hcost := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ r / 4 by positivity) hlower (4 * B.rank))
      (Nat.cast_nonneg B.carrier.card : (0 : ℝ) ≤ B.carrier.card)
    have hfull := hcost.trans hvol
    simpa only [C, ndilate, dilate_dilate] using hfull

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

@[simp] theorem carrier_ndilate_whole (t : ℝ≥0) :
    ((whole : Set N).ndilate t).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, whole, ndilate, ofFrequencies, dilate]

theorem isRankRegular_whole : (whole : Set N).IsRankRegular := by
  intro kappa _
  simp only [rank_whole, max_self, Nat.mul_one, Nat.cast_ofNat, carrier_whole,
    carrier_ndilate_whole]
  have hcard : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod N)).card := Nat.cast_nonneg _
  constructor <;> nlinarith [mul_nonneg kappa.coe_nonneg hcard]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def torusUpperApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff B.radius (B.approximationWidth rho)

noncomputable def torusLowerApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ScaledPairBasisHeight
namespace OAI

section

namespace Erdos3

open Module

theorem exists_scaledPair_basis_height {ι α β L : Type*} [Fintype α] [Fintype β]
    [AddCommGroup L] [Module ℚ L] (e : Basis ι ℚ L)
    (P Q : Submodule ℚ L) (hQP : Q ≤ P) (a : Basis α ℚ Q) (b : Basis β ℚ P)
    (q : ℚ) {H K : ℕ} (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : RationalHeightLE q K)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ c : Basis (Fin (finrank ℚ (scaledPairLayer P Q q))) ℚ (scaledPairLayer P Q q),
      ∀ j k, RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
  classical
  let c := (a.prod b).map (scaledPairLayerEquiv P Q hQP q)
  have hHK : H ≤ H * K := Nat.le_mul_of_pos_right H (by omega)
  have hz (k : ι) : RationalHeightLE (e.repr 0 k) (H * K) := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero (hH.trans hHK)
  have hc (j : α ⊕ β) (k : ι) :
      RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
    rcases j with j | j
    · simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) (H * K) ∧
          RationalHeightLE (e.repr 0 k) (H * K) from ⟨(ha j k).mono hHK, hz k⟩)
    · have hmul : RationalHeightLE (q * e.repr (b j : L) k) (H * K) := by
        simpa only [Nat.mul_comm K H] using hq.mul (hb j k)
      simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble, smul_eq_mul] using
        (show RationalHeightLE (q * e.repr (b j : L) k) (H * K) ∧
          RationalHeightLE (e.repr (b j : L) k) (H * K) from ⟨hmul, (hb j k).mono hHK⟩)
  let c' := c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)
  exact ⟨c', fun j k => by simpa only [c', Basis.reindex_apply] using hc _ k⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedPairCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realPairEquiv :
    (ℝ ⊗[ℚ] (L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  TensorProduct.prodRight ℚ ℝ ℝ L L

@[simp] theorem realPairEquiv_tmul (r : ℝ) (x : L × L) :
    realPairEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2) := rfl

theorem realPairEquiv_first (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).1 = (LinearMap.fst ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

theorem realPairEquiv_second (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).2 = (LinearMap.snd ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

theorem realPairEquiv_difference (q : ℚ) (x : ℝ ⊗[ℚ] (L × L)) :
    scaledPairDifference q (realPairEquiv x) =
      (scaledPairDifference (L := L) q).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realPairEquiv_tmul, LinearMap.baseChange_tmul, scaledPairDifference_apply,
      TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedSpanningPadding
namespace OAI

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)

theorem exists_bounded_ambient_spanning (v : η → K)
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a : L) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K.toSubmodule ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  obtain ⟨b, hb⟩ := exists_bounded_lie_subalgebra_basis e K v hspan hv
  have hr := lie_subalgebra_finrank_le e K
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < Module.finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (Module.finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dif_pos i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.incl.toLinearMap := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def spatialStarDensity {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ)
    (y : (Unit ⊕ I) → ℝ) : ℂ := f (spatialUnstar y)

noncomputable def spatialSiteApprox {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ)
    (v : (Unit ⊕ I) → ℤ) : ℂ :=
  maskedIntervalApprox b r H m (spatialStarDensity f) (latticeStarMask (pivotFullImage A B) m)
    (spatialStar v)

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

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev SpatialSiteLabel (I : Type*) (m : ℕ) (b r : ℝ) :=
  ((Unit ⊕ I) → ZMod m) × ((Unit ⊕ I) → Fin (intervalSiteCount b r))

noncomputable def spatialSiteCoefficient {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) (t : SpatialSiteLabel I m b r) : ℂ :=
  latticeStarMask (pivotFullImage A B) m t.1 *
    spatialStarDensity f (fun i => intervalSiteCenter b r (t.2 i))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def fiberComplexMean {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => if F x = r then f x else 0)

theorem sum_fiberComplexMean_on {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R) (f : X → ℂ) :
    (∑ r ∈ S, p.fiberComplexMean F r f) = p.complexMean (fun x => if F x ∈ S then f x else 0) := by
  unfold fiberComplexMean complexMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases h : F x ∈ S <;> simp [eq_comm, h]

theorem mass_mul_condition_complexMean {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) (hG : 0 < p.mass G) (f : X → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).complexMean f =
      p.complexMean (fun x => if x ∈ G then f x else 0) := by
  have h := p.mass_mul_condition_correlation G hG f (fun _ => 1)
  simpa only [correlation, complexMean, finiteMask_apply, star_one, mul_one] using h

theorem fiberComplexMean_eq_condition {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ)
    (hG : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    p.fiberComplexMean F r f =
      (p.mass (Finset.univ.filter (fun x => F x = r)) : ℂ) *
        (p.condition (Finset.univ.filter (fun x => F x = r)) hG).complexMean f := by
  rw [p.mass_mul_condition_complexMean]
  simp only [fiberComplexMean, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X C : Type*} [Fintype X] [DecidableEq X]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem exists_large_correlating_fiber (p : FiniteProbabilityWeights X)
    (cell : X → C) (f : X → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hbias : δ ≤ ‖p.complexMean f‖) :
    ∃ (c : C) (hc : 0 < p.mass (Finset.univ.filter (fun x => cell x = c))),
      δ / (2 * Fintype.card C) ≤ p.mass (Finset.univ.filter (fun x => cell x = c)) ∧
      δ / 2 ≤ ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hc).complexMean f‖ := by
  let mass := fun c => p.mass (Finset.univ.filter (fun x => cell x = c))
  let term := fun c => p.fiberComplexMean cell c f
  have hmass : (∑ c, mass c) = 1 := by
    simpa only [mass, ← p.fiberLaw_weight_eq_mass cell] using (p.fiberLaw cell).total
  have hsum : (∑ c, term c) = p.complexMean f := by
    simpa only [term, Finset.mem_univ, ite_true] using
      p.sum_fiberComplexMean_on cell Finset.univ f
  have hcap (c : C) : ‖term c‖ ≤ mass c := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    dsimp only [mass]
    rw [← p.mean_indicator (Finset.univ.filter (fun x => cell x = c))]
    apply p.mean_mono
    intro x
    by_cases hx : cell x = c
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_true] using hf x
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_false, norm_zero, le_refl]
  have hcard : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hscore : δ / (2 * Fintype.card C) ≤
      𝔼 c, (‖term c‖ - δ / 2 * mass c) := by
    rw [Fintype.expect_eq_sum_div_card, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_one]
    have hn := (norm_sum_le _ _).trans' (hsum.symm ▸ hbias)
    apply (le_div_iff₀ hcard).mpr
    have he : δ / (2 * Fintype.card C) * Fintype.card C = δ / 2 := by
      field_simp
    rw [he]
    linarith
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hscore
  have hsmall : 0 < δ / (2 * Fintype.card C) := div_pos hδ (by positivity)
  have hmass0 : 0 ≤ mass c := p.mass_nonneg _
  have hmasslower : δ / (2 * Fintype.card C) ≤ mass c := by
    nlinarith [hcap c]
  have hmasspos : 0 < mass c := hsmall.trans_le hmasslower
  refine ⟨c, hmasspos, hmasslower, ?_⟩
  have hid : ‖term c‖ = mass c *
      ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hmasspos).complexMean f‖ := by
    dsimp only [term]
    rw [p.fiberComplexMean_eq_condition cell c f hmasspos, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hmass0]
  rw [hid] at hc
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RestrictedSymbolAlgebraicMajorStep
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem BasisGradedSubmodule.coordinate_dilation_mem
    {R B : Type*} [Field R] [Fintype B]
    (w : B → ℕ) (K : Submodule R (B → R))
    (hK : BasisGradedSubmodule (Pi.basisFun R B) w K)
    (r : R) (x : B → R) (hx : x ∈ K) :
    (fun i => r ^ w i * x i) ∈ K := by
  classical
  have hprojection (j : ℕ) (i : B) :
      basisGradeProjection (Pi.basisFun R B) w j x i =
        if w i = j then x i else 0 := by
    simpa only [Pi.basisFun_repr] using
      basisGradeProjection_repr (Pi.basisFun R B) w j x i
  have hdilation : (fun i => r ^ w i * x i) =
      ∑ j ∈ Finset.univ.image w, r ^ j • basisGradeProjection (Pi.basisFun R B) w j x := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hprojection,
      mul_ite, mul_zero]
    simp
  rw [hdilation]
  exact K.sum_mem (fun j _ => K.smul_mem (r ^ j) (hK j x hx))

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Classical

variable {X B J ι L : Type*} [Fintype B] [Fintype J]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : B → ℕ)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def smoothPairCoefficientScale {J : Type*} (H L : ℝ) : Option J → ℝ :=
  fun c => match c with | none => H | some _ => H / L

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

noncomputable def smoothPairProbabilityError {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  normalizedFiberErrorConstant 2 (Fintype.card {j : J // j ≠ k}) Q
    (4 * C / κ) ((Fintype.card J : ℝ) * C) 1 1 (smoothPairRowLipschitz k) * δ

noncomputable def smoothPairProbabilityCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ : ℝ) : ℝ :=
  1 + (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothPairKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairProductDensity {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (y : I → Fin 2 → ℝ) : ℝ :=
  ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) hL
    (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalPairPointLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def fullSmoothPairError {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  n * smoothPairProbabilityError k Q C κ δ *
    (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ n

noncomputable def shiftedPairLocationKernel {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (b : Option J × I → ℤ) (x y : I → ℤ) : ℝ :=
  smoothPairProductDensity t u k hne H L hH hL
    (fun i j => ((affinePairRowsOfLocations (x, y) i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairKernelBaseCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelBaseLip {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
    2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelCap {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 := (smoothPairKernelBaseCap k C κ) ^ n

noncomputable def smoothPairKernelLip {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 :=
  n * smoothPairKernelBaseLip k C κ * smoothPairKernelCap n k C κ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
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

namespace Erdos3

noncomputable def smoothPairErrorCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : ℝ := fullSmoothPairError n k Q C κ 1

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def smoothPairRowErrorLog (d : ℕ) (P : ℝ) : ℝ :=
  (16 + 4 * d) * P + 16 * d + 48

noncomputable def smoothPairErrorLog (n d : ℕ) (P : ℝ) : ℝ :=
  P + smoothPairRowErrorLog d P + n * (smoothPairRowErrorLog d P + 6 * P + 12)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.TowerDominatingGrowth
namespace OAI

section

namespace Erdos3.FixedDensity

structure DescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth : ℕ) where
  level : Fin (depth + 1) → ℕ
  step_eq :
    ∀ i : Fin depth,
      level i.castSucc = F (level i.succ)

namespace DescendingGrowthHierarchy

theorem lower_le_growth
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) := by
  exact (Nat.le_succ _).trans
    (F.above_diagonal (H.level i.succ))

theorem growth_eq_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    F (H.level i.succ) = H.level i.castSucc :=
  (H.step_eq i).symm

theorem antitone
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth) :
    Antitone H.level := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  exact (H.lower_le_growth i).trans_eq
    (H.growth_eq_upper i)

end DescendingGrowthHierarchy

def canonicalDescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    DescendingGrowthHierarchy F depth where
  level q :=
    (F.toFun ^[depth - q.1]) bottom
  step_eq := by
    intro i
    have hexponent :
        depth - i.castSucc.1 =
          (depth - i.succ.1) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hexponent]
    exact Function.iterate_succ_apply'
      F.toFun (depth - i.succ.1) bottom

@[simp]
theorem canonicalDescendingGrowthHierarchy_last
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level (Fin.last depth) =
        bottom := by
  simp [canonicalDescendingGrowthHierarchy]

@[simp]
theorem canonicalDescendingGrowthHierarchy_zero
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level 0 =
        (F.toFun ^[depth]) bottom := by
  simp [canonicalDescendingGrowthHierarchy]

noncomputable def selectedGrowthCoarseComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j)

noncomputable def selectedGrowthFineComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j + 1)

noncomputable def selectedGrowthCoarseLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthCoarseComplexityBound
        k r initialBound F index j)

noncomputable def selectedGrowthFineLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthFineComplexityBound
        k r initialBound F index j)

structure GrowthFunctionOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt :
    ∀ j : Fin r,
      index j <
        growthRegularityLength k j.1 (γ j)
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound F index j) : ℝ))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        γ j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (coarse.partition q e) ≤
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F index q
  fine_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (fine.partition q e) ≤
        selectedGrowthFineLayerComplexityBound
          k r initialBound F index q

namespace GrowthFunctionOrderedComplexRegularityCertificate

end GrowthFunctionOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def growthRegularityOneStep
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  (2 ^ (j + 1)) ^
      growthRegularityStepBudget k j F M * M

@[simp]
theorem growthRegularityComplexity_succ_eq_oneStep
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      growthRegularityOneStep k j F
        (growthRegularityComplexity
          k j initialBound F n) :=
  rfl

noncomputable def boundedGrowthRegularityOneStepMaximum
    (k j : ℕ) (F : NatGrowthFunction) : ℕ → ℕ
  | 0 => growthRegularityOneStep k j F 0
  | M + 1 =>
      max
        (boundedGrowthRegularityOneStepMaximum k j F M)
        (growthRegularityOneStep k j F (M + 1))

theorem boundedGrowthRegularityOneStepMaximum_monotone
    (k j : ℕ) (F : NatGrowthFunction) :
    Monotone
      (boundedGrowthRegularityOneStepMaximum k j F) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [boundedGrowthRegularityOneStepMaximum]
  exact le_max_left _ _

noncomputable def finiteRankGrowthRegularityOneStepMaximum
    (k : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      max
        (finiteRankGrowthRegularityOneStepMaximum k F M r)
        (boundedGrowthRegularityOneStepMaximum k r F M)

theorem finiteRankGrowthRegularityOneStepMaximum_monotone
    (k r : ℕ) (F : NatGrowthFunction) :
    Monotone
      (fun M =>
        finiteRankGrowthRegularityOneStepMaximum
          k F M r) := by
  intro a b hab
  induction r with
  | zero =>
      simp [finiteRankGrowthRegularityOneStepMaximum]
  | succ r ih =>
      simp only [finiteRankGrowthRegularityOneStepMaximum]
      exact max_le_max ih
        (boundedGrowthRegularityOneStepMaximum_monotone
          k r F hab)

noncomputable def towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) :
    NatGrowthFunction where
  toFun M :=
    max (M + 1)
      (max (F M)
        (finiteRankGrowthRegularityOneStepMaximum
          k F M r))
  monotone' := by
    intro a b hab
    exact max_le_max
      (Nat.add_le_add_right hab 1)
      (max_le_max
        (F.monotone hab)
        (finiteRankGrowthRegularityOneStepMaximum_monotone
          k r F hab))
  above_diagonal := by
    intro M
    exact le_max_left _ _

@[simp]
theorem towerDominatingGrowth_apply
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    towerDominatingGrowth k r F M =
      max (M + 1)
        (max (F M)
          (finiteRankGrowthRegularityOneStepMaximum
            k F M r)) :=
  rfl

noncomputable def towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ℕ → NatGrowthFunction
  | 0 => F
  | stage + 1 =>
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage)

@[simp]
theorem towerDominatingGrowthIteration_zero
    (k r : ℕ) (F : NatGrowthFunction) :
    towerDominatingGrowthIteration k r F 0 = F :=
  rfl

@[simp]
theorem towerDominatingGrowthIteration_succ
    (k r : ℕ) (F : NatGrowthFunction) (stage : ℕ) :
    towerDominatingGrowthIteration k r F (stage + 1) =
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage) :=
  rfl

def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))

namespace GrowthFunctionOrderedComplexRegularityCertificate

noncomputable def selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) 1 :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level (Fin.last 1) =
      selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level 0 =
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  simp [selectedRankTowerHierarchy]

noncomputable def selectedFineLayerMaximum
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) : ℕ :=
  finiteMaximum (r + 1)
    (selectedGrowthFineLayerComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index)

noncomputable def selectedAllRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) r :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

@[simp]
theorem selectedAllRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    (selectedAllRankTowerHierarchy R).level (Fin.last r) =
      selectedFineLayerMaximum R := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

end GrowthFunctionOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

theorem massCoeff_realUniformMass (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (realUniformMass A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (realUniformMass A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realUniformMass, hx]
      · simp
      · intro x hxU hxA
        simp [realUniformMass, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
    (A : Finset G) (hA : A.Nonempty) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum A (1 / 2)) :
    ‖massCoeff (realUniformMass A) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hspectrum :
      ‖Chang.spectrumSum A ψ‖ < (1 / 2 : ℝ) * A.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (realUniformMass A) ψ‖ =
        (A.card : ℝ)⁻¹ * ‖Chang.spectrumSum A ψ‖ := by
      rw [massCoeff_realUniformMass, norm_mul]
      simp [norm_inv]
    _ < (A.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * A.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

omit [DecidableEq G] in

theorem massCoeff_massConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (massConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff massConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp)
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [realUniformMass]
      · intro y hy
        simp [realUniformMass, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_massConvolution, ihn, pow_succ]

omit [DecidableEq G] in

theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hw x]

end

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {N : ℕ} [NeZero N]

theorem convolutionPower_realUniformMass_support
    (B : CyclicBohr.Set N) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (realUniformMass (B.ndilate σ).carrier) n x ≠ 0 →
      x ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (realUniformMass_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa only [Nat.cast_zero, zero_mul, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using (B.ndilate 0).zero_mem
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, massConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (realUniformMass (B.ndilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : realUniformMass (B.ndilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.ndilate σ).carrier :=
        (realUniformMass_ne_zero_iff
          (B.ndilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := CyclicBohr.Set.add_mem_ndilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp
      rw [hxsum] at hadd
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hadd

def bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) : (ZMod N) → ℝ :=
  massConvolution
    (realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (realUniformMass (B.ndilate σ).carrier) n)

theorem bohrSmoothingMeasure_nonneg (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (x : (ZMod N)) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact massConvolution_nonneg
    (realUniformMass_nonneg _)
    (convolutionPower_nonneg (realUniformMass_nonneg _) n) x

theorem sum_bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : (ZMod N), bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_massConvolution,
    sum_realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_realUniformMass (B.ndilate σ).carrier_nonempty), one_mul]

theorem bohrSmoothingMeasure_apply_of_mem
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) {x : (ZMod N)} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, massConvolution_comm]
  simp only [massConvolution]
  calc
    ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_realUniformMass_support B σ n t hνt
        have hxt : x - t ∈
            (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact CyclicBohr.Set.sub_mem_ndilate
            (B := B) (r := 1) (s := (n : ℝ≥0) * σ)
            (by simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
              CyclicBohr.Set.mem_carrier] using hx) htB
        rw [realUniformMass_apply_mem hxt]
    _ = (∑ t : (ZMod N),
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t) *
        (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_realUniformMass (B.ndilate σ).carrier_nonempty)]
      simp

theorem card_dilate_one_add_le_two_mul
    {B : CyclicBohr.Set N} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := 2 * max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar (ZMod N) ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (realUniformMass (B.ndilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_massConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (realUniformMass
        (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_realUniformMass
      (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := realUniformMass
          (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
        (realUniformMass_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

end

end Erdos3

end

section

open AddChar _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [realUniformMass, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ∑ x : G,
        ((realUniformMass A x - realUniformMass A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (realUniformMass A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (realUniformMass A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

variable {N : ℕ} [NeZero N]

theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : (ZMod N), (realUniformMass C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : (ZMod N),
          ((realUniformMass C.carrier x -
              realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : (ZMod N),
            ‖((realUniformMass C.carrier x -
                realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := hphase
      _ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 800 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  classical
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

noncomputable def initialSamplingScale (B : Set N) : ℝ≥0 :=
  1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped Pointwise NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxOverlapSize
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem weight_correlating_large_overlaps {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) {ρ B δ : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) - δ * (cubeDifferenceSupport Q).card / Q.card ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  classical
  let I := cubeDifferenceSupport Q
  let w := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let good := fun h => ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
    (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖
  let small := fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card
  have hw (h : A) : 0 ≤ w h := by dsimp [w]; positivity
  have hpoint (h : A) : w h * (if good h then (1 : ℝ) else 0) ≤
      w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) + (if small h then w h else 0) := by
    by_cases hg : good h <;> by_cases hs : small h <;> simp [hg, hs, hw]
  have hsplit := Finset.sum_le_sum (fun h (_ : h ∈ I) => hpoint h)
  rw [Finset.sum_add_distrib] at hsplit
  have hgood := weight_correlating_overlaps hQ f u hρ hB hf hu hcorr
  change ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ I, w h * (if good h then (1 : ℝ) else 0) at hgood
  have hsmall : (∑ h ∈ I, if small h then w h else 0) ≤ δ * I.card / Q.card := by
    rw [← Finset.sum_filter]
    exact weight_small_overlaps hQ hδ
  have hresult : ρ ^ 2 / (2 * B ^ 2) - δ * I.card / Q.card ≤
      ∑ h ∈ I, w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) := by linarith
  simpa only [I, w, good, small, not_le] using hresult

theorem weight_correlating_large_box_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (f u : (ι → ℤ) → ℂ)
    {ρ B δ : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ translatedIntegerBox a T, ‖f x‖ ≤ 1)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation (translatedIntegerBox a T) f u‖) :
    let Q := translatedIntegerBox a T
    ρ ^ 2 / (2 * B ^ 2) - 2 ^ Fintype.card ι * δ ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  let Q := translatedIntegerBox a T
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hd : ((cubeDifferenceSupport Q).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * Q.card := by
    exact_mod_cast card_box_differenceSupport_le a T
  have hloss : δ * (cubeDifferenceSupport Q).card / Q.card ≤ 2 ^ Fintype.card ι * δ := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hδ]
  exact le_trans (by linarith) (weight_correlating_large_overlaps hQ f u hρ hB hδ hf hu hcorr)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem box_gowers_lower_bound_of_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (j : ℕ)
    (f : (ι → ℤ) → ℂ) (P : (ι → ℤ) → Prop) [DecidablePred P]
    {δ η μ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport (translatedIntegerBox a T),
      (((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) /
        ((translatedIntegerBox a T).card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0))
    (hretained : ∀ h ∈ cubeDifferenceSupport (translatedIntegerBox a T), P h →
      δ * (translatedIntegerBox a T).card ≤
        ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ) ∧
      η ≤ finiteSupportGowersNorm (j + 1) (derivativeSupport (translatedIntegerBox a T) h)
        (multiplicativeDerivative f h)) :
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        η ^ (2 ^ (j + 1)) * μ ≤
      finiteSupportGowersNorm (j + 2) (translatedIntegerBox a T) f ^ (2 ^ (j + 2)) := by
  let Q := translatedIntegerBox a T
  let c := ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι
  let K := c * δ ^ (j + 1) * η ^ (2 ^ (j + 1))
  let W := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let V := fun h => (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) : ℝ) /
    Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ)))
  let N := fun h => finiteSupportGowersNorm (j + 1) (derivativeSupport Q h) (multiplicativeDerivative f h)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hN (h : ι → ℤ) : 0 ≤ N h := by
    have hφ := (translatedIntegerBox_reflectsPairSums T a).mono
      (fun _ hx => (Finset.mem_filter.mp hx).1 :
        (derivativeSupport Q h : Set (ι → ℤ)) ⊆ (Q : Set (ι → ℤ)))
    dsimp [N]
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg j _ _
  have hpoint (h : ι → ℤ) (hh : h ∈ cubeDifferenceSupport Q) :
      K * (W h * (if P h then (1 : ℝ) else 0)) ≤ V h * N h ^ (2 ^ (j + 1)) := by
    by_cases hp : P h
    · simp only [if_pos hp, mul_one]
      have hw : c * δ ^ (j + 1) * W h ≤ V h :=
        box_overlap_cube_weight a T j hh hδ (hretained h hh hp).1
      have hn : η ^ (2 ^ (j + 1)) ≤ N h ^ (2 ^ (j + 1)) :=
        pow_le_pow_left₀ hη (hretained h hh hp).2 _
      calc
        _ = (c * δ ^ (j + 1) * W h) * η ^ (2 ^ (j + 1)) := by dsimp [K]; ring
        _ ≤ _ := mul_le_mul hw hn (pow_nonneg hη _) (by dsimp [V]; positivity)
    · simp only [if_neg hp, mul_zero]
      exact mul_nonneg (by dsimp [V]; positivity) (pow_nonneg (hN h) _)
  calc
    _ ≤ K * (∑ h ∈ cubeDifferenceSupport Q, W h * (if P h then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hμ hK
    _ = ∑ h ∈ cubeDifferenceSupport Q, K * (W h * (if P h then (1 : ℝ) else 0)) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ h ∈ cubeDifferenceSupport Q, V h * N h ^ (2 ^ (j + 1)) := Finset.sum_le_sum hpoint
    _ = _ := (finiteSupportGowersNorm_derivative (translatedIntegerBox_reflectsPairSums T a)
      (translatedIntegerBox_nonempty T a) j f).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem side_gt_of_prod_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : ι → ℝ) (hS : ∀ i, 0 ≤ S i) (hT : ∀ i, 0 < T i)
    (hST : ∀ i, S i ≤ T i) {δ : ℝ}
    (hprod : δ * ∏ i, T i < ∏ i, S i) (i : ι) : δ * T i < S i := by
  have hrest : (∏ j ∈ Finset.univ.erase i, S j) ≤ ∏ j ∈ Finset.univ.erase i, T j :=
    Finset.prod_le_prod (fun j _ => hS j) (fun j _ => hST j)
  have hrestpos : 0 < ∏ j ∈ Finset.univ.erase i, T j := Finset.prod_pos (fun j _ => hT j)
  have hbound : (∏ j, S j) ≤ S i * ∏ j ∈ Finset.univ.erase i, T j := by
    rw [← Finset.mul_prod_erase Finset.univ S (Finset.mem_univ i)]
    exact mul_le_mul_of_nonneg_left hrest (hS i)
  have hlt := hprod.trans_le hbound
  rw [← Finset.mul_prod_erase Finset.univ T (Finset.mem_univ i), ← mul_assoc] at hlt
  exact (mul_lt_mul_iff_left₀ hrestpos).mp hlt

theorem box_overlap_side_gt_of_card_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (h : ι → ℤ) {δ : ℝ}
    (hcard : δ * (translatedIntegerBox a T).card <
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) (i : ι) :
    δ * T i < (((T i : ℤ) - |h i|).toNat : ℝ) := by
  have hlen (j : ι) : ((T j : ℤ) - |h j|).toNat ≤ T j := by
    have ha := abs_nonneg (h j)
    omega
  apply side_gt_of_prod_gt (fun j => (((T j : ℤ) - |h j|).toNat : ℝ))
    (fun j => (T j : ℝ)) (fun j => Nat.cast_nonneg _) (fun j => by exact_mod_cast hT j)
    (fun j => by exact_mod_cast hlen j) _ i
  rw [derivativeSupport_translatedIntegerBox] at hcard
  simpa only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hcard

theorem cardinality_ge_overlap_weight {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (I : Finset A) (P : A → Prop) [DecidablePred P]
    {μ : ℝ}
    (hweight : μ ≤ ∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) :
    μ * Q.card ≤ ((I.filter P).card : ℝ) := by
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hbound (h : A) : ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤
      1 / Q.card := by
    have hc : ((derivativeSupport Q h).card : ℝ) ≤ Q.card := by
      exact_mod_cast Finset.card_filter_le Q (fun x => x + h ∈ Q)
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  have hsum : (∑ h ∈ I, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
      (if P h then (1 : ℝ) else 0)) ≤ ((I.filter P).card : ℝ) / Q.card := by
    calc
      _ = ∑ h ∈ I.filter P, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
      _ ≤ ∑ _h ∈ I.filter P, 1 / (Q.card : ℝ) := Finset.sum_le_sum (fun h _ => hbound h)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact (le_div_iff₀ hq).mp (hweight.trans hsum)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CyclicProgressionCoordinates
namespace OAI

section

open scoped BigOperators

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

variable {N : ℕ}

def minParam (Q : CyclicCenteredGAP N) : Q.Param := fun _ => 0

def unitParam (Q : CyclicCenteredGAP N) (i : Fin Q.rank)
    (hi : 0 < Q.radius i) : Q.Param := fun j =>
  if hji : j = i then ⟨1, by subst j; omega⟩ else 0

def predParam (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) : Q.Param := fun j =>
  if hji : j = i then
    ⟨(x i : ℕ) - 1, by
      subst j
      have hx := (x i).isLt
      omega⟩
  else x j

@[simp] lemma minParam_apply (Q : CyclicCenteredGAP N) (i : Fin Q.rank) :
    (Q.minParam i : ℕ) = 0 := rfl

@[simp] lemma unitParam_apply_self (Q : CyclicCenteredGAP N)
    (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    (Q.unitParam i hi i : ℕ) = 1 := by
  simp [unitParam]

@[simp] lemma unitParam_apply_ne (Q : CyclicCenteredGAP N)
    (i j : Fin Q.rank) (hi : 0 < Q.radius i) (hji : j ≠ i) :
    (Q.unitParam i hi j : ℕ) = 0 := by
  simp [unitParam, hji]

@[simp] lemma predParam_apply_self (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (Q.predParam x i hi i : ℕ) = (x i : ℕ) - 1 := by
  simp [predParam]

@[simp] lemma predParam_apply_ne (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i j : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hji : j ≠ i) :
    (Q.predParam x i hi j : ℕ) = x j := by
  simp [predParam, hji]

lemma eval_eq_eval_minParam_add_sum {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param) :
    Q.eval x = Q.eval Q.minParam +
      ∑ i, (x i : ZMod N) * Q.step i := by
  simp only [eval, coeff, minParam, Fin.val_zero,
    Nat.cast_zero, Int.cast_sub, Int.cast_natCast,
    zero_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.cast_neg, Int.cast_natCast]
  ring

lemma eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    Q.eval (Q.unitParam i hi) = Q.eval Q.minParam + Q.step i := by
  rw [Q.eval_eq_eval_minParam_add_sum]
  congr 1
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  simp only [unitParam_apply_self, Nat.cast_one, one_mul]
  have hzero : ∑ j ∈ Finset.univ.erase i,
      ((Q.unitParam i hi j : ℕ) : ZMod N) * Q.step j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      exact Finset.ne_of_mem_erase hj
    simp [Q.unitParam_apply_ne i j hi hji]
  rw [hzero, zero_add]

lemma eval_predParam_add_eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    Q.eval (Q.predParam x i hi) + Q.eval (Q.unitParam i hradius) =
      Q.eval x + Q.eval Q.minParam := by
  have hpred := Q.eval_eq_eval_minParam_add_sum (Q.predParam x i hi)
  have hunit := Q.eval_unitParam i hradius
  have hx := Q.eval_eq_eval_minParam_add_sum x
  rw [hpred, hunit, hx]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          Q.step i =
        ∑ j, (x j : ZMod N) * Q.step j := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => (x j : ZMod N) * Q.step j) (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j =
      ∑ j ∈ Finset.univ.erase i, (x j : ZMod N) * Q.step j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Q.predParam_apply_ne x i j hi hji]
    rw [hrest, Q.predParam_apply_self]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    rw [← hxi]
    push_cast
    ring
  calc
    Q.eval Q.minParam +
          (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          (Q.eval Q.minParam + Q.step i) =
        Q.eval Q.minParam + Q.eval Q.minParam +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
            Q.step i) := by abel
    _ = Q.eval Q.minParam + Q.eval Q.minParam +
          ∑ j, (x j : ZMod N) * Q.step j := by rw [hsum]
    _ = Q.eval Q.minParam + (∑ j, (x j : ZMod N) * Q.step j) +
          Q.eval Q.minParam := by abel

lemma sum_predParam_add_one (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (∑ j, (Q.predParam x i hi j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ)) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Q.predParam x i hi j : ℕ) =
        ∑ j ∈ Finset.univ.erase i, (x j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)
  rw [hrest, Q.predParam_apply_self]
  omega

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_supported_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I] [DecidableEq X]
    (A : Finset X) (hA : A.Nonempty) (S : I → Finset X) (hSA : ∀ i, S i ⊆ A)
    (B : X → ℂ) (v : I → X → ℂ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hB : ∀ x ∈ A, ‖B x‖ ≤ 1) (hv : ∀ i x, x ∈ S i → ‖v i x‖ ≤ 1)
    (hsize : ∀ i, α ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, δ ≤ ‖𝔼 x ∈ S i, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      (α * δ) ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        (α * δ) ^ 2 / 2 ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ∧
        (α * δ) ^ 2 / 2 ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hA
  have hA : A.Nonempty := ⟨x₀, hx₀⟩
  let : Nonempty A := ⟨⟨x₀, hx₀⟩⟩
  let u (i : I) (x : A) := zeroExtendFinset (S i) (v i) x.val
  have huc (i : I) : α * δ ≤ ‖𝔼 x : A, B x.val * u i x‖ := by
    have heq : ‖𝔼 x : A, B x.val * u i x‖ =
        ((S i).card / (A.card : ℝ)) * ‖𝔼 x ∈ S i, B x * v i x‖ := by
      change ‖𝔼 x : A, B x.val * zeroExtendFinset (S i) (v i) x.val‖ = _
      rw [expect_finset_subtype A (fun x => B x * zeroExtendFinset (S i) (v i) x)]
      simp_rw [zeroExtendFinset_mul_left]
      exact norm_expect_zeroExtendFinset A (S i) (hSA i) _
    rw [heq]
    exact mul_le_mul (hsize i) (hcorr i) hδ.le (by positivity)
  obtain ⟨P, hP, hPsize, hPcor⟩ := exists_dense_correlation_pairs
    (fun x : A => B x.val) u (mul_pos hα hδ) (fun x => hB x.val x.property)
    (fun i x => zeroExtendFinset_norm_le_one (S i) (v i) (hv i) x.val) huc
  refine ⟨P, hP, hPsize, ?_⟩
  intro t ht
  have hJA : S t.1 ∩ S t.2 ⊆ A := Finset.Subset.trans Finset.inter_subset_left (hSA t.1)
  have heq : ‖𝔼 x : A, u t.1 x * star (u t.2 x)‖ =
      ((S t.1 ∩ S t.2).card / (A.card : ℝ)) *
        ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ := by
    change ‖𝔼 x : A, zeroExtendFinset (S t.1) (v t.1) x.val *
      star (zeroExtendFinset (S t.2) (v t.2) x.val)‖ = _
    rw [expect_finset_subtype A (fun x => zeroExtendFinset (S t.1) (v t.1) x *
      star (zeroExtendFinset (S t.2) (v t.2) x))]
    simp_rw [zeroExtendFinset_mul_star]
    exact norm_expect_zeroExtendFinset A (S t.1 ∩ S t.2) hJA _
  have hp := hPcor t ht
  rw [heq] at hp
  have hpos : 0 < (α * δ) ^ 2 / 2 := by positivity
  have hJ : (S t.1 ∩ S t.2).Nonempty := by
    by_contra hempty
    have he : S t.1 ∩ S t.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hp
    exact (not_le_of_gt hpos) hp
  have hnorm : ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hJ 1)
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x hx₁)).trans (hv t.2 x hx₂)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((S t.1 ∩ S t.2).card / (A.card : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hApos).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Finset.card_le_card hJA) :
      ((S t.1 ∩ S t.2).card : ℝ) ≤ A.card)
  refine ⟨hJ, ?_, ?_⟩
  · exact hp.trans ((mul_le_mul_of_nonneg_right hratio (norm_nonneg _)).trans_eq (one_mul _))
  · exact hp.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (mul_one _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProperAffineBoxRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def centeredScalarBlock (R k : ℕ) (x : ℤ) : ℕ :=
  (x + (R : ℤ)).toNat / (2 * (R / (2 * k)) + 1)

def centeredScalarCenter (R k c : ℕ) : ℤ :=
  (c : ℤ) * (2 * (R / (2 * k) : ℕ) + 1) - R + (R / (2 * k) : ℕ)

theorem centeredScalarBlock_lt (R k : ℕ) (hk : 0 < k) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) : centeredScalarBlock R k x < 4 * k := by
  have htwo : 0 < 2 * k := by omega
  have hR := Nat.lt_mul_div_succ R htwo
  have ht : (x + (R : ℤ)).toNat ≤ 2 * R := by
    have h := abs_le.mp hx
    omega
  have hku : 0 ≤ k * (R / (2 * k)) := Nat.zero_le _
  have hcover : 2 * R < 4 * k * (2 * (R / (2 * k)) + 1) := by
    nlinarith only [hR, hku]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * (R / (2 * k)) + 1)).mpr
  exact ht.trans_lt hcover

theorem centeredScalarCenter_offset (R k : ℕ) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) :
    |x - centeredScalarCenter R k (centeredScalarBlock R k x)| ≤ (R / (2 * k) : ℕ) := by
  let t := (x + (R : ℤ)).toNat
  let L := 2 * (R / (2 * k)) + 1
  have ht : (t : ℤ) = x + R := by
    apply Int.toNat_of_nonneg
    have h := abs_le.mp hx
    omega
  have hmod : t % L < L := Nat.mod_lt t (by dsimp [L]; omega)
  have hrem : ((t % L : ℕ) : ℤ) + (L : ℤ) * (t / L : ℕ) = x + R := by
    rw [← ht]
    exact_mod_cast Nat.mod_add_div t L
  have hcancel : x - centeredScalarCenter R k (centeredScalarBlock R k x) =
      (t % L : ℕ) - (R / (2 * k) : ℕ) := by
    unfold centeredScalarCenter centeredScalarBlock
    change x - ((t / L : ℕ) * (2 * ((R / (2 * k) : ℕ) : ℤ) + 1) - R +
      ((R / (2 * k) : ℕ) : ℤ)) = ((t % L : ℕ) : ℤ) - ((R / (2 * k) : ℕ) : ℤ)
    have hL : (L : ℤ) = 2 * ((R / (2 * k) : ℕ) : ℤ) + 1 := by
      simp only [L, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hL] at hrem
    nlinarith only [hrem]
  have hmod' : ((t % L : ℕ) : ℤ) ≤ 2 * ((R / (2 * k) : ℕ) : ℤ) := by
    have h : t % L ≤ 2 * (R / (2 * k)) := Nat.le_of_lt_succ hmod
    exact_mod_cast h
  rw [hcancel, abs_le]
  constructor <;> linarith only [hmod', Int.natCast_nonneg (t % L)]

theorem exists_dense_centered_box_block {ι α : Type*} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (x : α → ι → ℤ) (R : ι → ℕ)
    (k : ℕ) (hk : 0 < k) (hbound : ∀ a ∈ S, ∀ i, |x a i| ≤ (R i : ℤ)) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ (4 * k) ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℤ, ∀ a ∈ T, ∀ i, |x a i - c i| ≤ (R i / (2 * k) : ℕ) := by
  classical
  have hfour : 0 < 4 * k := by omega
  let : NeZero (4 * k) := ⟨hfour.ne'⟩
  let label (a : α) (i : ι) : Fin (4 * k) :=
    ⟨centeredScalarBlock (R i) k (x a i) % (4 * k), Nat.mod_lt _ hfour⟩
  obtain ⟨b, hT, hsize⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter fun a => label a = b
  refine ⟨T, Finset.filter_subset _ _, hT, ?_,
    (fun i => centeredScalarCenter (R i) k (b i).val), ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · intro a ha i
    have hmem := (Finset.mem_filter.mp ha).1
    have heq := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    have hlt := centeredScalarBlock_lt (R i) k hk (x a i) (hbound a hmem i)
    change centeredScalarBlock (R i) k (x a i) % (4 * k) = (b i).val at heq
    rw [Nat.mod_eq_of_lt hlt] at heq
    change |x a i - centeredScalarCenter (R i) k (b i).val| ≤ (R i / (2 * k) : ℕ)
    rw [← heq]
    exact centeredScalarCenter_offset (R i) k (x a i) (hbound a hmem i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_proper_coordinate_restriction
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (x : {h // h ∈ J} → Fin r → ℤ)
    (hx : ∀ h i, |x h i| ≤ (R i : ℤ))
    (hrepr : ∀ h, h.val = a + η (x h)) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    ∃ (T : Finset G) (hTJ : T ⊆ J), T.Nonempty ∧
      J.card ≤ (4 * k) ^ r * T.card ∧
      ∃ c : Fin r → ℤ,
        Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
        ∀ h : {h // h ∈ T}, ∀ i,
          |x ⟨h.val, hTJ h.property⟩ i - c i| ≤ (R i / (2 * k) : ℕ) := by
  intro k
  classical
  let : Nonempty {h // h ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  have hk : 0 < k := Nat.succ_pos _
  have hproper := injOn_shrunk_integer_box_of_distinct_points J hJ R η a
    (fun h hh => ⟨x ⟨h, hh⟩, hx ⟨h, hh⟩, hrepr ⟨h, hh⟩⟩)
  obtain ⟨U, _hUuniv, hU, hsize, c, hsmall⟩ :=
    exists_dense_centered_box_block (Finset.univ : Finset {h // h ∈ J})
      Finset.univ_nonempty x R k hk (fun h _ => hx h)
  let T := U.image Subtype.val
  have hTJ : T ⊆ J := by
    intro h hh
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hh
    exact h'.property
  have hcard : T.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, hTJ, hU.image _, ?_, c, hproper, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_coe, Fintype.card_fin, hcard] using hsize
  · intro h i
    obtain ⟨h', hh', heq⟩ := Finset.mem_image.mp h.property
    have hident : h' = ⟨h.val, hTJ h.property⟩ := Subtype.ext heq
    simpa only [hident] using hsmall h' hh' i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FourBalancedDual
namespace OAI

section

namespace Erdos3

variable {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup E] [Module R E]

def fourDiagonalMap : V →ₗ[R] (Fin 4 → V) := LinearMap.pi (fun _ => LinearMap.id)

theorem four_annihilator_decomposition (C D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourCommonModulo C D) :
    ℓ v = ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (fourAlternatingMap (R := R) v)) := by
  let a := fourAlternatingMap (R := R) v
  have ha : a ∈ D := fourAlternatingMap_mem_dependent C D v hv
  let z : Fin 4 → V := fun k => v k - v 0 - (Pi.single (0 : Fin 4) a : Fin 4 → V) k
  have hz : z ∈ fourBalancedDependent D := by
    apply (mem_fourBalancedDependent D z).mpr
    refine ⟨?_, ?_⟩
    · intro k
      apply D.sub_mem (((mem_fourCommonModulo C D v).mp hv).2 k)
      by_cases hk : k = 0
      · subst k; simpa only [Pi.single_eq_same] using ha
      · simpa only [Pi.single_eq_of_ne hk] using D.zero_mem
    · change (v 0 - v 0 - a) + (v 1 - v 0 - 0) - (v 2 - v 0 - 0) - (v 3 - v 0 - 0) = 0
      dsimp only [a]
      rw [fourAlternatingMap_apply]
      abel
  have h := hℓ z hz
  change ℓ (v - fourDiagonalMap (R := R) (v 0) -
    LinearMap.single R (fun _ : Fin 4 => V) 0 a) = 0 at h
  rw [map_sub, map_sub] at h
  calc
    ℓ v = (ℓ v - ℓ (fourDiagonalMap (R := R) (v 0))) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := (sub_add_cancel _ _).symm
    _ = ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 a) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := by rw [sub_eq_zero.mp h]
    _ = _ := add_comm _ _

theorem four_annihilator_common_zero (D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0) (v : V) (hv : v ∈ D) :
    ℓ (fourDiagonalMap (R := R) v) = 0 := by
  apply hℓ
  apply (mem_fourBalancedDependent D _).mpr
  exact ⟨fun _ => hv, by change v + v - v - v = 0; abel⟩

theorem four_refined_annihilator_identity (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourRefinedRelation C D K, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourRefinedRelation C D K) :
    ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (v 0 + v 1 - v 2 - v 3)) = 0 := by
  have h := four_annihilator_decomposition C D ℓ
    (fun z hz => hℓ z (fourBalancedDependent_le_refined C D K hz)) v
    (fourRefinedRelation_le_common C D hDC K hv)
  rw [fourAlternatingMap_apply] at h
  exact h.symm.trans (hℓ v hv)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHPairCoordinateMetric
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
  (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem lieBCH_pair_coordinates_bound (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ∀ i, |e.repr x₁ i| ≤ B) (hy₁ : ∀ i, |e.repr y₁ i| ≤ B)
    (hx₂ : ∀ i, |e.repr x₂ i| ≤ B) (hy₂ : ∀ i, |e.repr y₂ i| ≤ B)
    (hxx : ∀ i, |e.repr x₁ i - e.repr x₂ i| ≤ δ)
    (hyy : ∀ i, |e.repr y₁ i - e.repr y₂ i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x₁ y₁) k - e.repr (lieBCH s x₂ y₂) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x₁, y₁] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![x₂, y₂] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₁ i
    · exact hy₁ i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₂ i
    · exact hy₂ i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxx i
    · exact hyy i
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x₁ y₁) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₁ y₁ k
  have hevalw : aeval w P = e.repr (lieBCH s x₂ y₂) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₂ y₂ k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

theorem lieBCH_pair_coordinate_dist_le (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ‖e.equivFun x₁‖ ≤ B) (hy₁ : ‖e.equivFun y₁‖ ≤ B)
    (hx₂ : ‖e.equivFun x₂‖ ≤ B) (hy₂ : ‖e.equivFun y₂‖ ≤ B)
    (hxx : dist (e.equivFun x₁) (e.equivFun x₂) ≤ δ)
    (hyy : dist (e.equivFun y₁) (e.equivFun y₂) ≤ δ) :
    dist (e.equivFun (lieBCH s x₁ y₁)) (e.equivFun (lieBCH s x₂ y₂)) ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  apply (dist_pi_le_iff (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H (by linarith)) hδ)).mpr
  intro i
  have hcoord (x : L) (hx : ‖e.equivFun x‖ ≤ B) (j : ι) : |e.repr x j| ≤ B := by
    calc
      _ ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using norm_le_pi_norm (e.equivFun x) j
      _ ≤ B := hx
  have hdiff (x y : L) (hxy : dist (e.equivFun x) (e.equivFun y) ≤ δ) (j : ι) :
      |e.repr x j - e.repr y j| ≤ δ := by
    calc
      _ ≤ dist (e.equivFun x) (e.equivFun y) := by
        simpa only [Real.dist_eq, Basis.equivFun_apply] using dist_le_pi_dist (e.equivFun x) (e.equivFun y) j
      _ ≤ δ := hxy
  exact lieBCH_pair_coordinates_bound e c hstructure hc x₁ y₁ x₂ y₂ hB hδ
    (hcoord _ hx₁) (hcoord _ hy₁) (hcoord _ hx₂) (hcoord _ hy₂) (hdiff _ _ hxx) (hdiff _ _ hyy) i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DenseRowPhaseAlignment
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_row_phase_alignment {G X : Type*} [Fintype G] [Nonempty G]
    (Q : Finset G) (S : Finset X) (f : G → X → ℂ) {δ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdense : δ * Fintype.card G ≤ (Q.card : ℝ))
    (hcorr : ∀ t ∈ Q, ρ ≤ ‖𝔼 x ∈ S, f t x‖) :
    ∃ w : G → ℂ, (∀ t, ‖w t‖ ≤ 1) ∧ (∀ t, t ∉ Q → w t = 0) ∧
      δ * ρ ≤ (𝔼 t, 𝔼 x ∈ S, w t * f t x).re := by
  classical
  choose c hc hphase using fun t => exists_complex_unit_phase (𝔼 x ∈ S, f t x)
  let w (t : G) := if t ∈ Q then c t else 0
  have hpoint (t : G) : (𝔼 x ∈ S, w t * f t x).re =
      if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    rw [← Finset.mul_expect]
    by_cases ht : t ∈ Q
    · simp only [w, ht, ite_true, hphase, Complex.ofReal_re]
    · simp only [w, ht, ite_false, zero_mul, Complex.zero_re]
  have hsum : ρ * (Q.card : ℝ) ≤
      ∑ t : G, if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    calc
      _ = ∑ t : G, if t ∈ Q then ρ else 0 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun t _ => by
        by_cases ht : t ∈ Q
        · simpa only [ht, ite_true] using hcorr t ht
        · simp only [ht, ite_false, le_refl]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Q <;> simp [w, ht, hc]
  · intro t ht
    simp only [w, ht, ite_false]
  · rw [expect_re]
    simp_rw [hpoint]
    rw [Fintype.expect_eq_sum_div_card]
    apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    calc
      _ = (δ * Fintype.card G) * ρ := by ring
      _ ≤ (Q.card : ℝ) * ρ := mul_le_mul_of_nonneg_right hdense hρ
      _ = ρ * (Q.card : ℝ) := mul_comm _ _
      _ ≤ _ := hsum

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteSupportedPolynomialSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {V W R : Type*} [CommSemiring R]

noncomputable def polynomialOfFiniteCoefficientVector (S : Finset (V →₀ ℕ))
    (c : S → R) : MvPolynomial V R :=
  ∑ α : S, MvPolynomial.monomial α.val (c α)

theorem polynomialOfFiniteCoefficientVector_coeff (S : Finset (V →₀ ℕ))
    (c : S → R) (α : S) :
    (polynomialOfFiniteCoefficientVector S c).coeff α.val = c α := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum, Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    rw [coeff_monomial, if_neg]
    exact fun h => hβα (Subtype.ext h)
  · simp

theorem polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem
    (S : Finset (V →₀ ℕ)) (c : S → R) (β : V →₀ ℕ) (hβ : β ∉ S) :
    (polynomialOfFiniteCoefficientVector S c).coeff β = 0 := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum]
  apply Finset.sum_eq_zero
  intro α _
  rw [coeff_monomial, if_neg]
  exact fun h => hβ (h ▸ α.property)

theorem polynomialOfFiniteCoefficientVector_support_subset (S : Finset (V →₀ ℕ))
    (c : S → R) : (polynomialOfFiniteCoefficientVector S c).support ⊆ S := by
  classical
  intro β hβ
  by_contra hout
  exact (MvPolynomial.mem_support_iff.mp hβ)
    (polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c β hout)

theorem polynomialOfFiniteCoefficientVector_reconstruct (S : Finset (V →₀ ℕ))
    (P : MvPolynomial V R) (hP : P.support ⊆ S) :
    polynomialOfFiniteCoefficientVector S (fun exponent => P.coeff exponent.val) = P := by
  classical
  ext β
  by_cases hβ : β ∈ S
  · exact polynomialOfFiniteCoefficientVector_coeff S _ ⟨β, hβ⟩
  · rw [polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S _ β hβ]
    exact (MvPolynomial.notMem_support_iff.mp (fun h => hβ (hP h))).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialDenominatorGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem add_integerPolynomial_coefficientGrid (R : MvPolynomial σ ℚ)
    (I : MvPolynomial σ ℤ) (q : ℕ)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid q) :
    (fun α => (R + map (Int.castRingHom ℚ) I).coeff α) ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨fun α => z α + (q : ℤ) * I.coeff α, fun α => ?_⟩
  change (q : ℚ) * (R + map (Int.castRingHom ℚ) I).coeff α = _
  have hα : (q : ℚ) * R.coeff α = (z α : ℚ) := hz α
  simp only [MvPolynomial.coeff_add, coeff_map, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, mul_add, hα]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceParameterCellLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem complexMean_finitePushforward_relativeSlice {U T : Type*} [Fintype U] [Fintype T]
    (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [apply_ite, ite_mul]

theorem uniform_finitePushforward_complexMean {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] (f : U → T) (g : T → ℂ) :
    ((uniform U).finitePushforward f).complexMean g = 𝔼 u, g (f u) := by
  rw [complexMean_finitePushforward_relativeSlice, uniform_complexMean]

theorem uniform_condition_complexMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℂ) :
    ((uniform Ω).condition G hG).complexMean f = 𝔼 x ∈ G, f x := by
  have hc : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℂ) ≠ 0 := by
    have hgNat : G.card ≠ 0 := by
      intro hz
      rw [uniform_mass, hz, Nat.cast_zero, zero_div] at hG
      exact (lt_irrefl _ hG)
    exact_mod_cast hgNat
  have hm : (((uniform Ω).mass G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  apply (mul_left_cancel₀ hm)
  rw [mass_mul_condition_complexMean, uniform_complexMean, uniform_mass,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  field_simp

end FiniteProbabilityWeights

namespace BoxProgressionPartition

variable {I : Type*} [Fintype I] [DecidableEq I] {L : I → ℕ}
  [Nonempty (∀ i, Fin (L i))] (Q : ∀ i, FiniteProgressionPartition (L i))

end BoxProgressionPartition

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_complexMean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0, hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

end ResidueBoxSlice
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicSamplingMoments
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N k m : ℕ} [NeZero N]

theorem sum_setAverageTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (n : ℕ) :
    ∑ x, |setAverageTranslate A f x| ^ n ≤ ∑ x, |f x| ^ n := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp
  | succ n =>
    have hpoint (x : ZMod N) : |setAverageTranslate A f x| ^ (n + 1) ≤
        (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card := by
      have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
        rw [setAverageTranslate, abs_div, abs_of_pos hc]
        exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
      have hj := pow_sum_div_card_le_sum_pow (s := A)
        (fun a _ => abs_nonneg (f (x - a))) n
      calc
        _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
          pow_le_pow_left₀ (abs_nonneg _) habs _
        _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
          rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
        _ ≤ _ := div_le_div_of_nonneg_right hj hc.le
    calc
      _ ≤ ∑ x, (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ a ∈ A, ∑ x, |f (x - a)| ^ (n + 1)) / A.card := by
        rw [← Finset.sum_div, Finset.sum_comm]
      _ = (∑ _a ∈ A, ∑ x, |f x| ^ (n + 1)) / A.card := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
      _ = _ := by simp [hc.ne']

theorem sum_centeredTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (a : ZMod N) (hm : m ≠ 0) :
    ∑ x, |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hpoint (x : ZMod N) : |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m - 1) * (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _).trans
    exact add_pow_le (abs_nonneg _) (abs_nonneg _) _
  have hshift : (∑ x, |f (x - a)| ^ (2 * m)) = ∑ x, |f x| ^ (2 * m) :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ x, 2 ^ (2 * m - 1) *
        (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) +
        ∑ x, |setAverageTranslate A f x| ^ (2 * m)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift]
    _ ≤ 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) + ∑ x, |f x| ^ (2 * m)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (sum_setAverageTranslate_pow_le hA f _)) (by positivity)
    _ = _ := by
      rw [← pow_sub_one_mul (show 2 * m ≠ 0 by omega) (2 : ℝ)]
      ring

theorem global_sampleDeviation_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * (A.card : ℝ) ^ k * k *
        (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
  apply (global_sampleDeviation_moment (k := k) hA f hm).trans
  have hsum (a : Fin k → ZMod N) :
      ∑ x, ∑ i, |centeredTranslate A f x (a i)| ^ (2 * m) ≤
        k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : Fin k, 2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) :=
        Finset.sum_le_sum (fun i _ => sum_centeredTranslate_pow_le hA f (a i) hm)
      _ = _ := by simp
  calc
    _ ≤ (8 * m) ^ m * k ^ (m - 1) *
        ∑ _a ∈ A ^^ k, k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun a _ => hsum a)
      · positivity
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset_const, Nat.cast_pow]
      ring

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSamplerRelativeInduction
namespace OAI

section

namespace Erdos3

def finiteSplitPoint_linearPart {K : Type*} (keep : K → Prop) [DecidablePred keep] :
    ({k // keep k} → ℤ) →+ (K → ℤ) where
  toFun x := finiteSplitPoint keep x 0
  map_zero' := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]
  map_add' x y := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

end OAI

end


