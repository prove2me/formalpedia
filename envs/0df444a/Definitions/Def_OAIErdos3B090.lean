-- Prove2me | Definitions.Def_OAIErdos3B090
-- name    : OAIErdos3B090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T16:54:50.009523+00:00
-- url     : https://prove2.me/theorems/5603e992-9777-4b8d-aaf5-96f53b525705
-- title:
--   OpenAI Erdős-3 split, definitions bundle 91 of 105
-- statement:
--   Definitions bundle 91 of 105 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B089`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 91 available.
--
--   Modules: `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.abs_det_eq_of_same_integer_span`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.basis_norm_le_of_integral_combination`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.basis_norm_le_of_short_spanning_family`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.exists_integral_spanning_product_certificate`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.exists_same_lattice_basis_norm_product_le`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.exists_short_same_lattice_basis`, `OAI.Erdos3.CellRefinement.coordinatedMatchingScale`, `OAI.Erdos3.CellRefinement.coordinatedMatchingScaleLoss`, `OAI.Erdos3.CellRefinement.matchingWidthLoss`, `OAI.Erdos3.CellRefinement.refinementComparisonBudget`, `OAI.Erdos3.CellRefinement.refinementMatchingLoss`, `OAI.Erdos3.CellRefinement.refinementMatchingWidthLoss`, `OAI.Erdos3.CellRefinement.refinementRoundLoss`, `OAI.Erdos3.CellRefinement.refinementScaleLoss`, `OAI.Erdos3.CyclicBohr.Set.adjoinCharacters`, `OAI.Erdos3.CyclicBohr.Set.adjoinCharacters_subset_ndilate`, `OAI.Erdos3.CyclicBohr.Set.characterBasis`, `OAI.Erdos3.CyclicBohr.Set.exists_regular_bohr_of_relative_cover`, `OAI.Erdos3.CyclicBohr.Set.norm_one_sub_le_of_mem_characterBasis`, `OAI.Erdos3.CyclicBohr.Set.norm_one_sub_le_of_mem_characterBasis_addSpan`, `OAI.Erdos3.CyclicBohr.Set.norm_one_sub_le_of_relative_cover`, `OAI.Erdos3.CyclicBohr.Set.radius_adjoinCharacters`, `OAI.Erdos3.CyclicBohr.Set.radius_characterBasis`, `OAI.Erdos3.CyclicBohr.Set.rank_adjoinCharacters_le`, `OAI.Erdos3.CyclicBohr.Set.rank_characterBasis`, `OAI.Erdos3.CyclicCrootSisask.almostPeriodicityWidthConstant`, `OAI.Erdos3.CyclicCrootSisask.almostPeriodicityWidthConstant_pos`, `OAI.Erdos3.CyclicCrootSisask.chosen_scales_error_le`, `OAI.Erdos3.CyclicCrootSisask.convolutionMomentOrder_le`, `OAI.Erdos3.CyclicCrootSisask.convolutionMomentOrder_le_of_ratio`, `OAI.Erdos3.CyclicCrootSisask.crootSisaskSampleSize_le`, `OAI.Erdos3.CyclicCrootSisask.differenceEventProbability`, `OAI.Erdos3.CyclicCrootSisask.differenceEventProbability_eq_triple`, `OAI.Erdos3.CyclicCrootSisask.differenceEventProbability_self_zero`, `OAI.Erdos3.CyclicCrootSisask.exists_difference_event_of_probability_pos`, `OAI.Erdos3.CyclicCrootSisask.exists_local_bohr_triple_almostPeriods_relative`, `OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov`, `OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov_progression`, `OAI.Erdos3.CyclicCrootSisask.exists_quartic_local_almostPeriods`, `OAI.Erdos3.CyclicCrootSisask.finiteIndicator_eq_ofReal_realSetIndicator`, `OAI.Erdos3.CyclicCrootSisask.finiteSetAverage_ofReal`, `OAI.Erdos3.CyclicCrootSisask.iteratedFiniteSetAverage_ofReal`, `OAI.Erdos3.CyclicCrootSisask.localBoostedSampleSize_le`, `OAI.Erdos3.CyclicCrootSisask.local_sample_size_le_cubic`, `OAI.Erdos3.CyclicCrootSisask.mem_fourfold_difference_of_probability_pos`, `OAI.Erdos3.CyclicCrootSisask.old_frequency_scale_le_regularity`, `OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant`, `OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant_pos`, `OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovProgressionConstant`, `OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovProgressionConstant_pos`, `OAI.Erdos3.CyclicCrootSisask.rankQuarticFactor`, `OAI.Erdos3.CyclicCrootSisask.rankQuarticFactor_le_widthConstant`, `OAI.Erdos3.CyclicCrootSisask.rankQuarticFactor_pos`, `OAI.Erdos3.CyclicCrootSisask.samplingCubicFactor`, `OAI.Erdos3.CyclicCrootSisask.samplingCubicFactor_pos`, `OAI.Erdos3.CyclicCrootSisask.setAverageTranslate_eq_expect`, `OAI.Erdos3.CyclicCrootSisask.smoothedDifferenceEventProbability`, `OAI.Erdos3.CyclicCrootSisask.sqrt_le_exp_of_le_exp_two_mul`, `OAI.Erdos3.CyclicCrootSisask.triple_average_ofReal`, `OAI.Erdos3.CyclicCrootSisask.triple_translate_le_of_iterated_approx`, `OAI.Erdos3.FixedDensity.SourceBundleRemovalGrowthConditions.recOn`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.Bounded`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.Bounded.Certificate.rec`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.Bounded.castInitialBound`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.Certificate`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.Certificate.scale_antitone`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.boundedZero`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.factorLowerInitialBound`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.fixedUpperLayerComplexityFactor_sourceFullStageBudget`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.lowerInitialBound`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.lowerInitialBound_sourceFullStageBudget`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.node`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.nodeScale`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.nodeScale_node`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.nodeScale_node_castSucc`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.nodeScale_node_last`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.recOn`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.scaleFloor_le`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.scale_antitone`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullCommonTolerance_nodeScale`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageBound`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageBudget`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageFactor`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageFactor_succ`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageFactor_zero`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageNext`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageNext_ceiling`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStagePlan`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.sourceFullStageTolerance`, `OAI.Erdos3.FixedDensity.SourceFullCoarseTargetSchedule.zero`, `OAI.Erdos3.FixedDensity.adaptiveSelectedCoarseLayerBound`, `OAI.Erdos3.FixedDensity.sourceBundleDefectScale`, `OAI.Erdos3.FixedDensity.sourceBundleDensity`, `OAI.Erdos3.FixedDensity.sourceBundleRankwiseDefect`, `OAI.Erdos3.FixedDensity.sourceBundleRankwiseDensity`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalGrowth`, `OAI.Erdos3.FixedDensity.sourceBundleRemovalGrowth_apply`, `OAI.Erdos3.FixedDensity.sourceBundleSelectedScale`, `OAI.Erdos3.FixedDensity.sourceBundleSelectedScale_zero`, `OAI.Erdos3.FixedDensity.sourceFullCommonTolerance`, `OAI.Erdos3.FixedDensity.sourceFullRankGap`, `OAI.Erdos3.FreeNilpotentLieAlgebra`, `OAI.Erdos3.FreeNilpotentLieAlgebra.hom_ext`, `OAI.Erdos3.FreeNilpotentLieAlgebra.instLieAlgebra`, `OAI.Erdos3.FreeNilpotentLieAlgebra.instLieRing`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_mk`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_of`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lowerCentralSeries_eq_bot`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lowerCentralSeries_le_lift_ker`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk_eq_zero`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk_surjective`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk_truncation`, `OAI.Erdos3.FreeNilpotentLieAlgebra.of`, `OAI.Erdos3.IntegerBasisReduction.Mahler.IsCenteredReduction`, `OAI.Erdos3.IntegerBasisReduction.Mahler.IsCenteredReduction.abs_coefficient_le_one`, `OAI.Erdos3.IntegerBasisReduction.Mahler.IsRawFlagReduction`, `OAI.Erdos3.IntegerBasisReduction.Mahler.abs_centeredStep_apply_self_le`, `OAI.Erdos3.IntegerBasisReduction.Mahler.basisOfUpperTriangularUnits`, `OAI.Erdos3.IntegerBasisReduction.Mahler.basisOfUpperTriangularUnits_apply`, `OAI.Erdos3.IntegerBasisReduction.Mahler.basisReductionStandardPoint`, `OAI.Erdos3.IntegerBasisReduction.Mahler.centeredReductionMatrix`, `OAI.Erdos3.IntegerBasisReduction.Mahler.centeredReductionMatrix_apply_self`, `OAI.Erdos3.IntegerBasisReduction.Mahler.centeredReductionMatrix_isUnit_diagonal`, `OAI.Erdos3.IntegerBasisReduction.Mahler.centeredReductionMatrix_isUpperTriangular`, `OAI.Erdos3.IntegerBasisReduction.Mahler.centeredStep`, `OAI.Erdos3.IntegerBasisReduction.Mahler.exists_centeredReduction_of_linearIndependent`, `OAI.Erdos3.IntegerBasisReduction.Mahler.exists_centeredReduction_of_rawFlagReduction`, `OAI.Erdos3.IntegerBasisReduction.Mahler.exists_integerCombination_abs_le_half`, `OAI.Erdos3.IntegerBasisReduction.Mahler.exists_prefix_integerCombination_abs_le_half`, `OAI.Erdos3.IntegerBasisReduction.Mahler.exists_rawFlagReduction_of_linearIndependent`, `OAI.Erdos3.IntegerBasisReduction.Mahler.extendPrefix`, `OAI.Erdos3.IntegerBasisReduction.Mahler.extendPrefix_prefixIndex`, `OAI.Erdos3.IntegerBasisReduction.Mahler.integralEmbed_basisReductionStandardPoint`, `OAI.Erdos3.IntegerBasisReduction.Mahler.prefixIndex`, `OAI.Erdos3.IntegerBasisReduction.Mahler.prefixIndexEquivIio`, `OAI.Erdos3.IntegerBasisReduction.Mahler.prefixIndex_lt`, `OAI.Erdos3.IntegerBasisReduction.Mahler.prefixIndex_val`, `OAI.Erdos3.IntegerBasisReduction.Mahler.rawFlagReduction_diag_abs_le_half_of_not_unit`, `OAI.Erdos3.IntegerBasisReduction.Mahler.rawFlagReduction_diag_abs_le_one`, `OAI.Erdos3.IntegerBasisReduction.Mahler.shearMatrix`, `OAI.Erdos3.IntegerBasisReduction.Mahler.shearMatrix_apply_self`, `OAI.Erdos3.IntegerBasisReduction.Mahler.shearMatrix_det`, `OAI.Erdos3.IntegerBasisReduction.Mahler.shearMatrix_isUpperTriangular`, `OAI.Erdos3.IntegerBasisReduction.Mahler.sum_extendPrefix_mul`, `OAI.Erdos3.IsDenseCommonStrideBox.card_ratio`, `OAI.Erdos3.IsDenseCommonStrideBox.of_large_subbox`, `OAI.Erdos3.LocalConvolution.unbalancedErrorBudget`, `OAI.Erdos3.LocalConvolution.unbalancedMinimumWidth`, `OAI.Erdos3.LocalConvolution.unbalancedRankExtra`, `OAI.Erdos3.LocalConvolution.unbalancedReturnWidthLoss`, `OAI.Erdos3.LocalConvolution.unbalancedWidthLoss`, `OAI.Erdos3.MultidegreeLieFiltration.realPairEquiv_mem_dilationPairLayer`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairEquiv_mem_multidegree`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedDilationPairEquiv_symm_mem_multidegree`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_realification`, `OAI.Erdos3.NilpotentLieFiltration.HasNativeLowerDegreeOrbit`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_adapted_basis_with_top_subspace`, `OAI.Erdos3.NilpotentLieFiltration.quotientStep_exact_grid_supported`, `OAI.Erdos3.NilpotentLieFiltration.quotientStep_inner_grid_supported`, `OAI.Erdos3.NilpotentLieFiltration.quotientStep_outer_grid_supported`, `OAI.Erdos3.NilpotentLieFiltration.realPairEquiv_mem_dilationPairLayer`, `OAI.Erdos3.NilpotentLieFiltration.realifiedDilationPairEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realifiedDilationPairEquiv_coe`, `OAI.Erdos3.NilpotentLieFiltration.realifiedDilationPairEquiv_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realifiedDilationPairLayerEquiv`, `OAI.Erdos3.NilpotentLieFiltration.topSubspaceIdeal`, `OAI.Erdos3.Peeling.admissibleBohrCarriers`, `OAI.Erdos3.Peeling.admissibleBohrShape`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisBracketCoefficient`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisBracketCoefficient_natAbs_le`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_structureConstants`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_structure_height`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_structure_height_succ`, `OAI.Erdos3.PrimeCoordinateStable`, `OAI.Erdos3.PrimeRefinementUpperBound`, `OAI.Erdos3.RelativeChangSanders.exists_regular_relative_spectrum_controller`, `OAI.Erdos3.RelativeChangSanders.localChangBaseScale_le_one`, `OAI.Erdos3.RelativeChangSanders.localChangBaseScale_pos`, `OAI.Erdos3.RelativeChangSanders.local_dimension_le_quartic_of_cubic_sampling`, `OAI.Erdos3.ResiduePhysicalTruncationControl`, `OAI.Erdos3.ResiduePrimeCoordinateCell`, `OAI.Erdos3.ResiduePrimeCoordinateStable`, `OAI.Erdos3.adaptiveAffineCountLog`, `OAI.Erdos3.adaptiveAffineCutoff`, `OAI.Erdos3.adaptiveAffineShell`, `OAI.Erdos3.adaptiveAffineSideLog`, `OAI.Erdos3.adaptiveLeafCouplingWeights`, `OAI.Erdos3.adaptiveLeafPairMass`, `OAI.Erdos3.adaptiveLeafPairMass_sum`, `OAI.Erdos3.adaptiveLeafPairMass_sum_empty`, `OAI.Erdos3.affineAccuracyPolynomialBudget`, `OAI.Erdos3.affineAdaptiveDegreeBudget`, `OAI.Erdos3.affineCommonReferenceBudget`, `OAI.Erdos3.affineComparisonContraction`, `OAI.Erdos3.affineComparisonDegree`, `OAI.Erdos3.affineComparisonLengthLog`, `OAI.Erdos3.affineComparisonMoment`, `OAI.Erdos3.affineComparisonPrimeThreshold`, `OAI.Erdos3.affineComparisonRequiredOrder`, `OAI.Erdos3.affineComparisonScale`, `OAI.Erdos3.affineComparisonTail`, `OAI.Erdos3.affineCountLogBudget`, `OAI.Erdos3.affineCyclicTorusCarry`, `OAI.Erdos3.affineCyclicTorusCarry_identity`, `OAI.Erdos3.affineCyclicTorusLocalLift`, `OAI.Erdos3.affineCyclicTorusLocalLift_eq_sub_carry`, `OAI.Erdos3.affineFinalDegree`, `OAI.Erdos3.affineGlobalComparisonDegree`, `OAI.Erdos3.affineInitialPrimeMask`, `OAI.Erdos3.affineLocalDegreeBudget`, `OAI.Erdos3.affineLocalDegreeInputBudget`, `OAI.Erdos3.affineMandatoryPrimes`, `OAI.Erdos3.affineOrderPolynomialBudget`, `OAI.Erdos3.affineOuterDegreeInputBudget`, `OAI.Erdos3.affineParameterProductCoupling`, `OAI.Erdos3.affinePeriodParameterLaw`, `OAI.Erdos3.affinePeriodProductCoupling`, `OAI.Erdos3.affinePeriodResidueSample`, `OAI.Erdos3.affinePrimitiveLogBudget`, `OAI.Erdos3.affineReferenceInput`, `OAI.Erdos3.affineReferencePower`, `OAI.Erdos3.affineRemovalDepth`, `OAI.Erdos3.affineResidueTruncatedPairing`, `OAI.Erdos3.affineSampleAlphabetEquiv`, `OAI.Erdos3.affineSampleAlphabet_mean`, `OAI.Erdos3.affineSampleAlphabet_weight`, `OAI.Erdos3.affineSampleCoupling`, `OAI.Erdos3.affineSampleFixedParameter_mean`, `OAI.Erdos3.affineSampleKernel`, `OAI.Erdos3.affineSampleKernel_preserves_mean`, `OAI.Erdos3.affineSampleParameterCoupling`, `OAI.Erdos3.affineSampleParameterKernel`, `OAI.Erdos3.affineSampleParameterKernel_mean`, `OAI.Erdos3.affineSampleParameterKernel_preserves_mean`, `OAI.Erdos3.affineSampleProductCoupling`, `OAI.Erdos3.affineSamplerPrimeMask`, `OAI.Erdos3.affineShellLogBudget`, `OAI.Erdos3.affineSidePolynomialBudget`, `OAI.Erdos3.affine_box_card_le_radius_product`, `OAI.Erdos3.amplificationSourceRankLogConstant`, `OAI.Erdos3.baseChange_coordinate_eq`, `OAI.Erdos3.baseChange_coordinate_projector_repr`, `OAI.Erdos3.bch_coset_eq_of_coordinate_congruence`, `OAI.Erdos3.bracketLiftMatrix`, `OAI.Erdos3.bracketSystemLift_coordinates`, `OAI.Erdos3.bracketSystemLift_grid`, `OAI.Erdos3.bracketSystemLift_norm_bound`, `OAI.Erdos3.centeredCircleLift`, `OAI.Erdos3.centeredCircleLift_abs_le_half`, `OAI.Erdos3.centeredCircleLift_coe`, `OAI.Erdos3.centeredCircleLift_eq_sub_floor`, `OAI.Erdos3.centeredTorusLift`, `OAI.Erdos3.coarseResidueIndicator`, `OAI.Erdos3.coe_centeredCircleLift`, `OAI.Erdos3.cyclicIntegerKernel_eq_zero_of_lt_radii`, `OAI.Erdos3.cyclicIntegerKernel_nonzero_large_coordinate`, `OAI.Erdos3.cyclicIntegerKernel_normalized_covolume_le`, `OAI.Erdos3.dense_commonStride_slice_card_ratio`, `OAI.Erdos3.differenceCoordinate_eval`, `OAI.Erdos3.differenceCoordinate_same`, `OAI.Erdos3.differenceInput`, `OAI.Erdos3.differenceInput_mem_denominatorGrid`, `OAI.Erdos3.differenceInput_sub_mem_scaledGrid`, `OAI.Erdos3.exists_ambient_bracket_correction_polynomials`, `OAI.Erdos3.exists_bracket_correction_polynomials`, `OAI.Erdos3.exists_controlled_bracket_corrections`, `OAI.Erdos3.exists_controlled_cyclic_torus_model`, `OAI.Erdos3.exists_dense_common_sampled_box`, `OAI.Erdos3.exists_dense_common_sampled_box_of_seminorm`, `OAI.Erdos3.exists_lattice_basis_bounded_expansion`, `OAI.Erdos3.exists_lattice_basis_coordinate_bound`, `OAI.Erdos3.exists_localized_cyclic_torus_chart`, `OAI.Erdos3.exists_proper_affine_torus_basis`, `OAI.Erdos3.exists_proper_cyclic_kernel_basis`, `OAI.Erdos3.exists_short_independent_cyclic_kernel_vectors`, `OAI.Erdos3.finiteFourierCoeff_averagingKernel`, `OAI.Erdos3.finiteFourierCoeff_finiteIndicator`, `OAI.Erdos3.fourierL1_triple_average_le`, `OAI.Erdos3.fourierL1_triple_average_sq_le`, `OAI.Erdos3.freeLieTruncation_eq_zero_iff`, `OAI.Erdos3.freeLie_lowerCentralSeries_iff_low_coeff_zero`, `OAI.Erdos3.goodDifferenceSet`, `OAI.Erdos3.local_cyclic_torus_cell_count_le_exp`, `OAI.Erdos3.local_cyclic_torus_density`, `OAI.Erdos3.local_cyclic_torus_total_loss_le`, `OAI.Erdos3.maskedIntegerPeriodization`, `OAI.Erdos3.maskedIntegerTorusKernel`, `OAI.Erdos3.mem_periodPrimeCoordinates`, `OAI.Erdos3.mem_primeCoordinateCell`, `OAI.Erdos3.mem_primeCoordinateCell_anchor`, `OAI.Erdos3.missingCoordinateBound`, `OAI.Erdos3.missingCoordinateBound_le`, `OAI.Erdos3.missingCoordinateDownset`, `OAI.Erdos3.missingCoordinateDownset_covers`, `OAI.Erdos3.missingCoordinateDownset_lower`, `OAI.Erdos3.missingCoordinateDownset_terminal`, `OAI.Erdos3.modEq_selected_prod_iff`, `OAI.Erdos3.norm_eq_abs_centeredCircleLift`, `OAI.Erdos3.normalizedResiduePrimeDensity`, `OAI.Erdos3.periodPrimeCoordinates`, `OAI.Erdos3.physicalBoxResidual`, `OAI.Erdos3.physicalBoxTruncation`, `OAI.Erdos3.physicalMeanAccuracyLog`, `OAI.Erdos3.physicalPairCoefficientLog`, `OAI.Erdos3.physicalPairGridAccuracy`, `OAI.Erdos3.physicalPairMeanAccuracy`, `OAI.Erdos3.physicalPairMeanLog`, `OAI.Erdos3.physicalPairPointAccuracy`, `OAI.Erdos3.physicalReplacementInputLog`, `OAI.Erdos3.physicalReplacementScaleThreshold`, `OAI.Erdos3.physicalReplacementThresholdLog`, `OAI.Erdos3.physicalResidualPairBudget`, `OAI.Erdos3.polynomialBCHMap`, `OAI.Erdos3.polynomialBCHMap_coordinates`, `OAI.Erdos3.polynomialBCHMap_coset_eq`, `OAI.Erdos3.polynomialBCHPeriod`, `OAI.Erdos3.primeCoordinateCell`, `OAI.Erdos3.primeCoordinateCellEquiv`, `OAI.Erdos3.primeCoordinateCell_subtypeEquiv`, `OAI.Erdos3.primeCoordinateMassRatio`, `OAI.Erdos3.primeCoordinateMean`, `OAI.Erdos3.primeCoordinateObservation`, `OAI.Erdos3.primeCoordinateReference`, `OAI.Erdos3.primeCoordinatesMod`, `OAI.Erdos3.productAtomTruncatedPairing`, `OAI.Erdos3.productTruncatedPairing`, `OAI.Erdos3.properCyclicCoordinateBound`, `OAI.Erdos3.properCyclicCoordinateBound_le_exp`, `OAI.Erdos3.properCyclicCoordinateBound_nonneg`, `OAI.Erdos3.properCyclicKernelBasisBound`, `OAI.Erdos3.properCyclicKernelBasisBound_le_exp`, `OAI.Erdos3.properCyclicKernelBasisBound_nonneg`, `OAI.Erdos3.proper_cyclic_kernel_box_card_le_covolume`, `OAI.Erdos3.proper_cyclic_kernel_covolume_lower_bound`, `OAI.Erdos3.rationalMatrix_piScalarRight_baseChange`, `OAI.Erdos3.realPairEquiv_mem_scaledPairLayer`, `OAI.Erdos3.realPeriodicTorusLift`, `OAI.Erdos3.realPeriodicTorusLift_coe`, `OAI.Erdos3.realPeriodicTorusLift_lipschitz`, `OAI.Erdos3.realPeriodicTorusLift_range`, `OAI.Erdos3.realPolynomialBCHMap`, `OAI.Erdos3.realPolynomialBCHMap_coordinates`, `OAI.Erdos3.realPolynomialBCHMap_integer`, `OAI.Erdos3.realSupportedQuotientBasis_repr_mk`, `OAI.Erdos3.realificationLieHom_comp_apply`, `OAI.Erdos3.realificationLieHom_eq_self`, `OAI.Erdos3.realificationLieHom_eq_self_on`, `OAI.Erdos3.realification_coset_eq`, `OAI.Erdos3.realification_rational_denseRange`, `OAI.Erdos3.realification_submodule_eq_of_rational`, `OAI.Erdos3.realification_submodule_mem_closure_rational`, `OAI.Erdos3.realification_submodule_property_of_rational`, `OAI.Erdos3.realifiedCentralBasisAction`, `OAI.Erdos3.realifiedCentralBasisAction_act_coe`, `OAI.Erdos3.realifiedCentralBasisAction_commutes`, `OAI.Erdos3.realifiedCentralBasisAction_displacement`, `OAI.Erdos3.realifiedScaledPairLayerEquiv`, `OAI.Erdos3.replacementCommonInputLog`, `OAI.Erdos3.replacementCutoffInputLog`, `OAI.Erdos3.residualCapEnvelope`, `OAI.Erdos3.residueAffineKernel`, `OAI.Erdos3.residueAffineKernel_mean`, `OAI.Erdos3.residueAffineKernel_preserves_mean`, `OAI.Erdos3.residueAffineSource`, `OAI.Erdos3.residueAffineTruncationError`, `OAI.Erdos3.residueCellOutsideDensity`, `OAI.Erdos3.residueColumnAverage`, `OAI.Erdos3.residueColumnMap`, `OAI.Erdos3.residueColumnRealAverage`, `OAI.Erdos3.residueColumnRealAverage_mean`, `OAI.Erdos3.residuePhysicalTruncation`, `OAI.Erdos3.residuePrimeCoordinateCellEquiv`, `OAI.Erdos3.residuePrimeCoordinateDensity`, `OAI.Erdos3.residuePrimeCoordinateMassRatio`, `OAI.Erdos3.residuePrimeCoordinateMean`, `OAI.Erdos3.residueTruncationCap`, `OAI.Erdos3.scalarTransferBaseAccuracy`, `OAI.Erdos3.scalarTransferMarginalAccuracy`, `OAI.Erdos3.scalarTransferTail`, `OAI.Erdos3.scaledPairLayer_eq_inf`, `OAI.Erdos3.selectedPrimeCRT`, `OAI.Erdos3.sum_sq_setFourierMultiplier`, `OAI.Erdos3.weightedReplacementTolerance`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B091

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TopSubspaceAdaptedBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}

def topSubspaceIdeal (F : NilpotentLieFiltration L s) (K : Submodule ℚ L)
    (hK : K ≤ F.layer s) : LieIdeal ℚ L :=
  { K with
    lie_mem := by
      intro x y hy
      rw [← lie_skew, F.top_layer_central (hK hy) x, neg_zero]
      exact K.zero_mem }

theorem exists_bounded_adapted_basis_with_top_subspace
    (F : NilpotentLieFiltration L s) (hs : 1 ≤ s) (e : Basis ι ℚ L)
    {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (K : Submodule ℚ L) (hK : K ≤ F.layer s) {κ : Type*} (vK : κ → K)
    (hspanK : Submodule.span ℚ (Set.range vK) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hvK : ∀ j k, RationalHeightLE (e.repr (vK j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (S : Set (Fin (finrank ℚ L))),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) ∧
      K = Submodule.span ℚ (b '' S) := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let bounded : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let flag : Fin (s + 1) → Submodule ℚ L := fun i => if i.val < s then F.layer (i.val + 1) else K
  have hflag : Antitone flag := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    dsimp only [flag]
    split_ifs with hi hj
    · exact F.antitone (Nat.add_le_add_right hij 1)
    · omega
    · exact hK.trans (F.antitone (by omega))
    · exact le_rfl
  have hbounded (i : Fin (s + 1)) :
      Submodule.span ℚ (bounded ∩ (flag i : Set L)) = flag i := by
    dsimp only [flag]
    split_ifs with hi
    · exact span_inter_eq_of_spanning_family _ (v i) (hspan i) bounded (hv i)
    · exact span_inter_eq_of_spanning_family K vK hspanK bounded hvK
  have hzero : flag 0 = ⊤ := by
    simpa only [flag, Fin.val_zero, show 0 < s by omega, ite_true, Nat.zero_add] using F.one_eq_top
  have htotal : Submodule.span ℚ bounded = ⊤ := by
    apply top_unique
    rw [← hzero, ← hbounded 0]
    exact Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, u, hu, hub, hbb, hbf⟩ :=
    exists_sorted_flag_basis_from_spanning_set flag hflag bounded htotal hbounded
  let w := fun i => min s (u i)
  have hw : Monotone w := fun i j hij => min_le_min le_rfl (hu hij)
  have hlayers (i : Fin (s + 1)) :
      F.layer (i.val + 1) = Submodule.span ℚ (b '' {j | i.val < w j}) := by
    by_cases hi : i.val < s
    · have h := hbf i
      simp only [flag, hi, ite_true] at h
      simpa only [w, lt_min_iff, hi, true_and] using h
    · have his : i.val = s := by omega
      rw [his, F.terminal]
      have hempty : {j | s < w j} = (∅ : Set (Fin (finrank ℚ L))) := by
        ext j
        simp [w]
      rw [hempty, Set.image_empty, Submodule.span_empty]
  have hlayer := F.layer_eq_span_of_weighted_flag b w (fun j =>
    (min_le_left s (u j)).trans (Nat.le_succ s)) hlayers
  refine ⟨b, w, {i | s < u i}, hw,
    centralLieBasis_of_sorted_filtration F b w hw hlayer, hbb, hlayer, ?_⟩
  simpa only [flag, lt_self_iff_false, ite_false] using hbf ⟨s, Nat.lt_succ_self s⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationStructureConstants
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def weightedBasisBracketCoefficient (w : σ → ℕ) (d : ℕ) :
    WeightedBasisIndex w d → WeightedBasisIndex w d → WeightedBasisIndex w d → ℤ := by
  classical
  exact fun a b c => match a, b, c with
    | Sum.inl i, Sum.inr a, Sum.inr c =>
        if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0
    | Sum.inr a, Sum.inl i, Sum.inr c =>
        -(if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0)
    | _, _, _ => 0

variable [Fintype σ]

theorem weightedBasis_structureConstants (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a b c : WeightedBasisIndex w d) :
    lieStructureConstants (weightedBasis w d hw) a b c =
      (weightedBasisBracketCoefficient w d a b c : ℚ) := by
  classical
  unfold lieStructureConstants
  cases c with
  | inl c =>
      rw [weightedBasis_repr_inl]
      cases a <;> cases b <;> rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw a).val.base
        (weightedBasis w d hw b).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw b).val.base
          (weightedBasis w d hw a).val.polynomial).coeff c.val = _
      cases a with
      | inl i =>
          cases b with
          | inl j => simp [weightedBasisBracketCoefficient]
          | inr a =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
      | inr a =>
          cases b with
          | inl i =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
          | inr b => simp [weightedBasisBracketCoefficient]

omit [Fintype σ] in
theorem weightedBasisBracketCoefficient_natAbs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    (weightedBasisBracketCoefficient w d a b c).natAbs ≤ d := by
  classical
  have hb : ∀ (i : σ) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}), a.val i ≤ d := by
    intro i a
    exact (Finsupp.le_weight w (hw i).ne' a.val).trans (Nat.le_of_lt a.property)
  cases a <;> cases b <;> cases c <;>
    simp only [weightedBasisBracketCoefficient, Int.natAbs_neg] <;>
    (try split_ifs) <;>
    simp only [Int.natAbs_zero, Int.natAbs_natCast, Nat.zero_le] <;> exact hb _ _

theorem weightedBasis_structure_height_succ (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (d + 1) := by
  rw [weightedBasis_structureConstants]
  constructor
  · simpa using (weightedBasisBracketCoefficient_natAbs_le w d hw a b c).trans (Nat.le_succ d)
  · simp

theorem weightedBasis_structure_height (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (2 * d + 1) :=
  (weightedBasis_structure_height_succ w d hw a b c).mono (by omega)

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealificationFixedSubmodule
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieHom_eq_self (φ : L →ₗ⁅ℚ⁆ L) (hφ : ∀ x, φ x = x)
    (x : ℝ ⊗[ℚ] L) : realificationLieHom φ x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [realificationLieHom_tmul, hφ]
  | add x y hx hy => rw [map_add, hx, hy]

theorem realificationLieHom_comp_apply (φ ψ θ : L →ₗ⁅ℚ⁆ L)
    (h : ∀ x, θ x = φ (ψ x)) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom θ x = realificationLieHom φ (realificationLieHom ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realificationLieHom_eq_self_on (φ : L →ₗ⁅ℚ⁆ L) (U : Submodule ℚ L)
    (hφ : ∀ x ∈ U, φ x = x) (x : ℝ ⊗[ℚ] L) (hx : x ∈ U.baseChange ℝ) :
    realificationLieHom φ x = x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul]
    change r ⊗ₜ[ℚ] φ y.val = r ⊗ₜ[ℚ] y.val
    rw [hφ y.val y.property]
  | add y z hy hz => simp only [map_add, hy, hz]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRationalMatrixPiNaturality
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalMatrix_piScalarRight_baseChange
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℚ) (x : ℝ ⊗[ℚ] (J → ℚ)) :
    TensorProduct.piScalarRight ℚ ℝ ℝ I (A.mulVecLin.baseChange ℝ x) =
      (Matrix.mulVecLin (fun i j => (A i j : ℝ)))
        (TensorProduct.piScalarRight ℚ ℝ ℝ J x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Rat.smul_def]
    funext i
    change ((∑ j, A i j * v j : ℚ) : ℝ) * a =
      ∑ j, (A i j : ℝ) * ((v j : ℝ) * a)
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AmbientBracketCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_bracket_corrections
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (Q : Matrix ν (κ × ι) ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      let C := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (small rational : κ × ι → ℝ) (v : ν → ℝ),
        ‖small‖ ≤ Real.exp p / monomialScale T α → rational ∈ realDenominatorGrid l →
        realBracketSystem f k (bracketSystemLift e v) = small + rational →
        bracketSystemLift e (C small) ∈ E.baseChange ℝ ∧
        bracketSystemLift e (C rational) ∈ E.baseChange ℝ ∧
        realBracketSystem f k (bracketSystemLift e (C small)) = small ∧
        realBracketSystem f k (bracketSystemLift e (C rational)) = rational ∧
        ‖C small‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
        C rational ∈ realDenominatorGrid m ∧
        ∀ b, ⁅bracketSystemLift e v - bracketSystemLift e (C small) -
          bracketSystemLift e (C rational), (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have hsplit := exists_controlled_linear_splitting (bracketSystemMatrix e f k)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := hsplit
  refine ⟨Q, m, hm, hmp, ?_⟩
  intro C α hα small rational v hsmall hrational heq
  have heq' := (bracketSystemMatrix_real_apply e f k v).trans heq
  obtain ⟨hsmallQ, hratQ, hnorm, hgrid, hzero⟩ :=
    hQ α hα small rational v hsmall hrational heq'
  refine ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _,
    (bracketSystemMatrix_real_apply e f k (C small)).symm.trans hsmallQ,
    (bracketSystemMatrix_real_apply e f k (C rational)).symm.trans hratQ,
    hnorm, hgrid, ?_⟩
  apply (realBracketSystem_eq_zero_iff f k _).mp
  have h := (bracketSystemMatrix_real_apply e f k (v - C small - C rational)).symm.trans hzero
  simpa only [map_sub] using h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ ν : Type*} [LieRing L] [LieAlgebra ℚ L] {E : Submodule ℚ L}

noncomputable def bracketLiftMatrix (b : Basis μ ℚ L) (e : Basis ν ℚ E) : Matrix μ ν ℚ :=
  fun i j => b.repr (e j : L) i

theorem bracketSystemLift_coordinates [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (x : ν → ℝ) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) =
      (fun i j => (bracketLiftMatrix b e i j : ℝ)) *ᵥ x := by
  classical
  have h : (b.baseChange ℝ).equivFun.toLinearMap.comp (bracketSystemLift e) =
      Matrix.mulVecLin (fun i j => (bracketLiftMatrix b e i j : ℝ)) := by
    apply (Pi.basisFun ℝ ν).ext
    intro j
    change (b.baseChange ℝ).equivFun (bracketSystemLift e (Pi.single j 1)) =
      Matrix.of (fun i n => (bracketLiftMatrix b e i n : ℝ)) *ᵥ Pi.single j 1
    rw [bracketSystemLift_single, Matrix.mulVec_single_one]
    funext i
    simp only [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Matrix.col_apply,
      Matrix.of_apply, bracketLiftMatrix]
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

theorem bracketSystemLift_norm_bound [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) {H : ℕ}
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) (x : ν → ℝ) :
    ‖(b.baseChange ℝ).equivFun (bracketSystemLift e x)‖ ≤
      ((Fintype.card ν : ℝ) + 1) * (H + 1) * ‖x‖ := by
  rw [bracketSystemLift_coordinates]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (he i j).abs_real_le) x

theorem bracketSystemLift_grid [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (m : ℕ) (x : ν → ℝ)
    (hx : x ∈ realDenominatorGrid m) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) ∈
      realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m) := by
  rw [bracketSystemLift_coordinates]
  exact real_matrix_denominator_grid (bracketLiftMatrix b e) m x hx

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_bracket_correction_polynomials
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ν → ℝ)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) A = small ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖coefficients A α‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, coefficients B α ∈ realDenominatorGrid m) ∧
      ∀ α b, ⁅bracketSystemLift e (coefficients (P - A - B) α),
        (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have h := exists_controlled_bracket_corrections e f k hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let C : (κ × ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let A := map (C.restrictScalars ℚ) small
  let B := map (C.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α = C (coefficients small α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = C (coefficients rational α) :=
    coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) (hα : α ≠ 0) :=
    hQ α hα (coefficients small α) (coefficients rational α) (coefficients P α)
      (hsmall α) (hrational α) (heq α)
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients small α))) = _
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero]
    · exact (hcoeff α hα).2.2.1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients rational α))) = _
    by_cases hα : α = 0
    · simp only [hα, hrational0, map_zero]
    · exact (hcoeff α hα).2.2.2.1
  · intro α hα
    rw [hAc, hα, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero]
  · intro α
    rw [hAc]
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact Real.exp_nonneg _
    · exact (hcoeff α hα).2.2.2.2.1
  · intro α
    rw [hBc]
    by_cases hα : α = 0
    · rw [hα, hrational0, map_zero]
      exact ⟨0, by ext i; simp⟩
    · exact (hcoeff α hα).2.2.2.2.2.1
  · intro α b
    simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
    by_cases hα : α = 0
    · simp only [hα, hP0, hsmall0, hrational0, map_zero, sub_zero, zero_lie]
      exact (V.baseChange ℝ).zero_mem
    · simpa only [map_sub] using (hcoeff α hα).2.2.2.2.2.2 b

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_ambient_bracket_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α t, ⁅coefficients (map ((bracketSystemLift e).restrictScalars ℚ) P - A - B) α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ := by
  have h := exists_bracket_correction_polynomials e f k hH hl hA hp hrows hcols hHp hlp
    T hT P small rational hP0 hsmall0 hrational0 hsmall hrational heq
  obtain ⟨m, A₀, B₀, hm, hmp, hAQ, hBQ, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  let A := map ((bracketSystemLift e).restrictScalars ℚ) A₀
  let B := map ((bracketSystemLift e).restrictScalars ℚ) B₀
  have hAc (α : σ →₀ ℕ) : coefficients A α = bracketSystemLift e (coefficients A₀ α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = bracketSystemLift e (coefficients B₀ α) :=
    coefficients_map _ _ _
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hAQ
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hBQ
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hAzero α hα, map_zero]
  · intro α hα
    rw [hBc, hBzero α hα, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hAnorm α)
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hBgrid α)
  · intro α t
    simp only [map_sub, Finsupp.sub_apply, coefficients_map, hAc, hBc]
    simpa only [map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] using hres α t

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

def FreeNilpotentLieAlgebra :=
  FreeLieAlgebra ℚ X ⧸ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s

namespace FreeNilpotentLieAlgebra

noncomputable instance instLieRing : LieRing (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieRing (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieAlgebra ℚ (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

noncomputable def mk : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeNilpotentLieAlgebra X s :=
  lieQuotientMap (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s)

theorem mk_surjective : Function.Surjective (mk X s) :=
  lieQuotientMap_surjective _

theorem mk_eq_zero (x : FreeLieAlgebra ℚ X) :
    mk X s x = 0 ↔ x ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s :=
  lieQuotientMap_eq_zero _ x

theorem lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (FreeNilpotentLieAlgebra X s) (FreeNilpotentLieAlgebra X s) s = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq s (mk_surjective X s), LieIdeal.map_eq_bot_iff]
  intro x hx
  exact (mk_eq_zero X s x).mpr hx

noncomputable def of (x : X) : FreeNilpotentLieAlgebra X s := mk X s (FreeLieAlgebra.of ℚ x)

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lowerCentralSeries_le_lift_ker (f : X → L)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ≤
      (FreeLieAlgebra.lift ℚ f).ker := by
  apply LieIdeal.map_eq_bot_iff.mp
  apply bot_unique
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

noncomputable def lift (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend _ (FreeLieAlgebra.lift ℚ f) (lowerCentralSeries_le_lift_ker f hnil)

theorem lift_mk (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x : FreeLieAlgebra ℚ X) : lift f hnil (mk X s x) = FreeLieAlgebra.lift ℚ f x := rfl

@[simp] theorem lift_of (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (x : X) :
    lift f hnil (of X s x) = f x := FreeLieAlgebra.lift_of_apply _ _

theorem hom_ext {f g : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L}
    (h : ∀ x, f (of X s x) = g (of X s x)) : f = g := by
  have heq : f.comp (mk X s) = g.comp (mk X s) := FreeLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := mk_surjective X s x
  exact LieHom.congr_fun heq y

theorem mk_truncation (x : FreeLieAlgebra ℚ X) :
    mk X s (freeLieTruncation s x) = mk X s x := by
  have h := lift_freeLieTruncation ((mk X s) ∘ FreeLieAlgebra.of ℚ)
    (lowerCentralSeries_eq_bot X s) x
  simpa only [FreeLieAlgebra.lift_comp_of] using h

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FreeLieTruncationKernel
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeLieTruncation_eq_zero_iff (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieTruncation s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  constructor
  · intro hp
    apply (FreeNilpotentLieAlgebra.mk_eq_zero X s p).mp
    rw [← FreeNilpotentLieAlgebra.mk_truncation p, hp, map_zero]
  · exact freeLie_lowerCentralSeries_truncation_zero s p

theorem freeLie_lowerCentralSeries_iff_low_coeff_zero (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ↔
      ∀ w, w.length ≤ s → (freeLieWordExpansion p).coeff w = 0 := by
  rw [← freeLieTruncation_eq_zero_iff, ← wordTruncation_eq_zero_iff]
  constructor
  · intro hp
    rw [← freeLieTruncation_expansion, hp, map_zero]
  · intro hp
    apply freeLieWordExpansion_injective
    rw [freeLieTruncation_expansion, hp, map_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

noncomputable def basisReductionStandardPoint {n : ℕ} (i : Fin n) :
    IntegralPoint n :=
  (Pi.basisFun ℤ (Fin n)) i

@[simp]
theorem integralEmbed_basisReductionStandardPoint {n : ℕ} (i : Fin n) :
    integralEmbed (basisReductionStandardPoint i) =
      (Pi.basisFun ℝ (Fin n)) i := by
  ext j
  by_cases hij : i = j
  · subst j
    simp [basisReductionStandardPoint, integralEmbed]
  · simp [basisReductionStandardPoint, integralEmbed, hij]

def IsCenteredReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (a : Fin n → Fin n → ℝ) : Prop :=
  ∀ i,
    integralEmbed (b i) = ∑ j, a i j • integralEmbed (x j) ∧
    (∀ j, i < j → a i j = 0) ∧
    ((|a i i| = 1 ∧ ∀ j, j < i → a i j = 0) ∨
      ∀ j, j ≤ i → |a i j| ≤ (1 : ℝ) / 2)

def IsRawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
  (u : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j)) ∧
  (∀ i j, i < j → u i j = 0) ∧
  (∀ i j, i < j → b.repr (x i) j = 0) ∧
  ∀ i, b.repr (x i) i ≠ 0 ∧
    ((b.repr (x i) i : ℝ) * u i i = 1)

theorem exists_rawFlagReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (u : Fin n → Fin n → ℝ), IsRawFlagReduction x b u := by
  classical
  have hrealEmbed (z : IntegralPoint n) :
      SaturatedFlag.realEmbed n z = integralEmbed z := by
    ext j
    rfl
  have hli' : LinearIndependent ℝ
      (fun i ↦ SaturatedFlag.realEmbed n (x i)) := by
    simpa only [hrealEmbed] using hli
  obtain ⟨b, hprefix, hxrepr, hxdiag⟩ :=
    SaturatedFlag.exists_prefix_adapted_basis_realPrefixLattice x hli'
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  let u : Fin n → Fin n → ℝ :=
    fun i j ↦ xb.repr (integralEmbed (b i)) j
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  have hexpand (i : Fin n) :
      integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (b i))).symm
  have htri : ∀ i j, i < j → u i j = 0 := by
    intro i j hij
    have hbi : b i ∈ SaturatedFlag.realPrefixLattice x i := by
      rw [hprefix i]
      apply Submodule.subset_span
      exact ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hbispan : integralEmbed (b i) ∈
        Submodule.span ℝ (xb '' Set.Iic i) := by
      have hm := SaturatedFlag.mem_realPrefixLattice.mp hbi
      have himage : SaturatedFlag.realEmbed n '' (x '' Set.Iic i) =
          xb '' Set.Iic i := by
        ext y
        constructor
        · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨k, hk, (hxb k).trans (hrealEmbed (x k)).symm⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨x k, ⟨k, hk, rfl⟩,
            (hrealEmbed (x k)).trans (hxb k).symm⟩
      rw [himage] at hm
      rw [hrealEmbed] at hm
      exact hm
    have hsupp := xb.repr_support_subset_of_mem_span (Set.Iic i) hbispan
    by_contra hne
    have hjmem : j ∈ Set.Iic i :=
      hsupp (Finsupp.mem_support_iff.mpr hne)
    exact (not_le_of_gt hij) (Set.mem_Iic.mp hjmem)
  refine ⟨b, u, hexpand, htri, hxrepr, ?_⟩
  intro i
  have hxreal :
      ∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j) =
        integralEmbed (x i) := by
    calc
      (∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j)) =
          integralEmbed (∑ j, b.repr (x i) j • b j) := by
        ext k
        simp [integralEmbed]
      _ = integralEmbed (x i) := congrArg integralEmbed (b.sum_repr (x i))
  have hcoord := congrArg (fun y : Fin n → ℝ ↦ xb.repr y i) hxreal
  have hrhs : xb.repr (integralEmbed (x i)) i = 1 := by
    rw [← hxb]
    simp
  rw [hrhs] at hcoord
  have hcoord' :
      ∑ j, (b.repr (x i) j : ℝ) * u j i = 1 := by
    simpa [u, hxb] using hcoord
  have hsingle :
      (∑ j, (b.repr (x i) j : ℝ) * u j i) =
        (b.repr (x i) i : ℝ) * u i i := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [htri j i hji]
        simp
      · rw [hxrepr i j hij]
        simp
    · simp
  have hrecip : (b.repr (x i) i : ℝ) * u i i = 1 := by
    rw [← hsingle]
    exact hcoord'
  exact ⟨hxdiag i, hrecip⟩

theorem rawFlagReduction_diag_abs_le_one {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n) :
    |u i i| ≤ 1 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (1 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (1 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

theorem rawFlagReduction_diag_abs_le_half_of_not_unit {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n)
    (hnot : |b.repr (x i) i| ≠ 1) :
    |u i i| ≤ (1 : ℝ) / 2 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (2 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (2 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

def prefixIndex {n : ℕ} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

@[simp] theorem prefixIndex_val {n : ℕ} (i : Fin n) (j : Fin i.val) :
    (prefixIndex i j).val = j.val := rfl

theorem prefixIndex_lt {n : ℕ} (i : Fin n) (j : Fin i.val) :
    prefixIndex i j < i := j.isLt

noncomputable def centeredStep {n : ℕ} (r u : Fin n → ℝ) (j : Fin n) :
    Fin n → ℝ :=
  fun h ↦ r h - (round (r j / u j) : ℝ) * u h

theorem abs_centeredStep_apply_self_le {n : ℕ}
    (r u : Fin n → ℝ) (j : Fin n)
    (hdiag_ne : u j ≠ 0) (hdiag_le : |u j| ≤ 1) :
    |centeredStep r u j j| ≤ (1 : ℝ) / 2 := by
  have heq : centeredStep r u j j =
      u j * (r j / u j - (round (r j / u j) : ℝ)) := by
    rw [centeredStep]
    field_simp
  rw [heq, abs_mul]
  calc
    |u j| * |r j / u j - (round (r j / u j) : ℝ)| ≤
        1 * ((1 : ℝ) / 2) :=
      mul_le_mul hdiag_le (abs_sub_round (r j / u j))
        (abs_nonneg _) (by positivity)
    _ = (1 : ℝ) / 2 := one_mul _

theorem exists_integerCombination_abs_le_half : ∀ {n : ℕ}
    (u : Fin n → Fin n → ℝ),
    (∀ j h, j < h → u j h = 0) →
    (∀ j, u j j ≠ 0) →
    (∀ j, |u j j| ≤ (1 : ℝ)) →
    ∀ r : Fin n → ℝ,
      ∃ t : Fin n → ℤ,
        ∀ h, |r h + ∑ j, (t j : ℝ) * u j h| ≤ (1 : ℝ) / 2 := by
  intro n
  induction n with
  | zero =>
      intro u _htri _hne _hle r
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      intro h
      exact Fin.elim0 h
  | succ n ih =>
      intro u htri hne hle r
      let last : Fin (n + 1) := Fin.last n
      let q : ℤ := -round (r last / u last last)
      let rHead : Fin n → ℝ := fun h ↦
        r h.castSucc + (q : ℝ) * u last h.castSucc
      let uHead : Fin n → Fin n → ℝ := fun j h ↦
        u j.castSucc h.castSucc
      have htriHead : ∀ j h, j < h → uHead j h = 0 := by
        intro j h hjh
        exact htri j.castSucc h.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hjh)
      have hneHead : ∀ j, uHead j j ≠ 0 := fun j ↦ hne j.castSucc
      have hleHead : ∀ j, |uHead j j| ≤ (1 : ℝ) := fun j ↦ hle j.castSucc
      obtain ⟨tHead, htHead⟩ := ih uHead htriHead hneHead hleHead rHead
      let t : Fin (n + 1) → ℤ := Fin.lastCases q tHead
      refine ⟨t, ?_⟩
      intro h
      refine Fin.lastCases ?_ (fun h ↦ ?_) h
      · have hzero :
            ∑ j : Fin n, (t j.castSucc : ℝ) * u j.castSucc last = 0 := by
          apply Finset.sum_eq_zero
          intro j _hj
          rw [htri j.castSucc last (Fin.castSucc_lt_last j)]
          simp
        rw [Fin.sum_univ_castSucc, hzero, zero_add]
        have hstep := abs_centeredStep_apply_self_le
          r (u last) last (hne last) (hle last)
        simpa [t, q, last, centeredStep, sub_eq_add_neg] using hstep
      · have hh := htHead h
        simpa [Fin.sum_univ_castSucc, t, rHead, uHead, q,
          add_assoc, add_comm, add_left_comm] using hh

theorem exists_prefix_integerCombination_abs_le_half {n : ℕ}
    (u : Fin n → Fin n → ℝ)
    (htri : ∀ j h, j < h → u j h = 0)
    (hne : ∀ j, u j j ≠ 0)
    (hle : ∀ j, |u j j| ≤ (1 : ℝ))
    (r : Fin n → ℝ) (i : Fin n) :
    ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |r (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
  let up : Fin i.val → Fin i.val → ℝ :=
    fun j h ↦ u (prefixIndex i j) (prefixIndex i h)
  have htrip : ∀ j h, j < h → up j h = 0 := by
    intro j h hjh
    exact htri (prefixIndex i j) (prefixIndex i h) hjh
  have hnep : ∀ j, up j j ≠ 0 := fun j ↦ hne (prefixIndex i j)
  have hlep : ∀ j, |up j j| ≤ (1 : ℝ) := fun j ↦ hle (prefixIndex i j)
  simpa [up] using exists_integerCombination_abs_le_half up htrip hnep hlep
    (fun h ↦ r (prefixIndex i h))

def shearMatrix {n : ℕ} (t : Fin n → Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun j i ↦ if j = i then 1 else if j < i then t i j else 0

theorem shearMatrix_isUpperTriangular {n : ℕ}
    (t : Fin n → Fin n → ℤ) :
    (shearMatrix t).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  change shearMatrix t i j = 0
  simp [shearMatrix, hji.ne', hji.asymm]

@[simp]
theorem shearMatrix_apply_self {n : ℕ}
    (t : Fin n → Fin n → ℤ) (i : Fin n) :
    shearMatrix t i i = 1 := by
  simp [shearMatrix]

@[simp]
theorem shearMatrix_det {n : ℕ}
    (t : Fin n → Fin n → ℤ) :
    (shearMatrix t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (shearMatrix_isUpperTriangular t)]
  simp

noncomputable def basisOfUpperTriangularUnits {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i)) :
    Basis (Fin n) ℤ M := by
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    exact IsUnit.prod_univ_iff.mpr hdiag
  exact b.map (A.toLinearEquiv b hdet)

theorem basisOfUpperTriangularUnits_apply {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i))
    (i : Fin n) :
    basisOfUpperTriangularUnits b A hupper hdiag i = ∑ j, A j i • b j := by
  simp [basisOfUpperTriangularUnits, Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]

def extendPrefix {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ) : Fin n → ℤ :=
  fun j ↦ if h : j < i then t ⟨j.val, h⟩ else 0

@[simp]
theorem extendPrefix_prefixIndex {n : ℕ} (i : Fin n)
    (t : Fin i.val → ℤ) (j : Fin i.val) :
    extendPrefix i t (prefixIndex i j) = t j := by
  simp [extendPrefix, prefixIndex_lt]

def prefixIndexEquivIio {n : ℕ} (i : Fin n) :
    Fin i.val ≃ {j : Fin n // j ∈ Finset.Iio i} where
  toFun j := ⟨prefixIndex i j, Finset.mem_Iio.mpr (prefixIndex_lt i j)⟩
  invFun j :=
    { val := j.1.val
      isLt := by
        have hji : j.1 < i := Finset.mem_Iio.mp j.2
        exact hji }
  left_inv j := by ext; rfl
  right_inv j := by ext; rfl

theorem sum_extendPrefix_mul {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ)
    (f : Fin n → ℝ) :
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
      ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
  classical
  calc
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
        ∑ j ∈ Finset.Iio i, (extendPrefix i t j : ℝ) * f j := by
      symm
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _hj hjnot
      have hnlt : ¬j < i := by simpa using hjnot
      simp [extendPrefix, hnlt]
    _ = ∑ j : {j : Fin n // j ∈ Finset.Iio i},
          (extendPrefix i t j : ℝ) * f j := by
      rw [← Finset.sum_attach]
      simp
    _ = ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
      symm
      refine Fintype.sum_equiv (prefixIndexEquivIio i) _ _ ?_
      intro j
      simp [prefixIndexEquivIio]

noncomputable def centeredReductionMatrix {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun j i ↦
    if |b.repr (x i) i| = 1 then
      b.repr (x i) i * b.repr (x i) j
    else if j = i then 1 else extendPrefix i (t i) j

theorem centeredReductionMatrix_isUpperTriangular {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ)
    (hupper : ∀ i j, i < j → b.repr (x i) j = 0) :
    (centeredReductionMatrix x b t).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  change centeredReductionMatrix x b t i j = 0
  by_cases hunit : |b.repr (x j) j| = 1
  · simp [centeredReductionMatrix, hunit, hupper j i hji]
  · have hne : i ≠ j := hji.ne'
    have hnlt : ¬i < j := hji.asymm
    simp [centeredReductionMatrix, hunit, hne, extendPrefix, hnlt]

@[simp]
theorem centeredReductionMatrix_apply_self {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) (i : Fin n) :
    centeredReductionMatrix x b t i i = 1 := by
  by_cases hunit : |b.repr (x i) i| = 1
  · have hsquare : b.repr (x i) i * b.repr (x i) i = 1 := by
      by_cases hnonneg : 0 ≤ b.repr (x i) i
      · rw [abs_of_nonneg hnonneg] at hunit
        simp [hunit]
      · have hnonpos : b.repr (x i) i ≤ 0 := le_of_not_ge hnonneg
        rw [abs_of_nonpos hnonpos] at hunit
        have hminus : b.repr (x i) i = -1 := by omega
        simp [hminus]
    simp [centeredReductionMatrix, hunit, hsquare]
  · simp [centeredReductionMatrix, hunit]

theorem centeredReductionMatrix_isUnit_diagonal {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) :
    ∀ i, IsUnit (centeredReductionMatrix x b t i i) := by
  intro i
  rw [centeredReductionMatrix_apply_self]
  exact isUnit_one

theorem exists_centeredReduction_of_rawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i)))
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (u : Fin n → Fin n → ℝ)
    (hraw : IsRawFlagReduction x b u) :
    ∃ (e : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x e a := by
  classical
  have hudiag_ne : ∀ i, u i i ≠ 0 := by
    intro i hui
    have hrecip := (hraw.2.2.2 i).2
    rw [hui] at hrecip
    norm_num at hrecip
  have hudiag_le : ∀ i, |u i i| ≤ (1 : ℝ) :=
    fun i ↦ rawFlagReduction_diag_abs_le_one hraw i
  have hround : ∀ i, ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |u i (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
    intro i
    exact exists_prefix_integerCombination_abs_le_half u hraw.2.1
      hudiag_ne hudiag_le (u i) i
  choose t ht using hround
  let A : Matrix (Fin n) (Fin n) ℤ := centeredReductionMatrix x b t
  have hAupper : A.IsUpperTriangular :=
    centeredReductionMatrix_isUpperTriangular x b t hraw.2.2.1
  have hAdiag : ∀ i, IsUnit (A i i) :=
    centeredReductionMatrix_isUnit_diagonal x b t
  let e : Basis (Fin n) ℤ (IntegralPoint n) :=
    basisOfUpperTriangularUnits b A hAupper hAdiag
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  let a : Fin n → Fin n → ℝ :=
    fun i h ↦ xb.repr (integralEmbed (e i)) h
  have hurepr (j h : Fin n) :
      xb.repr (integralEmbed (b j)) h = u j h := by
    rw [hraw.1 j]
    simp_rw [← hxb]
    simp [Finsupp.single_apply]
  have he_apply (i : Fin n) : e i = ∑ j, A j i • b j :=
    basisOfUpperTriangularUnits_apply b A hAupper hAdiag i
  have hembed (i : Fin n) :
      integralEmbed (e i) = ∑ j, (A j i : ℝ) • integralEmbed (b j) := by
    rw [he_apply]
    ext k
    simp [integralEmbed]
  have haformula (i h : Fin n) :
      a i h = ∑ j, (A j i : ℝ) * u j h := by
    change xb.repr (integralEmbed (e i)) h = _
    rw [hembed]
    simp [hurepr]
  have hexpand (i : Fin n) :
      integralEmbed (e i) = ∑ j, a i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (e i))).symm
  refine ⟨e, a, ?_⟩
  intro i
  refine ⟨hexpand i, ?_⟩
  by_cases hunit : |b.repr (x i) i| = 1
  · have heprim : e i = b.repr (x i) i • x i := by
      rw [he_apply]
      simp only [A, centeredReductionMatrix, hunit, ite_true]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, b.sum_repr]
    have hembedprim : integralEmbed (e i) =
        (b.repr (x i) i : ℝ) • xb i := by
      rw [heprim]
      ext k
      simp [integralEmbed, hxb]
    have haprim (h : Fin n) : a i h =
        (b.repr (x i) i : ℝ) * (if i = h then 1 else 0) := by
      change xb.repr (integralEmbed (e i)) h = _
      rw [hembedprim]
      simp [Finsupp.single_apply]
    have habove : ∀ j, i < j → a i j = 0 := by
      intro j hij
      rw [haprim]
      simp [hij.ne]
    refine ⟨habove, Or.inl ⟨?_, ?_⟩⟩
    · rw [haprim]
      have hcabs : |(b.repr (x i) i : ℝ)| = 1 := by
        exact_mod_cast hunit
      simpa using hcabs
    · intro j hji
      rw [haprim]
      simp [hji.ne']
  · have hainon (h : Fin n) : a i h =
        u i h + ∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h := by
      rw [haformula]
      calc
        (∑ j, (A j i : ℝ) * u j h) =
            ∑ j, ((if j = i then 1 else 0) +
              (extendPrefix i (t i) j : ℤ) : ℤ) * u j h := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp [A, extendPrefix]
          · simp [A, centeredReductionMatrix, hunit, hji]
        _ = u i h + ∑ j, (extendPrefix i (t i) j : ℝ) * u j h := by
          simp_rw [Int.cast_add, add_mul]
          rw [Finset.sum_add_distrib]
          simp
        _ = u i h + ∑ j : Fin i.val,
              (t i j : ℝ) * u (prefixIndex i j) h := by
          rw [sum_extendPrefix_mul]
    have habove : ∀ h, i < h → a i h = 0 := by
      intro h hih
      rw [hainon, hraw.2.1 i h hih]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) h
          (lt_trans (prefixIndex_lt i j) hih)]
        simp
      rw [hsum, add_zero]
    refine ⟨habove, Or.inr ?_⟩
    intro h hhi
    rcases lt_or_eq_of_le hhi with hlt | heq
    · let h' : Fin i.val := ⟨h.val, hlt⟩
      have hp : prefixIndex i h' = h := by
        apply Fin.ext
        rfl
      rw [hainon]
      simpa only [hp] using ht i h'
    · subst h
      rw [hainon]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) i) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) i (prefixIndex_lt i j)]
        simp
      rw [hsum, add_zero]
      exact rawFlagReduction_diag_abs_le_half_of_not_unit hraw i hunit

theorem exists_centeredReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x b a := by
  obtain ⟨b, u, hraw⟩ := exists_rawFlagReduction_of_linearIndependent x hli
  exact exists_centeredReduction_of_rawFlagReduction x hli b u hraw

end Erdos3.IntegerBasisReduction.Mahler

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem IntegerBasisReduction.Mahler.IsCenteredReduction.abs_coefficient_le_one
    {n : ℕ} {x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegerBasisReduction.Mahler.IntegralPoint n)}
    {a : Fin n → Fin n → ℝ}
    (h : IntegerBasisReduction.Mahler.IsCenteredReduction x b a) (i j : Fin n) :
    |a i j| ≤ 1 := by
  obtain ⟨_, habove, hprim | hhalf⟩ := h i
  · rcases lt_trichotomy j i with hlt | rfl | hgt
    · simp [hprim.2 j hlt]
    · exact hprim.1.le
    · simp [habove j hgt]
  · rcases le_or_gt j i with hle | hgt
    · exact (hhalf j hle).trans (by norm_num)
    · simp [habove j hgt]

theorem exists_lattice_basis_bounded_expansion
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → E)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v) :
    ∃ (b : Basis (Fin n) ℤ Λ) (a : Fin n → Fin n → ℝ),
      (∀ i j, |a i j| ≤ 1) ∧ ∀ i, (b i : E) = ∑ j, a i j • v j := by
  classical
  let B := (b₀.ofZLatticeBasis ℝ Λ).equivFun
  let w : Fin n → Λ := fun i => ⟨v i, hv i⟩
  let x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n := fun i => b₀.equivFun (w i)
  have hcoord (i) : IntegerBasisReduction.Mahler.integralEmbed (x i) = B (v i) := by
    ext j
    change (b₀.repr (w i) j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (w i : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
  have hxi : LinearIndependent ℝ (fun i => IntegerBasisReduction.Mahler.integralEmbed (x i)) := by
    simpa only [hcoord, Function.comp_def, LinearEquiv.coe_coe] using
      hli.map_injOn B.toLinearMap B.injective.injOn
  obtain ⟨c, a, hred⟩ := IntegerBasisReduction.Mahler.exists_centeredReduction_of_linearIndependent x hxi
  let b := c.map b₀.equivFun.symm
  have hcast (z : Fin n → ℤ) :
      B.symm (IntegerBasisReduction.Mahler.integralEmbed z) = (b₀.equivFun.symm z : E) := by
    apply B.injective
    ext j
    rw [LinearEquiv.apply_symm_apply]
    change (z j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (b₀.equivFun.symm z : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
    exact (congrArg (fun q : ℤ => (q : ℝ))
      (congrFun (b₀.equivFun.apply_symm_apply z) j)).symm
  refine ⟨b, a, hred.abs_coefficient_le_one, ?_⟩
  intro i
  have h := congrArg B.symm (hred i).1
  rw [map_sum] at h
  simp only [map_smul, hcoord, LinearEquiv.symm_apply_apply] at h
  rw [hcast] at h
  exact h

theorem exists_lattice_basis_coordinate_bound
    {ι : Type} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → ι → ℝ)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v)
    (R : ι → ℝ) (hbound : ∀ i j, |v i j| ≤ R j) :
    ∃ b : Basis (Fin n) ℤ Λ, ∀ i j, |(b i : ι → ℝ) j| ≤ (n : ℝ) * R j := by
  obtain ⟨b, a, ha, he⟩ := exists_lattice_basis_bounded_expansion Λ b₀ v hv hli
  refine ⟨b, ?_⟩
  intro i j
  rw [he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    |∑ k, a i k * v k j| ≤ ∑ k, |a i k * v k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, R j := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg (v k j))
      have h' : |a i k| * |v k j| ≤ |v k j| := by simpa only [one_mul] using h
      exact h'.trans (hbound k j)
    _ = (n : ℝ) * R j := by simp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem cyclicIntegerKernel_eq_zero_of_lt_radii
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η)
    (hsmall : ∀ i, |y i| < (R i : ℝ) + 1) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  change ∀ i, |(x i : ℝ)| < (R i : ℝ) + 1 at hsmall
  have hbound : ∀ i, |x i| ≤ (R i : ℤ) := by
    intro i
    have h : |x i| < (R i : ℤ) + 1 := by exact_mod_cast hsmall i
    omega
  have he : x = 0 := hinj hbound (by simp) (by simpa using hx)
  rw [he, map_zero]

theorem cyclicIntegerKernel_nonzero_large_coordinate
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η) (hne : y ≠ 0) :
    ∃ i, (R i : ℝ) + 1 ≤ |y i| := by
  by_contra! h
  exact hne (cyclicIntegerKernel_eq_zero_of_lt_radii η R hinj y hy h)

theorem affine_box_card_le_radius_product
    {ι G : Type} [Fintype ι] [AddCommGroup G]
    (η : (ι → ℤ) →+ G) (R : ι → ℕ) (h₀ : G) (J : Finset G)
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    (J.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * ∏ i, ((R i : ℝ) + 1) := by
  classical
  have hsub : J ⊆ (centeredIntegerBox R).image (fun x => h₀ + η x) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := hrep h hh
    exact Finset.mem_image.mpr ⟨x, (mem_centeredIntegerBox R x).mpr hx, rfl⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hp : (centeredIntegerBox R).card ≤ 2 ^ Fintype.card ι * ∏ i, (R i + 1) := by
    rw [card_centeredIntegerBox]
    calc
      (∏ i, (2 * R i + 1)) ≤ ∏ i, (2 * (R i + 1)) := by
        gcongr with i
        omega
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  exact_mod_cast hc.trans hp

theorem cyclicIntegerKernel_normalized_covolume_le
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ) (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹ ≤
      (2 : ℝ) ^ Fintype.card ι / δ := by
  have hprod : 0 < ∏ i, ((R i : ℝ) + 1) := Finset.prod_pos (by intros; positivity)
  rw [← div_eq_mul_inv, div_le_div_iff₀ hprod hδ]
  have hcov := mul_le_mul_of_nonneg_left (cyclicIntegerKernel_covolume_le η) hδ.le
  have hc := affine_box_card_le_radius_product η R h₀ J hrep
  nlinarith

theorem exists_short_independent_cyclic_kernel_vectors
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ v : Fin r → Fin r → ℝ, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ cyclicIntegerKernel η) ∧
      ∀ i j, |v i j| ≤
        (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
          ((R j : ℝ) + 1) := by
  classical
  let b : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  have hB : Submodule.span ℤ (Set.range B) = cyclicIntegerKernel η :=
    b.ofZLatticeBasis_span ℝ _
  have hdet : |(Matrix.of B).det| = ZLattice.covolume (cyclicIntegerKernel η) := by
    have he : (B : Fin r → Fin r → ℝ) = fun i => (b i : Fin r → ℝ) :=
      funext (fun i => Basis.ofZLatticeBasis_apply ℝ (cyclicIntegerKernel η) b i)
    rw [he]
    exact (ZLattice.covolume_eq_det (cyclicIntegerKernel η) b).symm
  obtain ⟨C⟩ := BohrLattice.MinkowskiSecondBox.realBox_has_minkowskiSecondCertificate
    B (fun i => (R i : ℝ) + 1) (by intro i; positivity)
  have hmem (i) : C.point i ∈ cyclicIntegerKernel η := hB ▸ C.point_mem i
  have hpoint (i j) : |C.point i j| ≤ C.scale i * ((R j : ℝ) + 1) := by
    have h := C.mem_scaledBox i
    exact abs_le.mpr ⟨h.1 j, h.2 j⟩
  have hone (i) : 1 ≤ C.scale i := by
    obtain ⟨j, hj⟩ := cyclicIntegerKernel_nonzero_large_coordinate η R hinj
      (C.point i) (hmem i) (C.independent.ne_zero i)
    have hp : 0 < (R j : ℝ) + 1 := by positivity
    nlinarith [hpoint i j]
  have hbound : ∏ i, C.scale i ≤
      BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ := by
    have hm : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
      unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
      positivity
    have hc := mul_le_mul_of_nonneg_left
      (cyclicIntegerKernel_normalized_covolume_le η R h₀ J δ hδ hdense hrep) hm
    have he : ∏ i, C.scale i ≤
        BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r *
          (ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹) := by
      simpa only [hdet, mul_assoc] using C.product_le
    simpa only [Fintype.card_fin, mul_div_assoc] using he.trans hc
  refine ⟨C.point, C.independent, hmem, ?_⟩
  intro i j
  have hi : C.scale i ≤ ∏ k, C.scale k := by
    calc
      C.scale i ≤ C.scale i * ∏ k ∈ Finset.univ.erase i, C.scale k :=
        le_mul_of_one_le_right (C.scale_nonneg i) (Finset.one_le_prod (fun k _ => hone k))
      _ = ∏ k, C.scale k := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  exact (hpoint i j).trans (mul_le_mul_of_nonneg_right (hi.trans hbound) (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem proper_cyclic_kernel_box_card_le_covolume
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  classical
  let f : {x // x ∈ centeredIntegerBox R} → η.range := fun x => η.rangeRestrict x.val
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinj ((mem_centeredIntegerBox R x.val).mp x.property)
      ((mem_centeredIntegerBox R y.val).mp y.property) (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  have hcard : (centeredIntegerBox R).card ≤ Nat.card η.range := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  rw [card_centeredIntegerBox] at hcard
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  exact_mod_cast hcard

theorem proper_cyclic_kernel_covolume_lower_bound
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    (∏ i, ((R i : ℝ) + 1)) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  have hp : (∏ i, (R i + 1)) ≤ ∏ i, (2 * R i + 1) := by
    gcongr with i
    omega
  have hpR : (∏ i, ((R i : ℝ) + 1)) ≤ ((∏ i, (2 * R i + 1) : ℕ) : ℝ) := by
    exact_mod_cast hp
  exact hpR.trans (proper_cyclic_kernel_box_card_le_covolume η R hinj)

noncomputable def properCyclicKernelBasisBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ

theorem properCyclicKernelBasisBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicKernelBasisBound r δ := by
  unfold properCyclicKernelBasisBound BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
  positivity

theorem exists_proper_cyclic_kernel_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η), ∀ i j,
      |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1) := by
  classical
  obtain ⟨v, hli, hv, hbound⟩ :=
    exists_short_independent_cyclic_kernel_vectors η R hinj h₀ J δ hδ hdense hrep
  let b₀ : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  obtain ⟨b, hb⟩ := exists_lattice_basis_coordinate_bound (cyclicIntegerKernel η) b₀ v hv hli
    (fun j => (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
      ((R j : ℝ) + 1)) hbound
  refine ⟨b, ?_⟩
  intro i j
  simpa only [properCyclicKernelBasisBound, mul_div_assoc, mul_assoc] using hb i j

theorem exists_proper_affine_torus_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_proper_cyclic_kernel_basis η R hinj h₀ J δ hδ hdense hrep
  exact ⟨b, hb, exists_affine_cyclic_kernel_real_frequencies η b h₀⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

open Module

noncomputable def properCyclicCoordinateBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * r.factorial * properCyclicKernelBasisBound r δ ^ (r - 1)

theorem properCyclicCoordinateBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicCoordinateBound r δ := by
  have h := properCyclicKernelBasisBound_nonneg r hδ
  unfold properCyclicCoordinateBound
  positivity

theorem exists_controlled_cyclic_torus_model
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      (∀ x : Fin r → ℝ, (∀ j, |x j| ≤ (R j : ℝ) + 1) → ∀ i,
        |cyclicKernelRealCoordinates η b x i| ≤ properCyclicCoordinateBound r δ) ∧
      Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x)
        {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb, t, ht, hperiod, hformula⟩ :=
    exists_proper_affine_torus_basis η R hinj h₀ J δ hδ hdense hrep
  refine ⟨b, hb, ?_, cyclicKernelCoordinateCharacters_injOn η b _ hinj,
    t, ht, hperiod, hformula⟩
  intro x hx i
  exact lattice_basis_coordinates_bound (cyclicIntegerKernel η) b
    (fun j => (R j : ℝ) + 1) (by intro j; positivity)
    (properCyclicKernelBasisBound_nonneg r hδ) hb
    (proper_cyclic_kernel_covolume_lower_bound η R hinj) x hx i

end Erdos3

end

section

namespace Erdos3

theorem properCyclicKernelBasisBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
    calc
      _ ≤ (Real.exp 2) ^ k := pow_le_pow_left₀ (by norm_num) htwo k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hk : r * (r - 1) / 2 ≤ r * r :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left r (Nat.sub_le _ _))
  have hkR : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ p ^ 2 := by
    have h : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ (r : ℝ) * r := by exact_mod_cast hk
    exact h.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) r])
  have hM : BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r ≤ Real.exp (2 * p ^ 2) :=
    (hpow _).trans (Real.exp_le_exp.mpr (by linarith))
  have h2r : (2 : ℝ) ^ r ≤ Real.exp (2 * p) :=
    (hpow r).trans (Real.exp_le_exp.mpr (by linarith))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hM0 : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
    unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
    positivity
  have hmain : properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp (2 * p ^ 2 + 4 * p) := by
    unfold properCyclicKernelBasisBound
    rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
    calc
      _ ≤ Real.exp p * Real.exp (2 * p ^ 2) * Real.exp (2 * p) * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 3 + 10 * p ^ 2 + 44 * p + 64 := by positivity
  nlinarith

theorem properCyclicCoordinateBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicCoordinateBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 5) := by
  have hB := properCyclicKernelBasisBound_le_exp hp hr
  have hB0 := properCyclicKernelBasisBound_nonneg r (Real.exp_pos (-p))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hfac : (r.factorial : ℝ) ≤ Real.exp (p ^ 2) :=
    (factorial_le_exp_sq r).trans (Real.exp_le_exp.mpr
      (by nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  have hsub : ((r - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le r 1)).trans hr
  have hpower : properCyclicKernelBasisBound r (Real.exp (-p)) ^ (r - 1) ≤
      Real.exp (p * (p + 4) ^ 3) := by
    calc
      _ ≤ (Real.exp ((p + 4) ^ 3)) ^ (r - 1) := pow_le_pow_left₀ hB0 hB _
      _ = Real.exp (((r - 1 : ℕ) : ℝ) * (p + 4) ^ 3) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsub (by positivity))
  have hmain : properCyclicCoordinateBound r (Real.exp (-p)) ≤
      Real.exp (p + p ^ 2 + p * (p + 4) ^ 3) := by
    unfold properCyclicCoordinateBound
    calc
      _ ≤ Real.exp p * Real.exp (p ^ 2) * Real.exp (p * (p + 4) ^ 3) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 5 + 19 * p ^ 4 + 148 * p ^ 3 + 591 * p ^ 2 + 1215 * p + 1024 := by
    positivity
  nlinarith

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def centeredCircleLift (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).val

theorem coe_centeredCircleLift (z : AddCircle (1 : ℝ)) :
    (centeredCircleLift z : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco

theorem centeredCircleLift_coe {y : ℝ} (hy : |y| ≤ 1 / 4) :
    centeredCircleLift (y : AddCircle (1 : ℝ)) = y := by
  apply AddCircle.equivIco_coe_of_mem
  constructor <;> linarith [(abs_le.mp hy).1, (abs_le.mp hy).2]

noncomputable def affineCyclicTorusLocalLift {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) : Fin r → ℝ :=
  fun i => centeredCircleLift
    (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ))

theorem exists_localized_cyclic_torus_chart
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (q : ℕ) (hq : 2 ≤ q) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∃ K ⊆ J, K.Nonempty ∧
          J.card ≤ realBoxCellCount (properCyclicCoordinateBound r δ) q ^ r * K.card ∧
          ∃ c : Fin r → ℝ,
            (∀ i, |c i| ≤ properCyclicCoordinateBound r δ + (1 / 2 : ℝ) / q) ∧
            ∀ h ∈ K,
              cyclicKernelRealCoordinates η b (integerVectorRealMap (x h)) =
                c + affineCyclicTorusLocalLift t c h₀ h ∧
              (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ (1 / 2 : ℝ) / q) ∧
              integerVectorRealMap (x h) = (cyclicKernelRealCoordinates η b).symm
                (c + affineCyclicTorusLocalLift t c h₀ h) := by
  classical
  obtain ⟨b, hb, hcoordinates, _, t, ht, hperiod, hphase⟩ :=
    exists_controlled_cyclic_torus_model η R hinj h₀ J δ hδ hdense
      (fun h hh => ⟨x h, hx h hh, hrep h hh⟩)
  let y (h : ZMod N) := cyclicKernelRealCoordinates η b (integerVectorRealMap (x h))
  have hy : ∀ h ∈ J, ∀ i, |y h i| ≤ properCyclicCoordinateBound r δ := by
    intro h hh i
    apply hcoordinates _ _ i
    intro j
    have hj : |(x h j : ℝ)| ≤ (R j : ℝ) := by exact_mod_cast hx h hh j
    change |(x h j : ℝ)| ≤ (R j : ℝ) + 1
    linarith
  obtain ⟨K, hKJ, hK, hcard, c, hc, hclose⟩ := exists_dense_real_box_cell J hJ y hy q (by omega)
  have hquarter : (1 / 2 : ℝ) / q ≤ 1 / 4 := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < q)).mpr
    linarith
  refine ⟨b, hb, t, ht, hperiod, K, hKJ, hK, ?_, c, hc, ?_⟩
  · simpa only [Fintype.card_fin] using hcard
  · intro h hh
    have hlocal (i) : affineCyclicTorusLocalLift t c h₀ h i = y h i - c i := by
      have he : ((y h i - c i : ℝ) : AddCircle (1 : ℝ)) =
          (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ)) := by
        rw [AddCircle.coe_sub, AddCircle.coe_sub]
        exact congrArg (fun z : AddCircle (1 : ℝ) => z - (c i : AddCircle (1 : ℝ)))
          (hphase h (x h) (hrep h (hKJ hh)) i)
      change centeredCircleLift _ = _
      rw [← he]
      exact centeredCircleLift_coe ((hclose h hh i).trans hquarter)
    have he : y h = c + affineCyclicTorusLocalLift t c h₀ h := by
      funext i
      rw [Pi.add_apply, hlocal]
      ring
    refine ⟨he, ?_, ?_⟩
    · intro i
      rw [hlocal]
      exact hclose h hh i
    · exact (LinearEquiv.eq_symm_apply (cyclicKernelRealCoordinates η b)).mpr he

end Erdos3

end

section

namespace Erdos3

theorem centeredCircleLift_eq_sub_floor (x : ℝ) :
    centeredCircleLift (x : AddCircle (1 : ℝ)) = x - (⌊x + 1 / 2⌋ : ℤ) := by
  have hmem : x - (⌊x + 1 / 2⌋ : ℤ) ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor
    · linarith [Int.floor_le (x + 1 / 2)]
    · linarith [Int.lt_floor_add_one (x + 1 / 2)]
  have hint : (((⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨⌊x + 1 / 2⌋, by simp⟩
  have he : ((x - (⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = x := by
    rw [AddCircle.coe_sub, hint, sub_zero]
  rw [← he]
  exact AddCircle.equivIco_coe_of_mem hmem

noncomputable def affineCyclicTorusCarry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) : ℤ :=
  ⌊((h.val : ℝ) - h₀.val) * t i - c i + 1 / 2⌋

theorem affineCyclicTorusLocalLift_eq_sub_carry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    affineCyclicTorusLocalLift t c h₀ h i =
      ((h.val : ℝ) - h₀.val) * t i - c i - affineCyclicTorusCarry t c h₀ h i :=
  centeredCircleLift_eq_sub_floor _

theorem affineCyclicTorusCarry_identity {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    (-(h₀.val : ℝ) * t i - c i) +
      ((-(affineCyclicTorusCarry t c h₀ h i) : ℤ) : ℚ) + (h.val : ℝ) * t i =
        affineCyclicTorusLocalLift t c h₀ h i := by
  rw [affineCyclicTorusLocalLift_eq_sub_carry]
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

theorem local_cyclic_torus_cell_count_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r ≤
      Real.exp ((r : ℝ) * ((p + 4) ^ 5 + 17)) := by
  have hC := properCyclicCoordinateBound_le_exp hp hr
  have hC0 := properCyclicCoordinateBound_nonneg r (Real.exp_pos (-p))
  have hm := realBoxCellCount_le hC0 8
  have hE : 1 ≤ Real.exp ((p + 4) ^ 5) := Real.one_le_exp (by positivity)
  have h17 : (17 : ℝ) ≤ Real.exp 17 := by linarith [Real.add_one_le_exp (17 : ℝ)]
  have hcount : (realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℝ) ≤
      Real.exp ((p + 4) ^ 5 + 17) := by
    calc
      _ ≤ 17 * Real.exp ((p + 4) ^ 5) := by norm_num at hm; linarith
      _ ≤ Real.exp 17 * Real.exp ((p + 4) ^ 5) :=
        mul_le_mul_of_nonneg_right h17 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp ((p + 4) ^ 5 + 17)) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount r
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem local_cyclic_torus_total_loss_le {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    p + (r : ℝ) * ((p + 4) ^ 5 + 17) ≤ (p + 4) ^ 7 := by
  let U := p + 4
  have hU : 4 ≤ U := by dsimp [U]; linarith
  have h1 : 1 ≤ U := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hpow : (4 : ℝ) ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ (by norm_num) hU 3
  have hlinear : 18 * U ≤ U ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hpow hU0
    nlinarith
  calc
    _ ≤ U + U * (U ^ 5 + 17) := by dsimp [U]; gcongr <;> linarith
    _ = U ^ 6 + 18 * U := by ring
    _ ≤ U ^ 6 + U ^ 4 := add_le_add (le_refl _) hlinear
    _ ≤ U ^ 6 + U ^ 6 := add_le_add (le_refl _) (pow_le_pow_right₀ h1 (by omega))
    _ ≤ U ^ 7 := by
      have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ U by linarith) (pow_nonneg hU0 6)
      nlinarith

theorem local_cyclic_torus_density {r N : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (J K : Finset (ZMod N))
    (hJ : Real.exp (-p) * N ≤ (J.card : ℝ))
    (hK : J.card ≤ realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 ^ r * K.card) :
    Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) := by
  let L := (r : ℝ) * ((p + 4) ^ 5 + 17)
  have hcount := local_cyclic_torus_cell_count_le_exp hp hr
  have hretain : Real.exp (-(p + L)) * N ≤ (K.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos L)).mp
    calc
      _ = Real.exp (-p) * N := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (J.card : ℝ) := hJ
      _ ≤ ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r * K.card := by
        exact_mod_cast hK
      _ ≤ Real.exp L * K.card := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (local_cyclic_torus_total_loss_le hp hr)))
    (Nat.cast_nonneg N)).trans hretain

end Erdos3

end

section

namespace Erdos3

theorem centeredCircleLift_abs_le_half (z : AddCircle (1 : ℝ)) :
    |centeredCircleLift z| ≤ 1 / 2 := by
  have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).property
  change -(1 / 2 : ℝ) ≤ centeredCircleLift z ∧ centeredCircleLift z < -(1 / 2) + 1 at h
  exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩

theorem norm_eq_abs_centeredCircleLift (z : AddCircle (1 : ℝ)) :
    ‖z‖ = |centeredCircleLift z| := by
  calc
    ‖z‖ = ‖(centeredCircleLift z : AddCircle (1 : ℝ))‖ :=
      congrArg norm (coe_centeredCircleLift z).symm
    _ = _ := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).mpr
      (by simpa only [abs_one] using centeredCircleLift_abs_le_half z)

noncomputable def centeredTorusLift {ι : Type*} (x : ι → AddCircle (1 : ℝ)) : ι → ℝ :=
  fun i => centeredCircleLift (x i)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def realPeriodicTorusLift (F : (D → ℝ) → ℝ) (x : D → UnitAddCircle) : ℝ :=
  (integerPeriodicTorusLift (fun y => (F y : ℂ)) x).re

omit [Fintype D] in
theorem realPeriodicTorusLift_coe (F : (D → ℝ) → ℝ)
    (hF : ∀ (x : D → ℝ) (n : D → ℤ), F (fun i => x i + (n i : ℝ)) = F x) (x : D → ℝ) :
    realPeriodicTorusLift F (fun i => (x i : UnitAddCircle)) = F x := by
  unfold realPeriodicTorusLift
  rw [integerPeriodicTorusLift_coe _ (fun x n => congrArg Complex.ofReal (hF x n))]
  rfl

theorem realPeriodicTorusLift_lipschitz (F : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L F)
    (hF : ∀ (x : D → ℝ) (n : D → ℤ), F (fun i => x i + (n i : ℝ)) = F x) :
    LipschitzWith L (realPeriodicTorusLift F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let a : D → ℝ := fun i => centeredCircleLift (x i)
  let b : D → ℝ := fun i => a i + centeredCircleLift (y i - x i)
  have ha : (fun i => (a i : UnitAddCircle)) = x := funext (fun i => coe_centeredCircleLift _)
  have hb : (fun i => (b i : UnitAddCircle)) = y := by
    funext i
    change ((a i + centeredCircleLift (y i - x i) : ℝ) : UnitAddCircle) = y i
    rw [AddCircle.coe_add, coe_centeredCircleLift, coe_centeredCircleLift]
    change x i + (y i - x i) = y i
    abel
  have hd : dist a b ≤ dist x y := by
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    change dist (a i) (a i + centeredCircleLift (y i - x i)) ≤ dist x y
    rw [Real.dist_eq, sub_add_cancel_left, abs_neg, ← norm_eq_abs_centeredCircleLift, ← dist_eq_norm]
    exact (dist_le_pi_dist y x i).trans_eq (dist_comm y x)
  have heA : realPeriodicTorusLift F x = F a := by
    rw [← ha]
    exact realPeriodicTorusLift_coe F hF a
  have heB : realPeriodicTorusLift F y = F b := by
    rw [← hb]
    exact realPeriodicTorusLift_coe F hF b
  rw [heA, heB]
  exact (hL.dist_le_mul a b).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

omit [Fintype D] in
theorem realPeriodicTorusLift_range (F : (D → ℝ) → ℝ) {B : ℝ}
    (hB : ∀ x, 0 ≤ F x ∧ F x ≤ B) (x : D → UnitAddCircle) :
    0 ≤ realPeriodicTorusLift F x ∧ realPeriodicTorusLift F x ≤ B := by
  exact hB _

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SupportedQuotientExactGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_inner_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) := by
  classical
  rintro x ⟨z, rfl⟩
  let y : ι → ℚ := fun i => if hi : i ∈ S then 0 else (N : ℚ) * (z ⟨i, hi⟩ : ℚ)
  have hy : y ∈ scaledIntegerGrid N := by
    refine ⟨fun i => if hi : i ∈ S then 0 else z ⟨i, hi⟩, ?_⟩
    funext i
    dsimp [y]
    split_ifs <;> simp
  have hg : (⟨b.equivFun.symm y⟩ : F.Group) ∈ Γ := hin hy
  apply Subgroup.mem_map.mpr
  refine ⟨⟨b.equivFun.symm y⟩, hg, ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (supportedQuotientBasis b I.toSubmodule S hspan).equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  change (supportedQuotientBasis b I.toSubmodule S hspan).repr
    (I.toSubmodule.mkQ (b.equivFun.symm y)) i = _
  rw [supportedQuotientBasis_repr_mk, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [y, i.property, dite_false, Pi.smul_apply, smul_eq_mul]

theorem quotientStep_outer_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) ⊆ denominatorGrid N := by
  classical
  intro x hx
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
  have hgc : b.equivFun g.coord ∈ bchSubgroupCoordinates b Γ := by
    change (⟨b.equivFun.symm (b.equivFun g.coord)⟩ : F.Group) ∈ Γ
    simpa only [LinearEquiv.symm_apply_apply] using hg
  obtain ⟨z, hz⟩ := hout hgc
  have hxrepr (i : {i // i ∉ S}) : x i = b.equivFun g.coord i := by
    have hec := congrArg NilpotentLieBCHGroup.coord he
    have hr := congrArg (fun v => (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v i) hec
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm
  refine ⟨fun i => z i, fun i => ?_⟩
  change (N : ℚ) * x i = (z i : ℚ)
  rw [hxrepr]
  exact hz i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_exact_grid_supported (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
    have hgc := (bchSubgroupCoordinates_repr b Γ g).mpr hg
    rw [hgrid] at hgc
    obtain ⟨z, hz⟩ := hgc
    refine ⟨fun i => z i, ?_⟩
    funext i
    have hr := congrArg
      (fun v : (F.quotientLie I hI).Group =>
        (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v.coord i) he
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm.trans (congrFun hz i)
  · exact F.quotientStep_inner_grid_supported b I hI S hspan Γ
      (by rw [hgrid])

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ReducedLatticeBasis
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

theorem exists_integral_spanning_product_certificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      ∃ C : SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|),
      span ℤ (Set.range C.point) = span ℤ (Set.range b) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }, ?_⟩
      · simp [minkowskiSecondConstant]
      · simp
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq, hcqspan⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      have hspan : span ℤ (Set.range point) = L := by
        have hz : deleteProjectionLinear h v (b' 0) = 0 := by
          rw [hb'0, deleteProjectionLinear_apply, deleteProjection_self h v hvh]
        have ht : ∀ j, deleteProjectionLinear h v (b' j.succ) = qB j := by
          intro j
          ext i
          simp [qB, projectedTail, M, deleteProjection, hb'0]
        have hw : ∀ j, lift j ∈ span ℤ (Set.range b') := by
          intro j
          rw [hb'span]
          exact hliftL j
        have hs : span ℤ (Set.range (fun j => deleteProjectionLinear h v (lift j))) =
            span ℤ (Set.range qB) := by
          simpa only [deleteProjectionLinear_apply, hproj_lift] using hcqspan
        have hhspan := span_fin_cons_of_projected_span b' qB
          (deleteProjectionLinear h v) hz ht lift hw hs
        simpa only [hb'0, hb'span] using hhspan
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }, hspan⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

theorem exists_same_lattice_basis_norm_product_le {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of b).det| := by
  obtain ⟨C, hspan⟩ := exists_integral_spanning_product_certificate b
  let c := basisOfLinearIndependentOfCardEqFinrank' C.point C.independent (by simp)
  have hc : ∀ i, c i = C.point i := by intro i; simp [c]
  refine ⟨c, ?_, ?_⟩
  · simpa only [show (c : Fin n → Fin n → ℝ) = C.point from funext hc] using hspan
  · apply le_trans (b := ∏ i, C.scale i) _ C.product_le
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [hc]
    apply (mem_realBox_const_iff_norm_le (C.scale_nonneg i) _).mp
    simpa only [realBox_smul_one_eq_const] using C.mem_scaledBox i

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShortGeneratingBasisBound
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem basis_norm_le_of_integral_combination {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C : ℝ}
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (c : Fin n → ℤ) (i : Fin n) (hci : c i ≠ 0) :
    ‖b i‖ ≤ (n.factorial : ℝ) * C * ‖∑ j, c j • b j‖ := by
  classical
  let x := ∑ j, c j • b j
  let H := Function.update (fun j => ‖b j‖) i ‖x‖
  have hentry : ∀ j k, |((Matrix.of b).updateRow i x) j k| ≤ H j := by
    intro j k
    by_cases hji : j = i
    · subst j
      simpa only [Matrix.updateRow_self, H, Function.update_self] using abs_apply_le_norm x k
    · simpa only [Matrix.updateRow_ne hji, Matrix.of_apply, H, Function.update_of_ne hji]
        using abs_apply_le_norm (b j) k
  have hx : x = ∑ j, (c j : ℝ) • b j := by
    simp only [x, Int.cast_smul_eq_zsmul]
  have hdetx : ((Matrix.of b).updateRow i x).det = (c i : ℝ) * (Matrix.of b).det := by
    rw [hx]
    exact Matrix.det_updateRow_sum (Matrix.of b) i (fun j => (c j : ℝ))
  have hH : (∏ j, H j) = ‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖ := by
    rw [← Finset.mul_prod_erase Finset.univ H (Finset.mem_univ i)]
    rw [show H i = ‖x‖ by simp [H]]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hbound := Erdos3.matrix_det_abs_le_row_bounds ((Matrix.of b).updateRow i x) H hentry
  rw [hdetx, abs_mul, hH, Fintype.card_fin] at hbound
  have hci1 : (1 : ℝ) ≤ |(c i : ℝ)| := by exact_mod_cast Int.one_le_abs hci
  have hdet : 0 < |(Matrix.of b).det| := by
    apply abs_pos.mpr
    have h := (AlternatingMap.map_basis_ne_zero_iff b (Pi.basisFun ℝ (Fin n)).det).mpr
      (Pi.basisFun ℝ (Fin n)).det_ne_zero
    simpa only [Pi.basisFun_det_apply] using h
  have hdetle : |(Matrix.of b).det| ≤
      (n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖) := by
    exact (le_mul_of_one_le_left hdet.le hci1).trans hbound
  have hmul : ‖b i‖ * |(Matrix.of b).det| ≤
      ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
    calc
      ‖b i‖ * |(Matrix.of b).det| ≤ ‖b i‖ *
          ((n.factorial : ℝ) * (‖x‖ * ∏ j ∈ Finset.univ.erase i, ‖b j‖)) :=
        mul_le_mul_of_nonneg_left hdetle (norm_nonneg _)
      _ = (n.factorial : ℝ) * ‖x‖ * (∏ j, ‖b j‖) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ‖b j‖) (Finset.mem_univ i)]
        ring
      _ ≤ (n.factorial : ℝ) * ‖x‖ * (C * |(Matrix.of b).det|) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = ((n.factorial : ℝ) * C * ‖∑ j, c j • b j‖) * |(Matrix.of b).det| := by
        dsimp only [x]
        ring
  nlinarith

theorem basis_norm_le_of_short_spanning_family {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) {C R : ℝ} (hC : 0 ≤ C)
    (hprod : (∏ j, ‖b j‖) ≤ C * |(Matrix.of b).det|)
    (v : A → Fin n → ℝ) (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R)
    (i : Fin n) : ‖b i‖ ≤ (n.factorial : ℝ) * C * R := by
  classical
  have hex : ∃ a, b.coord i (v a) ≠ 0 := by
    by_contra! h
    have hs : span ℝ (Set.range v) ≤ LinearMap.ker (b.coord i) := by
      apply span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.mpr (h a)
    rw [hspan] at hs
    have hz := LinearMap.mem_ker.mp (hs (show b i ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial))
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_ne_zero] at hz
  obtain ⟨a, ha⟩ := hex
  have hm := hmem a
  rw [mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hci : c i ≠ 0 := by
    intro hz
    apply ha
    rw [← hc, map_sum]
    simp only [map_zsmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    simp [hz]
  have hb := basis_norm_le_of_integral_combination b hprod c i hci
  rw [hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hnorm a) (mul_nonneg (Nat.cast_nonneg _) hC))

theorem abs_det_eq_of_same_integer_span {n : ℕ}
    (b c : Basis (Fin n) ℝ (Fin n → ℝ))
    (hspan : span ℤ (Set.range b) = span ℤ (Set.range c)) :
    |(Matrix.of b).det| = |(Matrix.of c).det| := by
  have hcov (d : Basis (Fin n) ℝ (Fin n → ℝ)) :
      ZLattice.covolume (span ℤ (Set.range d)) = |(Matrix.of d).det| := by
    simpa only [Function.comp_def, Basis.restrictScalars_apply] using
      ZLattice.covolume_eq_det (span ℤ (Set.range d)) (d.restrictScalars ℤ)
  rw [← hcov b, hspan, hcov c]

theorem exists_short_same_lattice_basis {n : ℕ} {A : Type*}
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (v : A → Fin n → ℝ) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤)
    (hmem : ∀ a, v a ∈ span ℤ (Set.range b)) (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ c : Basis (Fin n) ℝ (Fin n → ℝ),
      span ℤ (Set.range c) = span ℤ (Set.range b) ∧
      (∏ i, ‖c i‖) ≤ minkowskiSecondConstant n * |(Matrix.of c).det| ∧
      ∀ i, ‖c i‖ ≤ (n.factorial : ℝ) * minkowskiSecondConstant n * R := by
  obtain ⟨c, hc, hp⟩ := exists_same_lattice_basis_norm_product_le b
  rw [← abs_det_eq_of_same_integer_span c b hc] at hp
  refine ⟨c, hc, hp, ?_⟩
  apply basis_norm_le_of_short_spanning_family c (minkowskiSecondConstant_nonneg n) hp v hspan
  · intro a
    rw [hc]
    exact hmem a
  · exact hnorm

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MaskedIntegerPeriodization
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def maskedIntegerPeriodization (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ))

noncomputable def maskedIntegerTorusKernel (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (fun x => maskedIntegerPeriodization q mask H (fun i => q * x i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealifiedCentralBasisAction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

variable (e : Basis ι ℚ L) (b : Basis κ ℚ L)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (N : ℕ) (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)

noncomputable def realifiedCentralBasisAction (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    CircleFourier.IsometricCircleAction
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ⧸
        Γ.map realificationHom) :=
  centralBCHCircleAction (e.baseChange ℝ) (Γ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl houter).1
    ((N : ℝ) • (b.baseChange ℝ) j) (scaled_real_basis_central b j hj N)
    (scaled_real_basis_mem_realification b Γ N hinner j)

theorem realifiedCentralBasisAction_act_coe (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    (r : ℝ) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := realification_lowerCentralSeries_eq_bot hnil)
        ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_act_coe _ _ _ _ _ _ r x

theorem realifiedCentralBasisAction_displacement (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    dist ((realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act t x) x ≤
      ((Fintype.card ι : ℝ) + 1) * ((N : ℝ) * B) * ‖t‖ := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  apply (centralBCHCircleAction_displacement _ _ _ _ _ _ t x).trans
  exact mul_le_mul_of_nonneg_right (scaled_real_basis_coordinate_bound e b N j hB hb) (norm_nonneg t)

theorem realifiedCentralBasisAction_commutes (i j : κ)
    (hi : ∀ w : L, ⁅b i, w⁆ = 0) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner i hi).Commutes
      (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj) := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_commutes _ _ _ _ _ _ _ _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

def differenceInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![-a ji.2, b ji.2, 0] ji.1

theorem differenceInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    differenceInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![-za ji.2, zb ji.2, 0] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

theorem differenceInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hba : b - a ∈ scaledIntegerGrid m) :
    differenceInput a b - differenceInput a a ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hba
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i - a i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [differenceInput, Pi.smul_apply, smul_eq_mul, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem differenceCoordinate_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a b : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (a⁻¹ * b).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![a⁻¹, b, 1]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [a⁻¹, b, 1] := by simp [f]; exact ⟨rfl, rfl⟩
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      differenceInput (e.equivFun a.coord) (e.equivFun b.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, differenceInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rwa [hi] at he

theorem differenceCoordinate_same (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
      (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using differenceCoordinate_eval e hnil a a i

theorem bch_coset_eq_of_coordinate_congruence (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (q l : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (a b : NilpotentLieBCHGroup L s hnil)
    (ha : e.equivFun a.coord ∈ denominatorGrid q) (hb : e.equivFun b.coord ∈ denominatorGrid q)
    (hba : e.equivFun b.coord - e.equivFun a.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b := by
  apply QuotientGroup.eq.mpr
  apply (bchSubgroupCoordinates_repr e Γ _).mp
  apply hinner
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
    (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
    (differenceInput_mem_denominatorGrid _ _ q ha hb)
    (differenceInput_mem_denominatorGrid _ _ q ha ha)
    (differenceInput_sub_mem_scaledGrid _ _ _ hba)
  simp only [differenceCoordinate_same] at h
  simpa only [differenceCoordinate_eval, sub_zero,
    ← Basis.equivFun_apply] using h

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialBCHMap (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => eval (fun j => (x j : ℚ)) (P i))⟩

omit [Fintype σ] in
@[simp] theorem polynomialBCHMap_coordinates (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    e.equivFun (polynomialBCHMap e hnil P x).coord = fun i => eval (fun j => (x j : ℚ)) (P i) :=
  e.equivFun.apply_symm_apply _

noncomputable def polynomialBCHPeriod (e : Basis ι ℚ L) (s l : ℕ)
    (P : ι → MvPolynomial σ ℚ) : ℕ :=
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) *
    polynomialFamilyDenominator P ^ s) * polynomialFamilyDenominator P

theorem polynomialBCHMap_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l r : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (polynomialBCHPeriod e s l P : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply Eq.symm
  apply bch_coset_eq_of_coordinate_congruence e hnil Γ (polynomialFamilyDenominator P) l
    (polynomialFamilyDenominator_pos _) hinner
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P y
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P x
  · simp only [polynomialBCHMap_coordinates]
    exact polynomial_family_integer_congruence P r _ hdegree x y hxy

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped Manifold ContDiff TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialBCHMap (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) : NilpotentLieBCHGroup L s hnil :=
  ⟨e.equivFun.symm (fun i => aeval x (P i))⟩

@[simp] theorem realPolynomialBCHMap_coordinates (e : Basis ι ℝ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℝ) :
    e.equivFun (realPolynomialBCHMap (hnil := hnil) e P x).coord =
      fun i => aeval x (P i) :=
  e.equivFun.apply_symm_apply _

section Smooth

variable [Fintype σ] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

end Smooth

end Erdos3

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realPolynomialBCHMap_integer (e : Basis ι ℚ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    realPolynomialBCHMap (hnil := realification_lowerCentralSeries_eq_bot hnil)
      (e.baseChange ℝ) P (fun j => (x j : ℝ)) =
        NilpotentLieBCHGroup.realificationHom (polynomialBCHMap e hnil P x) := by
  apply NilpotentLieBCHGroup.ext
  apply (e.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates, NilpotentLieBCHGroup.realificationHom_coordinates]
  funext i
  change aeval (fun j => (x j : ℝ)) (P i) =
    ((e.equivFun (polynomialBCHMap e hnil P x).coord i : ℚ) : ℝ)
  rw [polynomialBCHMap_coordinates]
  change aeval (fun j => (x j : ℝ)) (P i) = ((eval (fun j => (x j : ℚ)) (P i) : ℚ) : ℝ)
  induction P i using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, eval_C]; rfl
  | add p q hp hq => simp only [map_add, Rat.cast_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, aeval_X, eval_X, Rat.cast_mul, hp,
      Rat.cast_intCast]

theorem realification_coset_eq
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (a b : NilpotentLieBCHGroup L s hnil)
    (hab : (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b) :
    (QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom a) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
        QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom b) := by
  apply QuotientGroup.eq.mpr
  rw [← map_inv, ← map_mul]
  exact Subgroup.mem_map.mpr ⟨a⁻¹ * b, QuotientGroup.eq.mp hab, rfl⟩

variable [Fintype σ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem scaledPairLayer_eq_inf (P Q : Submodule ℚ L) (q : ℚ) :
    scaledPairLayer P Q q = P.comap (LinearMap.fst ℚ L L) ⊓
      (P.comap (LinearMap.snd ℚ L L) ⊓ Q.comap (scaledPairDifference q)) := by
  ext x
  rfl

theorem realPairEquiv_mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q ↔
      x ∈ (scaledPairLayer P Q q).baseChange ℝ := by
  change ((realPairEquiv x).1 ∈ P.baseChange ℝ ∧
    (realPairEquiv x).2 ∈ P.baseChange ℝ ∧
    scaledPairDifference q (realPairEquiv x) ∈ Q.baseChange ℝ) ↔ _
  rw [realPairEquiv_difference, realPairEquiv_first, realPairEquiv_second]
  simp only [scaledPairLayer_eq_inf, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedScaledPairLayerEquiv (P Q : Submodule ℚ L) (q : ℚ) :
    ((scaledPairLayer P Q q).baseChange ℝ) ≃ₗ[ℚ]
      scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q where
  toFun x := ⟨realPairEquiv x.val, (realPairEquiv_mem_scaledPairLayer P Q q x.val).mpr x.property⟩
  invFun x := ⟨realPairEquiv.symm x.val, (realPairEquiv_mem_scaledPairLayer P Q q _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realPairEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realPairEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realPairEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realPairEquiv.restrictScalars ℚ).map_smul r x.val)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q n ↔
      x ∈ (F.dilationPairLayer q n).baseChange ℝ :=
  realPairEquiv_mem_scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n) x

noncomputable def realifiedDilationPairLayerEquiv (q : ℚ) (n : ℕ) :
    ((F.dilationPairLayer q n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.dilationPairLayer q n :=
  realifiedScaledPairLayerEquiv (F.layer n) (F.layer (n + 1)) (q ^ n)

noncomputable def realifiedDilationPairEquiv (q : ℚ) :
    (ℝ ⊗[ℚ] F.dilationPairSubalgebra q) ≃ₗ[ℚ]
      F.realification.dilationPairSubalgebra q :=
  ((realificationSubmoduleEquiv (F.dilationPairLayer q 1)).restrictScalars ℚ).trans
    (F.realifiedDilationPairLayerEquiv q 1)

theorem realifiedDilationPairEquiv_coe (q : ℚ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
      realPairEquiv (realificationLieHom (F.dilationPairSubalgebra q).incl x) := rfl

theorem realifiedDilationPairEquiv_mem_layer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).realification.layer n ↔
      F.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairFiltration q).layer n := by
  change x ∈ ((F.dilationPairLayer q n).comap
    (F.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q n).baseChange ℝ ↔
      (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q n
  rw [F.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_realification (a : σ → ℕ) :
    (F.realification.strictUpperLayer a).toSubmodule =
      ((F.strictUpperLayer a).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [strictUpperLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q a ↔
      x ∈ (F.dilationPairLayer q a).baseChange ℝ := by
  change realPairEquiv x ∈ scaledPairLayer (F.realification.layer a)
    (F.realification.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i) ↔ _
  rw [F.strictUpperLayer_realification]
  exact realPairEquiv_mem_scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule _ x

theorem realifiedDilationPairEquiv_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).realification.layer a ↔
      F.ordinary.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  change x ∈ ((F.dilationPairLayer q a).comap
    (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.ordinary.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q a).baseChange ℝ ↔
      (F.ordinary.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q a
  rw [F.ordinary.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

theorem realifiedDilationPairEquiv_symm_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.realification.dilationPairSubalgebra q) :
    (F.ordinary.realifiedDilationPairEquiv q).symm x ∈
        (F.dilationPairMultidegree q).realification.layer a ↔
      x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  rw [F.realifiedDilationPairEquiv_mem_multidegree, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSupportedQuotientCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientBasis_repr_mk (x : ℝ ⊗[ℚ] V) (i : {i // i ∉ S}) :
    ((supportedQuotientBasis b P S hP).baseChange ℝ).repr (P.mkQ.baseChange ℝ x) i =
      (b.baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientBasis_repr_mk]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BaseChangeCoordinateProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem baseChange_coordinate_eq
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (P : V →ₗ[ℚ] W) (r : κ → ι)
    (hP : ∀ x i, c.repr (P x) i = b.repr x (r i))
    (x : ℝ ⊗[ℚ] V) (i : κ) :
    (c.baseChange ℝ).repr (P.baseChange ℝ x) i = (b.baseChange ℝ).repr x (r i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul t x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, hP]

theorem baseChange_coordinate_projector_repr
    {V W ι : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis ι ℚ V) (P : V →ₗ[ℚ] W) (S : W →ₗ[ℚ] V)
    (p : ι → Prop) [DecidablePred p]
    (hproj : ∀ x i, b.repr (S (P x)) i = if p i then b.repr x i else 0)
    (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (S.baseChange ℝ (P.baseChange ℝ x)) i =
      if p i then (b.baseChange ℝ).repr x i else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply] at *
    rw [hx, hy]
    split_ifs <;> simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, hproj]
    split_ifs <;> simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RetainedPhysicalLowerDegree
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

def HasNativeLowerDegreeOrbit {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : Prop :=
  ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
    ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
      (F.gradedRefiltration W).realQuotientStepHom
        ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
        ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q)

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LocalSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem crootSisaskSampleSize_le (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (crootSisaskSampleSize m epsilon : ℝ) ≤ 256 * (m : ℝ) / epsilon ^ 2 + 1 := by
  apply (Nat.ceil_lt_add_one (show 0 ≤ 256 * (m : ℝ) / epsilon ^ 2 by positivity)).le

variable {N : ℕ}

theorem convolutionMomentOrder_le (M L : Finset (ZMod N)) :
    (convolutionMomentOrder M L : ℝ) ≤ 2 + Real.log (max 1 ((M.card : ℝ) / L.card)) := by
  have hlog := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  have h := Nat.ceil_lt_add_one (show 0 ≤ 1 + Real.log (max 1 ((M.card : ℝ) / L.card)) by linarith)
  change (⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊ : ℝ) ≤ _
  linarith

theorem convolutionMomentOrder_le_of_ratio (M L : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp p) :
    (convolutionMomentOrder M L : ℝ) ≤ p + 2 := by
  have hmax : max 1 ((M.card : ℝ) / L.card) ≤ Real.exp p :=
    max_le (Real.one_le_exp_iff.mpr hp) hratio
  have hpos : (0 : ℝ) < max 1 ((M.card : ℝ) / L.card) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog := Real.log_le_log hpos hmax
  rw [Real.log_exp] at hlog
  exact (convolutionMomentOrder_le M L).trans (by linarith)

theorem localBoostedSampleSize_le (M L : Finset (ZMod N)) {p delta : ℝ}
    (hp : 0 ≤ p) (hratio : (M.card : ℝ) / L.card ≤ Real.exp p)
    (hdelta : 0 < delta) (q : ℕ) (hq : 0 < q) :
    (crootSisaskSampleSize (convolutionMomentOrder M L) ((delta / q) / Real.exp 1) : ℝ) ≤
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (p + 2) * (q : ℝ) ^ 2 + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < (delta / (q : ℝ)) / Real.exp 1 := by positivity
  have hm := convolutionMomentOrder_le_of_ratio M L hp hratio
  apply (crootSisaskSampleSize_le _ he).trans
  have hid : 256 * (convolutionMomentOrder M L : ℝ) / ((delta / q) / Real.exp 1) ^ 2 + 1 =
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (convolutionMomentOrder M L : ℝ) * (q : ℝ) ^ 2 + 1 := by
    field_simp
  rw [hid]
  gcongr

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineDegreeChoice
namespace OAI

section

namespace Erdos3

noncomputable def affineRemovalDepth (T : ℝ) : ℕ := CyclicCrootSisask.spectralIterations 1 T

noncomputable def affineFinalDegree (j r : ℕ) (shell Q : ℝ) : ℕ :=
  j + max r (CyclicCrootSisask.spectralIterations shell Q)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonTail (ε L T : ℝ) : ℕ :=
  CyclicCrootSisask.spectralIterations (ε / (2 + ε)) (L + 2 * T + 4)

noncomputable def affineComparisonScale (ε L T C : ℝ) : ℝ :=
  L + T + 2 + (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) + C

noncomputable def affineComparisonMoment (P : ℝ) : ℕ :=
  2 * (Nat.floor (P / 2) + 1)

end Erdos3

end

section

namespace Erdos3

noncomputable def affinePrimitiveLogBudget (P : ℝ) : ℝ := 16 * (P + 3)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => prime i ∣ M)

@[simp] theorem mem_periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) (i : ι) :
    i ∈ periodPrimeCoordinates prime M ↔ prime i ∣ M := by
  classical
  simp [periodPrimeCoordinates]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem modEq_selected_prod_iff {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (a b : ℤ) :
    a ≡ b [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] ↔ ∀ i ∈ I, a ≡ b [ZMOD (q i : ℤ)] := by
  induction I using Finset.induction_on with
  | empty => simp [Int.ModEq]
  | @insert i I hi ih =>
    have hc : (q i).Coprime (∏ j ∈ I, q j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply hcop
      intro heq
      subst j
      exact hi hj
    have hci : Int.natAbs (q i : ℤ) |>.Coprime (Int.natAbs ((∏ j ∈ I, q j : ℕ) : ℤ)) := by
      simpa only [Int.natAbs_natCast] using hc
    rw [Finset.prod_insert hi, Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hci, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

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

noncomputable def affineComparisonPrimeThreshold (ξ P : ℝ) : ℝ :=
  (P + 2) ^ (4 + CyclicCrootSisask.spectralIterations ξ 18)

noncomputable def affineComparisonContraction (ξ P : ℝ) : ℝ :=
  (affineComparisonPrimeThreshold ξ P)⁻¹

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineInitialPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) : Finset ι :=
  (affineMandatoryPrimes prime ξ P ∪ periodPrimeCoordinates prime sourceM) ∪
    periodPrimeCoordinates prime siteM

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineSamplerPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) : Finset ι :=
  affineInitialPrimeMask prime ξ P sourceM siteM ∪ periodPrimeCoordinates prime D

end Erdos3

end

section

namespace Erdos3

noncomputable def affineReferencePower (epsilon : ℝ) : ℕ :=
  4 + CyclicCrootSisask.spectralIterations (epsilon / (2 + epsilon)) 18

noncomputable def affineReferenceInput (epsilon U : ℝ) : ℝ :=
  (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon +
    affinePrimitiveLogBudget U + 3 * U + 10

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    Finset (σ → ℤ) := by
  classical
  exact (translatedIntegerBox lo N).filter (fun z => ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i)

@[simp] theorem mem_primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I x ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i := by
  classical
  simp only [primeCoordinateCell, Finset.mem_filter]

theorem mem_primeCoordinateCell_anchor {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ j, z j ≡ u j [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] := by
  rw [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, heq⟩
    refine ⟨hz, ?_⟩
    intro j
    apply (modEq_selected_prod_iff q hcop I (z j) (u j)).mpr
    intro i hi
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mp (congrFun (heq i hi) j)
  · rintro ⟨hz, hmod⟩
    refine ⟨hz, ?_⟩
    intro i hi
    funext j
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mpr
      ((modEq_selected_prod_iff q hcop I (z j) (u j)).mp (hmod j) i hi)

noncomputable def primeCoordinateCellEquiv {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u : σ → ℤ) :
    primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ≃
      IntegerResidueBox lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u where
  toFun z := fun j => ⟨z.val j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ((mem_translatedIntegerBox lo N z.val).mp ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).1 j),
    ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).2 j⟩⟩
  invFun z := ⟨fun j => (z j).val, (mem_primeCoordinateCell_anchor lo N q hcop I u _).mpr
    ⟨(mem_translatedIntegerBox lo N _).mpr (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (z j).property).1),
      fun j => (Finset.mem_filter.mp (z j).property).2⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by funext j; apply Subtype.ext; rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnMap (V : J → G) : (J → ZMod q) →+ G where
  toFun t := ∑ j, t j • V j
  map_zero' := by simp
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]

noncomputable def residueColumnAverage (V : J → G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {p a : ℕ} [NeZero (p ^ a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnRealAverage (V : J → G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

variable [Fintype G]

theorem residueColumnRealAverage_mean (V : J → G) (f : G → ℝ) :
    (𝔼 x : G, residueColumnRealAverage (q := q) V f x) = 𝔼 x : G, f x := by
  unfold residueColumnRealAverage
  rw [Finset.expect_comm]
  have hshift (t : J → ZMod q) : (𝔼 x : G, f (x + residueColumnMap (q := q) V t)) = 𝔼 x : G, f x :=
    Fintype.expect_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) _ _ (fun _ => rfl)
  simp only [hshift, Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

noncomputable def residueAffineSource : FiniteProbabilityWeights ((J → G) × G) :=
  (FiniteProbabilityWeights.uniform (J → G)).prod (FiniteProbabilityWeights.uniform G)

noncomputable def residueAffineKernel (z : (J → G) × G) : FiniteProbabilityWeights G :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun t => z.2 + residueColumnMap (q := q) z.1 t)

theorem residueAffineKernel_mean (z : (J → G) × G) (f : G → ℝ) :
    (residueAffineKernel (q := q) z).mean f = residueColumnRealAverage (q := q) z.1 f z.2 := by
  rw [residueAffineKernel, FiniteProbabilityWeights.fiberLaw_mean, FiniteProbabilityWeights.uniform_mean]
  rfl

theorem residueAffineKernel_preserves_mean (f : G → ℝ) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f) =
      (FiniteProbabilityWeights.uniform G).mean f := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean, residueColumnRealAverage_mean, Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
  (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)

include hp hcard

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

noncomputable def primeCoordinateMean {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ :=
  𝔼 z : primeCoordinateCell lo N q I x, f z.val

noncomputable def PrimeCoordinateStable {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → (primeCoordinateCell lo N q (I ∪ J) y).Nonempty →
    ‖primeCoordinateMean f lo N q I x - primeCoordinateMean f lo N q (I ∪ J) y‖ ≤ δ

universe u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def primeCoordinateObservation {ι σ : Type*} (q : ι → ℕ) (z : σ → ℤ) : ∀ i, σ → ZMod (q i) :=
  fun i j => (z j : ZMod (q i))

noncomputable def primeCoordinateReference {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] : ∀ i, FiniteProbabilityWeights (σ → ZMod (q i)) :=
  fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev ResiduePrimeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :=
  {z : IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a //
    ∀ i ∈ I, (fun j => ((z j).val : ZMod (q i))) = x i}

noncomputable def residuePrimeCoordinateMean {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℂ := by
  classical
  exact 𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)

noncomputable def ResiduePrimeCoordinateStable {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    ‖residuePrimeCoordinateMean f lo N M a q I x -
      residuePrimeCoordinateMean f lo N M a q (I ∪ J) y‖ ≤ δ

noncomputable def primeCoordinateCell_subtypeEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell lo N q I x ≃
      {z : translatedIntegerBox lo N // ∀ i ∈ I, (fun j => (z.val j : ZMod (q i))) = x i} where
  toFun z := ⟨⟨z.val, ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).1⟩,
    ((mem_primeCoordinateCell lo N q I x z.val).mp z.property).2⟩
  invFun z := ⟨z.val.val, (mem_primeCoordinateCell lo N q I x z.val.val).mpr ⟨z.val.property, z.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def affineSampleAlphabetEquiv {J I R : Type*} :
    (Option J × I → R) ≃ (J → I → R) × (I → R) where
  toFun z := (fun j i => z (some j, i), fun i => z (none, i))
  invFun z := baseArrayJoin (fun k => z.1 k.1 k.2) z.2
  left_inv z := baseArrayJoin_eta z
  right_inv _ := rfl

theorem affineSampleAlphabet_weight {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (z : Option J × I → R) :
    (residueAffineSource (J := J) (G := I → R)).weight (affineSampleAlphabetEquiv z) =
      (FiniteProbabilityWeights.uniform (Option J × I → R)).weight z := by
  change (Fintype.card (J → I → R) : ℝ)⁻¹ * (Fintype.card (I → R) : ℝ)⁻¹ =
    (Fintype.card (Option J × I → R) : ℝ)⁻¹
  rw [Fintype.card_congr (affineSampleAlphabetEquiv (J := J) (I := I) (R := R))]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

theorem affineSampleAlphabet_mean {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (f : ((J → I → R) × (I → R)) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → R)).mean
      (fun z => f (affineSampleAlphabetEquiv z)) =
      (residueAffineSource (J := J) (G := I → R)).mean f :=
  FiniteProbabilityWeights.mean_equiv _ _ affineSampleAlphabetEquiv affineSampleAlphabet_weight f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoprimeResiduePhysicalStability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateCellEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x ≃
    ResiduePrimeCoordinateCell lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) := by
  refine (primeCoordinateCell_subtypeEquiv _ _ q I x).trans
    ((integerResidueBoxEquiv lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a
      (fun _ => Nat.cast_pos.mpr hM)).subtypeEquiv ?_)
  intro z
  constructor
  · intro hz i hi
    change (fun j => ((a j + (M : ℤ) * z.val j : ℤ) : ZMod (q i))) = _
    rw [← affineResidueCoordinateEquiv_intCast M (q i) a (hcop i)]
    exact congrArg (affineResidueCoordinateEquiv M (q i) a (hcop i)) (hz i hi)
  · intro hz i hi
    apply (affineResidueCoordinateEquiv M (q i) a (hcop i)).injective
    rw [affineResidueCoordinateEquiv_intCast]
    exact hz i hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  ((primeCoordinateCell lo N q I x).card : ℝ) / (translatedIntegerBox lo N).card /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

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

noncomputable def residuePrimeCoordinateDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) : (∀ i, σ → ZMod (q i)) → ℝ := by
  let := hne
  exact observedProductDensity (primeCoordinateReference (σ := σ) q)
    (FiniteProbabilityWeights.uniform
      (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (fun z => primeCoordinateObservation q (fun j => (z j).val)) (fun z => f (fun j => (z j).val))

noncomputable def residuePrimeCoordinateMassRatio {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  (Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) : ℝ) /
    Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) /
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x

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

noncomputable def normalizedResiduePrimeDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) (scale : ℝ)
    (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  scale⁻¹ * residuePrimeCoordinateDensity lo N M a hne q f x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))

noncomputable def selectedPrimeCRT :
    ZMod (∏ i : I, q i.val) ≃+* (∀ i : I, ZMod (q i.val)) :=
  ZMod.prodEquivPi (fun i : I => q i.val)
    (fun i j hij => hpair (by intro h; exact hij (Subtype.ext h)))

noncomputable def primeCoordinatesMod (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) :
    (∀ i, σ → ZMod (q i)) →+ (σ → ZMod m) where
  toFun x k := (ZMod.castHom hd (ZMod m))
    ((selectedPrimeCRT q I hpair).symm (fun i : I => x i.val k))
  map_zero' := by
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm 0) = 0
    rw [map_zero, map_zero]
  map_add' := by
    intro x y
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm
      ((fun i : I => x i.val k) + (fun i : I => y i.val k))) = _
    rw [map_add, map_add]
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def coarseResidueIndicator {ι σ : Type*}
    (q : ι → ℕ) (I : Finset ι) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  if primeCoordinatesMod q I hpair m hd x = r then 1 else 0

section

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
  (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m)

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueTruncationCap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) (eta : ℝ) : ℝ :=
  ((lowDegreeCoordinateSets ι b).card : ℝ) * (2 : ℝ) ^ b * (1 + eta)

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def residuePhysicalTruncation (b : ℕ) (f : (σ → ℤ) → ℝ) (u : σ → ℤ) : ℝ :=
  productANOVATruncation (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι b)
    (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q u)

def ResiduePhysicalTruncationControl (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ) : Prop :=
  let low := residuePhysicalTruncation lo N M a hne q b f
  let cap := residueTruncationCap ι b eta
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    low (fun k => (z k).val) ^ 2) ≤ 2 + 3 * eta * cap ^ 2 ∧
  (𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
    (f (fun k => (z k).val) - low (fun k => (z k).val)) ^ 2) ≤ 1 + eta * cap ^ 2 ∧
  ∀ (I : Finset ι), I.card ≤ b → ∀ test : (∀ i, σ → ZMod (q i)) → ℝ, ProductDependsOn I test →
    |𝔼 z : IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a,
      (f (fun k => (z k).val) - low (fun k => (z k).val)) *
        test (primeCoordinateObservation q (fun k => (z k).val))| ≤
      eta * cap * (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).mean
        (fun x => |test x|)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

noncomputable def physicalBoxTruncation (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if hx : x ∈ translatedIntegerBox lo N then
    let c := physicalBoxCell lo N P ⟨x, hx⟩
    residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x
  else 0

noncomputable def physicalBoxResidual (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if x ∈ translatedIntegerBox lo N then f x - physicalBoxTruncation lo N P hpos q b f x else 0

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarTransferBaseAccuracy (targetLog : ℝ) : ℝ := Real.exp (-(targetLog + 10))

noncomputable def scalarTransferMarginalAccuracy (targetLog capLog : ℝ) : ℝ :=
  Real.exp (-(targetLog + capLog + 10))

noncomputable def scalarTransferTail (targetLog : ℝ) : ℝ := 2 * (targetLog + 10)

end Erdos3

end

section

namespace Erdos3

noncomputable def residualCapEnvelope (ι : Type*) [Fintype ι] [DecidableEq ι] (degree : ℕ) : ℝ :=
  1 + 2 * ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalResidualPairBudget {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (k : J) (Q : ℕ)
    (C κ δ : ℝ) (degree : ℕ) (eta ρ : ℝ) : ℝ :=
  ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
    ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap (BoundedPrime Q) degree eta) ^ 2 +
      (fullSmoothPairError (Fintype.card I) k Q C κ δ + (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
        (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2))

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalPairPointAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) : ℝ :=
  residualPointAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairErrorCoefficient n k Q C κ)
    ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) epsilon

noncomputable def physicalPairGridAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ A epsilon : ℝ) : ℝ :=
  residualGridAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairKernelLip n k C κ) epsilon

noncomputable def physicalPairMeanAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  residualMeanAccuracy (A ^ (2 * n)) (smoothPairKernelCap n k C κ)
    (residualCapEnvelope (BoundedPrime Q) degree) epsilon

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def physicalPairCoefficientLog (n d : ℕ) (P : ℝ) : ℝ :=
  30 + 2 * n * P + 2 * n + smoothPairErrorLog n d P +
    n * (5 * P + 11) + 10 * P + 4 * (2 + d)

noncomputable def physicalPairMeanLog (n degree : ℕ) (P : ℝ) : ℝ :=
  2 * ((degree : ℝ) * (P + 2) + 2) + 4 + 2 * n * P + n * (5 * P + 11) + P

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledConditionedComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productAtomTruncatedPairing (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D (fun z => productFiberIndicator I x z * w z))
    (productANOVATruncation ν D (fun z => productFiberIndicator I y z * f z))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productTruncatedPairing (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) : ℝ :=
  productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

variable {Ω : Type*} [Fintype Ω] [∀ i, DecidableEq (X i)]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X Y : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (e : J ↪ I)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)

include baseX baseY

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

noncomputable def affineSampleKernel (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  residueAffineKernel (q := q) (affineSampleAlphabetEquiv z)

theorem affineSampleKernel_preserves_mean (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f) = (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f)]
  exact residueAffineKernel_preserves_mean f

noncomputable def affineSampleCoupling :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ affineSampleKernel affineSampleKernel_preserves_mean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleFixedParameter_mean (t : J → ZMod q) (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => f (z.2 + residueColumnMap (q := q) z.1 t))]
  rw [residueAffineSource, FiniteProbabilityWeights.mean_prod]
  have hs (V : J → I → ZMod q) :
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean
        (fun x => f (x + residueColumnMap (q := q) V t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f :=
    FiniteProbabilityWeights.uniform_mean_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) f
  simp only [hs, FiniteProbabilityWeights.mean_const]

noncomputable def affineSampleParameterKernel (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  π.fiberLaw (fun t => (affineSampleAlphabetEquiv z).2 +
    residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)

theorem affineSampleParameterKernel_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) (f : (I → ZMod q) → ℝ) :
    (affineSampleParameterKernel π z).mean f =
      π.mean (fun t => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) :=
  π.fiberLaw_mean _ f

theorem affineSampleParameterKernel_preserves_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleParameterKernel π z).mean f) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  simp only [affineSampleParameterKernel_mean]
  rw [FiniteProbabilityWeights.mean_comm]
  simp only [affineSampleFixedParameter_mean, FiniteProbabilityWeights.mean_const]

noncomputable def affineSampleParameterCoupling (π : FiniteProbabilityWeights (J → ZMod q)) :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ (affineSampleParameterKernel π)
    (affineSampleParameterKernel_preserves_mean π)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineSampleProductCoupling {ι J σ : Type*} [Fintype J] [Fintype σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleCoupling (J := J) (I := σ) (q := q i)

noncomputable def affineResidueTruncatedPairing {ι J σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [Fintype σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (D : Finset (Finset ι)) (w : (∀ i, Option J × σ → ZMod (q i)) → ℝ)
    (f : (∀ i, σ → ZMod (q i)) → ℝ) : ℝ :=
  productTruncatedPairing (affineSampleProductCoupling (J := J) (σ := σ) q) D w f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

noncomputable def affinePeriodParameterLaw (D : ℕ) (a : J → ℤ) :
    FiniteProbabilityWeights (J → ZMod q) :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun s j => (a j : ZMod q) + (D : ZMod q) * s j)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affineParameterProductCoupling
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i))) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleParameterCoupling (π i)

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodProductCoupling (D : ℕ) (a : J → ℤ) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  affineParameterProductCoupling q (fun i => affinePeriodParameterLaw (q := q i) D a)

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodResidueSample (D : ℕ) (a : J → ℤ)
    (z : ∀ i, Option J × I → ZMod (q i)) (s : ∀ i, J → ZMod (q i)) :
    ∀ i, I → ZMod (q i) :=
  fun i => (affineSampleAlphabetEquiv (z i)).2 +
    residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
      (fun j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j)

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I Ω Θ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [Fintype I] [Fintype Ω] [Fintype Θ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

noncomputable def residueAffineTruncationError : ℝ :=
  |(𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
      w (fun i => (z i).val) *
        (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
          residuePhysicalTruncation siteLo siteN 1 (fun _ => 0) siteHne q b f
            (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) -
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q f)|

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StablePrimeUpperComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def PrimeRefinementUpperBound {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (h g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (level ε δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) : Prop :=
  ∀ J : Finset ι, Disjoint I J → J.card ≤ r → ∀ y : ∀ i, σ → ZMod (q i),
    (∀ i ∈ I, y i = x i) → Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y) →
    (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε + level * δ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCellNormLengths
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
  (moduli : ι → ℕ) [∀ i, NeZero (moduli i)]
  (f : (σ → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)

include hf

end Erdos3

end

section

namespace Erdos3

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueCellOutsideDensity {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) :
    (∀ i : {i // i ∉ K}, σ → ZMod (q i.val)) → ℝ :=
  observedProductDensity (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
    (@FiniteProbabilityWeights.uniform (ResiduePrimeCoordinateCell lo N M a q K base) _ ⟨u⟩)
    (fun z => primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z.val k).val))
    (fun z => f (fun k => (z.val k).val))

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*}

variable [Fintype J]

variable [Fintype Ω]

variable [Fintype ι]

variable [LinearOrder ι]

variable [Fintype σ]

variable {h g : (σ → ℤ) → ℂ}

variable {lo a : σ → ℤ}

variable {N : σ → ℕ}

variable {M : ℕ}

variable {q : ι → ℕ}

variable [∀ i, NeZero (q i)]

variable {j r b moment : ℕ}

variable {level inc δ η τ L T P : ℝ}

variable {K : Finset ι}

variable {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {regK κ ε ξ shell modLog : ℝ}

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F regK τ j r w rem cs)

variable (hregK : 1 ≤ regK)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ τ)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hlevel : 0 < level)

variable (hτ : 0 < τ)

variable (hδ : δ ≤ τ / 8)

variable (hinc : inc ≤ level * τ / 8)

variable (hη0 : 0 ≤ η)

variable (hη : η < 1)

variable (hητ : η ≤ τ / 8)

variable (hηlevel : η ≤ level * τ / 8)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hτinv : τ⁻¹ ≤ Real.exp T)

variable (hlog : L + T + 2 ≤ P)

variable (hrP : ((j + r : ℕ) : ℝ) ≤ P)

variable (hmoment : 2 ≤ moment)

variable (heven : Even moment)

variable (hPq : P ≤ (moment : ℝ))

variable (hqP : (moment : ℝ) ≤ P + 2)

variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)

variable (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))

variable (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)

variable (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))

variable (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)

variable (hε : 0 ≤ ε)

variable (hξ : 0 < ξ)

variable (hξ1 : ξ ≤ 1)

variable (hslack : ξ * (2 + ε) ≤ ε)

variable (hκ0 : 0 ≤ κ)

variable (hκhalf : κ ≤ 1 / 2)

variable (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)

variable (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r)

variable (hrb : j + r ≤ b)

variable (hshell : 0 < shell)

variable (hb : j + CyclicCrootSisask.spectralIterations shell ((j : ℝ) * (P + ((Fintype.card (Option J × σ) : ℝ) * modLog) + ((Fintype.card σ : ℝ) * modLog) + 2) + ε + L + 2 * T + 10) ≤ b)

variable (hlevel2 : level ≤ 2)

variable (hτ1 : τ ≤ 1)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

include p F sourceBase siteBase hchain hregK hw hrem hmass hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall herror hgram hsourceclose hresGram prime power hprime hpower hJ hlarge hε hξ hξ1 hslack hκ0 hκhalf hlow hrtail hrb hshell hb hlevel2 hτ1 hmodLog hmoduli

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineComparisonDegree (sourceDim siteDim : ℕ) (ε L T C shell modLog : ℝ) : ℕ :=
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
  affineFinalDegree j r shell
    ((j : ℝ) * (P + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) + ε + L + 2 * T + 10)

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F (2 : ℝ) (Real.exp (-T)) (affineRemovalDepth T) (affineComparisonTail ε L T) w rem cs)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ (Real.exp (-T)))

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include p F sourceBase siteBase hchain hw hrem hmass hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

end

end Erdos3

end

section

namespace Erdos3

noncomputable def affineComparisonRequiredOrder (b : ℕ) (ε L T C : ℝ) : ℕ :=
  max ((affineRemovalDepth T + affineComparisonTail ε L T) *
    (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
    (2 * b + affineRemovalDepth T)

noncomputable def affineComparisonLengthLog (b : ℕ) (ε L T C modLog dimLog : ℝ) : ℝ :=
  modLog * (affineComparisonRequiredOrder b ε L T C : ℕ) +
    affineComparisonAccuracyLog b (affineComparisonScale ε L T C) L T + dimLog + 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w : Ω → ℝ}

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include p F sourceBase siteBase hw hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

end

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

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceNonempty : Nonempty (IntegerResidueBox sourceLo
  (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA))
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
    (fun _ => (sourceM : ℤ)) sourceA,
  0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k) : ℝ))

include hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceNonempty w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

include hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

end

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GlobalAffineDegreeChoice
namespace OAI

section

namespace Erdos3

noncomputable def affineGlobalComparisonDegree (A sourceDim siteDim : ℕ)
    (ε L T C shell modLog countLog : ℝ) : ℕ :=
  A + max (affineComparisonDegree sourceDim siteDim ε L T C shell modLog)
    (CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

noncomputable def adaptiveAffineCountLog (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) : ℝ :=
  (A : ℝ) * (affineComparisonScale ε L T C +
    (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1)

noncomputable def adaptiveAffineShell (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℝ :=
  totalShell * Real.exp (-adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog)

noncomputable def adaptiveAffineCutoff (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℕ :=
  affineGlobalComparisonDegree A sourceDim siteDim ε L T C
    (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog 0

noncomputable def adaptiveAffineSideLog (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog dimLog : ℝ) : ℝ :=
  modLog * A + affineComparisonLengthLog
    (adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog)
    ε L T C modLog dimLog + 2

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptiveShellLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineCountLogBudget (P : ℝ) : ℝ :=
  P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 1)

noncomputable def affineShellLogBudget (P : ℝ) : ℝ := P + affineCountLogBudget P

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalBohrAlmostPeriodsRelative
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def characterBasis (Delta : Finset (AddChar (ZMod N) ℂ))
    (r : ℝ≥0) : Set N :=
  ofFrequencies (Delta.map AddChar.zmodAddEquiv.symm.toEmbedding) r r.coe_nonneg

@[simp] theorem rank_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).rank = Delta.card := by
  simp [characterBasis]

@[simp] theorem radius_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).radius = r := rfl

theorem norm_one_sub_le_of_mem_characterBasis
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Delta) :
    ‖1 - psi x‖ ≤ r := by
  have hmem : AddChar.zmodAddEquiv.symm psi ∈
      Delta.map AddChar.zmodAddEquiv.symm.toEmbedding :=
    Finset.mem_map.mpr ⟨psi, hpsi, rfl⟩
  have h := mem_iff.mp hx _ hmem
  simpa only [characterBasis, radius_ofFrequencies, character,
    AddEquiv.apply_symm_apply] using h

theorem norm_one_sub_le_of_mem_characterBasis_addSpan
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ}
    (hpsi : psi ∈ Delta.addSpan) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r := by
  obtain ⟨epsilon, hepsilon, hsum⟩ := Finset.mem_addSpan.mp hpsi
  rw [← hsum, AddChar.sum_apply]
  calc
    ‖1 - ∏ gamma ∈ Delta, (epsilon gamma • gamma) x‖ ≤
        ∑ gamma ∈ Delta, ‖1 - (epsilon gamma • gamma) x‖ :=
      norm_one_sub_prod_le_sum Delta _ (fun gamma _ => by simp)
    _ ≤ ∑ _gamma ∈ Delta, (r : ℝ) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      have h := norm_one_sub_le_of_mem_characterBasis hx hgamma
      rcases hepsilon gamma with hneg | hzero | hone
      · rw [hneg, neg_one_zsmul, AddChar.neg_apply, AddChar.map_neg_eq_conj]
        have heq : ‖1 - (starRingEnd ℂ) (gamma x)‖ = ‖1 - gamma x‖ := by
          simpa using (RCLike.norm_conj (1 - gamma x))
        rwa [heq]
      · simp [hzero]
      · simpa [hone] using h
    _ = (Delta.card : ℝ) * r := by simp

noncomputable def adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) : Set N :=
  (B.ndilate sigma).meet (characterBasis Delta r)

theorem rank_adjoinCharacters_le (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).rank ≤ B.rank + Delta.card := by
  simpa only [adjoinCharacters, rank_ndilate, rank_characterBasis] using
    rank_meet_le (B.ndilate sigma) (characterBasis Delta r)

@[simp] theorem radius_adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).radius = min ((sigma : ℝ) * B.radius) r := by
  simp only [adjoinCharacters, radius_meet, radius_ndilate, radius_characterBasis]

theorem adjoinCharacters_subset_ndilate (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).carrier ⊆ (B.ndilate sigma).carrier :=
  carrier_meet_subset_left _ _

theorem norm_one_sub_le_of_relative_cover
    (B : Set N) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s)
    {x : ZMod N} (hx : x ∈ adjoinCharacters B Delta sigma r)
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Q) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
      800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨z, hz, s, hs, rfl⟩ := hcover psi hpsi
  have hxB := adjoinCharacters_subset_ndilate B Delta sigma r hx
  have hxDelta : x ∈ characterBasis Delta r :=
    carrier_meet_subset_right (B.ndilate sigma) (characterBasis Delta r) hx
  have hzbound := norm_one_sub_le_of_mem_characterBasis_addSpan hxDelta hz
  have hsbound := Erdos3.norm_one_sub_le_of_mem_largeSpectrum_half hBreg hsigma hs hxB
  rw [AddChar.add_apply]
  exact (norm_one_sub_mul_of_norm_le_one (by simp)).trans (add_le_add hzbound hsbound)

theorem exists_regular_bohr_of_relative_cover
    (B : Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s) :
    ∃ R : Set N, R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
      min ((sigma : ℝ) * B.radius) r / 2 ≤ R.radius ∧
      R.radius ≤ min ((sigma : ℝ) * B.radius) r ∧
      R.carrier ⊆ (B.ndilate sigma).carrier ∧
      ∀ x ∈ R.carrier, ∀ psi ∈ Q,
        ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
          800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  let D := adjoinCharacters B Delta sigma r
  have hDpos : 0 < D.radius := by
    rw [radius_adjoinCharacters]
    exact lt_min (mul_pos (by exact_mod_cast hsigma0) hBpos) (by exact_mod_cast hr0)
  obtain ⟨R, hfreq, hRreg, hlo, hhi, hsub, _⟩ :=
    exists_controlled_regular_subdilate D hDpos 1 (by norm_num) le_rfl
  have hRD : R.carrier ⊆ D.carrier := by simpa only [ndilate_one] using hsub
  have hrank : R.rank = D.rank := congrArg Finset.card hfreq
  refine ⟨R, hRreg, hrank.le.trans (rank_adjoinCharacters_le B Delta sigma r), ?_, ?_,
    hRD.trans (adjoinCharacters_subset_ndilate B Delta sigma r), ?_⟩
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hlo
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hhi
  · intro x hx psi hpsi
    exact norm_one_sub_le_of_relative_cover B hBreg hsigma hcover (hRD hx) hpsi

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.RelativeChangSanders

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem localChangBaseScale_pos (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    0 < localChangBaseScale B X eta := by
  unfold localChangBaseScale
  positivity

theorem exists_regular_relative_spectrum_controller
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) (sigma r : ℝ≥0)
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    ∃ rho : ℝ≥0, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ), ∃ R : CyclicBohr.Set N,
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
        min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius / 2)) r / 2 ≤
          R.radius ∧
        R.radius ≤ min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius)) r ∧
        R.carrier ⊆ (C.ndilate sigma).carrier ∧
        ∀ x ∈ R.carrier, ∀ psi ∈ Chang.largeSpectrum X eta,
          ‖1 - psi x‖ ≤ localChangDimension B X eta * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨rho, C, Delta, hrho0, hrho1, hC, hCreg, hcard, hDelta, hcover⟩ :=
    exists_relativeLargeSpectrum_cover B hBpos hBreg X hX hXB eta heta
  have hCrank : C.rank = B.rank := by simp [hC]
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have ha : (0 : ℝ) < localChangBaseScale B X eta := by
    exact_mod_cast localChangBaseScale_pos B X eta
  have hCradius : C.radius = (rho : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius) := by
    simp only [hC, CyclicBohr.Set.radius_ndilate, NNReal.coe_mul, mul_assoc]
  have hCpos : 0 < C.radius := by
    rw [hCradius]
    exact mul_pos (by linarith) (mul_pos ha hBpos)
  have hClo : (localChangBaseScale B X eta : ℝ) * B.radius / 2 ≤ C.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hChi : C.radius ≤ (localChangBaseScale B X eta : ℝ) * B.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hsigmaC : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0) := by
    simpa only [hCrank] using hsigma
  obtain ⟨R, hRreg, hRrank, hRlo, hRhi, hRsub, hRphase⟩ :=
    CyclicBohr.Set.exists_regular_bohr_of_relative_cover
      C hCpos hCreg hsigma0 hr0 hsigmaC hcover
  refine ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta, hRreg,
    ?_, ?_, ?_, hRsub, ?_⟩
  · simpa only [hCrank] using hRrank
  · apply le_trans _ hRlo
    exact div_le_div_of_nonneg_right
      (min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hClo sigma.coe_nonneg))
      (by norm_num)
  · apply hRhi.trans
    exact min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hChi sigma.coe_nonneg)
  · intro x hx psi hpsi
    have hphase := hRphase x hx psi hpsi
    rw [hCrank] at hphase
    exact hphase.trans (add_le_add
      (mul_le_mul_of_nonneg_right hcard r.coe_nonneg) le_rfl)

end Erdos3.RelativeChangSanders

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem finiteFourierCoeff_finiteIndicator (A : Finset G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteIndicator A) psi =
      (∑ a ∈ A, star (psi a)) / (Fintype.card G : ℂ) := by
  simp [finiteFourierCoeff, Fintype.expect_eq_sum_div_card, finiteIndicator, ite_mul]

theorem finiteFourierCoeff_averagingKernel {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) :
    finiteFourierCoeff (averagingKernel A) psi = setFourierMultiplier A psi := by
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (A.card : ℂ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have heq : finiteFourierCoeff (averagingKernel A) psi =
      ((Fintype.card G : ℂ) / A.card) * finiteFourierCoeff (finiteIndicator A) psi := by
    unfold finiteFourierCoeff averagingKernel
    simp only [mul_assoc, Finset.mul_expect]
  rw [heq, finiteFourierCoeff_finiteIndicator, setFourierMultiplier,
    Finset.expect_eq_sum_div_card]
  field_simp

theorem sum_sq_setFourierMultiplier {A : Finset G} (hA : A.Nonempty) :
    (∑ psi : AddChar G ℂ, ‖setFourierMultiplier A psi‖ ^ 2) =
      (Fintype.card G : ℝ) / A.card := by
  simp_rw [← finiteFourierCoeff_averagingKernel hA]
  rw [finiteFourier_parseval, mean_averagingKernel_norm_sq hA]

theorem fourierL1_triple_average_sq_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ^ 2 ≤
      (M.card : ℝ) / L.card := by
  let s : ℝ := ∑ psi : AddChar G ℂ,
    ‖setFourierMultiplier L psi‖ * ‖finiteFourierCoeff (finiteIndicator M) psi‖
  have hbound : fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤ s := by
    unfold fourierL1
    apply Finset.sum_le_sum
    intro psi _
    rw [finiteFourierCoeff_finiteSetAverage, finiteFourierCoeff_finiteSetAverage]
    simp only [norm_mul]
    have hAone := norm_setFourierMultiplier_le_one hA psi
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hAone) (norm_nonneg _)
  have hnonneg : 0 ≤ fourierL1
      (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCS : s ^ 2 ≤
      (∑ psi : AddChar G ℂ, ‖setFourierMultiplier L psi‖ ^ 2) *
        ∑ psi : AddChar G ℂ, ‖finiteFourierCoeff (finiteIndicator M) psi‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [sum_sq_setFourierMultiplier hL, finiteFourier_parseval, mean_indicator_norm_sq] at hCS
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcancel : ((Fintype.card G : ℝ) / L.card) * (M.card / (Fintype.card G : ℝ)) =
      (M.card : ℝ) / L.card := by field_simp
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans (hCS.trans_eq hcancel)

theorem fourierL1_triple_average_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤
      Real.sqrt ((M.card : ℝ) / L.card) :=
  Real.le_sqrt_of_sq_le (fourierL1_triple_average_sq_le hA hL M)

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem finiteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    finiteSetAverage A (fun x => (u x : ℂ)) = fun x => (setAverageTranslate A u x : ℂ) := by
  funext x
  rw [finiteSetAverage, Finset.expect_eq_sum_div_card, setAverageTranslate]
  push_cast
  rfl

omit [NeZero N] in
theorem iteratedFiniteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) (q : ℕ) :
    iteratedFiniteSetAverage A (fun x => (u x : ℂ)) q =
      fun x => (iteratedSetAverage A u q x : ℂ) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [iteratedFiniteSetAverage, ih, finiteSetAverage_ofReal]
      rfl

omit [NeZero N] in
theorem finiteIndicator_eq_ofReal_realSetIndicator (M : Finset (ZMod N)) :
    finiteIndicator M = fun x => (realSetIndicator M x : ℂ) := by
  funext x
  by_cases hx : x ∈ M <;> simp [finiteIndicator, realSetIndicator, hx]

omit [NeZero N] in
theorem triple_average_ofReal (A L M : Finset (ZMod N)) :
    finiteSetAverage L (finiteSetAverage A (finiteIndicator M)) =
      fun x => (setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x : ℂ) := by
  rw [finiteIndicator_eq_ofReal_realSetIndicator, finiteSetAverage_ofReal, finiteSetAverage_ofReal]

theorem triple_translate_le_of_iterated_approx
    {A L X : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (hX : X.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) {delta eta theta : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : ZMod N) :
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    (∀ y, |iteratedSetAverage X u q y - u y| ≤ delta) →
    (∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) →
    |u (x - t) - u x| ≤
      2 * delta + (theta + 2 * eta ^ q) * Real.sqrt ((M.card : ℝ) / L.card) := by
  intro u happrox hphase
  let f := finiteSetAverage L (finiteSetAverage A (finiteIndicator M))
  have hf : f = fun y => (u y : ℂ) := triple_average_ofReal A L M
  have happrox' : ∀ y, ‖iteratedFiniteSetAverage X f q y - f y‖ ≤ delta := by
    intro y
    rw [hf, iteratedFiniteSetAverage_ofReal]
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using happrox y
  have h := translate_le_of_iteratedFiniteSetAverage_approx hX q f heta htheta t x happrox' hphase
  have hreal : |u (x - t) - u x| ≤ 2 * delta + (theta + 2 * eta ^ q) * fourierL1 f := by
    simpa only [hf, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  exact hreal.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (fourierL1_triple_average_le hA hL M)
      (add_nonneg htheta (mul_nonneg (by norm_num) (pow_nonneg heta q)))))

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

open scoped BigOperators NNReal Pointwise

variable {N : ℕ} [NeZero N]

namespace RelativeChangSanders

theorem localChangBaseScale_le_one
    (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    localChangBaseScale B X eta ≤ 1 := by
  have hd : (1 : ℝ≥0) ≤ (2 * max B.rank 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * max B.rank 1 by omega)
  have hk : (1 : ℝ≥0) ≤ (2 * localChangCap B X eta + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * localChangCap B X eta + 1 by omega)
  unfold localChangBaseScale
  rw [← one_div, div_le_one (by positivity)]
  nlinarith

end RelativeChangSanders

namespace CyclicCrootSisask

open RelativeChangSanders

end CyclicCrootSisask
end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators NNReal Pointwise
open RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem exists_local_bohr_triple_almostPeriods_relative
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A S L : Finset (ZMod N)} (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (hSB : S ⊆ B.carrier) (M : Finset (ZMod N))
    (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta)
    (sigma r : ℝ≥0) (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T : Finset (ZMod N)) (R : CyclicBohr.Set N),
      T.Nonempty ∧ T ⊆ S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + localChangDimension B T (1 / 2) ∧
      min ((sigma : ℝ) * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2 ≤
        R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧
      ∀ t ∈ R.carrier, ∀ x,
        |u (x + t) - u x| ≤ 2 * delta +
          (localChangDimension B T (1 / 2) * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma + 2 * (1 / 2 : ℝ) ^ q) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  intro m k u
  obtain ⟨T, X, z, hTS, hz, hXeq, hzero, hXS, hcount, happrox⟩ :=
    exists_local_boosted_triple_almostPeriods hA hS hL M q hq hdelta
  have hX : X.Nonempty := ⟨0, hzero⟩
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta,
      hRreg, hRrank, hRwidth, hRupper, hRsub, hphase⟩ :=
    exists_regular_relative_spectrum_controller B hBpos hBreg T hT (hTS.trans hSB)
      (1 / 2) (by norm_num) sigma r hsigma0 hr0 hsigma
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have ha1 := localChangBaseScale_le_one B T (1 / 2)
  have hscale : sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 := by
    calc
      sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 * (1 * 1) :=
        mul_le_mul hsigma1 (mul_le_mul hrho1 ha1 (by positivity) (by norm_num))
          (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hCB : (C.ndilate sigma).carrier ⊆ B.carrier := by
    rw [hC, CyclicBohr.Set.ndilate_ndilate]
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := B) hscale
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) :=
    (Nat.cast_nonneg Delta.card).trans hcard
  refine ⟨T, R, hT, hTS, hcount, hRreg, ?_, hRwidth,
    hRupper.trans (min_le_right _ _), hRsub.trans hCB, ?_⟩
  · have hRrankR : (R.rank : ℝ) ≤ B.rank + Delta.card := by exact_mod_cast hRrank
    exact hRrankR.trans (add_le_add le_rfl hcard)
  · intro t ht x
    have htheta : 0 ≤ localChangDimension B T (1 / 2) * (r : ℝ) +
        800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by positivity
    have h := triple_translate_le_of_iterated_approx hA hL hX M q
      (eta := (1 / 2 : ℝ)) (by norm_num) htheta t (x + t) happrox
      (fun psi hpsi => hphase t ht psi (by
        rw [hXeq] at hpsi
        exact (Chang.mem_largeSpectrum_map_subRight_iff T z (1 / 2) psi).1 hpsi))
    simpa only [add_sub_cancel_right, abs_sub_comm] using h

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DifferenceEventProbability
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem setAverageTranslate_eq_expect (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A f x = 𝔼 a ∈ A, f (x - a) := by
  rw [setAverageTranslate, Finset.expect_eq_sum_div_card]

noncomputable def differenceEventProbability
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) : ℝ :=
  𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)

theorem differenceEventProbability_eq_triple
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) :
    differenceEventProbability A₁ A₂ K t =
      setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) t := by
  rw [differenceEventProbability, setAverageTranslate_eq_expect, Finset.expect_neg_index]
  apply Finset.expect_congr rfl
  intro a _
  rw [setAverageTranslate_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  congr 1
  abel

noncomputable def smoothedDifferenceEventProbability
    (A₁ A₂ K R : Finset (ZMod N)) : ℝ :=
  𝔼 t ∈ R, differenceEventProbability A₁ A₂ K t

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DifferenceEventSupport
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem differenceEventProbability_self_zero (A : Finset (ZMod N)) (hA : A.Nonempty) :
    differenceEventProbability A A (A - A) 0 = 1 := by
  unfold differenceEventProbability
  have hone : ∀ a ∈ A, ∀ b ∈ A, realSetIndicator (A - A) (a - b + 0) = 1 := by
    intro a ha b hb
    simp only [add_zero, realSetIndicator, if_pos (Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩)]
  calc
    (𝔼 a ∈ A, 𝔼 b ∈ A, realSetIndicator (A - A) (a - b + 0)) =
        𝔼 _a ∈ A, 𝔼 _b ∈ A, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact hone a ha b hb
    _ = 1 := by rw [Finset.expect_const hA, Finset.expect_const hA]

theorem exists_difference_event_of_probability_pos
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A₁ A₂ K t) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, a - b + t ∈ K := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : differenceEventProbability A₁ A₂ K t = 0 := by
    unfold differenceEventProbability
    calc
      (𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)) =
          𝔼 _a ∈ A₁, 𝔼 _b ∈ A₂, (0 : ℝ) := by
        apply Finset.expect_congr rfl
        intro a ha
        apply Finset.expect_congr rfl
        intro b hb
        simp only [realSetIndicator, if_neg (hnone a ha b hb)]
      _ = 0 := by simp
  linarith

theorem mem_fourfold_difference_of_probability_pos (A : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A A (A - A) t) : t ∈ 2 • A - 2 • A := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_difference_event_of_probability_pos A A (A - A) t h
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_sub.mp hab
  have htwo : 2 • A = A + A := two_nsmul A
  rw [htwo]
  apply Finset.mem_sub.mpr
  refine ⟨c + b, Finset.mem_add.mpr ⟨c, hc, b, hb, rfl⟩,
    d + a, Finset.mem_add.mpr ⟨d, hd, a, ha, rfl⟩, ?_⟩
  calc
    (c + b) - (d + a) = (c - d) - (a - b) := by abel
    _ = (a - b + t) - (a - b) := by rw [hcd]
    _ = t := by abel

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def samplingCubicFactor (epsilon : ℝ) : ℝ :=
  2 * (256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2) * spectralIterationFactor epsilon ^ 2 + 1

theorem samplingCubicFactor_pos (epsilon : ℝ) : 0 < samplingCubicFactor epsilon := by
  unfold samplingCubicFactor
  positivity

theorem local_sample_size_le_cubic {N : ℕ} (M L : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p)) :
    (crootSisaskSampleSize (convolutionMomentOrder M L)
      (((epsilon / 8) / spectralIterations epsilon p) / Real.exp 1) : ℝ) ≤
        samplingCubicFactor epsilon * (p + 1) ^ 3 := by
  let q := spectralIterations epsilon p
  let H := 256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2
  have hH : 0 ≤ H := by positivity
  have hq := spectralIterations_le hepsilon hepsilon1 hp
  have hraw := localBoostedSampleSize_le M L (p := 2 * p) (by positivity) hratio
    (by positivity : 0 < epsilon / 8) q (spectralIterations_pos epsilon p)
  have hp1 : 1 ≤ p + 1 := by linarith
  have hp3 : 1 ≤ (p + 1) ^ 3 := one_le_pow₀ hp1
  calc
    _ ≤ H * (2 * p + 2) * (q : ℝ) ^ 2 + 1 := hraw
    _ ≤ H * (2 * p + 2) * (spectralIterationFactor epsilon * (p + 1)) ^ 2 + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg q) hq 2) (mul_nonneg hH (by positivity))) le_rfl
    _ = (2 * H * spectralIterationFactor epsilon ^ 2) * (p + 1) ^ 3 + 1 := by ring
    _ ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 := by
      unfold samplingCubicFactor
      dsimp [H]
      nlinarith

noncomputable def rankQuarticFactor (epsilon : ℝ) : ℝ :=
  8 * (1 + Real.log 4 + samplingCubicFactor epsilon)

theorem rankQuarticFactor_pos (epsilon : ℝ) : 0 < rankQuarticFactor epsilon := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC := samplingCubicFactor_pos epsilon
  unfold rankQuarticFactor
  positivity

end Erdos3.CyclicCrootSisask

namespace Erdos3.RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem local_dimension_le_quartic_of_cubic_sampling
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {p C : ℝ} (hp : 0 ≤ p) (_hC : 0 ≤ C) (k : ℕ)
    (hk : (k : ℝ) ≤ C * (p + 1) ^ 3)
    (hcount : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + C) * (p + 1) ^ 4 := by
  have hdim := localChangDimension_half_le_of_card B hT
    (by positivity : 0 < 2 * Real.exp p) k hcount
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogK : Real.log (2 * Real.exp p) ≤ p + 1 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero p), Real.log_exp]
    linarith
  have hprod : (k : ℝ) * Real.log (2 * Real.exp p) ≤ C * (p + 1) ^ 4 := by
    calc
      _ ≤ (k : ℝ) * (p + 1) := mul_le_mul_of_nonneg_left hlogK (Nat.cast_nonneg _)
      _ ≤ (C * (p + 1) ^ 3) * (p + 1) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = C * (p + 1) ^ 4 := by ring
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hconst : 1 + Real.log 4 ≤ (1 + Real.log 4) * (p + 1) ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp4 (by positivity : 0 ≤ 1 + Real.log 4)
  nlinarith

end Erdos3.RelativeChangSanders

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def goodDifferenceSet (S T : Finset G) (f : G → ℝ) (threshold : ℝ) : Finset G :=
  (S - T).filter (fun x => threshold ≤ f x)

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

theorem sqrt_le_exp_of_le_exp_two_mul {beta p : ℝ} (hbeta : beta ≤ Real.exp (2 * p)) :
    Real.sqrt beta ≤ Real.exp p := by
  apply (Real.sqrt_le_left (Real.exp_pos p).le).mpr
  simpa only [two_mul, Real.exp_add, pow_two] using hbeta

theorem old_frequency_scale_le_regularity {epsilon p d : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) (hd : 0 < d) :
    epsilon * Real.exp (-p) / (6400 * d) ≤ 1 / (200 * d) := by
  have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : epsilon * Real.exp (-p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left he hepsilon).trans (by simpa using hepsilon1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem chosen_scales_error_le
    {epsilon p d D dim beta : ℝ} (hepsilon : 0 < epsilon) (hd : 0 < d)
    (hD : 0 ≤ D) (hdim0 : 0 ≤ dim) (hdim : dim ≤ D)
    (hbeta : beta ≤ Real.exp (2 * p)) :
    2 * (epsilon / 8) +
      (dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
        800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
        2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p) * Real.sqrt beta ≤ epsilon := by
  have hcancel : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add]
    simp
  have hDpos : 0 < D + 1 := by linarith
  have hnew : dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p ≤ epsilon / 8 := by
    calc
      _ ≤ (D + 1) * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p := by
        gcongr
        linarith
      _ = epsilon / 8 := by
        field_simp
        nlinarith [hcancel]
  have hold : 800 * d * (epsilon * Real.exp (-p) / (6400 * d)) * Real.exp p = epsilon / 8 := by
    field_simp
    nlinarith [hcancel]
  have htail : 2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 8 := by
    have h := half_pow_spectralIterations_mul_exp_le (p := p) hepsilon
    linarith
  have hsqrt := sqrt_le_exp_of_le_exp_two_mul hbeta
  have hfactor : 0 ≤ dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
      800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
      2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p := by positivity
  have hbound := mul_le_mul_of_nonneg_left hsqrt hfactor
  nlinarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_quartic_local_almostPeriods
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A L : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p))
    (hdoubling : ((A + B.carrier).card : ℝ) ≤ (2 * Real.exp p) * A.card) :
    let D := rankQuarticFactor epsilon * (p + 1) ^ 4
    let d := max B.rank 1
    let a : ℝ≥0 := (100 * ((2 * d : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
    let sigma := epsilon * Real.exp (-p) / (6400 * (d : ℝ))
    let r := epsilon * Real.exp (-p) / (8 * (D + 1))
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + D ∧
      min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤ R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧ ∀ t ∈ R.carrier, ∀ x, |u (x + t) - u x| ≤ epsilon := by
  intro D d a sigma r u
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (rankQuarticFactor_pos epsilon).le (pow_nonneg (by positivity) _)
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  let sigmaN : ℝ≥0 := ⟨sigma, hsigma.le⟩
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hsigreg : sigmaN ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by
    have h := old_frequency_scale_le_regularity hepsilon.le hepsilon1 hp hd
    change sigma ≤ ((1 : ℝ) / (100 * ((2 * max B.rank 1 : ℕ) : ℝ)))
    dsimp [sigma, d] at h ⊢
    push_cast at h ⊢
    convert h using 1
    ring
  let q := spectralIterations epsilon p
  let k := crootSisaskSampleSize (convolutionMomentOrder M L) (((epsilon / 8) / q) / Real.exp 1)
  obtain ⟨T, R, hT, hTB, hcount, hRreg, hRrank, hRwidth, hRupper, hRB, hshift⟩ :=
    exists_local_bohr_triple_almostPeriods_relative B hBpos hBreg hA B.carrier_nonempty hL
      (fun _ h => h) M q (spectralIterations_pos epsilon p)
      (by positivity : 0 < epsilon / 8) sigmaN rN hsigma hr hsigreg
  have hcount' : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card :=
    samplingDensity_le_of_smallDoubling hA B.carrier_nonempty k (by positivity) hdoubling hcount
  have hk : (k : ℝ) ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 :=
    local_sample_size_le_cubic M L hepsilon hepsilon1 hp hratio
  have hdim : localChangDimension B T (1 / 2) ≤ D :=
    local_dimension_le_quartic_of_cubic_sampling B hT hp (samplingCubicFactor_pos epsilon).le k hk hcount'
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) := by
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hcard : (T.card : ℝ) ≤ B.carrier.card := by exact_mod_cast Finset.card_le_card hTB
    have hratio1 : 1 ≤ 2 * (B.carrier.card : ℝ) / T.card := by
      rw [le_div_iff₀ hTpos]
      linarith
    have hlog := Real.log_nonneg hratio1
    unfold localChangDimension
    positivity
  have ha : a ≤ localChangBaseScale B T (1 / 2) :=
    localChangBaseScale_ge_of_dimension_le B T (1 / 2) D hdim
  refine ⟨R, hRreg, hRrank.trans (add_le_add le_rfl hdim), ?_, hRupper, hRB, ?_⟩
  · apply le_trans _ hRwidth
    change min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤
      min (sigma * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2
    gcongr
  · intro t ht x
    apply (hshift t ht x).trans
    exact chosen_scales_error_le hepsilon hd hD hdim0 hdim hratio

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

noncomputable def almostPeriodicityWidthConstant (epsilon : ℝ) : ℝ :=
  10240000000 * (rankQuarticFactor epsilon + 1) / epsilon + 8

theorem almostPeriodicityWidthConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  unfold almostPeriodicityWidthConstant
  positivity

theorem rankQuarticFactor_le_widthConstant {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    rankQuarticFactor epsilon ≤ almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  have hprod := mul_le_mul_of_nonneg_left hepsilon1 hC.le
  have hquot : rankQuarticFactor epsilon ≤
      10240000000 * (rankQuarticFactor epsilon + 1) / epsilon := by
    rw [le_div_iff₀ hepsilon]
    nlinarith
  unfold almostPeriodicityWidthConstant
  linarith

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

noncomputable def quarticBogolyubovConstant : ℝ :=
  3 * almostPeriodicityWidthConstant (1 / 2)

theorem quarticBogolyubovConstant_pos : 0 < quarticBogolyubovConstant := by
  exact mul_pos (by norm_num) (almostPeriodicityWidthConstant_pos (by norm_num))

theorem exists_quartic_bogolyubov {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius ∧
      R.carrier ⊆ 2 • A - 2 • A := by
  have hApos : (0 : ℝ) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hdensity
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hNle : (N : ℝ) ≤ Real.exp p * A.card := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hratio : ((A - A).card : ℝ) / (-A).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hApos]
    calc
      ((A - A).card : ℝ) ≤ N := by
        exact_mod_cast (show (A - A).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ (A - A))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ Real.exp (2 * p) * A.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hApos.le
  have hdoubling : ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤
      (2 * Real.exp p) * A.card := by
    calc
      ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ
            (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ (2 * Real.exp p) * A.card := by nlinarith [Real.exp_pos p]
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, _, hshift⟩ :=
    exists_quartic_local_almostPeriods CyclicBohr.Set.whole (by norm_num)
      CyclicBohr.Set.isRankRegular_whole hA hA.neg (A - A)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hp hratio hdoubling
  let C₀ := rankQuarticFactor (1 / 2)
  let D := C₀ * (p + 1) ^ 4
  let a : ℝ≥0 := (100 * 2 * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have hC₀ : 0 < C₀ := rankQuarticFactor_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  simp only [CyclicBohr.Set.rank_whole, CyclicBohr.Set.radius_whole, max_self,
    Nat.cast_one, Nat.cast_ofNat, mul_one] at hRrank hRwidth hRupper
  change (R.rank : ℝ) ≤ 1 + D at hRrank
  change min (((1 / 2 : ℝ) * Real.exp (-p) / 6400) * ((a : ℝ) / 2))
      (((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1))) / 2 ≤ R.radius at hRwidth
  change R.radius ≤ ((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1)) at hRupper
  have ha : 1 / (1000 * (1 : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa only [a, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_ofNat, mul_one] using BohrWidthBudget.selector_scale_lower_bound
        (d := 1) (by norm_num) hD
  have hRrat : ((1 / 2 : ℝ) * Real.exp (-p)) /
      (10240000000 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := (1 / 2 : ℝ) * Real.exp (-p)) (d := 1) (D := D) (w := 1) (v := 1)
      (by positivity) (by norm_num) hD (by norm_num) (by norm_num) (by norm_num) ha
    apply le_trans _ hRwidth
    simpa only [one_pow, mul_one] using h
  have hC : 0 < almostPeriodicityWidthConstant (1 / 2) :=
    almostPeriodicityWidthConstant_pos (by norm_num)
  have hRexp : Real.exp (-(almostPeriodicityWidthConstant (1 / 2) *
      (1 + p + Real.log 3))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential
      (epsilon := 1 / 2) (C := C₀) (p := p) (d := 1) (w := 1)
      (by norm_num) hC₀.le hp (by norm_num) (by norm_num)
    apply le_trans _ hRrat
    simpa only [almostPeriodicityWidthConstant, D, C₀, one_pow, mul_one, one_mul,
      show (2 : ℝ) + 1 = 3 by norm_num] using h
  have hlog : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hbudget : almostPeriodicityWidthConstant (1 / 2) * (1 + p + Real.log 3) ≤
      quarticBogolyubovConstant * (p + 1) := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    unfold quarticBogolyubovConstant
    nlinarith [mul_nonneg hC.le hp]
  have hwidth : Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius :=
    (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hRexp
  refine ⟨R, hRreg, (Real.exp_pos _).trans_le hwidth, ?_, ?_, hwidth, ?_⟩
  · apply hRupper.trans
    apply (div_le_one (by positivity)).mpr
    have h := Real.exp_le_one_iff.mpr (by linarith : -p ≤ 0)
    nlinarith
  · have hC₀C := rankQuarticFactor_le_widthConstant
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hCC : C₀ ≤ quarticBogolyubovConstant := by
      dsimp [C₀, quarticBogolyubovConstant]
      linarith
    have hh : C₀ * (p + 1) ^ 4 ≤ quarticBogolyubovConstant * (p + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right hCC (by positivity)
    exact hRrank.trans (add_le_add le_rfl hh)
  · intro t ht
    have hprob : |differenceEventProbability A A (A - A) t - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [← differenceEventProbability_eq_triple, zero_add,
        differenceEventProbability_self_zero A hA] using hshift t ht 0
    apply mem_fourfold_difference_of_probability_pos A t
    have h := (abs_le.mp hprob).1
    linarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

noncomputable def quarticBogolyubovProgressionConstant : ℝ :=
  11 * (quarticBogolyubovConstant + 2) ^ 2

theorem quarticBogolyubovProgressionConstant_pos :
    0 < quarticBogolyubovProgressionConstant := by
  have h := quarticBogolyubovConstant_pos
  unfold quarticBogolyubovProgressionConstant
  positivity

theorem exists_quartic_bogolyubov_progression {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ Q : BohrProgression.CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Q.Proper ∧ Q.carrier ⊆ 2 • A - 2 • A ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨B, _hreg, hB, hB1, hrank, hwidth, hsub⟩ := exists_quartic_bogolyubov A hp hdensity
  obtain ⟨Q, hr, hQ, hQB, hcard⟩ := BohrProgression.exists_proper_progression_of_quartic_bounds
    B quarticBogolyubovConstant_pos.le hp hB hB1 hrank hwidth
  exact ⟨Q, hr, hQ, hQB.trans hsub, hcard⟩

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def admissibleBohrShape (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (C : CyclicBohr.Set N) : Prop :=
  C.IsRankRegular ∧ C.carrier ⊆ (B.ndilate scale).carrier ∧
    C.rank ≤ B.rank + rankExtra ∧ minimumWidth ≤ C.radius

def admissibleBohrCarriers (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (A : Finset (ZMod N)) : Prop :=
  ∃ C : CyclicBohr.Set N, admissibleBohrShape B scale rankExtra minimumWidth C ∧ A = C.carrier

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

noncomputable def unbalancedRankExtra (c p H : ℝ) : ℕ :=
  ⌈almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4⌉₊

noncomputable def unbalancedMinimumWidth (S : CyclicBohr.Set N) (M c p H : ℝ) (q : ℕ) : ℝ :=
  (localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ) *
    (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
    S.radius / 8 * Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank))))

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

noncomputable def unbalancedErrorBudget (c : ℝ) : ℝ := -Real.log (c / 32)

noncomputable def unbalancedWidthLoss (rank : ℕ) (c p H : ℝ) : ℝ :=
  ((rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c + 1600) +
    (((rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c + 1600) +
    8 + almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + rank))

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinatedMatchingScale
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def coordinatedMatchingScale (rank : ℕ) (M delta c : ℝ)
    (kappa : ℝ≥0) : ℝ≥0 :=
  min (kappa / 2) (min (controlledLocalMomentScale rank M delta)
    (localizedAverageScale rank (M ^ 2) (c / 32) / 2))

noncomputable def coordinatedMatchingScaleLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + rank + 2 * P + localMomentErrorBudget delta + unbalancedErrorBudget c + 1604

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoordinatedBohrMatching
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def matchingWidthLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + coordinatedMatchingScaleLoss rank P K delta c + 12

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementMatchingGeometry
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

noncomputable def unbalancedReturnWidthLoss (rank : ℕ) (c p H A E : ℝ) : ℝ :=
  (rank : ℝ) + A + E + 1602 + unbalancedWidthLoss rank c p H

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def refinementMatchingWidthLoss (rank : ℕ) (p H Q E J T delta : ℝ) : ℝ :=
  matchingWidthLoss rank p (outerMatchingScaleLoss rank Q E T) delta (localMomentGain delta) +
    unbalancedReturnWidthLoss rank (localMomentGain delta) p H Q J

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedRefinementBudget
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def refinementScaleLoss (rank : ℕ) (p : ℝ) : ℝ :=
  (rank : ℝ) + p / 8 + 3 * p + 1600

noncomputable def refinementMatchingLoss (rank : ℕ) (p epsilon : ℝ) : ℝ :=
  5 * rank + (25 / 2 : ℝ) * p + localMomentErrorBudget (flatComparisonDelta epsilon) +
    unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) + 8020

noncomputable def refinementRoundLoss (rank : ℕ) (p H epsilon : ℝ) : ℝ :=
  refinementMatchingLoss rank p epsilon +
    unbalancedReturnWidthLoss rank (localMomentGain (flatComparisonDelta epsilon)) p H (p / 8) (2 * p)

noncomputable def refinementComparisonBudget (rank : ℕ) (p R epsilon : ℝ) : ℝ :=
  max (2 * rank + p + ((1 / 4 : ℝ) + 2) * p +
      (R + refinementMatchingLoss rank p epsilon) + 1612)
    (((1 / 4 : ℝ) + 2) * p + 2 +
      rank * (R + refinementMatchingLoss rank p epsilon + 10))

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

noncomputable def weightedReplacementTolerance (F E epsilon : ℝ) : ℝ :=
  replacementAccuracy (F ^ 2 * (1 + E)) (epsilon ^ 2)

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalReplacementInputLog (m n : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) * (P + 3) + n * P + 2 * (n + 1) + P + 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalMeanAccuracyLog {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  -Real.log (physicalPairMeanAccuracy n k Q C κ A degree epsilon)

noncomputable def physicalReplacementScaleThreshold {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) (degree : ℕ) (modLog dimLog : ℝ) : ℝ :=
  replacementScaleThreshold C (physicalPairPointAccuracy n k Q C κ A epsilon)
    (physicalPairGridAccuracy n k C κ A epsilon)
    (Real.exp (modLog * (2 * degree : ℕ) + physicalMeanAccuracyLog n k Q C κ A degree epsilon + dimLog + 1))
    Q 2 (8 * probabilityProfileLipschitz)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def physicalReplacementThresholdLog (n d degree : ℕ) (P : ℝ) : ℝ :=
  2 * physicalPairCoefficientLog n d P + 2 * physicalPairMeanLog n degree P +
    (2 * degree + 2) * P + 20

end Erdos3

end

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

noncomputable def replacementCutoffInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  6 * physicalReplacementInputLog m n P + P + 3 * d + 10

noncomputable def replacementCommonInputLog (m n d : ℕ) (P : ℝ) : ℝ :=
  4 * replacementCutoffInputLog m n d P + 2 * P + 10

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

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCommonStrideCardRatio
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem IsDenseCommonStrideBox.card_ratio {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    ((integerBox N).card : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  obtain ⟨c, step, H, hstep, hH, _, hdense, rfl⟩ := h
  rw [commonStrideBox_card c hstep H, card_integerBox, Nat.cast_prod, Nat.cast_prod]
  apply (div_le_iff₀ (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hH i)))).mpr
  have haxis (i) : (N i : ℝ) ≤ Real.exp p * H i := by
    calc
      _ = Real.exp p * (Real.exp (-p) * (N i : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdense i) (Real.exp_nonneg _)
  calc
    _ ≤ ∏ i, (Real.exp p * (H i : ℝ)) :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => haxis i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      rw [mul_comm (Fintype.card I : ℝ) p]

theorem dense_commonStride_slice_card_ratio {I T : Type*}
    [Fintype I] [DecidableEq I] [Fintype T]
    (e : T → I → ℤ) (he : Function.Injective e) {N : I → ℕ}
    (himage : Finset.univ.image e = integerBox N)
    {p : ℝ} {A : Finset T} (hA : IsDenseCommonStrideBox N p (A.image e)) :
    (Fintype.card T : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  have hcard : (integerBox N).card = Fintype.card T := by
    rw [← himage, Finset.card_image_of_injective _ he, Finset.card_univ]
  simpa only [hcard, Finset.card_image_of_injective _ he] using hA.card_ratio

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseSubboxCost
namespace OAI

section

namespace Erdos3

theorem IsDenseCommonStrideBox.of_large_subbox {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A B : Finset (I → ℤ)} (hB : IsDenseCommonStrideBox N p B)
    (hshape : ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
      0 < m ∧ (∀ i, 0 < H i) ∧ A = commonStrideBox c m H)
    (hsub : A ⊆ B) (hloss : 2 * (1 - (A.card : ℝ) / B.card) ≤ 1) :
    IsDenseCommonStrideBox N (p + 1) A := by
  obtain ⟨c, m, H, hm, hH, hBsub, hBdense, rfl⟩ := hB
  obtain ⟨c', m', H', hm', hH', rfl⟩ := hshape
  have haxis (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm] using hH i)
  have haxis' (i : I) : (integerProgressionSupport (c' i) m' (H' i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm'] using hH' i)
  refine ⟨c', m', H', hm', hH', ?_, ?_, rfl⟩
  · intro i
    exact (piFinset_axis_subset _ _ haxis' hsub i).trans (hBsub i)
  · intro i
    have hi := piFinset_card_ratio_le_axis _ _ haxis' haxis hsub i
    simp only [card_integerProgressionSupport _ _ _ hm, card_integerProgressionSupport _ _ _ hm'] at hi
    have hhalf : (1 / 2 : ℝ) ≤ (H' i : ℝ) / H i := by
      change ((commonStrideBox c' m' H').card : ℝ) / (commonStrideBox c m H).card ≤ _ at hi
      linarith
    have hlen : (H i : ℝ) ≤ 2 * H' i := by
      have ht := (le_div_iff₀ (by exact_mod_cast hH i : (0 : ℝ) < H i)).mp hhalf
      linarith
    have he : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
    have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (N i))
    nlinarith [hBdense i]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

noncomputable def sourceFullCommonTolerance
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)

noncomputable def sourceFullRankGap
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2

def adaptiveSelectedCoarseLayerBound
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      fixedUpperLayerComplexityFactor
          j.1 (P.budget j) (P.index j) *
        initialBound j.castSucc)

structure SourceFullCoarseTargetSchedule
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  scale : schedule.Landing → Fin (r + 1) → ℕ
  scaleFloor_le_deepest :
    ∀ P, scaleFloor ≤ scale P (Fin.last r)
  scale_hierarchy :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  selected_tolerance_le_common :
    ∀ P (j : Fin r),
      P.tolerance j (P.index j) ≤
        sourceFullCommonTolerance F (scale P)
  reciprocal_gap_le :
    ∀ P (j : Fin r),
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        sourceFullRankGap F (scale P) j
  selected_coarse_bound :
    ∀ P q,
      adaptiveSelectedCoarseLayerBound initialBound P q ≤
        scale P q

namespace SourceFullCoarseTargetSchedule

theorem scale_antitone
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (S.scale P j.succ)).trans
        (S.scale_hierarchy P j))

theorem scaleFloor_le
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing)
    (q : Fin (r + 1)) :
    scaleFloor ≤ S.scale P q := by
  exact (S.scaleFloor_le_deepest P).trans
    (S.scale_antitone P (Fin.le_last q))

structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length
  scale : Fin (r + 1) → ℕ
  scaleFloor_le : ∀ q, scaleFloor ≤ scale q
  scale_hierarchy :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  selected_tolerance_nonneg :
    ∀ j : Fin r,
      0 ≤
        selectedOrderedComplexTolerance
          tolerance regularity.index j
  selected_tolerance_le_common :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance
          tolerance regularity.index j ≤
        sourceFullCommonTolerance F scale
  rank_gap_le :
    ∀ j : Fin r,
      regularity.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
        sourceFullRankGap F scale j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (regularity.coarse.partition q e) ≤
        scale q

def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    SourceFullCoarseTargetSchedule
      k 0 initialBound F scaleFloor where
  schedule := .nil
  schedule_admissible := trivial
  scale := fun _ _ =>
    max scaleFloor (initialBound 0)
  scaleFloor_le_deepest := by
    intro P
    exact le_max_left _ _
  scale_hierarchy := by
    intro P j
    exact Fin.elim0 j
  selected_tolerance_le_common := by
    intro P j
    exact Fin.elim0 j
  reciprocal_gap_le := by
    intro P j
    exact Fin.elim0 j
  selected_coarse_bound := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max scaleFloor (initialBound 0)
    exact le_max_right _ _

def nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (P :
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length next).Landing) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node chosen lower =>
      Fin.lastCases topScale
        (lowerScale chosen lower)

@[simp]
theorem nodeScale_node
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower) =
      Fin.lastCases topScale
        (lowerScale chosen lower) :=
  rfl

@[simp]
theorem nodeScale_node_last
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        (Fin.last (r + 1)) =
      topScale := by
  simp [nodeScale]

@[simp]
theorem nodeScale_node_castSucc
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (q : Fin (r + 1)) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        q.castSucc =
      lowerScale chosen lower q := by
  simp [nodeScale]

@[simp]
theorem sourceFullCommonTolerance_nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    sourceFullCommonTolerance F
        (nodeScale (tolerance := tolerance) (budget := budget)
          topScale lowerScale
          (AdaptiveCoarseTargetSchedule.Landing.node
            (tolerance := tolerance) (budget := budget)
            chosen lower)) =
      sourceFullCommonTolerance F
        (lowerScale chosen lower) := by
  unfold sourceFullCommonTolerance
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [nodeScale_node_castSucc]

def lowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (budget : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (fixedUpperLayerComplexityFactor r budget i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (topScale : ℕ)
    (tolerance : ℕ → ℝ)
    (budget : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        SourceFullCoarseTargetSchedule
          k r (lowerInitialBound initialBound budget i)
            F (F topScale))
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    (hlength : 0 < length)
    (hscaleFloor : scaleFloor ≤ topScale)
    (hinitialTop :
      initialBound (Fin.last (r + 1)) ≤ topScale)
    (htopTolerance :
      ∀ (i : Fin length)
          (P : (next i).schedule.Landing),
        tolerance i.1 ≤
          sourceFullCommonTolerance F ((next i).scale P))
    (htopGap :
      (Fintype.card
          (OrderedFace k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F topScale : ℝ) ^ 2) :
    SourceFullCoarseTargetSchedule
      k (r + 1) initialBound F scaleFloor where
  schedule :=
    .node tolerance budget length
      (fun i => (next i).schedule)
  schedule_admissible := by
    exact ⟨htolerance, hbudget, hlength,
      fun i => (next i).schedule_admissible⟩
  scale :=
    nodeScale topScale
      (fun i => (next i).scale)
  scaleFloor_le_deepest := by
    intro P
    cases P with
    | node chosen lower =>
        simpa only [nodeScale_node_last] using
          hscaleFloor
  scale_hierarchy := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              nodeScale_node_last,
              nodeScale_node_castSucc] using
              (next chosen).scaleFloor_le_deepest lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              nodeScale_node_castSucc] using
              (next chosen).scale_hierarchy lower q
  selected_tolerance_le_common := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last,
              AdaptiveCoarseTargetSchedule.Landing.index_node_last,
              sourceFullCommonTolerance_nodeScale] using
              htopTolerance chosen lower
        | cast q =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc,
              AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc,
              sourceFullCommonTolerance_nodeScale] using
              (next chosen).selected_tolerance_le_common
                lower q
  reciprocal_gap_le := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_last,
              sourceFullRankGap, Fin.succ_last,
              nodeScale_node_last, Fin.val_last]
            convert htopGap using 1
        | cast q =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc,
              sourceFullRankGap, Fin.succ_castSucc,
              nodeScale_node_castSucc,
              Fin.val_castSucc]
            convert
              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1
  selected_coarse_bound := by
    intro P q
    cases P with
    | node chosen lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [adaptiveSelectedCoarseLayerBound,
              nodeScale_node_last] using
              hinitialTop
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower (Fin.last r)
            | cast j =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower j.castSucc

structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  plan :
    SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor
  ceiling : ℕ
  scale_zero_le :
    ∀ P : plan.schedule.Landing,
      plan.scale P 0 ≤ ceiling

namespace Bounded

def castInitialBound
    {k r : ℕ}
    {initialBound newInitialBound :
      Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : Bounded k r initialBound F scaleFloor)
    (h : initialBound = newInitialBound) :
    Bounded k r newInitialBound F scaleFloor where
  plan := h ▸ S.plan
  ceiling := S.ceiling
  scale_zero_le := by
    subst newInitialBound
    exact S.scale_zero_le

end Bounded

def boundedZero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Bounded k 0 initialBound F scaleFloor where
  plan := zero k initialBound F scaleFloor
  ceiling := max scaleFloor (initialBound 0)
  scale_zero_le := by
    intro P
    change
      max scaleFloor (initialBound 0) ≤
        max scaleFloor (initialBound 0)
    exact le_rfl

def factorLowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

noncomputable def sourceFullStageFactor
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n
      let lower :=
        lowerBuilder
          (factorLowerInitialBound
            initialBound previous)
      let tolerance :=
        growthRegularityStepTolerance
          F lower.ceiling
      let budget :=
        orderedRemovalRegularityBudget
          k r tolerance
      (2 ^ (r + 1)) ^ budget * previous

noncomputable def sourceFullStageBound
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  factorLowerInitialBound initialBound
    (sourceFullStageFactor
      initialBound F topScale lowerBuilder n)

noncomputable def sourceFullStagePlan
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Bounded k r
      (sourceFullStageBound
        initialBound F topScale lowerBuilder n)
      F (F topScale) :=
  lowerBuilder
    (sourceFullStageBound
      initialBound F topScale lowerBuilder n)

noncomputable def sourceFullStageTolerance
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℝ :=
  growthRegularityStepTolerance F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

noncomputable def sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℕ :=
  orderedRemovalRegularityBudget k r
    (sourceFullStageTolerance
      initialBound F topScale lowerBuilder n)

@[simp]
theorem sourceFullStageFactor_zero
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    sourceFullStageFactor
      initialBound F topScale lowerBuilder 0 = 1 :=
  rfl

@[simp]
theorem sourceFullStageFactor_succ
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    sourceFullStageFactor
        initialBound F topScale lowerBuilder (n + 1) =
      (2 ^ (r + 1)) ^
          sourceFullStageBudget
            initialBound F topScale lowerBuilder n *
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n :=
  rfl

theorem fixedUpperLayerComplexityFactor_sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ∀ n,
      fixedUpperLayerComplexityFactor r
          (sourceFullStageBudget
            initialBound F topScale lowerBuilder) n =
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            fixedUpperLayerComplexityFactor r
              (sourceFullStageBudget
                initialBound F topScale lowerBuilder) n =
          (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            sourceFullStageFactor
              initialBound F topScale lowerBuilder n
      rw [ih]

theorem lowerInitialBound_sourceFullStageBudget
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i =
      sourceFullStageBound
        initialBound F topScale lowerBuilder i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound,
        fixedUpperLayerComplexityFactor_sourceFullStageBudget]
  | cast q =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound]

noncomputable def sourceFullStageNext
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    Bounded k r
      (lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i)
      F (F topScale) :=
  (sourceFullStagePlan
      initialBound F topScale lowerBuilder i.1).castInitialBound
    (lowerInitialBound_sourceFullStageBudget
      initialBound F topScale lowerBuilder i).symm

@[simp]
theorem sourceFullStageNext_ceiling
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    (sourceFullStageNext
      initialBound F topScale lowerBuilder i).ceiling =
      (sourceFullStagePlan
        initialBound F topScale lowerBuilder i.1).ceiling :=
  rfl

end SourceFullCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullBundleRemovalParameters
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def sourceBundleDensity (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)

noncomputable def sourceBundleDefectScale
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * sourceBundleDensity δ m ^ N

def sourceBundleSelectedScale
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩

@[simp]
theorem sourceBundleSelectedScale_zero
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    sourceBundleSelectedScale scale 0 = scale 0 := by
  simp [sourceBundleSelectedScale]

noncomputable def sourceBundleRankwiseDensity
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDensity δ (sourceBundleSelectedScale scale d)

noncomputable def sourceBundleRankwiseDefect
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDefectScale δ κ N
      (sourceBundleSelectedScale scale d) ^ 2

def sourceBundleRemovalGrowth (Q N : ℕ) : NatGrowthFunction where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  above_diagonal := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))

@[simp]
theorem sourceBundleRemovalGrowth_apply
    (Q N m : ℕ) :
    sourceBundleRemovalGrowth Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl

structure SourceBundleRemovalGrowthConditions
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  gap :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)

namespace SourceFullCoarseTargetSchedule.Certificate

theorem scale_antitone
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (C.scale j.succ)).trans
        (C.scale_hierarchy j))

end SourceFullCoarseTargetSchedule.Certificate

namespace SourceFullCoarseTargetSchedule.Bounded

structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r) where
  toSourceFull :
    SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor
  scale_zero_le_ceiling : toSourceFull.scale 0 ≤ S.ceiling

end SourceFullCoarseTargetSchedule.Bounded

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateDownsets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def missingCoordinateBound (s : ℕ) (i j : Fin (s + 1)) : ℕ :=
  if j = i then 0 else s

def missingCoordinateDownset (s : ℕ) (i : Fin (s + 1)) : Set (Fin (s + 1) →₀ ℕ) :=
  {a | ∀ j, a j ≤ missingCoordinateBound s i j}

theorem missingCoordinateBound_le (s : ℕ) (i : Fin (s + 1)) :
    missingCoordinateBound s i ≤ fun _ => s := by
  intro j
  by_cases h : j = i <;> simp [missingCoordinateBound, h]

theorem missingCoordinateDownset_lower (s : ℕ) (i : Fin (s + 1)) :
    IsLowerSet (missingCoordinateDownset s i) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem missingCoordinateDownset_covers (s : ℕ) (a : Fin (s + 1) →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) : ∃ i, a ∈ missingCoordinateDownset s i := by
  classical
  have hall (j : Fin (s + 1)) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  have hz : ∃ i, a i = 0 := by
    by_contra hn
    push Not at hn
    have hsum : s + 1 ≤ ∑ i, a i := by
      calc
        _ = ∑ _i : Fin (s + 1), 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hn i)
    omega
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simp [missingCoordinateBound, hi]
  · simpa [missingCoordinateBound, hji] using hall j

theorem missingCoordinateDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin (s + 1) →₀ ℕ)
    (ha : ∀ i, a ∉ missingCoordinateDownset s i) :
    (F.totalDegreeMultifiltration (Fin (s + 1))).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  apply Nat.lt_of_not_ge
  intro h
  obtain ⟨i, hi⟩ := missingCoordinateDownset_covers s a h
  exact ha i hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledDenseCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_dense_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hsmall : Fintype.card I * Real.exp (-p) ≤ 1)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hshape, G, j, hmass, hlocal⟩ := exists_common_sampled_box μ F S w e he hp N
    hslice hw v hv hε hρ hlarge hmean
  have hpos : 0 < μ.mass G := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (by linarith)) hmass
  have hGn : G.Nonempty := by
    by_contra h
    have hz : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz, FiniteProbabilityWeights.mass, Finset.sum_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨z, hz⟩ := hGn
  refine ⟨A, hAn, ?_, G, j, hmass, hlocal⟩
  apply (hslice z (j z)).of_large_subbox hshape (Finset.image_subset_image (hlocal z hz).1)
  simpa only [Finset.card_image_of_injective _ he] using ((hlocal z hz).2.1.trans hsmall)

theorem exists_dense_common_sampled_box_of_seminorm {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α : ℝ} (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card I * Real.exp (-p) ≤ α / 8)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧ α / 4 ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hAdense, G, j, hmass, hlocal⟩ := exists_dense_common_sampled_box μ F S w
    e he hp N hslice hw v hv (show 0 < α / 8 by positivity) (show 0 ≤ α / 4 by positivity)
    (show α / 8 + Fintype.card I * Real.exp (-p) + α / 4 < α by linarith)
    (show Fintype.card I * Real.exp (-p) ≤ 1 by linarith) hmean
  refine ⟨A, hAn, hAdense, G, j, ?_, fun z hz => ⟨(hlocal z hz).1, (hlocal z hz).2.2⟩⟩
  exact (mul_le_mul_of_nonneg_left (by linarith : α / 2 ≤
    α - α / 8 - Fintype.card I * Real.exp (-p) - α / 4) (Real.exp_nonneg _)).trans hmass

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineSidePolynomialBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineLocalDegreeInputBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 2) + 3 * P + 11

noncomputable def affineOuterDegreeInputBudget (P : ℝ) : ℝ := P * (2 * P ^ 2 + 1) + 4

noncomputable def affineLocalDegreeBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P + 2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2

noncomputable def affineAdaptiveDegreeBudget (P : ℝ) : ℝ :=
  P + affineLocalDegreeBudget P + 2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2

end Erdos3

end

section

namespace Erdos3

noncomputable def affineOrderPolynomialBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 3) +
    2 * affineAdaptiveDegreeBudget P + affinePrimitiveLogBudget P

noncomputable def affineAccuracyPolynomialBudget (P : ℝ) : ℝ :=
  (affinePrimitiveLogBudget P + 3) ^ 3 +
    2 * affineAdaptiveDegreeBudget P * (affinePrimitiveLogBudget P + 2) + 2 * P + 4

noncomputable def affineSidePolynomialBudget (P : ℝ) : ℝ :=
  P ^ 2 + P * affineOrderPolynomialBudget P + affineAccuracyPolynomialBudget P + P + 3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def affineCommonReferenceBudget (E : ℕ) (epsilon U : ℝ) : ℝ :=
  2 * (affineReferenceInput epsilon U + 2) ^ E

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AmplificationSourceRankBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def amplificationSourceRankLogConstant (b C : ℕ) (K : ℝ) : ℝ :=
  1 + levelCoefficient K * Real.log b + C

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AdaptiveCouplingComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def adaptiveLeafPairMass (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (z : Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) : ℝ :=
  productCouplingAtomMass c z.1.1 (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY)

theorem adaptiveLeafPairMass_sum (tree : CoordinateDecisionTree ι Y) (I : Finset ι)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree I baseY,
      adaptiveLeafPairMass c baseX baseY z) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I baseY := by
  simp only [CoordinateDecisionTree.leafSourceAssignments, Finset.sum_sigma, adaptiveLeafPairMass,
    productCouplingAtomMass_sum_left]
  exact CoordinateDecisionTree.leafCylinders_mass_sum tree I baseY (FiniteProbabilityWeights.pi ν).weight

theorem adaptiveLeafPairMass_sum_empty (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      adaptiveLeafPairMass c baseX baseY z) = 1 := by
  rw [adaptiveLeafPairMass_sum, productFiberMass_empty, (FiniteProbabilityWeights.pi ν).total]

noncomputable def adaptiveLeafCouplingWeights (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    FiniteProbabilityWeights (CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY) where
  weight z := adaptiveLeafPairMass c baseX baseY z.val
  nonneg z := productCouplingAtomMass_nonneg c _ _ _
  total := by
    rw [Finset.sum_coe_sort]
    exact adaptiveLeafPairMass_sum_empty c tree baseX baseY

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RealificationRationalDensity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_rational_denseRange
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] :
    DenseRange (fun v : V => (1 : ℝ) ⊗ₜ[ℚ] v) := by
  let S := (LinearMap.range ((TensorProduct.mk ℚ ℝ V) 1)).toAddSubgroup
  have htmul (r : ℝ) (v : V) : r ⊗ₜ[ℚ] v ∈ S.topologicalClosure := by
    have hc : Continuous (fun r : ℝ => r • ((1 : ℝ) ⊗ₜ[ℚ] v)) :=
      (continuous_id : Continuous (fun r : ℝ => r)).smul
        (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ) ⊗ₜ[ℚ] v)))
    have hq (q : ℚ) : (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure := by
      apply S.le_topologicalClosure
      refine ⟨q • v, ?_⟩
      simp only [TensorProduct.mk_apply, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Rat.smul_def, smul_eq_mul, mul_one]
    have h : r • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure :=
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).induction_on r
      (S.isClosed_topologicalClosure.preimage hc) hq
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  intro x
  change x ∈ S.topologicalClosure
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => exact htmul r v
  | add x y hx hy => exact S.topologicalClosure.add_mem hx hy

theorem realification_submodule_mem_closure_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) :
    x ∈ closure (Set.range (fun v : P => (1 : ℝ) ⊗ₜ[ℚ] (v : V))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] P)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] P) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  have hc : Continuous (P.subtype.baseChange ℝ) :=
    IsModuleTopology.continuous_of_linearMap (P.subtype.baseChange ℝ)
  obtain ⟨z, rfl⟩ := hx
  have hz := realification_rational_denseRange (V := P) z
  have h := image_closure_subset_closure_image hc ⟨z, hz, rfl⟩
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.baseChange_tmul,
    Submodule.subtype_apply] using h

theorem realification_submodule_property_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {C : Set (ℝ ⊗[ℚ] V)} (hC : IsClosed C)
    (h : ∀ v : P, (1 : ℝ) ⊗ₜ[ℚ] (v : V) ∈ C)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : x ∈ C := by
  exact closure_minimal (Set.range_subset_iff.mpr h) hC
    (realification_submodule_mem_closure_rational P hx)

theorem realification_submodule_eq_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : (ℝ ⊗[ℚ] V) → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ v : P, f ((1 : ℝ) ⊗ₜ[ℚ] (v : V)) = g ((1 : ℝ) ⊗ₜ[ℚ] (v : V)))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : f x = g x :=
  realification_submodule_property_of_rational P (isClosed_eq hf hg) h hx

end Erdos3

end

end OAI

end


