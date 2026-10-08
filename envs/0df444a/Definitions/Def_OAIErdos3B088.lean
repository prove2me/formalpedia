-- Prove2me | Definitions.Def_OAIErdos3B088
-- name    : OAIErdos3B088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T13:11:39.522417+00:00
-- url     : https://prove2.me/theorems/bff0ff4c-a33f-4a8e-9878-0c5d3386265a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 89 of 93
-- statement:
--   Definitions bundle 89 of 93 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B087`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 89 available.
--
--   Modules: `OAI.Erdos3.CenteredForecastModel.noConfusion`, `OAI.Erdos3.CenteredForecastModelBounds`, `OAI.Erdos3.CircleFourier.FejerChoice`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_norm_sub_le`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_sub`, `OAI.Erdos3.CircleFourier.card_fejerChoices`, `OAI.Erdos3.CircleFourier.exists_controlled_commuting_circle_decomposition`, `OAI.Erdos3.CircleFourier.exists_controlled_finite_circle_decomposition`, `OAI.Erdos3.CircleFourier.exists_uniform_controlled_commuting_circle_operators`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent_character`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent_equivariant`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent_lipschitz`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent_norm_le`, `OAI.Erdos3.CircleFourier.iteratedCircleComponent_norm_sub_le`, `OAI.Erdos3.CircleFourier.iteratedCircleSmooth`, `OAI.Erdos3.CircleFourier.iteratedCircleSmooth_eq_sum`, `OAI.Erdos3.CircleFourier.iteratedCircleSmooth_error`, `OAI.Erdos3.CircleFourier.iteratedCircleSmooth_lipschitz`, `OAI.Erdos3.CircleFourier.sum_fin_tuple_cons`, `OAI.Erdos3.DegreeRankLieFiltration.rank_zero_top_eq_bot`, `OAI.Erdos3.EpochStackEvent`, `OAI.Erdos3.FiniteProbabilityCoupling.casesOn`, `OAI.Erdos3.FiniteProbabilityCoupling.ofKernel`, `OAI.Erdos3.FiniteProbabilityWeights.exists_large_mass_choice_fiber`, `OAI.Erdos3.FiniteProbabilityWeights.exists_uniformResidualGood`, `OAI.Erdos3.FiniteProbabilityWeights.exists_uniformSliceResidualGood`, `OAI.Erdos3.FiniteProbabilityWeights.mass_mul_le_mean_of_lower_bound`, `OAI.Erdos3.FiniteProbabilityWeights.mass_superlevel_ge`, `OAI.Erdos3.FiniteProbabilityWeights.sum_mass_choice_fibers`, `OAI.Erdos3.FiniteProbabilityWeights.uniformResidualGood_exp_budget`, `OAI.Erdos3.FixedDensity.ClosedOrderedAtomConfiguration.AvoidsSourceFullBadBases`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.mem_sourceFullAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.mem_sourceFullCoarseOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.mem_sourceFullLargeDefectBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.mem_sourceFullOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullAtomDefectSq`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullBadBaseDeletionFamily`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullCoarseOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullLargeDefectBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion`, `OAI.Erdos3.FixedDensity.topPositiveOrderedFace`, `OAI.Erdos3.FixedDensity.topPositiveOrderedFace_lowerRank_succ`, `OAI.Erdos3.FixedDensity.topPositiveOrderedFace_rank`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.IsSaturated`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.IsSaturated.comap_subtype`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_basis_with_nested_supports_of_monotone_saturated_flag`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_basis_with_nested_supports_of_saturated_flag`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_basis_with_nested_supports_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_fin_basis_with_nested_supports_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_isCompl_of_isSaturated`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.exists_prefix_adapted_basis_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.isSaturated_bot`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.isSaturated_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.isSaturated_top`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.mem_rationalSpanLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.mem_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.monotone_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.rationalEmbed`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.rationalEmbed_apply`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.rationalSpanLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.realEmbed`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.realEmbed_apply`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.realEmbed_zsmul`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.repr_eq_zero_of_mem_span_image`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.self_mem_realPrefixLattice`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.smithVector_mem_of_isSaturated`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.span_image_inl_eq_of_span_comap_eq`, `OAI.Erdos3.IntegerBasisReduction.SaturatedFlag.span_range_inl_prod_eq`, `OAI.Erdos3.IsDenseCommonStrideBox`, `OAI.Erdos3.IsDenseCommonStrideBox.mono`, `OAI.Erdos3.IsDenseCommonStrideBox.nonempty`, `OAI.Erdos3.MultidegreeLieFiltration.blockLayerMap`, `OAI.Erdos3.MultidegreeLieFiltration.blockLayerMap_coe`, `OAI.Erdos3.MultidegreeLieFiltration.blockLayerMap_lie`, `OAI.Erdos3.MultidegreeLieFiltration.blockLayerMap_mem_degree`, `OAI.Erdos3.MultidegreeLieFiltration.blockPermutation_symm`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonProductLayer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonProductLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonProductLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonProductLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.factorialBlockMonomial_mem_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_bracket_coefficient_height`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_coefficient_ne`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_coefficient_self`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_monomial`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_permute`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_repr`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBlockPermute`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBlockPermute_apply`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBlockPermute_eq_self_top`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBlockPermute_one`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeCoefficientLayer_permute`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeComponent`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeComponent_eq_zero_of_degree`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeComponent_mem_multidegree`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeLayer`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeLayer_one`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeLayerMap`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeLayerMap_coe`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeLayerMap_mem`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeLayerMap_zero`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer_le_degree`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeLayer_zero`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeOrdinaryFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreePermute_mem_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeSupport_eq_span`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeSupportedBasis`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeSupportedBasis_coe`, `OAI.Erdos3.MultidegreeLieFiltration.squarefree_degree_eq`, `OAI.Erdos3.MultidegreeLieFiltration.sum_squarefreeComponent`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBCH_insertion_quotient`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_tangent_add`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_value_tangent`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogarithmicDifferential`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogarithmicDifferential_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogarithmicDifferential_smul_real`, `OAI.Erdos3.NilpotentLieBCHGroup.dualRealLogarithmicDifferential`, `OAI.Erdos3.NilpotentLieFiltration.dropTop`, `OAI.Erdos3.NilpotentLieFiltration.dropTop_layer`, `OAI.Erdos3.NilpotentLieFiltration.dropTop_realification_layer`, `OAI.Erdos3.NilpotentLieFiltration.exists_adapted_basis_and_grid`, `OAI.Erdos3.NilpotentLieFiltration.layer_eq_bot_above_step`, `OAI.Erdos3.NilpotentLieFiltration.raiseStep`, `OAI.Erdos3.NilpotentLieFiltration.raiseStep_layer`, `OAI.Erdos3.PatchKernel.grid_approx`, `OAI.Erdos3.PolynomialPatch.exists_gridKernelReplacement_score`, `OAI.Erdos3.PolynomialPatch.gridKernelReplacement`, `OAI.Erdos3.PolynomialPatch.gridKernelReplacement_approx`, `OAI.Erdos3.PolynomialPatch.gridKernelReplacement_score`, `OAI.Erdos3.PolynomialPatch.gridKernelReplacement_value`, `OAI.Erdos3.ProductCylinder.referenceMass`, `OAI.Erdos3.ResidueBoxSlice.axisInclusion`, `OAI.Erdos3.ResidueBoxSlice.axisInsertion`, `OAI.Erdos3.ResidueBoxSlice.axisInsertion_injective`, `OAI.Erdos3.ResidueBoxSlice.axisInsertion_kept`, `OAI.Erdos3.ResidueBoxSlice.comap`, `OAI.Erdos3.ResidueBoxSlice.comap_isDenseCommonStrideBox`, `OAI.Erdos3.ResidueBoxSlice.commonStrideIndex_integerPoint`, `OAI.Erdos3.ResidueBoxSlice.coordinateProjection`, `OAI.Erdos3.ResidueBoxSlice.coordinate_complexMean`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox_fullSlicePointInIntegerBox`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox_integerPoint`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox_integerPoints`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox_length`, `OAI.Erdos3.ResidueBoxSlice.enlargeBox_start`, `OAI.Erdos3.ResidueBoxSlice.exists_affine_normalized_cell_of_width`, `OAI.Erdos3.ResidueBoxSlice.exists_coordinate_fiber_norm`, `OAI.Erdos3.ResidueBoxSlice.exists_coordinate_fiber_score`, `OAI.Erdos3.ResidueBoxSlice.expect_extendAxes`, `OAI.Erdos3.ResidueBoxSlice.expect_integerPoints`, `OAI.Erdos3.ResidueBoxSlice.expect_subtypeSites`, `OAI.Erdos3.ResidueBoxSlice.extendAxes`, `OAI.Erdos3.ResidueBoxSlice.extendAxes_dense`, `OAI.Erdos3.ResidueBoxSlice.extendAxes_integerPoints`, `OAI.Erdos3.ResidueBoxSlice.finiteSplitPoint_mem_integerPoints`, `OAI.Erdos3.ResidueBoxSlice.integerPoint`, `OAI.Erdos3.ResidueBoxSlice.integerPoint_eq`, `OAI.Erdos3.ResidueBoxSlice.integerPoint_injective`, `OAI.Erdos3.ResidueBoxSlice.integerPoints`, `OAI.Erdos3.ResidueBoxSlice.integerPoints_eq_commonStrideBox`, `OAI.Erdos3.ResidueBoxSlice.integerPoints_subset_integerBox`, `OAI.Erdos3.ResidueBoxSlice.isDenseCommonStrideBox`, `OAI.Erdos3.ResidueBoxSlice.keepTrueParameterEquiv`, `OAI.Erdos3.ResidueBoxSlice.keepTrueSlice`, `OAI.Erdos3.ResidueBoxSlice.length_lower_of_dense`, `OAI.Erdos3.ResidueBoxSlice.length_pos_of_dense`, `OAI.Erdos3.ResidueBoxSlice.length_pos_of_integerPoints_nonempty`, `OAI.Erdos3.ResidueBoxSlice.mem_integerPoints_iff`, `OAI.Erdos3.ResidueBoxSlice.mem_subtypeSites`, `OAI.Erdos3.ResidueBoxSlice.progression_inside`, `OAI.Erdos3.ResidueBoxSlice.scalarParameterEquiv`, `OAI.Erdos3.ResidueBoxSlice.subtypeSites`, `OAI.Erdos3.ResidueBoxSlice.subtypeSites_dense`, `OAI.Erdos3.ResidueBoxSlice.subtypeSites_image_val`, `OAI.Erdos3.ResidueBoxSlice.subtypeSites_nonempty_of_integerPoints`, `OAI.Erdos3.SquarefreeIndex.full`, `OAI.Erdos3.SquarefreeIndex.full_apply`, `OAI.Erdos3.SquarefreeIndex.one_le_iff`, `OAI.Erdos3.SquarefreeIndex.permute_full`, `OAI.Erdos3.SquarefreeIndex.permute_one`, `OAI.Erdos3.VectorPolynomial.eq_of_eval₂_eq_on_residueBoxSlice`, `OAI.Erdos3.affineCubePlateauApproximation`, `OAI.Erdos3.affineCubePlateauCoefficient`, `OAI.Erdos3.affineWeightedCubeGridCoefficient`, `OAI.Erdos3.affineWeightedCubeIntegerBlock`, `OAI.Erdos3.affineWeightedCubeIntegerSum`, `OAI.Erdos3.basisFun_mem_realIntegerGrid`, `OAI.Erdos3.basis_change_structure_height`, `OAI.Erdos3.bchPiEquiv`, `OAI.Erdos3.bchPiEquiv_single`, `OAI.Erdos3.bchPiSingle`, `OAI.Erdos3.bchPiSingle_comap_inner_grid`, `OAI.Erdos3.bchPiSingle_eq_symm_mulSingle`, `OAI.Erdos3.bchSubgroupCoordinates_changeStep`, `OAI.Erdos3.bchSubgroup_comap_inner_grid_of_columns`, `OAI.Erdos3.blockMonomial_lie`, `OAI.Erdos3.blockMonomial_lie_coefficient`, `OAI.Erdos3.bracketSystemLift`, `OAI.Erdos3.bracketSystemLift_mem`, `OAI.Erdos3.bracketSystemLift_single`, `OAI.Erdos3.bracketSystemMatrix`, `OAI.Erdos3.bracketSystemMatrix_height`, `OAI.Erdos3.bracketSystemMatrix_real_apply`, `OAI.Erdos3.central_smul_eq_self_of_mem`, `OAI.Erdos3.comap_eq_section_image_sup_kernel`, `OAI.Erdos3.commonStrideBox_axis_card`, `OAI.Erdos3.commonStrideCount_exp_bound`, `OAI.Erdos3.cyclicIntegerKernel`, `OAI.Erdos3.cyclicIntegerKernel_covolume_eq_card_range`, `OAI.Erdos3.cyclicIntegerKernel_covolume_le`, `OAI.Erdos3.cyclicIntegerKernel_discrete`, `OAI.Erdos3.cyclicIntegerKernel_full`, `OAI.Erdos3.cyclicIntegerKernel_le_integerCoordinateLattice`, `OAI.Erdos3.cyclicKernelCoordinateCharacter`, `OAI.Erdos3.cyclicKernelCoordinateCharacter_eq_zero`, `OAI.Erdos3.cyclicKernelCoordinateCharacters_eq_iff`, `OAI.Erdos3.cyclicKernelCoordinateCharacters_eq_zero_iff`, `OAI.Erdos3.cyclicKernelCoordinateCharacters_injOn`, `OAI.Erdos3.cyclicKernelRealCoordinates`, `OAI.Erdos3.dualTangentLinear_bch_add`, `OAI.Erdos3.dualTangentLinear_lift_add`, `OAI.Erdos3.epochStackRank`, `OAI.Erdos3.exists_affine_cyclic_kernel_real_frequencies`, `OAI.Erdos3.exists_basis_change_grid_exp_bound`, `OAI.Erdos3.exists_common_inner_sampled_slice`, `OAI.Erdos3.exists_common_sampled_box`, `OAI.Erdos3.exists_cyclic_kernel_real_frequencies`, `OAI.Erdos3.exists_dense_box_inner_family`, `OAI.Erdos3.exists_factorwise_bch_covers`, `OAI.Erdos3.exists_finite_site_box_inner_family`, `OAI.Erdos3.exists_fixed_linear_model_partners_of_pointwise_error`, `OAI.Erdos3.exists_integral_grid_subgroup_exp`, `OAI.Erdos3.exists_long_frozen_box`, `OAI.Erdos3.exists_long_residue_cell_frozen_score`, `OAI.Erdos3.exists_monomial_coordinate_rows`, `OAI.Erdos3.exists_normalized_residue_block_cells`, `OAI.Erdos3.exists_patch_kernel_mesh`, `OAI.Erdos3.exists_positive_combination_term`, `OAI.Erdos3.factorialBlockMonomial_lie`, `OAI.Erdos3.finiteResidueModeModel`, `OAI.Erdos3.finiteSupportGowersNorm_le_one_of_embedding`, `OAI.Erdos3.frozenCosetMap`, `OAI.Erdos3.frozenCosetMap_mk`, `OAI.Erdos3.gridPatchKernel`, `OAI.Erdos3.gridPatchKernel_original_support`, `OAI.Erdos3.gridPatchKernel_translate`, `OAI.Erdos3.integerBooleanBlockJet`, `OAI.Erdos3.integerBooleanBlockValue`, `OAI.Erdos3.integerBoxInclusion`, `OAI.Erdos3.integerBoxInclusion_val`, `OAI.Erdos3.integerCoordinateLattice`, `OAI.Erdos3.integerCoordinateLattice_covolume`, `OAI.Erdos3.integerCoordinateLattice_discrete`, `OAI.Erdos3.integerCoordinateLattice_full`, `OAI.Erdos3.integerGridApproximation`, `OAI.Erdos3.integerGridCoefficient`, `OAI.Erdos3.integerGridDensity`, `OAI.Erdos3.integerGridMass`, `OAI.Erdos3.integerVectorRealEquiv`, `OAI.Erdos3.integerVectorRealMap`, `OAI.Erdos3.integerVectorRealMap_injective`, `OAI.Erdos3.integerVectorRealMap_mem_cyclicIntegerKernel`, `OAI.Erdos3.integer_lattice_covolume_eq_index`, `OAI.Erdos3.integer_lattice_index_nsmul_mem`, `OAI.Erdos3.integer_lattice_index_pos`, `OAI.Erdos3.integralVector_mulVec_of_column_denominators`, `OAI.Erdos3.integral_frequency_grid_allowance_le_exp`, `OAI.Erdos3.integral_grid_allowance_le_exp`, `OAI.Erdos3.inverse_basis_entries_height`, `OAI.Erdos3.isometry_quotient_central_smul`, `OAI.Erdos3.latticeImage`, `OAI.Erdos3.latticeImage_basis_lifts`, `OAI.Erdos3.latticeImage_discrete`, `OAI.Erdos3.latticeImage_full`, `OAI.Erdos3.latticeImage_index_lift`, `OAI.Erdos3.latticeImage_index_pos`, `OAI.Erdos3.latticeImage_le_integer`, `OAI.Erdos3.lattice_basis_coordinates_bound`, `OAI.Erdos3.liePiSingle`, `OAI.Erdos3.lieSubalgebra_comap_inner_grid_of_columns`, `OAI.Erdos3.lie_bracket_coordinate_height`, `OAI.Erdos3.lie_mem_real_baseChange`, `OAI.Erdos3.lipschitz_frozenCosetMap`, `OAI.Erdos3.lipschitz_quotient_left_smul`, `OAI.Erdos3.lipschitz_quotient_orbit`, `OAI.Erdos3.mem_integerCoordinateLattice_iff`, `OAI.Erdos3.mem_piBCHSubgroup`, `OAI.Erdos3.normalizedSupportedCubeSum`, `OAI.Erdos3.normalizedSupportedCubeSum_le_vertex`, `OAI.Erdos3.normalizedSupportedCubeSum_norm_le_one`, `OAI.Erdos3.normalizedSupportedCubeSum_self_re`, `OAI.Erdos3.normalized_residue_block_cell`, `OAI.Erdos3.nsmul_integerVectorRealMap_mem_cyclicIntegerKernel`, `OAI.Erdos3.patchKernelGridRadius`, `OAI.Erdos3.patchKernelGridRadius_pos`, `OAI.Erdos3.patchKernelGridRadius_small`, `OAI.Erdos3.piBCHSubgroup`, `OAI.Erdos3.piBCHSubgroup_coordinates`, `OAI.Erdos3.piBCHSubgroup_inner_grid`, `OAI.Erdos3.piBCHSubgroup_le_of_factors`, `OAI.Erdos3.piBCHSubgroup_outer_grid`, `OAI.Erdos3.pi_basis_equivFun_symm_apply`, `OAI.Erdos3.productCoordinate_indicator`, `OAI.Erdos3.productCouplingAtomMass`, `OAI.Erdos3.productCouplingAtomMass_nonneg`, `OAI.Erdos3.productCouplingAtomMass_sum_left`, `OAI.Erdos3.productCouplingPairing`, `OAI.Erdos3.productCouplingPairing_indicators`, `OAI.Erdos3.productCouplingPairing_sum_left`, `OAI.Erdos3.productCoupling_right_mean`, `OAI.Erdos3.productMean_coordinate_transport`, `OAI.Erdos3.quotientRightEDist_left_smul_le`, `OAI.Erdos3.quotientRightEDist_orbit_le`, `OAI.Erdos3.realBracketSystem`, `OAI.Erdos3.realBracketSystem_apply`, `OAI.Erdos3.realBracketSystem_eq_zero_iff`, `OAI.Erdos3.realification_inf`, `OAI.Erdos3.rectangularScalarDiscrepancy`, `OAI.Erdos3.rightCosetEDist_left_mul_le`, `OAI.Erdos3.rightCosetMetricSpace_lipschitz_lift`, `OAI.Erdos3.rowPolynomial_single`, `OAI.Erdos3.sampled_normalized_cube_lower_bound`, `OAI.Erdos3.scaledIntegerGrid_mulVec_of_column_denominators`, `OAI.Erdos3.span_range_sumElim`, `OAI.Erdos3.split_preimage_spanning`, `OAI.Erdos3.squarefreeBracketHeight`, `OAI.Erdos3.squarefreeBracketHeight_pos`, `OAI.Erdos3.squarefreePermute_lie`, `OAI.Erdos3.squarefreePermute_monomial_lie`, `OAI.Erdos3.squarefreePermute_mul`, `OAI.Erdos3.squarefreePermute_one`, `OAI.Erdos3.squarefree_top_monomial`, `OAI.Erdos3.supportedSubmoduleBasis_comap_span`, `OAI.Erdos3.weightedAffineModerateGridApproximation`, `OAI.Erdos3.weightedAffineModerateIntegerBlock`, `OAI.Erdos3.weightedAffineModerateIntegerJetSum`, `OAI.Erdos3.weightedAffineModeratePlateauApproximation`, `OAI.Erdos3.weightedAffinePlateauModeCoefficient`, `OAI.Erdos3.weightedAffinePlateauModeModel`, `OAI.Erdos3.weightedCubeIntegerSource`, `OAI.Erdos3.weightedModerateIntegerProductSource`, `OAI.Erdos3.weightedModerateIntegerSource`, `_private.Linear.DualLogarithmicDifferential.0.OAI.Erdos3.base_lift_congr`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B089

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

theorem rightCosetEDist_left_mul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G) :
    rightCosetEDist Γ (a * x) (a * y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  apply (iInf_le (fun δ : Γ => edist (a * x) (a * y * δ)) γ).trans
  simpa only [mul_assoc] using hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_left_smul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G ⧸ Γ) :
    quotientRightEDist Γ (a • x) (a • y) ≤ C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_left_mul_le Γ a hLip)

theorem quotientRightEDist_orbit_le (Γ : Subgroup G) (x : G ⧸ Γ) (a b : G) :
    quotientRightEDist Γ (a • x) (b • x) ≤ edist a b := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact (quotientRightEDist_mk_le Γ (a * x) (b * x)).trans_eq (edist_mul_right a b x)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem lipschitz_quotient_left_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (a : G) {C : ℝ≥0} (hLip : LipschitzWith C (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C (fun x : G ⧸ Γ => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  exact quotientRightEDist_left_smul_le Γ a hLip x y

theorem lipschitz_quotient_orbit (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (fun a : G => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro a b
  change quotientRightEDist Γ (a • x) (b • x) ≤ 1 * edist a b
  simpa only [one_mul] using quotientRightEDist_orbit_le Γ x a b

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G X : Type*} [Group G] [MetricSpace G]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] [PseudoEMetricSpace X]

theorem rightCosetMetricSpace_lipschitz_lift (Γ : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (f : G ⧸ Γ → X) {C : ℝ≥0}
    (hf : LipschitzWith C (fun x : G => f (QuotientGroup.mk x))) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C f := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      rw [rightCosetMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
      apply le_iInf
      intro γ
      simpa only [quotient_mk_mul_mem] using hf x (y * γ)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

theorem central_smul_eq_self_of_mem (Γ : Subgroup G) {g : G}
    (hg : g ∈ Γ) (hc : ∀ a : G, Commute g a) (x : G ⧸ Γ) : g • x = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (g * a) : G ⧸ Γ) = QuotientGroup.mk a
    rw [(hc a).eq]
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using Γ.inv_mem hg

variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem isometry_quotient_central_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (hc : ∀ a : G, Commute g a) :
    letI := rightCosetMetricSpace Γ hΓ
    Isometry (fun x : G ⧸ Γ => g • x) := by
  let := rightCosetMetricSpace Γ hΓ
  have hgroup : LipschitzWith 1 (fun a : G => g * a) := by
    have heq : (fun a : G => g * a) = (fun a : G => a * g) := funext (fun a => (hc a).eq)
    rw [heq]
    exact (isometry_mul_right g).lipschitz
  have hinv : LipschitzWith 1 (fun a : G => g⁻¹ * a) := by
    have heq : (fun a : G => g⁻¹ * a) = (fun a : G => a * g⁻¹) :=
      funext (fun a => (hc a).inv_left.eq)
    rw [heq]
    exact (isometry_mul_right g⁻¹).lipschitz
  have hforward := lipschitz_quotient_left_smul Γ hΓ g hgroup
  have hback := lipschitz_quotient_left_smul Γ hΓ g⁻¹ hinv
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using hforward.dist_le_mul x y
  · simpa only [inv_smul_smul, NNReal.coe_one, one_mul] using hback.dist_le_mul (g • x) (g • y)

end Erdos3

end

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

def frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) : (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map (fun x => a * φ x * r) (fun {x y} hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have heq : (a * φ x * r)⁻¹ * (a * φ y * r) = r⁻¹ * φ (x⁻¹ * y) * r := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact h (x⁻¹ * y) (QuotientGroup.leftRel_apply.mp hxy))

@[simp] theorem frozenCosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) (x : G) :
    frozenCosetMap Γ Λ φ a r h (QuotientGroup.mk x) = QuotientGroup.mk (a * φ x * r) := rfl

open scoped NNReal

variable [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (a r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)
    {A C : ℝ≥0} (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith (A * C) (frozenCosetMap Γ Λ φ a r h) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  apply rightCosetMetricSpace_lipschitz_lift Γ hΓ
  have hf : LipschitzWith (A * C) (fun x : G => a * φ x * r) := by
    simpa only [one_mul, Function.comp_def] using
      (isometry_mul_right r).lipschitz.comp (ha.comp hφ)
  simpa only [one_mul, Function.comp_def, frozenCosetMap_mk] using
    (rightCosetMetricSpace_lipschitz_mk Λ hΛ).comp hf

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (Γ : Subgroup G) (Λ : Subgroup H)
  (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
  (φ : G →* H) (r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def integerCoordinateLattice : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

instance integerCoordinateLattice_discrete :
    DiscreteTopology (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

instance integerCoordinateLattice_full : IsZLattice ℝ (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

theorem mem_integerCoordinateLattice_iff (x : ι → ℝ) :
    x ∈ integerCoordinateLattice ↔ x ∈ realIntegerGrid := by
  change x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      simpa using hx i
    choose z hz using h
    exact ⟨z, funext hz⟩
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, by simpa using congrFun hz i⟩

theorem integerCoordinateLattice_covolume :
    ZLattice.covolume (integerCoordinateLattice (ι := ι)) = 1 := by
  change ZLattice.covolume (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) = 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume), measureReal_def]
  have hv : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]
  rw [hv]
  simp

theorem integer_lattice_covolume_eq_index
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    ZLattice.covolume L = L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex L integerCoordinateLattice hL
  simpa only [integerCoordinateLattice_covolume, div_one] using h

theorem integer_lattice_index_pos
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    0 < L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_pos L volume
  rw [integer_lattice_covolume_eq_index L hL] at h
  exact_mod_cast h

theorem integer_lattice_index_nsmul_mem (L : Submodule ℤ (ι → ℝ))
    (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup • x ∈ L :=
  L.toAddSubgroup.nsmul_relIndex_mem ((mem_integerCoordinateLattice_iff x).mpr hx)

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι : Type*}

def integerVectorRealMap : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem integerVectorRealMap_injective :
    Function.Injective (integerVectorRealMap (ι := ι)) := by
  intro x y h
  ext i
  exact Int.cast_injective (congrFun h i)

variable [Fintype ι] {N : ℕ}

noncomputable def integerVectorRealEquiv :
    (ι → ℤ) ≃ₗ[ℤ] (integerCoordinateLattice (ι := ι)) :=
  LinearEquiv.ofBijective
    (integerVectorRealMap.codRestrict integerCoordinateLattice (fun x =>
      (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩))
    ⟨fun _ _ h => integerVectorRealMap_injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := (mem_integerCoordinateLattice_iff _).mp y.property
      exact ⟨x, Subtype.ext hx⟩⟩

def cyclicIntegerKernel (η : (ι → ℤ) →+ ZMod N) : Submodule ℤ (ι → ℝ) :=
  (LinearMap.ker η.toIntLinearMap).map integerVectorRealMap

omit [Fintype ι] in
theorem integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    integerVectorRealMap x ∈ cyclicIntegerKernel η ↔ η x = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact integerVectorRealMap_injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem cyclicIntegerKernel_le_integerCoordinateLattice
    (η : (ι → ℤ) →+ ZMod N) : cyclicIntegerKernel η ≤ integerCoordinateLattice := by
  rintro y ⟨x, _, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩

instance cyclicIntegerKernel_discrete (η : (ι → ℤ) →+ ZMod N) :
    DiscreteTopology (cyclicIntegerKernel η) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff _).mp
    (cyclicIntegerKernel_le_integerCoordinateLattice η hy)

omit [Fintype ι] in
theorem nsmul_integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    N • integerVectorRealMap x ∈ cyclicIntegerKernel η := by
  rw [← map_nsmul, integerVectorRealMap_mem_cyclicIntegerKernel, map_nsmul]
  simp [nsmul_eq_mul]

instance cyclicIntegerKernel_full [NeZero N] (η : (ι → ℤ) →+ ZMod N) :
    IsZLattice ℝ (cyclicIntegerKernel η) := by
  classical
  constructor
  apply top_unique
  rw [← (Pi.basisFun ℝ ι).span_eq]
  apply Submodule.span_le.mpr
  rintro y ⟨i, rfl⟩
  have hmem := nsmul_integerVectorRealMap_mem_cyclicIntegerKernel η (Pi.single i 1)
  have hcast : integerVectorRealMap (Pi.single i (1 : ℤ)) = Pi.basisFun ℝ ι i := by
    ext j
    simp [integerVectorRealMap, Pi.basisFun_apply, Pi.single_apply]
  rw [hcast] at hmem
  have hmemR : (N : ℝ) • Pi.basisFun ℝ ι i ∈ cyclicIntegerKernel η := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hmem
  have hspan : (N : ℝ) • Pi.basisFun ℝ ι i ∈
      Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ)) := Submodule.subset_span hmemR
  have hscale := (Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ))).smul_mem
    ((N : ℝ)⁻¹) hspan
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [smul_smul, inv_mul_cancel₀ hN, one_smul] at hscale
  exact hscale

theorem cyclicIntegerKernel_covolume_eq_card_range [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) = (Nat.card η.range : ℝ) := by
  classical
  rw [integer_lattice_covolume_eq_index _ (cyclicIntegerKernel_le_integerCoordinateLattice η)]
  have hindex : (cyclicIntegerKernel η).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup = Nat.card η.range := by
    let e := (integerVectorRealEquiv (ι := ι)).toAddEquiv.toAddMonoidHom
    let H := (cyclicIntegerKernel η).toAddSubgroup.addSubgroupOf
      (integerCoordinateLattice (ι := ι)).toAddSubgroup
    have he : H.comap e = η.ker := by
      ext x
      exact integerVectorRealMap_mem_cyclicIntegerKernel η x
    change H.index = Nat.card η.range
    rw [← H.index_comap_of_surjective (f := e) (integerVectorRealEquiv (ι := ι)).surjective,
      he, AddSubgroup.index_ker]
  exact_mod_cast hindex

theorem cyclicIntegerKernel_covolume_le [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) ≤ (N : ℝ) := by
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  have h := Nat.card_le_card_of_injective (fun x : η.range => (x : ZMod N))
    Subtype.val_injective
  have hcard : Nat.card (ZMod N) = N := by simp
  rw [hcard] at h
  exact_mod_cast h

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImage : Submodule ℤ (ι → ℝ) := Λ.map (π.restrictScalars ℤ)

theorem latticeImage_le_integer (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    latticeImage Λ π ≤ integerCoordinateLattice := by
  rintro y ⟨x, hx, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr (hπ x hx)

theorem latticeImage_discrete (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    DiscreteTopology (latticeImage Λ π) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff y).mp (latticeImage_le_integer Λ π hπ hy)

theorem latticeImage_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (latticeImage Λ π)] (hπ : Function.Surjective π) :
    IsZLattice ℝ (latticeImage Λ π) := by
  constructor
  change Submodule.span ℝ (π '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hπ

theorem latticeImage_index_lift (x : ι → ℝ) (hx : x ∈ realIntegerGrid) :
    ∃ y ∈ Λ, π y = (latticeImage Λ π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup • x := by
  exact integer_lattice_index_nsmul_mem (latticeImage Λ π) x hx

theorem latticeImage_index_pos [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    0 < (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  let : DiscreteTopology (latticeImage Λ π) := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ (latticeImage Λ π) := latticeImage_full Λ π hsurj
  exact integer_lattice_index_pos (latticeImage Λ π) (latticeImage_le_integer Λ π hinteger)

end Erdos3

end

section

namespace Erdos3

open Module BohrLattice.MinkowskiDiagonalNormalization
open scoped BigOperators Matrix

theorem lattice_basis_coordinates_bound
    {r : ℕ} (Λ : Submodule ℤ (Fin r → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin r) ℤ Λ) (ρ : Fin r → ℝ) (hρ : ∀ j, 0 < ρ j)
    {H : ℝ} (hH : 0 ≤ H) (hb : ∀ i j, |(b i : Fin r → ℝ) j| ≤ H * ρ j)
    (hcov : (∏ j, ρ j) ≤ ZLattice.covolume Λ)
    (x : Fin r → ℝ) (hx : ∀ j, |x j| ≤ ρ j) (i : Fin r) :
    |(b.ofZLatticeBasis ℝ Λ).equivFun x i| ≤
      (r : ℝ) * r.factorial * H ^ (r - 1) := by
  classical
  let B := b.ofZLatticeBasis ℝ Λ
  let M : Matrix (Fin r) (Fin r) ℝ := fun i j => B j i / ρ i
  have hM : M = (Matrix.of (normalizedBasis B ρ hρ))ᵀ := by
    ext i j
    simp [M]
  have hB : |(Matrix.of B).det| = ZLattice.covolume Λ := by
    have he : (B : Fin r → Fin r → ℝ) = fun j => (b j : Fin r → ℝ) :=
      funext (fun j => Basis.ofZLatticeBasis_apply ℝ Λ b j)
    rw [he]
    exact (ZLattice.covolume_eq_det Λ b).symm
  have hprod : 0 < ∏ j, ρ j := Finset.prod_pos (fun j _ => hρ j)
  have hdet : 1 ≤ |M.det| := by
    rw [hM, Matrix.det_transpose, abs_det_normalizedBasis, hB, ← div_eq_mul_inv]
    exact (le_div_iff₀ hprod).mpr (by simpa using hcov)
  have hentry : ∀ j k, |M j k| ≤ H := by
    intro j k
    change |B k j / ρ j| ≤ H
    rw [abs_div, abs_of_pos (hρ j)]
    apply (div_le_iff₀ (hρ j)).mpr
    simpa only [B, Basis.ofZLatticeBasis_apply] using hb k j
  have hinv : ∀ j k, |M⁻¹ j k| ≤ (r.factorial : ℝ) * H ^ (r - 1) := by
    intro j k
    simpa only [Fintype.card_fin, div_one] using
      matrix_inverse_entry_abs_le M hentry (by norm_num : (0 : ℝ) < 1) hdet j k
  have hMx : M.mulVec (B.equivFun x) = fun j => x j / ρ j := by
    exact basis_coordinate_matrix_mulVec B (divideCoordinates ρ hρ).toLinearMap x
  have hback : M⁻¹.mulVec (fun j => x j / ρ j) = B.equivFun x := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (abs_pos.mp (lt_of_lt_of_le zero_lt_one hdet))), Matrix.one_mulVec]
  have hsmall (j) : |x j / ρ j| ≤ 1 := by
    rw [abs_div, abs_of_pos (hρ j)]
    exact (div_le_one (hρ j)).mpr (hx j)
  change |B.equivFun x i| ≤ _
  rw [← hback]
  change |∑ j, M⁻¹ i j * (x j / ρ j)| ≤ _
  calc
    _ ≤ ∑ j, |M⁻¹ i j * (x j / ρ j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin r, (r.factorial : ℝ) * H ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have h := mul_le_mul (hinv i j) (hsmall j) (abs_nonneg _) (by positivity)
      simpa only [mul_one] using h
    _ = _ := by simp [mul_assoc]

end Erdos3

end

section

namespace Erdos3

theorem basisFun_mem_realIntegerGrid {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Pi.basisFun ℝ ι i ∈ realIntegerGrid := by
  refine ⟨Pi.single i (1 : ℤ), ?_⟩
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply]

theorem latticeImage_basis_lifts {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) :
    let I := (latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup
    ∀ i, ∃ x ∈ Λ, π x = (I : ℝ) • Pi.basisFun ℝ ι i := by
  intro I i
  obtain ⟨x, hx, hπx⟩ := latticeImage_index_lift Λ π (Pi.basisFun ℝ ι i)
    (basisFun_mem_realIntegerGrid i)
  refine ⟨x, hx, ?_⟩
  simpa only [Nat.cast_smul_eq_nsmul] using hπx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreePermute_monomial_lie (e : ι ≃ κ) (a b : SquarefreeIndex ι) (v w : L) :
    squarefreePermute e ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      ⁅squarefreePermute e (squarefreeMonomial a v),
        squarefreePermute e (squarefreeMonomial b w)⁆ := by
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_disjoint _ _ ((SquarefreeIndex.permute_disjoint e a b).mpr hab),
      SquarefreeIndex.permute_disjointAdd]
  · rw [squarefreeMonomial_lie_overlap a b hab, map_zero]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_overlap _ _
      (fun h => hab ((SquarefreeIndex.permute_disjoint e a b).mp h))]

theorem squarefreePermute_lie (e : ι ≃ κ) (x y : SquarefreePolynomial ι L) :
    squarefreePermute e ⁅x, y⁆ = ⁅squarefreePermute e x, squarefreePermute e y⁆ := by
  classical
  conv_lhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
    simp only [map_sum]
  conv_rhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y]
    simp only [map_sum]
    rw [sum_lie_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact squarefreePermute_monomial_lie e a b _ _

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}

theorem layer_eq_bot_above_step (F : NilpotentLieFiltration L s) {i : ℕ}
    (hi : s < i) : F.layer i = ⊥ := by
  apply bot_unique
  rw [← F.terminal]
  exact F.antitone (by omega)

def raiseStep (F : NilpotentLieFiltration L s) (hst : s ≤ t) : NilpotentLieFiltration L t where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := F.layer_eq_bot_above_step (by omega)

theorem raiseStep_layer (F : NilpotentLieFiltration L s) (hst : s ≤ t) (i : ℕ) :
    (F.raiseStep hst).layer i = F.layer i := rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open Module

theorem bchSubgroupCoordinates_changeStep
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)
    (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hs)) :
    bchSubgroupCoordinates e (Γ.map (NilpotentLieBCHGroup.changeStep hs ht).toMonoidHom) =
      bchSubgroupCoordinates e Γ := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hcoord := congrArg NilpotentLieBCHGroup.coord heq
    have hg' : g = ⟨e.equivFun.symm x⟩ := NilpotentLieBCHGroup.ext hcoord
    change (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hs) ∈ Γ
    rwa [← hg']
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨e.equivFun.symm x⟩, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeComponent (a : SquarefreeIndex ι) :
    F.SquarefreeAlgebra π →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreeMonomial a (squarefreePolynomialEquiv x.val a),
    F.squarefreeMonomial_component_mem π x.val x.property a⟩
  map_add' x y := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (x.val + y.val) a) = _
    simp only [map_add, Pi.add_apply]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (r • x.val) a) = _
    simp only [map_smul, Pi.smul_apply]
    rfl

theorem sum_squarefreeComponent (x : F.SquarefreeAlgebra π) :
    ∑ a : SquarefreeIndex ι, F.squarefreeComponent π a x = x := by
  classical
  apply Subtype.ext
  change (F.squarefreeAdaptedSubalgebra π).incl (∑ a, F.squarefreeComponent π a x) = x.val
  rw [map_sum]
  exact sum_squarefreeMonomial x.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (hF : F.layer (s + 1) = ⊥)

def dropTop : NilpotentLieFiltration L s where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := hF

@[simp] theorem dropTop_layer (i : ℕ) : (F.dropTop hF).layer i = F.layer i := rfl

@[simp] theorem dropTop_realification_layer (i : ℕ) :
    (F.dropTop hF).realification.layer i = F.realification.layer i := rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem rank_zero_top_eq_bot (F : DegreeRankLieFiltration L s 0) :
    F.associatedDegree.layer s = ⊥ := by
  change F.layer s 0 = ⊥
  rw [F.rank_zero_eq_one]
  exact F.terminal

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeMultidegreeLayer (c : ι → ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => c ≤ fun i => a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

noncomputable def squarefreeDegreeLayer (n : ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => n ≤ ∑ i, a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

theorem squarefreeMultidegreeLayer_antitone : Antitone (F.squarefreeMultidegreeLayer π) := by
  intro c d h x hx a ha
  exact hx a (fun hd => ha (h.trans hd))

theorem squarefreeDegreeLayer_antitone : Antitone (F.squarefreeDegreeLayer π) := by
  intro n m h x hx a ha
  exact hx a (fun hm => ha (h.trans hm))

theorem squarefreeMultidegreeLayer_lie_mem {c d : ι → ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeMultidegreeLayer π c) (hy : y ∈ F.squarefreeMultidegreeLayer π d) :
    ⁅x, y⁆ ∈ F.squarefreeMultidegreeLayer π (c + d) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb i
  exact Nat.add_le_add (ha i) (hb i)

theorem squarefreeDegreeLayer_lie_mem {n m : ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (hy : y ∈ F.squarefreeDegreeLayer π m) :
    ⁅x, y⁆ ∈ F.squarefreeDegreeLayer π (n + m) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb
  rw [squarefreeDisjointAdd_total]
  exact Nat.add_le_add ha hb

theorem squarefreeMultidegreeLayer_le_degree (c : ι → ℕ) (n : ℕ) (h : n ≤ ∑ i, c i) :
    F.squarefreeMultidegreeLayer π c ≤ F.squarefreeDegreeLayer π n := by
  intro x hx a ha
  apply hx a
  intro hca
  exact ha (h.trans (Finset.sum_le_sum fun i _ => hca i))

theorem squarefreeComponent_mem_multidegree (a : SquarefreeIndex ι) (x : F.SquarefreeAlgebra π) :
    F.squarefreeComponent π a x ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  exact squarefreeMonomial_mem_support a (fun _ => le_rfl) _

theorem squarefreeComponent_eq_zero_of_degree {n : ℕ} {x : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (a : SquarefreeIndex ι) (ha : ¬n ≤ ∑ i, a.val i) :
    F.squarefreeComponent π a x = 0 := by
  apply Subtype.ext
  change squarefreeMonomial a (squarefreePolynomialEquiv x.val a) = 0
  have hz : squarefreePolynomialEquiv x.val a = 0 := hx a ha
  rw [hz, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeDegreeLayer_one : F.squarefreeDegreeLayer π 1 = ⊤ := by
  apply top_unique
  intro x _ a ha
  have hzero : a.val = 0 := (exponent_total_eq_zero_iff a.val).mp (by omega)
  exact (x.property a).2 hzero

theorem squarefreeDegreeLayer_terminal : F.squarefreeDegreeLayer π (Fintype.card ι + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  apply hx a
  have h := squarefreeExponent_total_le a
  omega

noncomputable def squarefreeOrdinaryFiltration :
    NilpotentLieFiltration (F.SquarefreeAlgebra π) (Fintype.card ι) where
  layer := F.squarefreeDegreeLayer π
  antitone := F.squarefreeDegreeLayer_antitone π
  one_eq_top := F.squarefreeDegreeLayer_one π
  lie_mem := F.squarefreeDegreeLayer_lie_mem π
  terminal := F.squarefreeDegreeLayer_terminal π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonProductLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n)

theorem comparisonProductLayer_antitone : Antitone (F.comparisonProductLayer π) :=
  fun _ _ h _ hx => ⟨F.ordinary.antitone h hx.1, F.squarefreeDegreeLayer_antitone π h hx.2⟩

theorem comparisonProductLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π i) (hy : y ∈ F.comparisonProductLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonProductLayer π (i + j) :=
  ⟨F.ordinary.lie_mem hx.1 hy.1, F.squarefreeDegreeLayer_lie_mem π hx.2 hy.2⟩

theorem comparisonProductLayer_terminal :
    F.comparisonProductLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  change (F.ordinary.layer _).prod ((F.squarefreeOrdinaryFiltration π).layer _) = ⊥
  rw [F.ordinary.layer_eq_bot_above_step (by omega),
    (F.squarefreeOrdinaryFiltration π).layer_eq_bot_above_step (by omega)]
  ext x
  simp only [Submodule.mem_prod, Submodule.mem_bot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeMultidegreeLayer_zero : F.squarefreeMultidegreeLayer π 0 = ⊤ := by
  apply top_unique
  intro x _ a ha
  exact False.elim (ha (fun _ => Nat.zero_le _))

theorem squarefreeMultidegreeLayer_terminal (c : ι → ℕ) (hc : ¬c ≤ (fun _ => 1)) :
    F.squarefreeMultidegreeLayer π c = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  exact hx a (fun hca => hc (fun i => (hca i).trans (a.property i)))

theorem squarefree_degree_eq (n : ℕ) :
    F.squarefreeDegreeLayer π n =
      ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← F.sum_squarefreeComponent π x]
    apply Submodule.sum_mem
    intro a _
    by_cases ha : n ≤ ∑ i, a.val i
    · have hle : F.squarefreeMultidegreeLayer π (fun i => a.val i) ≤
          ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c :=
        le_iSup_of_le (fun i => a.val i) (le_iSup_of_le ha le_rfl)
      exact hle (F.squarefreeComponent_mem_multidegree π a x)
    · rw [F.squarefreeComponent_eq_zero_of_degree π hx a ha]
      exact Submodule.zero_mem _
  · apply iSup_le
    intro c
    apply iSup_le
    intro hc
    exact F.squarefreeMultidegreeLayer_le_degree π c n hc

noncomputable def squarefreeMultidegreeFiltration :
    MultidegreeLieFiltration ι (F.SquarefreeAlgebra π) (Fintype.card ι) (fun _ => 1) where
  ordinary := F.squarefreeOrdinaryFiltration π
  layer := F.squarefreeMultidegreeLayer π
  antitone := F.squarefreeMultidegreeLayer_antitone π
  zero_eq_top := F.squarefreeMultidegreeLayer_zero π
  lie_mem := F.squarefreeMultidegreeLayer_lie_mem π
  terminal := F.squarefreeMultidegreeLayer_terminal π
  degree_eq := F.squarefree_degree_eq π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

omit [Fintype ι] [Fintype σ] in
theorem blockPermutation_symm (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    ∀ i, π (e.symm i) = π i := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm

theorem squarefreePermute_mem_adapted (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : SquarefreePolynomial ι L) (hx : x ∈ F.squarefreeAdaptedModule π) :
    squarefreePermute e x ∈ F.squarefreeAdaptedModule π := by
  intro a
  rw [squarefreePermute_coefficient]
  have hd : blockDegree π ((SquarefreeIndex.permute e).symm a).val = blockDegree π a.val :=
    SquarefreeIndex.permute_blockDegree π e.symm (blockPermutation_symm π e he) a
  refine ⟨?_, ?_⟩
  · rw [← hd]
    exact (hx _).1
  · intro ha
    exact (hx _).2 ((SquarefreeIndex.permute_zero_iff e.symm a).mpr ha)

noncomputable def squarefreeBlockPermute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    F.SquarefreeAlgebra π ≃ₗ⁅ℚ⁆ F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreePermute e x.val, F.squarefreePermute_mem_adapted π e he _ x.property⟩
  invFun x := ⟨squarefreePermute e.symm x.val,
    F.squarefreePermute_mem_adapted π e.symm (blockPermutation_symm π e he) _ x.property⟩
  left_inv x := Subtype.ext (squarefreePermute_symm_apply e x.val)
  right_inv x := Subtype.ext (squarefreePermute_symm_apply e.symm x.val)
  map_add' x y := Subtype.ext (map_add (squarefreePermute e) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (squarefreePermute e) r x.val)
  map_lie' {x y} := Subtype.ext (squarefreePermute_lie e x.val y.val)

theorem squarefreeBlockPermute_apply (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) :
    (F.squarefreeBlockPermute π e he x).val = squarefreePermute e x.val := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeLayerMap (a : SquarefreeIndex ι) :
    F.layer (blockDegree π a.val) →ₗ[ℚ] F.SquarefreeAlgebra π := by
  classical
  exact if ha : a.val = 0 then 0 else
    { toFun := fun v => ⟨squarefreeMonomial a v.val, F.squarefreeMonomial_mem_adapted π a ha v.val v.property⟩
      map_add' := fun v w => Subtype.ext (map_add (squarefreeMonomial a) v.val w.val)
      map_smul' := fun r v => Subtype.ext (map_smul (squarefreeMonomial a) r v.val) }

theorem squarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : F.layer (blockDegree π a.val)) : F.squarefreeLayerMap π a v = 0 := by
  simp only [squarefreeLayerMap, dif_pos ha, LinearMap.zero_apply]

theorem squarefreeLayerMap_coe (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : F.layer (blockDegree π a.val)) :
    (F.squarefreeLayerMap π a v).val = squarefreeMonomial a v.val := by
  simp only [squarefreeLayerMap, dif_neg ha, LinearMap.coe_mk, AddHom.coe_mk]

theorem squarefreeLayerMap_mem (a : SquarefreeIndex ι) (v : F.layer (blockDegree π a.val)) :
    F.squarefreeLayerMap π a v ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  by_cases ha : a.val = 0
  · rw [F.squarefreeLayerMap_zero π a ha]
    exact Submodule.zero_mem _
  · change (F.squarefreeLayerMap π a v).val ∈ squarefreeSupportModule _
    rw [F.squarefreeLayerMap_coe π a ha]
    exact squarefreeMonomial_mem_support a (fun _ => le_rfl) v.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem factorialBlockMonomial_mem_adapted (a : σ → ℕ) (ha : a ≠ 0)
    (x : L) (hx : x ∈ F.layer a) :
    factorialBlockMonomial π a x ∈ F.squarefreeAdaptedModule π := by
  classical
  intro c
  rw [factorialBlockMonomial_coefficient]
  by_cases hca : blockDegree π c.val = a
  · rw [if_pos hca]
    refine ⟨?_, ?_⟩
    · rw [hca]
      exact (F.layer a).smul_mem _ hx
    · intro hc
      apply False.elim
      apply ha
      rw [hc, blockDegree_zero] at hca
      exact hca.symm
  · rw [if_neg hca]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

noncomputable def blockLayerMap (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨factorialBlockMonomial π a x.val,
    F.factorialBlockMonomial_mem_adapted π a ha x.val x.property⟩
  map_add' x y := Subtype.ext (map_add (factorialBlockMonomial π a) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (factorialBlockMonomial π a) r x.val)

theorem blockLayerMap_coe (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    (F.blockLayerMap π a ha x).val = factorialBlockMonomial π a x.val := rfl

theorem blockLayerMap_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.blockLayerMap π a ha x ∈ F.squarefreeDegreeLayer π (∑ i, a i) := by
  classical
  intro c hc
  change squarefreePolynomialEquiv (factorialBlockMonomial π a x.val) c = 0
  rw [factorialBlockMonomial_coefficient]
  apply if_neg
  intro hca
  apply hc
  have ht : (∑ i, a i) = ∑ j, c.val j := by
    rw [← hca]
    exact blockDegree_total π c.val
  exact ht.le

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem SquarefreeIndex.permute_one (a : SquarefreeIndex ι) : permute (1 : Equiv.Perm ι) a = a := by
  apply Subtype.ext
  ext i
  rfl

theorem squarefreePermute_one (x : SquarefreePolynomial ι L) :
    squarefreePermute (1 : Equiv.Perm ι) x = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  exact SquarefreeIndex.permute_one a

theorem squarefreePermute_mul (e f : Equiv.Perm ι) (x : SquarefreePolynomial ι L) :
    squarefreePermute (e * f) x = squarefreePermute e (squarefreePermute f x) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient, squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  apply Subtype.ext
  ext i
  rfl

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_one (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π 1 (fun _ => rfl) x = x :=
  Subtype.ext (squarefreePermute_one x.val)

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquarefreeBasisPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeBasis : Basis (Σ a, κ a) ℚ (F.SquarefreeAlgebra π) :=
  (Pi.basis b).map (F.squarefreeAlgebraEquiv π).symm

theorem squarefreeBasis_repr (x : F.SquarefreeAlgebra π) (j : Σ a, κ a) :
    (F.squarefreeBasis π b).repr x j = (b j.1).repr (F.squarefreeAlgebraEquiv π x j.1) j.2 := by
  rfl

theorem squarefreeBasis_coefficient_self (a : SquarefreeIndex ι) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val a = (b a j).val := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) a).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_same]

theorem squarefreeBasis_coefficient_ne (a c : SquarefreeIndex ι) (h : a ≠ c) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val c = 0 := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) c).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem squarefreeBasis_monomial (j : Σ a, κ a) :
    (F.squarefreeBasis π b j).val = squarefreeMonomial j.1 (b j.1 j.2).val := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases h : j.1 = a
  · subst a
    rw [F.squarefreeBasis_coefficient_self, squarefreePolynomialEquiv_monomial_self]
  · rw [F.squarefreeBasis_coefficient_ne π b _ _ h,
      squarefreePolynomialEquiv_monomial_ne _ _ h]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

theorem squarefreeSupport_eq_span (P : SquarefreeIndex ι → Prop) :
    (squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap =
      Submodule.span ℚ (F.squarefreeBasis π b '' {j | P j.1}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx j hj
    have hz : F.squarefreeAlgebraEquiv π x j.1 = 0 := Subtype.ext (hx j.1 hj)
    rw [F.squarefreeBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hx a ha
    have hz : F.squarefreeAlgebraEquiv π x a = 0 := by
      apply (b a).repr.injective
      ext j
      simpa only [F.squarefreeBasis_repr, map_zero, Finsupp.zero_apply] using hx ⟨a, j⟩ ha
    exact congrArg Subtype.val hz

noncomputable def squarefreeSupportedBasis (P : SquarefreeIndex ι → Prop) :
    Basis {j : Σ a, κ a // P j.1} ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) :=
  supportedSubmoduleBasis (F.squarefreeBasis π b) _ _ (F.squarefreeSupport_eq_span π b P)

theorem squarefreeSupportedBasis_coe (P : SquarefreeIndex ι → Prop)
    (j : {j : Σ a, κ a // P j.1}) :
    (F.squarefreeSupportedBasis π b P j).val = F.squarefreeBasis π b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeCoefficientLayer_permute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (a : SquarefreeIndex ι) :
    F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e a) = F.squarefreeCoefficientLayer π a := by
  classical
  simp only [squarefreeCoefficientLayer, SquarefreeIndex.permute_zero_iff,
    SquarefreeIndex.permute_blockDegree π e he a]

theorem squarefreeBasis_permute
    (b : ∀ U : Submodule ℚ L, Basis (Fin (finrank ℚ U)) ℚ U)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (j : Σ a : SquarefreeIndex ι, Fin (finrank ℚ (F.squarefreeCoefficientLayer π a))) :
    ∃ k, F.squarefreeBlockPermute π e he (F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) j) =
      F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) k := by
  have hex : ∃ k,
      (b (F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e j.1)) k).val =
        (b (F.squarefreeCoefficientLayer π j.1) j.2).val := by
    rw [F.squarefreeCoefficientLayer_permute π e he]
    exact ⟨j.2, rfl⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨⟨SquarefreeIndex.permute e j.1, k⟩, ?_⟩
  apply Subtype.ext
  rw [F.squarefreeBlockPermute_apply, F.squarefreeBasis_monomial, squarefreePermute_monomial,
    F.squarefreeBasis_monomial]
  exact congrArg (squarefreeMonomial (SquarefreeIndex.permute e j.1)) hk.symm

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realification_inf {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P Q : Submodule ℚ V) :
    (P ⊓ Q).baseChange ℝ = P.baseChange ℝ ⊓ Q.baseChange ℝ := by
  have hker : LinearMap.ker (P.mkQ.prod Q.mkQ) = P ⊓ Q := by
    ext v
    change (P.mkQ v, Q.mkQ v) = (0, 0) ↔ v ∈ P ∧ v ∈ Q
    rw [Prod.mk.injEq]
    exact and_congr (Submodule.Quotient.mk_eq_zero P) (Submodule.Quotient.mk_eq_zero Q)
  rw [← hker, realification_ker]
  ext v
  rw [LinearMap.mem_ker, realification_prod_eq_zero_iff,
    realification_mkQ_eq_zero_iff, realification_mkQ_eq_zero_iff, Submodule.mem_inf]

theorem lie_mem_real_baseChange {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P Q W : Submodule ℚ L)
    (h : ∀ a ∈ P, ∀ b ∈ Q, ⁅a, b⁆ ∈ W)
    {a b : ℝ ⊗[ℚ] L} (ha : a ∈ P.baseChange ℝ) (hb : b ∈ Q.baseChange ℝ) :
    ⁅a, b⁆ ∈ W.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      change (r * t) ⊗ₜ[ℚ] ⁅(x : L), (y : L)⁆ ∈ W.baseChange ℝ
      exact Submodule.tmul_mem_baseChange_of_mem _ (h x x.property y y.property)
    | add y z hy hz =>
      simpa only [map_add, lie_add] using (W.baseChange ℝ).add_mem hy hz
  | add x z hx hz =>
    simpa only [map_add, add_lie] using (W.baseChange ℝ).add_mem hx hz

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def bracketSystemMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (k : κ → L) : Matrix (κ × ι) ν ℚ :=
  fun bi n => f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2

noncomputable def realBracketSystem (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ × ι → ℝ) :=
  LinearMap.pi (fun bi => ((f.baseChange ℝ).coord bi.2).comp
    ((V.mkQ.baseChange ℝ).comp
      ({
        toFun := fun x => ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆
        map_add' := fun x y => add_lie x y _
        map_smul' := fun r x => smul_lie r x _ } :
          (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))))

@[simp] theorem realBracketSystem_apply (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) (bi : κ × ι) :
    realBracketSystem f k x bi =
      (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆) bi.2 := rfl

noncomputable def bracketSystemLift [Fintype ν] (e : Basis ν ℚ E) :
    (ν → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (E.subtype.baseChange ℝ).comp (e.baseChange ℝ).equivFun.symm.toLinearMap

theorem bracketSystemLift_mem [Fintype ν] (e : Basis ν ℚ E) (x : ν → ℝ) :
    bracketSystemLift e x ∈ E.baseChange ℝ := ⟨(e.baseChange ℝ).equivFun.symm x, rfl⟩

theorem bracketSystemLift_single [Fintype ν] [DecidableEq ν] (e : Basis ν ℚ E) (n : ν) :
    bracketSystemLift e (Pi.single n 1) = (1 : ℝ) ⊗ₜ[ℚ] (e n : L) := by
  simp [bracketSystemLift, Basis.equivFun_symm_apply]

theorem bracketSystemMatrix_real_apply [Fintype ν] (e : Basis ν ℚ E)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (x : ν → ℝ) :
    (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) *ᵥ x =
      realBracketSystem f k (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) =
      (realBracketSystem f k).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 =
      realBracketSystem f k (bracketSystemLift e (Pi.single n 1))
    rw [bracketSystemLift_single]
    change Matrix.of (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 = _
    rw [Matrix.mulVec_single_one]
    funext bi
    rw [realBracketSystem_apply, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    change (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2 : ℝ) =
      (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2) • (1 : ℝ)
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

theorem realBracketSystem_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    realBracketSystem f k x = 0 ↔ ∀ b, ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  constructor
  · intro h b
    apply (realification_mkQ_eq_zero_iff V _).mp
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realBracketSystem_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h (b, i)
  · intro h
    funext bi
    rw [realBracketSystem_apply, (realification_mkQ_eq_zero_iff V _).mpr (h bi.1)]
    rfl

theorem lie_bracket_coordinate_height {α : Type*} [Fintype α] (b : Basis α ℚ L)
    {H A B : ℕ} (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (x y : L) (hx : ∀ i, RationalHeightLE (b.repr x i) A)
    (hy : ∀ i, RationalHeightLE (b.repr y i) B) (n : α) :
    RationalHeightLE (b.repr ⁅x, y⁆ n)
      ((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ij : α × α => lieStructureConstants b ij.1 ij.2 n * b.repr x ij.1 * b.repr y ij.2)
    (fun ij => ((hbr ij.1 ij.2 n).mul (hx ij.1)).mul (hy ij.2))
  simpa only [Fintype.card_prod, ← pow_two] using h

theorem bracketSystemMatrix_height {α : Type*} [Fintype α]
    (b : Basis α ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H A B C : ℕ}
    (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) A)
    (hk : ∀ t i, RationalHeightLE (b.repr (k t) i) B)
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) C) (bi : κ × ι) (n : ν) :
    RationalHeightLE (bracketSystemMatrix e f k bi n)
      ((Fintype.card α + 1) *
        (((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) * C) ^
          Fintype.card α) :=
  linearMap_coordinate_height b f V.mkQ hq _
    (lie_bracket_coordinate_height b hbr (e n : L) (k bi.1) (he n) (hk bi.1)) bi.2

end Erdos3

end

section

namespace Erdos3

open Module

def squarefreeBracketHeight (n H : ℕ) : ℕ := (n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)

theorem squarefreeBracketHeight_pos (n : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < squarefreeBracketHeight n H := by
  have hHpos : 0 < H := by omega
  unfold squarefreeBracketHeight
  positivity

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_bracket_coefficient_height (x y : Σ a, κ a) (a : SquarefreeIndex ι) (k : ν) :
    RationalHeightLE (e.repr
      (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  rw [F.squarefreeAlgebraEquiv_apply]
  change RationalHeightLE (e.repr (squarefreePolynomialEquiv
    ⁅(F.squarefreeBasis π b x).val, (F.squarefreeBasis π b y).val⁆ a) k) _
  rw [F.squarefreeBasis_monomial, F.squarefreeBasis_monomial]
  by_cases hxy : Disjoint x.1.val.support y.1.val.support
  · rw [squarefreeMonomial_lie_disjoint x.1 y.1 hxy]
    by_cases ha : x.1.disjointAdd y.1 hxy = a
    · subst a
      rw [squarefreePolynomialEquiv_monomial_self]
      exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
    · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)
  · rw [squarefreeMonomial_lie_overlap _ _ hxy, map_zero, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialCoordinateRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem rowPolynomial_single {K : Type*} [Fintype K] (k : K) :
    rowPolynomial (Pi.single k (1 : ℤ)) = MvPolynomial.X k := by
  simp [rowPolynomial, Pi.single_apply]

theorem exists_monomial_coordinate_rows {K : Type*} [Fintype K]
    (d : K →₀ ℕ) {h : ℕ} (hd : d.degree = h) :
    ∃ rows : Fin h → K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ 1) ∧
      (∏ i, rowPolynomial (rows i)) = MvPolynomial.monomial d 1 := by
  have hlen : d.toMultiset.toList.length = h := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hd
  rcases hlen with rfl
  let indices : Fin d.toMultiset.toList.length → K := fun i => d.toMultiset.toList[i.val]
  refine ⟨fun i => Pi.single (indices i) 1, ?_, ?_⟩
  · intro i k
    by_cases he : indices i = k <;> simp [he]
  · simp only [rowPolynomial_single]
    change (∏ i : Fin d.toMultiset.toList.length,
      (MvPolynomial.X d.toMultiset.toList[i.val] : MvPolynomial K ℤ)) = _
    rw [Fin.prod_univ_fun_getElem, Multiset.prod_map_toList]
    rw [Finset.prod_multiset_map_count]
    simpa only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset] using
      (MvPolynomial.prod_X_pow_eq_monomial (R := ℤ) (s := d))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleSmooth (N : ℕ) (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).smooth N (iteratedCircleSmooth N A is f)

theorem iteratedCircleSmooth_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (iteratedCircleSmooth N A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).smooth_lipschitz hN ih

theorem iteratedCircleSmooth_error {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0} {ε : ℝ}
    (hf : LipschitzWith L f)
    (hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ x,
      ‖(A i).smooth N g x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleSmooth N A is f x - f x‖ ≤ is.length * ε := by
  induction is with
  | nil => simp [iteratedCircleSmooth]
  | cons i is ih =>
    have ht := ih (fun j hj => hstep j (List.mem_cons_of_mem i hj))
    have hs := hstep i (List.mem_cons_self) (iteratedCircleSmooth N A is f)
      (iteratedCircleSmooth_lipschitz hN A is hf) x
    change ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - f x‖ ≤ _
    calc
      _ ≤ ‖(A i).smooth N (iteratedCircleSmooth N A is f) x - iteratedCircleSmooth N A is f x‖ +
          ‖iteratedCircleSmooth N A is f x - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + is.length * ε := add_le_add hs ht
      _ = (i :: is).length * ε := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleComponent (N : ℕ) (A : α → IsometricCircleAction X) :
    (is : List α) → (Fin is.length → ℤ) → (X → ℂ) → X → ℂ
  | [], _, f => f
  | i :: is, k, f => (A i).component N (k 0)
      (iteratedCircleComponent N A is (fun j => k j.succ) f)

theorem iteratedCircleComponent_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleComponent N A is k f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_lipschitz hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_norm_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleComponent N A is k f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_norm_le hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_character (N : ℕ)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : Fin is.length) : ∀ (t : Circle) x,
    iteratedCircleComponent N A is k f ((A (is.get j)).act t x) =
      character ((-k j) • t) * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact Fin.elim0 j
  | cons i is ih =>
    have ht : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
      fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b (List.mem_cons_of_mem i hb)
    refine Fin.cases ?_ (fun q => ?_) j
    · exact (A i).component_character N (k 0) (iteratedCircleComponent N A is (fun q => k q.succ) f)
    · have hm : is.get q ∈ is := List.get_mem is q
      exact (A i).component_preserves_character (A (is.get q))
        (hcomm i (List.mem_cons_self) (is.get q) (List.mem_cons_of_mem i hm))
        N (k 0) (-(k q.succ)) (ih (fun r => k r.succ) ht q)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

abbrev FejerChoice (N : ℕ) := ↥(fejerFrequencies N)

theorem sum_fin_tuple_cons {β : Type*} [Fintype β] (n : ℕ) (f : (Fin (n + 1) → β) → ℂ) :
    ∑ k, f k = ∑ b : β, ∑ k : Fin n → β, f (Fin.cons b k) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => β)).sum_comp f]
  exact Fintype.sum_prod_type _

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleSmooth_eq_sum {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) :
    iteratedCircleSmooth N A is f x =
      ∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x := by
  classical
  induction is generalizing x with
  | nil => simp [iteratedCircleSmooth, iteratedCircleComponent]
  | cons i is ih =>
    have ht : iteratedCircleSmooth N A is f = fun y =>
        ∑ k : Fin is.length → FejerChoice N,
          iteratedCircleComponent N A is (fun j => (k j : ℤ)) f y := funext ih
    change (A i).smooth N (iteratedCircleSmooth N A is f) x = _
    rw [ht, (A i).smooth_eq_sum]
    apply Eq.trans ?_ (sum_fin_tuple_cons is.length (fun k : Fin (is.length + 1) → FejerChoice N =>
      iteratedCircleComponent N A (i :: is) (fun j => (k j : ℤ)) f x)).symm
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    rw [(A i).component_sum N (b : ℤ) Finset.univ
      (fun k : Fin is.length → FejerChoice N =>
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f)
      (fun k _ => (iteratedCircleComponent_lipschitz hN A is (fun j => (k j : ℤ)) hf).continuous) x]
    apply Finset.sum_congr rfl
    intro k _
    rfl

theorem card_fejerChoices (N d : ℕ) :
    Fintype.card (Fin d → FejerChoice N) ≤ N ^ (2 * d) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  apply (Nat.pow_le_pow_left (card_fejerFrequencies_le N) d).trans_eq
  rw [pow_mul]

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier
open MeasureTheory
open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

namespace IsometricCircleAction

theorem component_sub (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.component N h (fun y => f y - g y) x =
      A.component N h f x - A.component N h g x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  change (fejerCoefficient N h : ℂ) *
    (∫ t : Circle, character ((-(-h)) • t) * (f (t +ᵥ x) - g (t +ᵥ x)) ∂circleHaar) = _
  simp_rw [mul_sub]
  rw [integral_sub (integrable_circleFourierComponent (-h) hf x)
    (integrable_circleFourierComponent (-h) hg x)]
  exact mul_sub _ _ _

theorem component_norm_sub_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) {ε : ℝ}
    (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖A.component N h f x - A.component N h g x‖ ≤ ε := by
  rw [← A.component_sub N h hf hg x]
  let := A.toAddAction
  change ‖(fejerCoefficient N h : ℂ) *
    circleFourierComponent (-h) (fun y => f y - g y) x‖ ≤ ε
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h)
    (norm_circleFourierComponent_le (-h) _ hfg x) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

end IsometricCircleAction

theorem iteratedCircleComponent_norm_sub_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f g : X → ℂ} {K H : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith H g)
    {ε : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleComponent N A is k f x - iteratedCircleComponent N A is k g x‖ ≤ ε := by
  induction is generalizing x with
  | nil => exact hfg x
  | cons i is ih =>
    apply (A i).component_norm_sub_le hN (k 0)
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hf).continuous
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hg).continuous
    intro y
    exact ih (fun j => k j.succ) y

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleComponent_equivariant (N : ℕ) (A : α → IsometricCircleAction X)
    (is : List α) (k : Fin is.length → ℤ) (g : X → X) (z : ℂ)
    (hg : ∀ i ∈ is, ∀ t x, (A i).act t (g x) = g ((A i).act t x))
    {f : X → ℂ} (hf : ∀ x, f (g x) = z * f x) :
    ∀ x, iteratedCircleComponent N A is k f (g x) = z * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    exact (A i).component_equivariant N (k 0) g z (hg i List.mem_cons_self)
      (ih (fun j => k j.succ) (fun a ha => hg a (List.mem_cons_of_mem i ha)))

theorem exists_controlled_finite_circle_decomposition
    (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i ∈ is, ∀ (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (is.length : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) ∧
      (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ k : Fin is.length → FejerChoice N,
        (∀ j, (|(k j : ℤ)| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
        LipschitzWith L (iteratedCircleComponent N A is (fun j => (k j : ℤ)) f) ∧
        (∀ x, ‖iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x‖ ≤ B) ∧
        ∀ (j : Fin is.length) (t : Circle) x,
          iteratedCircleComponent N A is (fun r => (k r : ℤ)) f ((A (is.get j)).act t x) =
            character ((-(k j : ℤ)) • t) *
              iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) ∧
      ∀ x, ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun j => (k j : ℤ)) f x) - f x‖ ≤ δ := by
  let O : ℝ := (L : ℝ) * D
  have hO : 0 ≤ O := mul_nonneg L.coe_nonneg D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul hLp hDp D.coe_nonneg (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  refine ⟨N, hN, hNe, ?_, ?_, ?_⟩
  · apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity))
  · intro k
    refine ⟨?_, iteratedCircleComponent_lipschitz hN A is _ hf,
      iteratedCircleComponent_norm_le hN A is _ hb, ?_⟩
    · intro j
      have hk : (|(k j : ℤ)| : ℝ) < N := by
        exact_mod_cast abs_lt_of_mem_fejerFrequencies (k j).property
      exact hk.le.trans hNe
    · exact fun j => iteratedCircleComponent_character N A is _ hcomm f j
  · intro x
    rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
    have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
        ‖(A i).smooth N g y - g y‖ ≤ ε := by
      intro i hi g hg y
      have hη : 0 < ε / (2 * (O + 1)) := by positivity
      apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
        (fejer_error_le_of_cutoff hO hε hN hcut)
      intro t z
      rw [← dist_eq_norm]
      exact (hg.dist_le_mul _ _).trans ((mul_le_mul_of_nonneg_left (horbit i hi t z) L.coe_nonneg).trans_eq
        (by dsimp [O]; ring))
    apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
    change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_controlled_commuting_circle_decomposition
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (v : J → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j, LipschitzWith L (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j i (t : Circle) x, v j ((A i).act t x) = character (ν j i • t) * v j x) ∧
      (∀ (g : X → X) (z : ℂ),
        (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
        (∀ x, f (g x) = z * f x) → ∀ j x, v j (g x) = z * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  obtain ⟨N, _, _, hcard, hprops, herr⟩ := exists_controlled_finite_circle_decomposition A is
    (fun i _ j _ => hcomm i j) f L B D hf hb (fun i _ => horbit i)
    δ p hδ hp hd' hLp hDp hδp
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let v : J → X → ℂ := fun k => iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, v, hcard, ?_, ?_, ?_, ?_, herr⟩
  · intro k i
    simpa only [ν, Int.cast_neg, abs_neg] using (hprops k).1 (index i)
  · intro k
    exact ⟨(hprops k).2.1, (hprops k).2.2.1⟩
  · intro k i t x
    have hi := (hprops k).2.2.2 (index i) t x
    rw [hindex i] at hi
    exact hi
  · intro g z hg hf k x
    exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
      g z (fun i _ => hg i) hf x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_uniform_controlled_commuting_circle_operators
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (D : ℝ≥0)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (V : J → (X → ℂ) → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j (f g : X → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : X → ℂ) (L B : ℝ≥0), LipschitzWith L f → (∀ x, ‖f x‖ ≤ B) →
        (L : ℝ) ≤ Real.exp p →
          (∀ j, LipschitzWith L (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
          (∀ j i (t : Circle) x, V j f ((A i).act t x) = character (ν j i • t) * V j f x) ∧
          (∀ (g : X → X) (z : ℂ),
            (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
            (∀ x, f (g x) = z * f x) → ∀ j x, V j f (g x) = z * V j f x) ∧
          ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  let O : ℝ := Real.exp p * D
  have hO : 0 ≤ O := mul_nonneg (Real.exp_nonneg _) D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hDp (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  have hcard : (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤
      Real.exp (2 * p * (2 * p + 2) ^ 4) := by
    apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd' (by norm_num)) (by positivity))
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let V : J → (X → ℂ) → X → ℂ := fun k f =>
    iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, V, hcard, ?_, ?_, ?_⟩
  · intro k i
    have hk : (|(k (index i) : ℤ)| : ℝ) < N := by
      exact_mod_cast abs_lt_of_mem_fejerFrequencies (k (index i)).property
    simpa only [ν, Int.cast_neg, abs_neg] using hk.le.trans hNe
  · intro k f g K H hf hg ε hfg x
    exact iteratedCircleComponent_norm_sub_le hN A is (fun r => (k r : ℤ)) hf hg hfg x
  · intro f L B hf hb hLp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact ⟨iteratedCircleComponent_lipschitz hN A is _ hf,
        iteratedCircleComponent_norm_le hN A is _ hb⟩
    · intro k i t x
      have hi := iteratedCircleComponent_character N A is (fun r => (k r : ℤ))
        (fun a _ b _ => hcomm a b) f (index i) t x
      rw [hindex i] at hi
      exact hi
    · intro g z hg hfz k x
      exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
        g z (fun i _ => hg i) hfz x
    · intro x
      change ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) - f x‖ ≤ δ
      rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
      have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
          ‖(A i).smooth N g y - g y‖ ≤ ε := by
        intro i _ g hg y
        have hη : 0 < ε / (2 * (O + 1)) := by positivity
        apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
          (fejer_error_le_of_cutoff hO hε hN hcut)
        intro t z
        rw [← dist_eq_norm]
        calc
          dist (g ((A i).act t z)) (g z) ≤ L * dist ((A i).act t z) z := hg.dist_le_mul _ _
          _ ≤ L * (D * ‖t‖) := mul_le_mul_of_nonneg_left (horbit i t z) L.coe_nonneg
          _ ≤ Real.exp p * (D * ‖t‖) :=
            mul_le_mul_of_nonneg_right hLp (mul_nonneg D.coe_nonneg (norm_nonneg _))
          _ = O * ‖t‖ := by dsimp [O]; ring
      apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
      change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

noncomputable def piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) : Subgroup (NilpotentLieFiltration.pi F).Group :=
  ⨅ a, (Δ a).comap (map (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a))

theorem mem_piBCHSubgroup (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (g : (NilpotentLieFiltration.pi F).Group) :
    g ∈ piBCHSubgroup F Δ ↔ ∀ a, (⟨g.coord a⟩ : (F a).Group) ∈ Δ a := by
  simp only [piBCHSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]

theorem pi_basis_equivFun_symm_apply (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : (Σ a, κ a) → ℚ) (a : α) :
    (Pi.basis f).equivFun.symm x a = (f a).equivFun.symm (fun i => x ⟨a, i⟩) := by
  apply (f a).equivFun.injective
  funext i
  change (Pi.basis f).equivFun ((Pi.basis f).equivFun.symm x) ⟨a, i⟩ = _
  simp only [LinearEquiv.apply_symm_apply]

theorem piBCHSubgroup_coordinates (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group)
    (x : (Σ a, κ a) → ℚ) :
    x ∈ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ↔
      ∀ a, (fun i => x ⟨a, i⟩) ∈ bchSubgroupCoordinates (f a) (Δ a) := by
  change (⟨(Pi.basis f).equivFun.symm x⟩ : (NilpotentLieFiltration.pi F).Group) ∈
    piBCHSubgroup F Δ ↔ _
  rw [mem_piBCHSubgroup]
  simp only [pi_basis_equivFun_symm_apply, bchSubgroupCoordinates, Set.mem_ofPred_eq]

theorem piBCHSubgroup_inner_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hin : ∀ a, scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Δ a)) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) := by
  rintro x ⟨z, rfl⟩
  apply (piBCHSubgroup_coordinates F f Δ _).mpr
  intro a
  exact hin a ⟨fun i => z ⟨a, i⟩, rfl⟩

theorem piBCHSubgroup_outer_grid (F : ∀ a, NilpotentLieFiltration (M a) s)
    (f : ∀ a, Basis (κ a) ℚ (M a)) (Δ : ∀ a, Subgroup (F a).Group) (m : ℕ)
    (hout : ∀ a, bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid m) :
    bchSubgroupCoordinates (Pi.basis f) (piBCHSubgroup F Δ) ⊆ denominatorGrid m := by
  intro x hx
  have h := (piBCHSubgroup_coordinates F f Δ x).mp hx
  choose z hz using fun a => hout a (h a)
  exact ⟨fun i => z i.1 i.2, fun i => hz i.1 i.2⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

def liePiSingle (a : α) : M a →ₗ⁅ℚ⁆ (∀ a, M a) where
  toLinearMap := LinearMap.single ℚ M a
  map_lie' {x y} := by
    ext i
    change Pi.single a ⁅x, y⁆ i = ⁅Pi.single a x i, Pi.single a y i⁆
    by_cases hi : i = a
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hi, lie_zero]

noncomputable def bchPiEquiv (F : ∀ a, NilpotentLieFiltration (M a) s) :
    (NilpotentLieFiltration.pi F).Group ≃* (∀ a, (F a).Group) where
  toFun g a := ⟨g.coord a⟩
  invFun g := ⟨fun a => (g a).coord⟩
  left_inv g := by cases g; rfl
  right_inv g := by funext a; exact NilpotentLieBCHGroup.ext rfl
  map_mul' g h := by
    funext a
    exact (map (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a)).map_mul g h

noncomputable def bchPiSingle (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) :
    (F a).Group →* (NilpotentLieFiltration.pi F).Group :=
  map (hnil := (F a).lowerCentralSeries_eq_bot)
    (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiSingle a)

theorem bchPiEquiv_single (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) (g : (F a).Group) :
    bchPiEquiv F (bchPiSingle F a g) = Pi.mulSingle a g := by
  funext i
  apply NilpotentLieBCHGroup.ext
  change Pi.single a g.coord i = ((Pi.mulSingle a g : ∀ i, (F i).Group) i).coord
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · simp only [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, coord_one]

theorem bchPiSingle_eq_symm_mulSingle (F : ∀ a, NilpotentLieFiltration (M a) s)
    (a : α) (g : (F a).Group) :
    bchPiSingle F a g = (bchPiEquiv F).symm (Pi.mulSingle a g) := by
  apply (bchPiEquiv F).injective
  rw [bchPiEquiv_single, MulEquiv.apply_symm_apply]

theorem piBCHSubgroup_le_of_factors [Finite α] (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (h : ∀ a, Δ a ≤ Λ.comap (bchPiSingle F a)) : piBCHSubgroup F Δ ≤ Λ := by
  intro g hg
  let Λ' := Λ.comap (bchPiEquiv F).symm.toMonoidHom
  have hp : bchPiEquiv F g ∈ Λ' := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro a
    change (bchPiEquiv F).symm (Pi.mulSingle a (bchPiEquiv F g a)) ∈ Λ
    rw [← bchPiSingle_eq_symm_mulSingle]
    exact h a ((mem_piBCHSubgroup F Δ g).mp hg a)
  simpa only [Λ', Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hp

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
  [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}
  (F : ∀ a, NilpotentLieFiltration (M a) s)
  {κ : α → Type*} [∀ a, Fintype (κ a)] (f : ∀ a, Basis (κ a) ℚ (M a))

theorem bchPiSingle_comap_inner_grid (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (m : ℕ) (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ) (a : α) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Λ.comap (bchPiSingle F a)) := by
  classical
  rintro x ⟨z, rfl⟩
  change bchPiSingle F a ⟨(f a).equivFun.symm ((m : ℚ) • fun i => (z i : ℚ))⟩ ∈ Λ
  apply (bchSubgroupCoordinates_repr (Pi.basis f) Λ _).mp
  apply hΛ
  refine ⟨fun i : Σ a, κ a => (Pi.single a z : ∀ a, κ a → ℤ) i.1 i.2, ?_⟩
  ext ⟨i, j⟩
  change (f i).repr (Pi.single a ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) i) j = _
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    change (f a).equivFun ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) j = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · simp only [Pi.single_eq_of_ne hi, map_zero, Finsupp.zero_apply, Pi.zero_apply,
      Int.cast_zero, Pi.smul_apply, smul_eq_mul, mul_zero]

theorem exists_factorwise_bch_covers (Γ : ∀ a, Subgroup (F a).Group) (l : α → ℕ)
    (hl : ∀ a, 0 < l a)
    (hΓin : ∀ a, scaledIntegerGrid (l a) ⊆ bchSubgroupCoordinates (f a) (Γ a))
    (hΓout : ∀ a, bchSubgroupCoordinates (f a) (Γ a) ⊆ denominatorGrid (l a))
    (Λ : Subgroup (NilpotentLieFiltration.pi F).Group) (m : ℕ) (hm : 0 < m)
    (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ)
    {p : ℝ} (hp : 0 ≤ p) (hd : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p)
    (hlp : ∀ a, (l a : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p) :
    ∃ (Δ : ∀ a, Subgroup (F a).Group) (N : α → ℕ),
      (∀ a, Δ a ≤ Γ a ∧ ((Δ a).subgroupOf (Γ a)).Characteristic ∧
        ((Δ a).subgroupOf (Γ a)).Normal ∧ ((Δ a).subgroupOf (Γ a)).FiniteIndex ∧
        ((Δ a).relIndex (Γ a) : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
        0 < N a ∧ (N a : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid (N a) ⊆ bchSubgroupCoordinates (f a) (Δ a) ∧
        bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid (N a)) ∧
      piBCHSubgroup F Δ ≤ Λ := by
  have h := fun a => (F a).exists_normal_cover_exp_quadratic (f a) (Γ a)
    (Λ.comap (bchPiSingle F a)) (l a) m (hl a) hm (hΓin a) (hΓout a)
    (bchPiSingle_comap_inner_grid F f Λ m hΛ a) hp (hd a) (hlp a) hmp
  choose Δ htarget hΔ hchar hnormal hfinite hindex N hN hNb hin hout using h
  exact ⟨Δ, N, fun a => ⟨hΔ a, hchar a, hnormal a, hfinite a, hindex a,
    hN a, hNb a, hin a, hout a⟩, piBCHSubgroup_le_of_factors F Δ Λ htarget⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTopDegree
namespace OAI

section

namespace Erdos3

noncomputable def SquarefreeIndex.full (ι : Type*) [Fintype ι] : SquarefreeIndex ι :=
  ⟨Finsupp.equivFunOnFinite.symm (fun _ => 1), fun _ => le_rfl⟩

theorem SquarefreeIndex.full_apply {ι : Type*} [Fintype ι] (i : ι) :
    (full ι).val i = 1 := rfl

theorem SquarefreeIndex.one_le_iff {ι : Type*} [Fintype ι] (a : SquarefreeIndex ι) :
    (fun _ => 1) ≤ (fun i => a.val i) ↔ a = full ι := by
  constructor
  · intro h
    apply Subtype.ext
    ext i
    exact le_antisymm (a.property i) (h i)
  · rintro rfl
    intro i
    exact le_rfl

theorem SquarefreeIndex.permute_full {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    permute e (full ι) = full κ := by
  apply Subtype.ext
  ext j
  rfl

theorem squarefree_top_monomial {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (x : SquarefreePolynomial ι L)
    (hx : x ∈ squarefreeSupportModule (fun a : SquarefreeIndex ι => (fun _ => 1) ≤ fun i => a.val i)) :
    x = squarefreeMonomial (SquarefreeIndex.full ι)
      (squarefreePolynomialEquiv x (SquarefreeIndex.full ι)) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases ha : SquarefreeIndex.full ι = a
  · subst a
    rw [squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha]
    exact hx a (fun h => ha ((SquarefreeIndex.one_le_iff a).mp h).symm)

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_eq_self_top (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) (hx : x ∈ F.squarefreeMultidegreeLayer π (fun _ => 1)) :
    F.squarefreeBlockPermute π e he x = x := by
  apply Subtype.ext
  change squarefreePermute e x.val = x.val
  rw [squarefree_top_monomial x.val hx, squarefreePermute_monomial, SquarefreeIndex.permute_full]

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AdaptedBasisGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem inverse_basis_entries_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H) :
    ∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix b e (LinearMap.id : L →ₗ[ℚ] L)
  let C := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  have hli : LinearIndependent ℚ A.col :=
    Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e LinearMap.id Function.injective_id)
  obtain ⟨P, hPA, hPH⟩ := exists_bounded_rational_left_inverse A hli hH hA
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hPC : P = C := by
    calc
      P = P * 1 := (Matrix.mul_one P).symm
      _ = P * (A * C) := by rw [hAC]
      _ = (P * A) * C := (Matrix.mul_assoc P A C).symm
      _ = C := by rw [hPA, Matrix.one_mul]
  intro i j
  have h := hPH j i
  rw [hPC] at h
  simpa only [C, LinearMap.toMatrix_apply, LinearMap.id_apply] using h

theorem basis_change_structure_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
      (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  classical
  obtain ⟨_, _, _, h⟩ := exists_bounded_lie_embedding_retraction b e
    (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hb j i)
  exact h

theorem exists_basis_change_grid_exp_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  have hid : NilpotentLieBCHGroup.map (hnil := hnil) (hM := hnil)
      (LieHom.id : L →ₗ⁅ℚ⁆ L) = MonoidHom.id _ := by
    ext g
    rfl
  simpa only [hid, Subgroup.comap_id] using exists_bchSubgroup_comap_grid_exp_bound
    (hM := hnil) b e (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id Γ hH hl
      (by intro i j; rw [LinearMap.toMatrix_apply]; exact hb j i)
      hinner houter hp hd hr hHp hlp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_adapted_basis_and_grid {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (Γ : Subgroup F.Group) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, RationalHeightLE (e.repr (b j) i) H) ∧
      (∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (finrank ℚ L) H)) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11)) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  obtain ⟨b, w, hw, _, hcentral, hb, hlayer⟩ := F.exists_bounded_sorted_adapted_basis e v hspan hv
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ :=
    exists_basis_change_grid_exp_bound e b Γ hH hl hb hinner houter hp hd hr hHp hlp
  have hbinv := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb hc
  have hbudget := rationalLieStructureHeight_inverse_budget (Fintype.card ι)
    (Fintype.card (Fin (finrank ℚ L))) H hp hd hr hHp
  refine ⟨b, w, N, hw, hcentral, hlayer, hb, ?_, ?_, hN, hNp, hin, hout⟩
  · simpa only [Fintype.card_fin] using hbinv
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hstructure i j k).1).trans hbudget,
      (Nat.cast_le.mpr (hstructure i j k).2).trans hbudget⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridMass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) : ℝ :=
  finiteImageMass p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

noncomputable def integerGridCoefficient {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) : ℂ :=
  p.complexMean (fun x => rectangularGridCharacter M k (Y x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerGridDensity {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) (z : J → ℤ) : ℝ :=
  (K : ℝ) ^ Fintype.card J * integerGridMass p Y M z

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

open scoped BigOperators

def integerBooleanBlockValue {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) : ℤ :=
  ∏ g, ∑ r, (booleanFeature r t : ℤ) * x g r

noncomputable def integerBooleanBlockJet {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) : ℤ :=
  booleanCoefficient (integerBooleanBlockValue x) S

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

noncomputable def weightedCubeIntegerSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b j, IntegerScalarCubeBox I (s b j).length) :=
  FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedModerateIntegerSource {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (IntegerScalarCubeBox Empty c.length ×
      (∀ j, IntegerScalarCubeBox I (s j).length)) :=
  c.source.prod (FiniteProbabilityWeights.pi (fun j => (s j).source))

noncomputable def weightedModerateIntegerProductSource {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I) :
    FiniteProbabilityWeights (∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :=
  FiniteProbabilityWeights.pi (fun b => weightedModerateIntegerSource (c b) (s b))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
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

open scoped BigOperators
open CircleFourier

noncomputable def affineWeightedCubeGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean (fun z => character
    ((booleanBlockPhase (gridJetFrequency M J k)
      (fun j => affineCubeCoordinates (u j) (v j) (fun i => (z j i : ℝ))) : ℝ) : CircleFourier.Circle))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineWeightedCubeIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (u : Fin (n + 1) → Option I → ℤ)
    (v : Fin (n + 1) → Option I → ℕ) (J : Finset (Finset I))
    (x : ∀ j, IntegerScalarCubeBox I (s j).length) : J → ℤ :=
  fun S => integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun i => (x j i : ℤ))) S

noncomputable def affineWeightedCubeIntegerSum {B : Type*} [Fintype B] {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (J : Finset (Finset I)) (shift : J → ℤ)
    (x : ∀ b j, IntegerScalarCubeBox I (s b j).length) : J → ℤ :=
  shift + ∑ b, affineWeightedCubeIntegerBlock (s b) (u b) (v b) J (x b)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def integerGridApproximation {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ℤ) : ℂ :=
  ((K : ℂ) / M) ^ Fintype.card J * ∑ k ∈ S, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
variable (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)

noncomputable def affineCubePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v rows shift) K M F z

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SaturatedFlag
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.SaturatedFlag

open scoped BigOperators
open Function _root_.Set Submodule
open Module

variable {M : Type*} [AddCommGroup M]

def IsSaturated (P : Submodule ℤ M) : Prop :=
  ∀ (a : ℤ) (x : M), a ≠ 0 → a • x ∈ P → x ∈ P

@[simp] theorem isSaturated_bot [Module.IsTorsionFree ℤ M] :
    IsSaturated (⊥ : Submodule ℤ M) := by
  intro a x ha hx
  rw [Submodule.mem_bot] at hx ⊢
  exact (smul_eq_zero.mp hx).resolve_left ha

@[simp] theorem isSaturated_top : IsSaturated (⊤ : Submodule ℤ M) := by
  intro _ _ _ _
  exact Submodule.mem_top

theorem IsSaturated.comap_subtype {P O : Submodule ℤ M}
    (hP : IsSaturated P) (_hPO : P ≤ O) :
    IsSaturated (P.comap O.subtype) := by
  intro a x ha hx
  change (a • (x : M)) ∈ P at hx
  change (x : M) ∈ P
  exact hP a x ha hx

def rationalEmbed (d : ℕ) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℚ) where
  toFun x i := (x i : ℚ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp] theorem rationalEmbed_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    rationalEmbed d x i = (x i : ℚ) := rfl

def rationalSpanLattice {d : ℕ} (S : Set (Fin d → ℤ)) :
    Submodule ℤ (Fin d → ℤ) :=
  ((Submodule.span ℚ (rationalEmbed d '' S)).restrictScalars ℤ).comap
    (rationalEmbed d)

@[simp] theorem mem_rationalSpanLattice {d : ℕ} {S : Set (Fin d → ℤ)}
    {x : Fin d → ℤ} :
    x ∈ rationalSpanLattice S ↔
      rationalEmbed d x ∈ Submodule.span ℚ (rationalEmbed d '' S) :=
  Iff.rfl

def realEmbed (d : ℕ) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp] theorem realEmbed_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    realEmbed d x i = (x i : ℝ) := rfl

theorem realEmbed_zsmul {d : ℕ} (a : ℤ) (x : Fin d → ℤ) :
    realEmbed d (a • x) = (a : ℝ) • realEmbed d x := by
  ext i
  simp [realEmbed]

def realPrefixLattice {d n : ℕ} (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    Submodule ℤ (Fin d → ℤ) :=
  ((Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).restrictScalars ℤ).comap
    (realEmbed d)

@[simp] theorem mem_realPrefixLattice {d n : ℕ}
    {x : Fin n → (Fin d → ℤ)} {i : Fin n} {z : Fin d → ℤ} :
    z ∈ realPrefixLattice x i ↔
      realEmbed d z ∈
        Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) :=
  Iff.rfl

theorem isSaturated_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    IsSaturated (realPrefixLattice x i) := by
  intro a z ha hz
  rw [mem_realPrefixLattice] at hz ⊢
  have haz : (a : ℝ) • realEmbed d z ∈
      Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) := by
    rw [← realEmbed_zsmul]
    exact hz
  have hinv :=
    (Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).smul_mem
      (a : ℝ)⁻¹ haz
  simpa [smul_smul, ha] using hinv

theorem monotone_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) : Monotone (realPrefixLattice x) := by
  intro i j hij z hz
  rw [mem_realPrefixLattice] at hz ⊢
  apply Submodule.span_mono (Set.image_mono (Set.image_mono ?_)) hz
  intro k hk
  exact hk.trans hij

theorem self_mem_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    x i ∈ realPrefixLattice x i := by
  rw [mem_realPrefixLattice]
  apply Submodule.subset_span
  exact ⟨x i, ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩, rfl⟩

section Smith

variable {ι : Type*} [Finite ι]

omit [Finite ι] in

theorem smithVector_mem_of_isSaturated (_b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) {n : ℕ}
    (snf : Basis.SmithNormalForm P ι n) (i : Fin n) :
    snf.bM (snf.f i) ∈ P := by
  classical
  have hai : snf.a i ≠ 0 := by
    intro hai
    apply (snf.bN.ne_zero i)
    apply Subtype.ext
    simp [snf.snf i, hai]
  exact hP (snf.a i) (snf.bM (snf.f i)) hai <| by
    simpa [snf.snf i] using (snf.bN i).property

theorem exists_isCompl_of_isSaturated (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) :
    ∃ Q : Submodule ℤ M, IsCompl P Q := by
  classical
  let snf := P.smithNormalForm b
  let selected : Set ι := Set.range snf.2.f
  let Q : Submodule ℤ M :=
    Submodule.span ℤ (snf.2.bM '' selectedᶜ)
  have hselected :
      P = Submodule.span ℤ (snf.2.bM '' selected) := by
    apply le_antisymm
    · intro x hx
      let xp : P := ⟨x, hx⟩
      have hxp : xp ∈ Submodule.span ℤ (Set.range snf.2.bN) := by
        rw [snf.2.bN.span_eq]
        exact Submodule.mem_top
      exact Submodule.span_induction (R := ℤ) (s := Set.range snf.2.bN)
        (p := fun y _ ↦ (y : M) ∈
          Submodule.span ℤ (snf.2.bM '' selected))
        (fun y hy ↦ by
          obtain ⟨i, rfl⟩ := hy
          rw [snf.2.snf i]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨snf.2.f i, ⟨i, rfl⟩, rfl⟩)
        (Submodule.zero_mem _)
        (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
        (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
        hxp
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, ⟨i, rfl⟩, rfl⟩
      exact smithVector_mem_of_isSaturated b P hP snf.2 i
  refine ⟨Q, ?_⟩
  rw [hselected]
  exact snf.2.bM.linearIndependent.isCompl_span_image
    snf.2.bM.span_eq (isCompl_compl)

theorem span_image_inl_eq_of_span_comap_eq
    {P R : Submodule ℤ M} (hRP : R ≤ P)
    {κ μ : Type*} (bP : Basis κ ℤ P) (bM : Basis (κ ⊕ μ) ℤ M)
    (hext : ∀ i, bM (Sum.inl i) = (bP i : M)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span ℤ (bP '' s)) :
    R = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bM '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span ℤ (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span ℤ (P.subtype '' (bP '' s)) := by
      rw [Submodule.map_span]
    _ = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by rw [himage]

theorem span_range_inl_prod_eq {P Q : Submodule ℤ M} (hPQ : IsCompl P Q)
    {κ μ : Type*}
    (bP : Basis κ ℤ P) (bQ : Basis μ ℤ Q) :
    let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span ℤ (bM '' Set.range Sum.inl) := by
  classical
  let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    let xp : P := ⟨x, hx⟩
    have hxp : xp ∈ Submodule.span ℤ (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := ℤ) (s := Set.range bP)
      (p := fun y _ ↦ (y : M) ∈
        Submodule.span ℤ (bM '' Set.range Sum.inl))
      (fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bM])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
      (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
      hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp

end Smith

universe u

theorem exists_basis_with_nested_supports_of_saturated_flag (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι],
      (b₀ : Basis ι ℤ N) →
      (P : Fin n → Submodule ℤ N) →
      (∀ i, IsSaturated (P i)) → Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
        (s : Fin n → Set κ), Antitone s ∧
          ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  induction n with
  | zero =>
      intro N _ ι _ b₀ P _ _
      classical
      let := Fintype.ofFinite ι
      let b : Basis (Fin (Fintype.card ι)) ℤ N :=
        b₀.reindex (Fintype.equivFin ι)
      let s : Fin 0 → Set (Fin (Fintype.card ι)) := Fin.elim0
      exact ⟨Fin (Fintype.card ι), inferInstance, b, s,
        fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      intro N _ ι _ b₀ P hsat hanti
      classical
      let P₀ : Submodule ℤ N := P 0
      obtain ⟨p, bP₀⟩ := Submodule.basisOfPid b₀ P₀
      let tail : Fin n → Submodule ℤ P₀ :=
        fun i ↦ (P i.succ).comap P₀.subtype
      have htail_sat : ∀ i, IsSaturated (tail i) := by
        intro i
        apply (hsat i.succ).comap_subtype
        exact hanti (Fin.zero_le i.succ)
      have htail_anti : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsPanti, hbP⟩ :=
        ih (N := P₀) (ι := Fin p) bP₀ tail htail_sat htail_anti
      let : Fintype κ := instκ
      obtain ⟨Q, hP₀Q⟩ :=
        exists_isCompl_of_isSaturated b₀ P₀ (hsat 0)
      obtain ⟨m, bQ⟩ := Submodule.basisOfPid b₀ Q
      let e : (P₀ × Q) ≃ₗ[ℤ] N := P₀.prodEquivOfIsCompl Q hP₀Q
      let b : Basis (κ ⊕ Fin m) ℤ N := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin m) :=
        fun i ↦ Fin.cases (Set.range Sum.inl)
          (fun j ↦ Sum.inl '' sP j) i
      refine ⟨κ ⊕ Fin m, inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx ↦ hx
          · rintro x ⟨k, hk, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsPanti (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact span_range_inl_prod_eq hP₀Q bP bQ
        · apply span_image_inl_eq_of_span_comap_eq
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k ↦ by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

theorem exists_basis_with_nested_supports_of_monotone_saturated_flag
    (n : ℕ) {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι]
    (b₀ : Basis ι ℤ N) (P : Fin n → Submodule ℤ N)
    (hsat : ∀ i, IsSaturated (P i)) (hmono : Monotone P) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  let Prev : Fin n → Submodule ℤ N := fun i ↦ P i.rev
  have hPrev : Antitone Prev := by
    intro i j hij
    exact hmono (Fin.rev_anti hij)
  obtain ⟨κ, instκ, b, t, htanti, ht⟩ :=
    exists_basis_with_nested_supports_of_saturated_flag n b₀ Prev
      (fun i ↦ hsat i.rev) hPrev
  let s : Fin n → Set κ := fun i ↦ t i.rev
  refine ⟨κ, instκ, b, s, ?_, ?_⟩
  · intro i j hij
    exact htanti (Fin.rev_anti hij)
  · intro i
    simpa [s, Prev] using ht i.rev

theorem repr_eq_zero_of_mem_span_image {N : Type*} [AddCommGroup N]
    {κ : Type*} (b : Basis κ ℤ N) (s : Set κ) {x : N}
    (hx : x ∈ Submodule.span ℤ (b '' s)) {j : κ} (hj : j ∉ s) :
    b.repr x j = 0 := by
  have hsupp := b.repr_support_subset_of_mem_span s hx
  by_contra hne
  exact hj (hsupp (Finsupp.mem_support_iff.mpr hne))

theorem exists_basis_with_nested_supports_realPrefixLattice
    {d n : ℕ} (x : Fin n → (Fin d → ℤ)) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ (Fin d → ℤ))
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, realPrefixLattice x i =
          Submodule.span ℤ (b '' s i) := by
  exact exists_basis_with_nested_supports_of_monotone_saturated_flag n
    (Pi.basisFun ℤ (Fin d)) (realPrefixLattice x)
    (isSaturated_realPrefixLattice x) (monotone_realPrefixLattice x)

theorem exists_fin_basis_with_nested_supports_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ)) :
    ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (s : Fin n → Set (Fin n)),
      Monotone s ∧
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' s i)) ∧
      ∀ i j, j ∉ s i → b.repr (x i) j = 0 := by
  classical
  obtain ⟨κ, instκ, bκ, sκ, hsmono, hs⟩ :=
    exists_basis_with_nested_supports_realPrefixLattice x
  let : Fintype κ := instκ
  let e : κ ≃ Fin n := bκ.indexEquiv (Pi.basisFun ℤ (Fin n))
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := bκ.reindex e
  let s : Fin n → Set (Fin n) := fun i ↦ e '' sκ i
  have himage (i : Fin n) : b '' s i = bκ '' sκ i := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b, e]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e k, ⟨k, hk, rfl⟩, by simp [b, e]⟩
  have hspan (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b '' s i) := by
    rw [himage]
    exact hs i
  refine ⟨b, s, ?_, hspan, ?_⟩
  · intro i j hij
    exact Set.image_mono (hsmono hij)
  · intro i j hj
    apply repr_eq_zero_of_mem_span_image b (s i)
    · rw [← hspan i]
      exact self_mem_realPrefixLattice x i
    · exact hj

theorem exists_prefix_adapted_basis_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ))
    (hli : LinearIndependent ℝ (fun i ↦ realEmbed n (x i))) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ),
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' Set.Iic i)) ∧
      (∀ i j, i < j → b.repr (x i) j = 0) ∧
      ∀ i, b.repr (x i) i ≠ 0 := by
  classical
  obtain ⟨b, s, hsmono, hspan, hzero⟩ :=
    exists_fin_basis_with_nested_supports_realPrefixLattice x
  have hpivot : ∀ i : Fin n, ∃ j : Fin n,
      j ∈ s i ∧ b.repr (x i) j ≠ 0 ∧
        ∀ hi : 0 < i.val,
          j ∉ s (⟨i.val - 1, by omega⟩ : Fin n) := by
    intro i
    by_cases hi : 0 < i.val
    · let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hset : Set.Iic ip = Set.Iio i := by
        ext k
        simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_iff_val_le_val,
          Fin.lt_def, ip]
        omega
      have hnot : x i ∉ realPrefixLattice x ip := by
        intro hmem
        have him := (mem_realPrefixLattice.mp hmem)
        apply hli.notMem_span_image (s := Set.Iio i) (lt_irrefl i)
        simpa [Set.image_image, Function.comp_def, hset] using him
      have hnotspan : x i ∉ Submodule.span ℤ (b '' s ip) := by
        rw [← hspan ip]
        exact hnot
      have hnsub : ¬ ((b.repr (x i)).support : Set (Fin n)) ⊆ s ip := by
        simpa [b.mem_span_image] using hnotspan
      obtain ⟨j, hjmem, hjnot⟩ := Set.not_subset.mp hnsub
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      refine ⟨j, hjcur, hjne, ?_⟩
      intro _hi
      simpa [ip] using hjnot
    · have hxne : x i ≠ 0 := by
        intro hx
        apply hli.ne_zero i
        simp [hx]
      have hrepr : b.repr (x i) ≠ 0 := by
        intro hr
        apply hxne
        apply b.repr.injective
        simpa using hr
      obtain ⟨j, hjmem⟩ := Finsupp.support_nonempty_iff.mpr hrepr
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      exact ⟨j, hjcur, hjne, fun h ↦ (hi h).elim⟩
  choose p hp_mem hp_ne hp_prev using hpivot
  have hp_injective : Function.Injective p := by
    intro i j hpij
    by_contra hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hjpos : 0 < j.val := lt_of_le_of_lt (Nat.zero_le _) hijlt
      let jp : Fin n := ⟨j.val - 1, by omega⟩
      have hijp : i ≤ jp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ j.val - 1
        omega
      have hpimem : p i ∈ s jp := hsmono hijp (hp_mem i)
      have hpjnot : p j ∉ s jp := by
        simpa [jp] using hp_prev j hjpos
      exact hpjnot (hpij ▸ hpimem)
    · have hipos : 0 < i.val := lt_of_le_of_lt (Nat.zero_le _) hjilt
      let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hjip : j ≤ ip := by
        apply Fin.le_iff_val_le_val.mpr
        change j.val ≤ i.val - 1
        omega
      have hpjmem : p j ∈ s ip := hsmono hjip (hp_mem j)
      have hpinot : p i ∉ s ip := by
        simpa [ip] using hp_prev i hipos
      exact hpinot (hpij.symm ▸ hpjmem)
  have hp_bijective : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).mpr
      ⟨hp_injective, rfl⟩
  let ep : Fin n ≃ Fin n := Equiv.ofBijective p hp_bijective
  have hs_eq (i : Fin n) : p '' Set.Iic i = s i := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hsmono (Set.mem_Iic.mp hk) (hp_mem k)
    · intro q hq
      obtain ⟨k, rfl⟩ := hp_bijective.2 q
      refine ⟨k, ?_, rfl⟩
      apply Set.mem_Iic.mpr
      by_contra hki
      have hik : i < k := lt_of_not_ge hki
      have hkpos : 0 < k.val := lt_of_le_of_lt (Nat.zero_le _) hik
      let kp : Fin n := ⟨k.val - 1, by omega⟩
      have hikp : i ≤ kp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ k.val - 1
        omega
      exact (hp_prev k hkpos) (hsmono hikp hq)
  let b' : Basis (Fin n) ℤ (Fin n → ℤ) := b.reindex ep.symm
  have hbimage (i : Fin n) : b' '' Set.Iic i = b '' s i := by
    rw [← hs_eq i]
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨p k, ⟨k, hk, rfl⟩, by simp [b', ep]⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b', ep]⟩
  have hspan' (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b' '' Set.Iic i) := by
    rw [hbimage]
    exact hspan i
  refine ⟨b', hspan', ?_, ?_⟩
  · intro i j hij
    apply repr_eq_zero_of_mem_span_image b' (Set.Iic i)
    · rw [← hspan' i]
      exact self_mem_realPrefixLattice x i
    · exact fun hj ↦ (not_le_of_gt hij) (Set.mem_Iic.mp hj)
  · intro i
    simpa [b', ep] using hp_ne i

end Erdos3.IntegerBasisReduction.SaturatedFlag

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicTorusCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} [NeZero N]
  (η : (ι → ℤ) →+ ZMod N) (b : Basis κ ℤ (cyclicIntegerKernel η))

noncomputable def cyclicKernelRealCoordinates : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
  (b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).equivFun

noncomputable def cyclicKernelCoordinateCharacter (i : κ) :
    (ι → ℤ) →+ AddCircle (1 : ℝ) where
  toFun x := (cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ)
  map_zero' := by simp
  map_add' x y := by simp only [map_add, Pi.add_apply, AddCircle.coe_add]

theorem cyclicKernelCoordinateCharacter_eq_zero (x : ι → ℤ) (hx : η x = 0) (i : κ) :
    cyclicKernelCoordinateCharacter η b i x = 0 := by
  let y : cyclicIntegerKernel η :=
    ⟨integerVectorRealMap x, (integerVectorRealMap_mem_cyclicIntegerKernel η x).mpr hx⟩
  change ((b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).repr (y : ι → ℝ) i :
    AddCircle (1 : ℝ)) = 0
  rw [Basis.ofZLatticeBasis_repr_apply]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨b.repr y i, by simp⟩

theorem cyclicKernelCoordinateCharacters_eq_zero_iff (x : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x = 0) ↔ η x = 0 := by
  refine ⟨?_, fun hx i => cyclicKernelCoordinateCharacter_eq_zero η b x hx i⟩
  intro h
  apply (integerVectorRealMap_mem_cyclicIntegerKernel η x).mp
  rw [← b.ofZLatticeBasis_span ℝ (cyclicIntegerKernel η)]
  rw [Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (h i)
  exact ⟨z, by simpa [cyclicKernelRealCoordinates, Basis.equivFun_apply] using hz⟩

theorem cyclicKernelCoordinateCharacters_eq_iff (x y : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x =
      cyclicKernelCoordinateCharacter η b i y) ↔ η x = η y := by
  rw [← sub_eq_zero, ← map_sub, ← cyclicKernelCoordinateCharacters_eq_zero_iff η b]
  simp only [map_sub, sub_eq_zero]

theorem exists_cyclic_kernel_real_frequencies :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (x : ι → ℤ) (n : ℤ), η x = (n : ZMod N) → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) = (((n : ℝ) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  have h := fun i => exists_cyclic_real_character_lift η
    (cyclicKernelCoordinateCharacter η b i)
    (fun x hx => cyclicKernelCoordinateCharacter_eq_zero η b x hx i)
  choose t ht hperiod hformula using h
  exact ⟨t, ht, hperiod, fun x n hn i => hformula i x n hn⟩

theorem cyclicKernelCoordinateCharacters_injOn
    (S : Set (ι → ℤ)) (hη : Set.InjOn η S) :
    Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x) S := by
  intro x hx y hy hxy
  apply hη hx hy
  exact (cyclicKernelCoordinateCharacters_eq_iff η b x y).mp (congrFun hxy)

theorem exists_affine_cyclic_kernel_real_frequencies
    (h₀ : ZMod N) :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (h : ZMod N) (x : ι → ℤ), h = h₀ + η x → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) =
            ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨t, ht, hperiod, hformula⟩ := exists_cyclic_kernel_real_frequencies η b
  refine ⟨t, ht, hperiod, ?_⟩
  intro h x hx i
  have he : η x = (((h.val : ℤ) - h₀.val : ℤ) : ZMod N) := by
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hx, add_sub_cancel_left]
  simpa only [Int.cast_sub, Int.cast_natCast] using hformula x _ he i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem sum_mass_choice_fibers {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    (∑ c, p.mass (G.filter (fun z => code z = c))) = p.mass G := by
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem exists_large_mass_choice_fiber {Ω C : Type*} [Fintype Ω] [Fintype C] [Nonempty C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    ∃ c, p.mass G / Fintype.card C ≤ p.mass (G.filter (fun z => code z = c)) := by
  have he : (𝔼 c, p.mass (G.filter (fun z => code z = c))) =
      p.mass G / Fintype.card C := by
    rw [Fintype.expect_eq_sum_div_card, p.sum_mass_choice_fibers]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty he.ge
  exact ⟨c, hc⟩

theorem mass_superlevel_ge {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f : Ω → ℝ) {α ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hcap : ∀ z, f z ≤ B) (hmean : α ≤ p.mean f) :
    (α - ρ) / B ≤ p.mass (Finset.univ.filter (fun z => ρ ≤ f z)) := by
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hpoint (z : Ω) : f z ≤ ρ + B * (if z ∈ G then 1 else 0) := by
    by_cases hz : ρ ≤ f z
    · simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_true,
        mul_one] using (hcap z).trans (by linarith)
    · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_false,
        mul_zero, add_zero]
      exact le_of_not_ge hz
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const, p.mean_const_mul, p.mean_indicator] at h
  apply (div_le_iff₀ hB).mpr
  change α - ρ ≤ p.mass G * B
  nlinarith only [hmean, h]

theorem mass_mul_le_mean_of_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (f : Ω → ℝ) {a : ℝ}
    (hf : ∀ z, 0 ≤ f z) (hG : ∀ z ∈ G, a ≤ f z) :
    a * p.mass G ≤ p.mean f := by
  rw [← p.mean_indicator G, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : z ∈ G
  · simpa only [hz, ite_true, mul_one] using hG z hz
  · simpa only [hz, ite_false, mul_zero] using hf z

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedSupportedCubeSum {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  supportedCubeSum j (Q : Set A) F / Nat.card (SupportedCube j (Q : Set A))

theorem normalizedSupportedCubeSum_self_re {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Fintype B] [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (normalizedSupportedCubeSum (j + 1) Q (fun _ => f)).re =
      finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  exact Complex.div_natCast_re _ _

theorem sampled_normalized_cube_lower_bound {Ω A B : Type*} [Fintype Ω]
    [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (j : ℕ) (f : Ω → A → ℂ)
    {τ a : ℝ} (ha : 0 ≤ a) (hmass : τ ≤ p.mass G)
    (hdetect : ∀ z ∈ G, a ≤ finiteSupportGowersNorm (j + 1) Q (f z)) :
    τ * a ^ (2 ^ (j + 1)) ≤
      (p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z))).re := by
  rw [p.complexMean_re]
  simp_rw [normalizedSupportedCubeSum_self_re hφ]
  have hn (z) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (f z) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hg := p.mass_mul_le_mean_of_lower_bound G
    (fun z => finiteSupportGowersNorm (j + 1) Q (f z) ^ (2 ^ (j + 1)))
    (fun z => pow_nonneg (hn z) _) (fun z hz => pow_le_pow_left₀ ha (hdetect z hz) _)
  exact (mul_le_mul_of_nonneg_right hmass (pow_nonneg ha _)).trans (by simpa [mul_comm] using hg)

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

theorem exists_common_inner_sampled_slice {Ω T X : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    (C : Finset (Finset T)) {α ε η ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + η + ρ < α)
    (hcover : ∀ z j, ∃ A ∈ C, A.Nonempty ∧ A ⊆ S z j ∧
      2 * (1 - (A.card : ℝ) / (S z j).card) ≤ η)
    (hmean : α ≤ sampledSliceSeminorm p F S w v) :
    ∃ A ∈ C, A.Nonempty ∧ ∃ G : Finset Ω, ∃ j : ∀ z, J z,
      (α - ε - η - ρ) / C.card ≤ p.mass G ∧
      ∀ z ∈ G, A ⊆ S z (j z) ∧
        2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ η ∧
        ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨j, hj⟩ := exists_nearly_maximizing_sampled_slice_tests p F S w hS hsize hw v hε
  choose A hAC hAn hAS hAerr using fun z => hcover z (j z)
  let code : Ω → C := fun z => ⟨A z, hAC z⟩
  let _ : Nonempty C := ⟨code (Classical.arbitrary Ω)⟩
  let f : Ω → ℝ := fun z => ‖𝔼 t ∈ A z, v (F z t) * w z (j z) t‖
  have hunit (z : Ω) (t : T) : ‖v (F z t) * w z (j z) t‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv _)).trans (hw _ _ _)
  have happrox (z : Ω) : ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ ≤ f z + η := by
    have he := (norm_expect_subset_sub_le (A z) (S z (j z)) (hAn z) (hAS z)
      (fun t => v (F z t) * w z (j z) t) (fun t _ => hunit z t)).trans (hAerr z)
    have ht := norm_sub_norm_le (𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t)
      (𝔼 t ∈ A z, v (F z t) * w z (j z) t)
    rw [norm_sub_rev] at he
    dsimp [f]
    linarith
  have hm : α - ε - η ≤ p.mean f := by
    have hm' := p.mean_mono happrox
    rw [p.mean_add, p.mean_const] at hm'
    linarith
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hG : α - ε - η - ρ ≤ p.mass G := by
    simpa only [div_one] using p.mass_superlevel_ge f hρ zero_lt_one
      (fun z => norm_finset_expect_le_one _ _ (fun t _ => hunit z t)) hm
  obtain ⟨c, hc⟩ := p.exists_large_mass_choice_fiber G code
  let H := G.filter (fun z => code z = c)
  have hmass : (α - ε - η - ρ) / C.card ≤ p.mass H := by
    convert (div_le_div_of_nonneg_right hG (Nat.cast_nonneg (Fintype.card C))).trans hc using 1
    all_goals first | rfl | simp only [H, Fintype.card_coe]
    unfold FiniteProbabilityWeights.mass
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_filter]
    · intro z _
      rfl
  have hHpos : 0 < p.mass H := lt_of_lt_of_le
    (div_pos (by linarith) (by exact_mod_cast C.card_pos.mpr ⟨c.val, c.property⟩)) hmass
  have hH : H.Nonempty := by
    by_contra h
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hHpos
    exact lt_irrefl _ hHpos
  have hcode (z : Ω) (hz : z ∈ H) : A z = c.val :=
    congrArg Subtype.val (Finset.mem_filter.mp hz).2
  obtain ⟨z₀, hz₀⟩ := hH
  refine ⟨c.val, c.property, ?_, H, j, hmass, ?_⟩
  · rw [← hcode z₀ hz₀]
    exact hAn z₀
  · intro z hz
    rw [← hcode z hz]
    exact ⟨hAS z, hAerr z, (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridBudget
namespace OAI

section

namespace Erdos3

open Module

theorem integral_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * l : ℕ) : ℝ) ≤ Real.exp ((p + (K + 5 : ℕ)) ^ (K + 5)) := by
  let C := K + 5
  let t : ℝ := p + C
  have ht : 5 ≤ t := by dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hpt : p ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (Nat.cast_nonneg C)
  have hKt : (K : ℝ) ≤ t := by dsimp [t, C]; push_cast; linarith
  have htt : t ≤ t ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ t by linarith) (by decide : 1 ≤ 4)
  have hp4 : ((d ^ 3 : ℕ) : ℝ) * p ≤ t ^ 4 := by
    rw [Nat.cast_pow]
    calc
      _ ≤ p ^ 3 * p := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg d) hd 3) hp
      _ = p ^ 4 := by ring
      _ ≤ t ^ 4 := pow_le_pow_left₀ hp hpt 4
  have hlog : (K : ℝ) + (d ^ 3 : ℕ) * p + p ≤ t ^ C := by
    calc
      _ ≤ t ^ 4 + t ^ 4 + t ^ 4 := add_le_add (add_le_add (hKt.trans htt) hp4) (hpt.trans htt)
      _ = 3 * t ^ 4 := by ring
      _ ≤ t * t ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = t ^ 5 := by ring
      _ ≤ t ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (d ^ 3) : ℕ) : ℝ) ≤ Real.exp ((d ^ 3 : ℕ) * p) := by
    rw [Nat.cast_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
  calc
    _ ≤ Real.exp K * Real.exp ((d ^ 3 : ℕ) * p) * Real.exp p := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hK hpow (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp ((K : ℝ) + (d ^ 3 : ℕ) * p + p) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem exists_integral_grid_subgroup_exp (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
        0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  refine ⟨bchIntegralDenominatorBound s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l H p hl hc hinner hp hd hH hlp
  obtain ⟨B, Λ, hB, hdiv, hbound, hΛ, hcoords⟩ := exists_integral_grid_subgroup e hnil Γ l hl hc hinner
  exact ⟨B, Λ, hB, hdiv, (Nat.cast_le.mpr hbound).trans
    (integral_grid_allowance_le_exp _ _ _ _ hp hd hH hlp), hΛ, hcoords⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLogarithmicDifferential
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem base_lift_congr (f g : X → DualLieAlgebra L)
    (hb : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x)) (p : FreeLieAlgebra ℚ X) :
    dualBaseLinear (FreeLieAlgebra.lift ℚ f p) = dualBaseLinear (FreeLieAlgebra.lift ℚ g p) := by
  change dualBaseLie (FreeLieAlgebra.lift ℚ f p) = dualBaseLie (FreeLieAlgebra.lift ℚ g p)
  rw [map_freeLie_lift, map_freeLie_lift]
  exact congrArg (fun a : X → L => FreeLieAlgebra.lift ℚ a p) (funext hb)

theorem dualTangentLinear_lift_add (f g k : X → DualLieAlgebra L)
    (hfg : ∀ x, dualBaseLinear (f x) = dualBaseLinear (g x))
    (hfk : ∀ x, dualBaseLinear (f x) = dualBaseLinear (k x))
    (ht : ∀ x, dualTangentLinear (f x) = dualTangentLinear (g x) + dualTangentLinear (k x))
    (p : FreeLieAlgebra ℚ X) :
    dualTangentLinear (FreeLieAlgebra.lift ℚ f p) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g p) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k p) := by
  have hbr (u v : FreeLieAlgebra ℚ X)
      (hu : dualTangentLinear (FreeLieAlgebra.lift ℚ f u) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g u) + dualTangentLinear (FreeLieAlgebra.lift ℚ k u))
      (hv : dualTangentLinear (FreeLieAlgebra.lift ℚ f v) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g v) + dualTangentLinear (FreeLieAlgebra.lift ℚ k v)) :
      dualTangentLinear (FreeLieAlgebra.lift ℚ f ⁅u, v⁆) =
        dualTangentLinear (FreeLieAlgebra.lift ℚ g ⁅u, v⁆) +
          dualTangentLinear (FreeLieAlgebra.lift ℚ k ⁅u, v⁆) := by
    simp only [LieHom.map_lie, dualTangentLinear_lie, hu, hv,
      ← base_lift_congr f g hfg, ← base_lift_congr f k hfk,
      LieRing.lie_add, LieRing.add_lie]
    abel
  apply freeLie_linear_induction (fun q =>
    dualTangentLinear (FreeLieAlgebra.lift ℚ f q) =
      dualTangentLinear (FreeLieAlgebra.lift ℚ g q) +
        dualTangentLinear (FreeLieAlgebra.lift ℚ k q))
  · simp only [map_zero, add_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
    abel
  · intro r q hq
    simp only [map_smul, hq, smul_add]
  · intro t
    induction t with
    | ih1 x => simpa only [lieTreeEval, FreeLieAlgebra.lift_of_apply] using ht x
    | ih2 u v hu hv => exact hbr _ _ hu hv

theorem dualTangentLinear_bch_add (s : ℕ) (a a₁ a₂ b b₁ b₂ : DualLieAlgebra L)
    (ha₁ : dualBaseLinear a = dualBaseLinear a₁)
    (ha₂ : dualBaseLinear a = dualBaseLinear a₂)
    (hb₁ : dualBaseLinear b = dualBaseLinear b₁)
    (hb₂ : dualBaseLinear b = dualBaseLinear b₂)
    (hat : dualTangentLinear a = dualTangentLinear a₁ + dualTangentLinear a₂)
    (hbt : dualTangentLinear b = dualTangentLinear b₁ + dualTangentLinear b₂) :
    dualTangentLinear (lieBCH s a b) =
      dualTangentLinear (lieBCH s a₁ b₁) + dualTangentLinear (lieBCH s a₂ b₂) := by
  apply dualTangentLinear_lift_add ![a, b] ![a₁, b₁] ![a₂, b₂]
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_value_tangent (x y : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ =
      dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y) (-dualConstantLie x)) := by
  change dualTangentLinear (lieBCH s (dualConstantLie x + dualInfinitesimal y)
    (-dualConstantLie (dualBaseLinear (dualConstantLie x + dualInfinitesimal y)))) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

theorem dualLogDerivative_tangent_add (x y z : L) :
    dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal (y + z)⟩ =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ +
        dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal z⟩ := by
  simp only [dualLogDerivative_value_tangent]
  apply dualTangentLinear_bch_add <;>
    simp only [map_add, map_neg, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
      dualTangentLinear_constant, dualTangentLinear_infinitesimal, add_zero, zero_add, neg_zero]

noncomputable def dualLogarithmicDifferential (x : L) : L →ₗ[ℚ] L :=
  (AddMonoidHom.mk'
    (fun y => dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩)
    (dualLogDerivative_tangent_add x)).toRatLinearMap

@[simp] theorem dualLogarithmicDifferential_apply (x y : L) :
    dualLogarithmicDifferential (hnil := hnil) x y =
      dualLogDerivative (hnil := hnil) ⟨dualConstantLie x + dualInfinitesimal y⟩ := rfl

theorem dualLogarithmicDifferential_smul_real [LieAlgebra ℝ L] (x y : L) (r : ℝ) :
    dualLogarithmicDifferential (hnil := hnil) x (r • y) =
      r • dualLogarithmicDifferential (hnil := hnil) x y := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  have he := dualLinearLift_logDerivative_eq (hL := hnil) hnil ⊤ LieHom.id T hT
    (⟨dualConstantLie x + dualInfinitesimal y⟩ : DualGroup hnil) (by trivial)
    (⟨dualConstantLie x + dualInfinitesimal (r • y)⟩ : DualGroup hnil)
    (by simp only [map_add, dualLinearLift_constant, dualLinearLift_infinitesimal]; rfl)
  exact he.symm

noncomputable def dualRealLogarithmicDifferential [LieAlgebra ℝ L] (x : L) : L →ₗ[ℝ] L where
  toFun := dualLogarithmicDifferential (hnil := hnil) x
  map_add' := (dualLogarithmicDifferential x).map_add
  map_smul' r y := dualLogarithmicDifferential_smul_real x y r

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealizedDualBCH
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualBCH_insertion_quotient (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (z : DualGroup hnil) (e m : L)
    (hz : dualTangentLinear z.coord ∈ I) (he : e ∈ I) (hm : m ∈ I) :
    lieBCH s
      (lieBCH s
        (lieBCH s (-lieQuotientMap J e)
          (lieQuotientMap J (dualBaseLinear z.coord + dualTangentLinear z.coord)))
        (-lieQuotientMap J m))
      (-lieQuotientMap J (dualBaseLinear z.coord)) =
      lieQuotientMap J (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  have ha : dualInfinitesimal (-e) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem he
  have hb : z.coord ∈ dualIdealSubalgebra I := hz
  have hc : dualInfinitesimal (-m) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem hm
  have hd : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hab := lieBCH_mem (dualIdealSubalgebra I) s ha hb
  have habc := lieBCH_mem (dualIdealSubalgebra I) s hab hc
  have h := congrArg (fun g : DualGroup hnil => dualQuotientEvaluate J g.coord)
    (dualBCH_insertion_identity z e m)
  change dualQuotientEvaluate J
    (lieBCH s (lieBCH s (lieBCH s (dualInfinitesimal (-e)) z.coord) (dualInfinitesimal (-m)))
      (-dualConstantLie (dualBaseLinear z.coord))) =
    dualQuotientEvaluate J (dualInfinitesimal (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m)) at h
  rw [dualQuotientEvaluate_lieBCH I J hIJ s habc hd,
    dualQuotientEvaluate_lieBCH I J hIJ s hab hc,
    dualQuotientEvaluate_lieBCH I J hIJ s ha hb] at h
  simpa only [dualQuotientEvaluate_apply, map_neg, dualBaseLinear_infinitesimal,
    dualTangentLinear_infinitesimal, dualBaseLinear_constant, dualTangentLinear_constant,
    zero_add, add_zero] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BlockLayerBracket
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem blockMonomial_lie_coefficient [DecidableEq ι] [DecidableEq σ] (π : ι → σ) (a b : σ → ℕ)
    (x y : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅blockMonomial π a x, blockMonomial π b y⁆ c =
      Fintype.card (SquarefreeSplit π c a b) • ⁅x, y⁆ := by
  classical
  rw [squarefree_lie_coefficient]
  simp only [blockMonomial_coefficient]
  have hterm (u v : SquarefreeIndex ι) :
      (if u.val + v.val = c.val then
        ⁅if blockDegree π u.val = a then x else 0,
          if blockDegree π v.val = b then y else 0⁆ else 0) =
      if u.val + v.val = c.val ∧ blockDegree π u.val = a ∧ blockDegree π v.val = b
        then ⁅x, y⁆ else 0 := by
    by_cases hs : u.val + v.val = c.val <;>
      by_cases hu : blockDegree π u.val = a <;>
      by_cases hv : blockDegree π v.val = b <;> simp [hs, hu, hv]
  simp_rw [hterm]
  rw [← Fintype.sum_prod_type']
  rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const]

theorem blockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅blockMonomial π a x, blockMonomial π b y⁆ =
      blockSplitMultiplicity a b • blockMonomial π (a + b) ⁅x, y⁆ := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext c
  rw [blockMonomial_lie_coefficient, map_nsmul, Pi.smul_apply, blockMonomial_coefficient]
  by_cases hc : blockDegree π c.val = a + b
  · rw [if_pos hc, card_squarefreeSplit π c a b hc]
  · have hz : Fintype.card (SquarefreeSplit π c a b) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun p => hc (squarefreeSplit_degree π c a b p)⟩
    rw [hz, zero_smul, if_neg hc, smul_zero]

theorem factorialBlockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅factorialBlockMonomial π a x, factorialBlockMonomial π b y⁆ =
      factorialBlockMonomial π (a + b) ⁅x, y⁆ := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, smul_lie, lie_smul, blockMonomial_lie]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
  have h := congrArg (fun n : ℕ => (n : ℚ)) (multidegreeFactorial_split a b)
  simp only [Nat.cast_mul] at h
  rw [mul_comm (multidegreeFactorial b : ℚ) (multidegreeFactorial a : ℚ), h]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem blockLayerMap_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.blockLayerMap π a ha x, F.blockLayerMap π b hb y⁆ =
      F.blockLayerMap π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ := by
  apply Subtype.ext
  exact factorialBlockMonomial_lie π a b x.val y.val

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem commonStrideCount_exp_bound {p : ℝ} (hp : 0 ≤ p) :
    (⌈2 / Real.exp (-p)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
  rw [Real.exp_neg, div_inv_eq_mul]
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp p by positivity)).le
  have h1 := Real.one_le_exp hp
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp p := by linarith
    _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem exists_dense_box_inner_family {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ D : Finset (Finset (I → ℤ)),
      (D.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ D, ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ m ≤ ⌈2 / Real.exp (-p)⌉₊ ∧ A = commonStrideBox c m H) ∧
      ∀ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m → (∀ i, 0 < H i) →
        (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) →
        (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) →
        ∃ A ∈ D, A.Nonempty ∧ A ⊆ commonStrideBox c m H ∧
          2 * (1 - (A.card : ℝ) / (commonStrideBox c m H).card) ≤
            Fintype.card I * Real.exp (-p) := by
  classical
  choose C hcount hshape hcover using fun i => exists_finite_inner_interval_family hp (N i)
  let M := ⌈2 / Real.exp (-p)⌉₊
  let D := finiteCommonStrideFamily M C
  have hprod : (∏ i, ((C i).card : ℝ)) ≤ Real.exp ((4 * p + 18) * Fintype.card I) := by
    calc
      _ ≤ ∏ _i : I, Real.exp (4 * p + 18) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcount i)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
  refine ⟨D, ?_, fun A hA => finiteCommonStrideFamily_shape M C hshape hA, ?_⟩
  · calc
      (D.card : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) * ∏ i, ((C i).card : ℝ) := by
        exact_mod_cast finiteCommonStrideFamily_card M C
      _ ≤ Real.exp (p + 2) ^ (Fintype.card I + 1) *
          Real.exp ((4 * p + 18) * Fintype.card I) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (commonStrideCount_exp_bound hp) _)
          hprod (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
  · intro c m H hm hH hsub hdense
    obtain ⟨d, r, a, hd, hdM, hcoord⟩ := exists_bounded_common_stride_reindex N H c hm hH
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hsub hdense
    choose S hSC hSn hSsub hShalf hSerr using fun i =>
      hcover i (a i) (H i) (hcoord i).2.1 (hH i) (hdense i)
    let Aaxis (i : I) := (S i).image (fun x => (r i : ℤ) + d * x)
    let A := Fintype.piFinset Aaxis
    have hg (i : I) : Function.Injective (fun x : ℤ => (r i : ℤ) + d * x) := by
      intro x y he
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) (add_left_cancel he)
    have hAsub (i : I) : Aaxis i ⊆ integerProgressionSupport (c i) m (H i) := by
      rw [(hcoord i).2.2]
      exact Finset.image_subset_image (hSsub i)
    have hB (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty := by
      apply Finset.card_pos.mp
      simpa only [card_integerProgressionSupport _ _ _ hm] using hH i
    refine ⟨A, mem_finiteCommonStrideFamily M C hd hdM r (fun i => (hcoord i).1) S hSC,
      Fintype.piFinset_nonempty.mpr (fun i => (hSn i).image _),
      Fintype.piFinset_subset _ _ hAsub, ?_⟩
    have hloss := piFinset_inner_normalized_loss Aaxis
      (fun i => integerProgressionSupport (c i) m (H i)) hB hAsub
      (fun _ => Real.exp (-p)) (fun i => by
        simpa only [Aaxis, Finset.card_image_of_injective _ (hg i),
          card_integerProgressionSupport _ _ _ hm] using hSerr i)
    simpa only [A, commonStrideBox, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hloss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def IsDenseCommonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (p : ℝ) (A : Finset (I → ℤ)) : Prop :=
  ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ (∀ i, 0 < H i) ∧
    (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) ∧
    (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) ∧ A = commonStrideBox c m H

theorem IsDenseCommonStrideBox.nonempty {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    A.Nonempty := by
  obtain ⟨c, m, H, hm, hH, _, _, rfl⟩ := h
  exact commonStrideBox_nonempty c hm H hH

theorem exists_finite_site_box_inner_family {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ C : Finset (Finset T),
      (C.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ C, A.Nonempty → ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∀ S : Finset T, IsDenseCommonStrideBox N p (S.image e) →
        ∃ A ∈ C, A.Nonempty ∧ A ⊆ S ∧
          2 * (1 - (A.card : ℝ) / S.card) ≤ Fintype.card I * Real.exp (-p) := by
  obtain ⟨D, hD, hshape, hcover⟩ := exists_dense_box_inner_family hp N
  refine ⟨finiteSiteInnerFamily e D, ?_, ?_, ?_⟩
  · exact (show ((finiteSiteInnerFamily e D).card : ℝ) ≤ D.card by
      exact_mod_cast finiteSiteInnerFamily_card e D).trans hD
  · intro A hA hAn
    obtain ⟨c, m, H, hm, _, heq⟩ := hshape (A.image e) (finiteSiteInnerFamily_image_mem e D hA)
    have hBn : (commonStrideBox c m H).Nonempty := heq ▸ hAn.image e
    have haxis := Fintype.piFinset_nonempty.mp hBn
    refine ⟨c, m, H, hm, ?_, heq⟩
    intro i
    have hcard := (haxis i).card_pos
    simpa only [card_integerProgressionSupport _ _ _ hm] using hcard
  · intro S hS
    obtain ⟨c, m, H, hm, hH, hsub, hdense, heq⟩ := hS
    obtain ⟨A, hAD, hAn, hAS, hloss⟩ := hcover c m H hm hH hsub hdense
    have hAS' : A ⊆ S.image e := by rw [heq]; exact hAS
    have hAall : A ⊆ Finset.univ.image e := hAS'.trans (Finset.image_subset_image (Finset.subset_univ S))
    have hcard := finiteSitePreimage_card e he A hAall
    refine ⟨finiteSitePreimage e A, mem_finiteSiteInnerFamily e D hAD hAall,
      Finset.card_pos.mp (by rw [hcard]; exact hAn.card_pos),
      finiteSitePreimage_subset e he A S hAS', ?_⟩
    rw [← heq, Finset.card_image_of_injective _ he] at hloss
    simpa only [hcard] using hloss

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

theorem exists_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧
      (∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨C, hcount, hshape, hcover⟩ := exists_finite_site_box_inner_family e he hp N
  have hS (z) (j) : (S z j).Nonempty := Finset.image_nonempty.mp (hslice z j).nonempty
  have hsize (z) (j) : (Fintype.card T : ℝ) / (S z j).card ≤ Fintype.card T :=
    div_le_self (Nat.cast_nonneg _) (by exact_mod_cast (hS z j).card_pos)
  obtain ⟨A, hAC, hAn, G, j, hmass, hlocal⟩ := exists_common_inner_sampled_slice μ F S w
    hS hsize hw v hv C hε hρ hlarge (fun z j => hcover (S z j) (hslice z j)) hmean
  refine ⟨A, hAn, hshape A hAC hAn, G, j, ?_, hlocal⟩
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr ⟨A, hAC⟩
  have hfrac := div_le_div_of_nonneg_left
    (show 0 ≤ α - ε - Fintype.card I * Real.exp (-p) - ρ by linarith) hcard hcount
  have h := hfrac.trans hmass
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

def integerPoint (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) : U → ℤ :=
  fun i => ((A.point j i).val : ℤ)

theorem integerPoint_eq (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) :
    A.integerPoint j = commonStridePoint (fun i => (A.start i : ℤ)) q
      (fun i => ((j i).val : ℤ)) := by
  funext i
  simp only [integerPoint, point, commonStridePoint, Nat.cast_add, Nat.cast_mul]

@[simp] theorem commonStrideIndex_integerPoint (A : ResidueBoxSlice N q) (hq : 0 < q)
    (j : ∀ i, Fin (A.length i)) :
    commonStrideIndex (fun i => (A.start i : ℤ)) q (A.integerPoint j) =
      (fun i => ((j i).val : ℤ)) := by
  rw [integerPoint_eq, commonStrideIndex_point _ hq]

theorem integerPoint_injective (A : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective A.integerPoint := by
  intro j k h
  have hi := congrArg (commonStrideIndex (fun i => (A.start i : ℤ)) q) h
  rw [A.commonStrideIndex_integerPoint hq, A.commonStrideIndex_integerPoint hq] at hi
  funext i
  apply Fin.ext
  exact_mod_cast congrFun hi i

variable [Fintype U] [DecidableEq U]

noncomputable def integerPoints (A : ResidueBoxSlice N q) : Finset (U → ℤ) :=
  Finset.univ.image A.integerPoint

theorem integerPoints_eq_commonStrideBox (A : ResidueBoxSlice N q) :
    A.integerPoints = commonStrideBox (fun i => (A.start i : ℤ)) q A.length := by
  classical
  rw [commonStrideBox_eq_image]
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨fun i => ((j i).val : ℤ), ?_, (A.integerPoint_eq j).symm⟩
    exact (mem_integerBox _ _).mpr (fun i => ⟨by positivity, by exact_mod_cast (j i).isLt⟩)
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := (mem_integerBox _ _).mp hz
    let j : ∀ i, Fin (A.length i) := fun i => ⟨(z i).toNat, by
      have hzi := hz' i
      omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    rw [A.integerPoint_eq]
    congr 1
    funext i
    exact Int.toNat_of_nonneg (hz' i).1

omit [Fintype U] [DecidableEq U] in
theorem progression_inside (A : ResidueBoxSlice N q) (i : U) :
    integerProgressionSupport (A.start i : ℤ) q (A.length i) ⊆
      Finset.Ico (0 : ℤ) (N i) := by
  intro y hy
  obtain ⟨j, hj0, hjlt, rfl⟩ := (mem_integerProgressionSupport_iff_parameter _ _ _ _).mp hy
  have hj : j.toNat < A.length i := by omega
  have hinside := A.inside i j.toNat hj
  have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  apply Finset.mem_Ico.mpr
  constructor
  · positivity
  · rw [← he]
    exact_mod_cast hinside

theorem isDenseCommonStrideBox (A : ResidueBoxSlice N q) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ i, 0 < A.length i)
    (hlength : ∀ i, ρ * N i ≤ 4 * q * A.length i) :
    IsDenseCommonStrideBox N (Real.log (4 * (q : ℝ) / ρ)) A.integerPoints := by
  refine ⟨fun i => (A.start i : ℤ), q, A.length, hq, hA,
    A.progression_inside, ?_, A.integerPoints_eq_commonStrideBox⟩
  intro i
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (q : ℝ) / ρ), inv_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (q : ℝ))).mpr
  nlinarith [hlength i]

theorem expect_integerPoints (A : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (U → ℤ) → V) :
    (𝔼 x ∈ A.integerPoints, f x) =
      (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) := by
  exact Finset.expect_image (A.integerPoint_injective hq).injOn

end Erdos3.ResidueBoxSlice

namespace Erdos3

theorem IsDenseCommonStrideBox.mono {U : Type*} [Fintype U] [DecidableEq U]
    {N : U → ℕ} {p p' : ℝ} {A : Finset (U → ℤ)}
    (hA : IsDenseCommonStrideBox N p A) (hpp' : p ≤ p') :
    IsDenseCommonStrideBox N p' A := by
  obtain ⟨c, m, H, hm, hH, hinside, hlength, heq⟩ := hA
  refine ⟨c, m, H, hm, hH, hinside, ?_, heq⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hpp')) (Nat.cast_nonneg (N i))).trans (hlength i)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem commonStrideBox_axis_card (c : I → ℤ) (m : ℕ) (H : I → ℕ)
    (hm : 0 < m) (hH : ∀ i, 0 < H i) (i : I) :
    ((commonStrideBox c m H).image (fun x => x i)).card = H i := by
  classical
  have hnonempty (j : I) : (integerProgressionSupport (c j) m (H j)).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_integerProgressionSupport _ _ _ hm]
    exact hH j
  have hproject := Fintype.eval_image_piFinset
    (fun j => integerProgressionSupport (c j) m (H j)) i (fun j _ => hnonempty j)
  exact (congrArg Finset.card hproject).trans (card_integerProgressionSupport _ _ _ hm)

namespace ResidueBoxSlice

variable {N : I → ℕ} {q : ℕ}

theorem length_pos_of_integerPoints_nonempty (A : ResidueBoxSlice N q)
    (hA : A.integerPoints.Nonempty) (i : I) : 0 < A.length i := by
  classical
  obtain ⟨x, hx⟩ := hA
  obtain ⟨j, _, _⟩ := Finset.mem_image.mp hx
  exact lt_of_le_of_lt (Nat.zero_le ((j i).val)) (j i).isLt

theorem length_pos_of_dense (A : ResidueBoxSlice N q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    0 < A.length i :=
  A.length_pos_of_integerPoints_nonempty hA.nonempty i

theorem length_lower_of_dense (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (i : I) :
    Real.exp (-c) * (N i : ℝ) ≤ (A.length i : ℝ) := by
  have hlength := A.length_pos_of_dense hA
  obtain ⟨start, m, H, hm, hH, _, hdense, heq⟩ := hA
  have hcard := congrArg
    (fun s : Finset (I → ℤ) => (s.image (fun x => x i)).card) heq
  rw [A.integerPoints_eq_commonStrideBox,
    commonStrideBox_axis_card _ _ _ hq hlength,
    commonStrideBox_axis_card _ _ _ hm hH] at hcard
  rw [hcard]
  exact hdense i

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} {P N : I → ℕ} {q : ℕ}

namespace ResidueBoxSlice

def enlargeBox (S : ResidueBoxSlice P q) (N : I → ℕ)
    (hPN : ∀ i, P i ≤ N i) : ResidueBoxSlice N q where
  start := S.start
  length := S.length
  inside i j hj := (S.inside i j hj).trans_le (hPN i)

@[simp] theorem enlargeBox_start (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).start = S.start := rfl

@[simp] theorem enlargeBox_length (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) : (S.enlargeBox N hPN).length = S.length := rfl

@[simp] theorem enlargeBox_integerPoint (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (u : ∀ i, Fin (S.length i)) :
    (S.enlargeBox N hPN).integerPoint u = S.integerPoint u := rfl

variable [Fintype I] [DecidableEq I]

@[simp] theorem enlargeBox_integerPoints (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) :
    (S.enlargeBox N hPN).integerPoints = S.integerPoints := rfl

end ResidueBoxSlice

variable [Fintype I] [DecidableEq I]

def integerBoxInclusion (hPN : ∀ i, P i ≤ N i) : integerBox P → integerBox N :=
  fun x => ⟨x.val, (mem_integerBox N x.val).mpr (fun i =>
    ⟨((mem_integerBox P x.val).mp x.property i).1,
      (((mem_integerBox P x.val).mp x.property i).2).trans_le
        (by exact_mod_cast hPN i)⟩)⟩

@[simp] theorem integerBoxInclusion_val (hPN : ∀ i, P i ≤ N i)
    (x : integerBox P) : (integerBoxInclusion hPN x).val = x.val := rfl

namespace ResidueBoxSlice

@[simp] theorem enlargeBox_fullSlicePointInIntegerBox (S : ResidueBoxSlice P q)
    (hPN : ∀ i, P i ≤ N i) (u : ∀ i, Fin (S.length i)) :
    (S.enlargeBox N hPN).fullSlicePointInIntegerBox u =
      integerBoxInclusion hPN (S.fullSlicePointInIntegerBox u) := rfl

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} [Fintype U] [DecidableEq U] {N : U → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

def comap (A : ResidueBoxSlice N q) (e : V → I) :
    ResidueBoxSlice (fun v => N (e v)) q where
  start v := A.start (e v)
  length v := A.length (e v)
  inside v j hj := A.inside (e v) j hj

def coordinateProjection (A : ResidueBoxSlice N q) (keep : I → Prop) :
    ResidueBoxSlice (fun i : {i // keep i} => N i) q :=
  A.comap Subtype.val

variable [Fintype I] [DecidableEq I]

theorem comap_isDenseCommonStrideBox [Fintype V] [DecidableEq V]
    (A : ResidueBoxSlice N q) (hq : 0 < q) {c : ℝ}
    (hA : IsDenseCommonStrideBox N c A.integerPoints) (e : V → I) :
    IsDenseCommonStrideBox (fun v => N (e v)) c (A.comap e).integerPoints := by
  refine ⟨fun v => ((A.comap e).start v : ℤ), q, (A.comap e).length,
    hq, ?_, (A.comap e).progression_inside, ?_,
    (A.comap e).integerPoints_eq_commonStrideBox⟩
  · intro v
    exact A.length_pos_of_dense hA (e v)
  · intro v
    exact A.length_lower_of_dense hq hA (e v)

theorem mem_integerPoints_iff (A : ResidueBoxSlice N q) (x : I → ℤ) :
    x ∈ A.integerPoints ↔
      ∀ i, x i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
  rw [A.integerPoints_eq_commonStrideBox]
  exact Fintype.mem_piFinset

theorem finiteSplitPoint_mem_integerPoints
    (A : ResidueBoxSlice N q) (keep : I → Prop)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i : {i // ¬keep i},
      fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i))
    {x : {i // keep i} → ℤ} (hx : x ∈ (A.coordinateProjection keep).integerPoints) :
    finiteSplitPoint keep x fixed ∈ A.integerPoints := by
  apply (A.mem_integerPoints_iff _).mpr
  have hx' := ((A.coordinateProjection keep).mem_integerPoints_iff x).mp hx
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dif_pos hi, coordinateProjection, comap] using hx' ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

theorem exists_coordinate_fiber_score
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ A.integerPoints, score x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      a ≤ 𝔼 x ∈ (A.coordinateProjection keep).integerPoints,
        score (finiteSplitPoint keep x fixed) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), score (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          score (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq score, hsplit] at hmean
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  refine ⟨fixedOf v, hfixed, ?_, ?_⟩
  · intro x hx
    exact A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx
  · rw [(A.coordinateProjection keep).expect_integerPoints hq]
    exact hv

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

def axisInclusion (hsub : ∀ i, keep i → oldKeep i) (i : {i // keep i}) :
    {i // oldKeep i} :=
  ⟨i.val, hsub i.val i.property⟩

noncomputable def axisInsertion
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) : {i // oldKeep i} → ℤ :=
  fun i => if hi : keep i.val then u ⟨i.val, hi⟩ else fixed ⟨i, hi⟩

@[simp] theorem axisInsertion_kept (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (u : {i // keep i} → ℤ) (i : {i // keep i}) :
    axisInsertion oldKeep keep fixed u (axisInclusion oldKeep keep hsub i) = u i := by
  simp [axisInsertion, axisInclusion, i.property]

theorem axisInsertion_injective (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ) :
    Function.Injective (axisInsertion oldKeep keep fixed) := by
  intro x y h
  funext i
  simpa only [axisInsertion_kept] using
    congrFun h (axisInclusion oldKeep keep hsub i)

variable {oldKeep keep} {N : K → ℕ} {q oldq : ℕ}

noncomputable def extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) q where
  start i := if hi : keep i.val then S.start ⟨i.val, hi⟩ else (fixed ⟨i, hi⟩).toNat
  length i := if hi : keep i.val then S.length ⟨i.val, hi⟩ else 1
  inside i j hj := by
    by_cases hi : keep i.val
    · simpa only [dif_pos hi] using
        S.inside ⟨i.val, hi⟩ j (by simpa only [dif_pos hi] using hj)
    · have hj0 : j = 0 := by
        simpa only [dif_neg hi, Nat.lt_one_iff] using hj
      have hf := Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))
      simpa only [dif_neg hi, hj0, mul_zero, add_zero] using
        (show (fixed ⟨i, hi⟩).toNat < N i.val by omega)

attribute [local irreducible] integerProgressionSupport

variable [Fintype K]

theorem extendAxes_integerPoints
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val)) :
    (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints =
      S.integerPoints.image (axisInsertion oldKeep keep fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // keep i}, Fin (S.length i) := fun i =>
      ⟨(j (axisInclusion oldKeep keep hsub i)).val, by
        simpa [extendAxes, axisInclusion, i.property] using
          (j (axisInclusion oldKeep keep hsub i)).isLt⟩
    refine Finset.mem_image.mpr ⟨S.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, t, axisInclusion]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [extendAxes, dif_neg hi, Nat.lt_one_iff] using this
      have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, hj0,
        Int.toNat_of_nonneg hf]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((@extendAxes K oldKeep keep N q oldq S A fixed hfixed).length i) := fun i =>
      if hi : keep i.val then
        ⟨(t ⟨i.val, hi⟩).val, by
          simp only [extendAxes, dif_pos hi]
          exact (t ⟨i.val, hi⟩).isLt⟩
      else ⟨0, by simp [extendAxes, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : keep i.val
    · simp [axisInsertion, integerPoint, point, extendAxes, hi, j]
    · have hf := (Finset.mem_Ico.mp (A.progression_inside i (hfixed ⟨i, hi⟩))).1
      simp [axisInsertion, integerPoint, point, extendAxes, hi, j,
        Int.toNat_of_nonneg hf]

theorem expect_extendAxes
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (hsub : ∀ i, keep i → oldKeep i)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W]
    (f : ({i // oldKeep i} → ℤ) → W) :
    (𝔼 x ∈ (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints, f x) =
      𝔼 x ∈ S.integerPoints, f (axisInsertion oldKeep keep fixed x) := by
  rw [S.extendAxes_integerPoints (N := N) A hsub fixed hfixed]
  exact Finset.expect_image (axisInsertion_injective oldKeep keep hsub fixed).injOn

theorem extendAxes_dense
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (A : ResidueBoxSlice (fun i : {i // oldKeep i} => N i.val) oldq)
    (fixed : {i : {i // oldKeep i} // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (A.start i.val : ℤ) oldq (A.length i.val))
    (hq : 0 < q) {outCost shortCost : ℝ}
    (hS : IsDenseCommonStrideBox (fun i : {i // keep i} => N i.val)
      outCost S.integerPoints)
    (hshort : ∀ i : {i // oldKeep i}, ¬keep i.val →
      (N i.val : ℝ) ≤ Real.exp shortCost) :
    IsDenseCommonStrideBox (fun i : {i // oldKeep i} => N i.val)
      (max outCost shortCost) (@extendAxes K oldKeep keep N q oldq S A fixed hfixed).integerPoints := by
  let T := @extendAxes K oldKeep keep N q oldq S A fixed hfixed
  refine ⟨fun i => (T.start i : ℤ), q, T.length, hq, ?_,
    T.progression_inside, ?_, T.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : keep i.val
    · simpa only [T, extendAxes, dif_pos hi] using S.length_pos_of_dense hS ⟨i.val, hi⟩
    · simp [T, extendAxes, hi]
  · intro i
    by_cases hi : keep i.val
    · calc
        _ ≤ Real.exp (-outCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ T.length i := by
          simpa only [T, extendAxes, dif_pos hi] using
            S.length_lower_of_dense hq hS ⟨i.val, hi⟩
    · simp only [T, extendAxes, dif_neg hi, Nat.cast_one]
      calc
        _ ≤ Real.exp (-shortCost) * (N i.val : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))) (Nat.cast_nonneg _)
        _ ≤ Real.exp (-shortCost) * Real.exp shortCost :=
          mul_le_mul_of_nonneg_left (hshort i hi) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem coordinate_complexMean
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ A.integerPoints, f x) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u
            (fun i => ((A.start i + q * (v i).val : ℕ) : ℤ))) := by
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => Fin (A.length i))
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hsplit : (𝔼 j : (∀ i, Fin (A.length i)), f (A.integerPoint j)) =
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        𝔼 u : (∀ i : {i // keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint u)
            (fixedOf v)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, Fin (A.length i)) ×
          (∀ i : {i // ¬keep i}, Fin (A.length i)),
          f (finiteSplitPoint keep ((A.coordinateProjection keep).integerPoint uv.1)
            (fixedOf uv.2)) := by
        apply Fintype.expect_equiv e
        intro j
        congr 1
        funext i
        by_cases hi : keep i <;>
          simp [e, integerPoint, point, coordinateProjection, comap, fixedOf,
            finiteSplitPoint, hi, Equiv.piEquivPiSubtypeProd]
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  rw [A.expect_integerPoints hq f, hsplit]
  apply Finset.expect_congr rfl
  intro v _
  exact ((A.coordinateProjection keep).expect_integerPoints hq
    (fun u => f (finiteSplitPoint keep u (fixedOf v)))).symm

theorem exists_coordinate_fiber_norm
    (A : ResidueBoxSlice N q) (hq : 0 < q) (hlength : ∀ i, 0 < A.length i)
    (keep : I → Prop) (f : (I → ℤ) → ℂ) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i : {i // ¬keep i},
        fixed i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i)) ∧
      (∀ x ∈ (A.coordinateProjection keep).integerPoints,
        finiteSplitPoint keep x fixed ∈ A.integerPoints) ∧
      ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u fixed)‖ := by
  let : ∀ i, Nonempty (Fin (A.length i)) := fun i => ⟨⟨0, hlength i⟩⟩
  let fixedOf (v : ∀ i : {i // ¬keep i}, Fin (A.length i)) : {i // ¬keep i} → ℤ :=
    fun i => ((A.start i + q * (v i).val : ℕ) : ℤ)
  have hmean : ‖𝔼 x ∈ A.integerPoints, f x‖ ≤
      𝔼 v : (∀ i : {i // ¬keep i}, Fin (A.length i)),
        ‖𝔼 u ∈ (A.coordinateProjection keep).integerPoints,
          f (finiteSplitPoint keep u (fixedOf v))‖ := by
    rw [A.coordinate_complexMean hq hlength keep f]
    exact RCLike.norm_expect_le (K := ℂ)
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have hfixed (i : {i // ¬keep i}) :
      fixedOf v i ∈ integerProgressionSupport (A.start i : ℤ) q (A.length i) := by
    simpa only [fixedOf, Nat.cast_add, Nat.cast_mul] using
      integerProgressionSupport_point (A.start i : ℤ) q (A.length i) hq
        (v i).val (v i).isLt
  exact ⟨fixedOf v, hfixed,
    fun _ hx => A.finiteSplitPoint_mem_integerPoints keep (fixedOf v) hfixed hx, hv⟩

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LieSubalgebraLatticeInnerGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators Matrix TensorProduct

theorem integralVector_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) (z : κ → ℤ) :
    IntegralVector (B *ᵥ ((q : ℚ) • (fun j => (z j : ℚ)))) := by
  classical
  choose c hc using hB
  refine ⟨fun i => ∑ j, c j i * z j, fun i => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h : (q : ℚ) * B i j = (c j i : ℚ) := hc j i
  rw [← h]
  ring

theorem scaledIntegerGrid_mulVec_of_column_denominators
    {ι κ : Type*} [Fintype κ] (B : Matrix ι κ ℚ) (l q : ℕ)
    (hB : ∀ j, B.col j ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ B.mulVec ⁻¹' scaledIntegerGrid l := by
  rintro x ⟨z, rfl⟩
  have h := scaled_grid_mulVec B l _ (integralVector_mulVec_of_column_denominators B q hB z)
  simpa only [Set.mem_preimage, smul_smul, Nat.cast_mul] using h

theorem bchSubgroup_comap_inner_grid_of_columns
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hcolumns : ∀ j, e.equivFun (φ (b j)) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates b
      (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  have hB : ∀ j, (LinearMap.toMatrix b e φ.toLinearMap).col j ∈ denominatorGrid q := by
    intro j
    have he : (LinearMap.toMatrix b e φ.toLinearMap).col j =
        e.equivFun (φ (b j)) := by
      funext i
      exact LinearMap.toMatrix_apply b e φ.toLinearMap i j
    rw [he]
    exact hcolumns j
  intro x hx
  exact hinner (scaledIntegerGrid_mulVec_of_column_denominators _ l q hB hx)

theorem lieSubalgebra_comap_inner_grid_of_columns
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hcolumns : ∀ j, b.equivFun (bk j : L) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates bk
      (Γ.comap (NilpotentLieBCHGroup.map
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) :=
  bchSubgroup_comap_inner_grid_of_columns bk b K.incl Γ l q hinner hcolumns

namespace NilpotentLieBCHGroup

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedSubquotient
namespace OAI

section

namespace Erdos3

open Module

theorem supportedSubmoduleBasis_comap_span {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (P Q : Submodule K V) (S T : Set ι)
    (hP : P = Submodule.span K (b '' S)) (hQ : Q = Submodule.span K (b '' T)) :
    Q.comap P.subtype = Submodule.span K
      (supportedSubmoduleBasis b P S hP '' {i : S | i.val ∈ T}) := by
  ext x
  change x.val ∈ Q ↔ _
  rw [hQ, basis_mem_span_image_iff, basis_mem_span_image_iff]
  constructor
  · intro h i hi
    rw [supportedSubmoduleBasis_repr]
    exact h i.val hi
  · intro h i hi
    by_cases hs : i ∈ S
    · have hh := h ⟨i, hs⟩ hi
      simpa only [supportedSubmoduleBasis_repr] using hh
    · exact (basis_mem_span_image_iff b S x.val).mp (hP.le x.property) i hs

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitPreimageSpanning
namespace OAI

section

namespace Erdos3

variable {R V W ι κ : Type*} [Field R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem comap_eq_section_image_sup_kernel (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W) :
    U.comap P = U.map S ⊔ LinearMap.ker P := by
  ext x
  constructor
  · intro hx
    apply Submodule.mem_sup.mpr
    refine ⟨S (P x), ⟨P x, hx, rfl⟩, x - S (P x), ?_, ?_⟩
    · change P (x - S (P x)) = 0
      rw [map_sub, hS, sub_self]
    · abel
  · intro hx
    obtain ⟨a, ⟨y, hy, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    change P (S y + b) ∈ U
    rw [map_add, hS, show P b = 0 from hb, add_zero]
    exact hy

theorem span_range_sumElim (v : ι → V) (w : κ → V) :
    Submodule.span R (Set.range (Sum.elim v w)) =
      Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range w) := by
  have he : Set.range (Sum.elim v w) = Set.range v ∪ Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [he, Submodule.span_union]

theorem split_preimage_spanning (P : V →ₗ[R] W) (S : W →ₗ[R] V)
    (hS : ∀ x, P (S x) = x) (U : Submodule R W)
    (v : ι → W) (hv : Submodule.span R (Set.range v) = U)
    (k : κ → V) (hk : Submodule.span R (Set.range k) = LinearMap.ker P) :
    Submodule.span R (Set.range (Sum.elim (fun i => S (v i)) k)) = U.comap P := by
  rw [span_range_sumElim, hk, comap_eq_section_image_sup_kernel P S hS, ← hv,
    Submodule.map_span]
  congr 1
  exact congrArg (Submodule.span R) (Set.range_comp S v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EpochEventRank
namespace OAI

section

namespace Erdos3

def epochStackRank (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r * (d + 1) ^ rs.length + epochStackRank d rs

inductive EpochStackEvent (d : ℕ) : List ℕ → List ℕ → Prop
  | head {r r' : ℕ} {xs ys : List ℕ} (drop : r' < r) (length : ys.length = xs.length)
      (bounded : ∀ q ∈ ys, q ≤ d) : EpochStackEvent d (r :: xs) (r' :: ys)
  | tail {r : ℕ} {xs ys : List ℕ} (event : EpochStackEvent d xs ys) :
      EpochStackEvent d (r :: xs) (r :: ys)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEquivTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [DecidableEq ι] [∀ i, Fintype (Y i)] in
theorem productCoordinate_indicator (x y : ∀ i, Y i) :
    (if x = y then (1 : ℝ) else 0) = ∏ i, if x i = y i then (1 : ℝ) else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem productMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => f (fun i => F i (x i))) =
      (FiniteProbabilityWeights.pi q).mean f := by
  classical
  have he (x : ∀ i, X i) : f (fun i => F i (x i)) =
      ∑ y : ∀ i, Y i, f y * ∏ i, if F i (x i) = y i then (1 : ℝ) else 0 := by
    simp_rw [← productCoordinate_indicator]
    simp
  have hi (i : ι) (y : Y i) : (p i).mean (fun z => if F i z = y then (1 : ℝ) else 0) =
      (q i).weight y := by
    rw [hF i (fun z => if z = y then (1 : ℝ) else 0)]
    simp [FiniteProbabilityWeights.mean]
  have hp (y : ∀ i, Y i) : (FiniteProbabilityWeights.pi p).mean
      (fun x => ∏ i, if F i (x i) = y i then (1 : ℝ) else 0) = ∏ i, (q i).weight (y i) := by
    rw [FiniteProbabilityWeights.mean_pi_product p (fun i z => if F i z = y i then (1 : ℝ) else 0)]
    exact Finset.prod_congr rfl (fun i _ => hi i (y i))
  simp_rw [he, FiniteProbabilityWeights.mean_sum, FiniteProbabilityWeights.mean_const_mul, hp]
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro y _
  change f y * (∏ i, (q i).weight (y i)) = (∏ i, (q i).weight (y i)) * f y
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityCoupling {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) where
  law : FiniteProbabilityWeights (X × Y)
  left_mean : ∀ f : X → ℝ, law.mean (fun z => f z.1) = p.mean f
  right_mean : ∀ f : Y → ℝ, law.mean (fun z => f z.2) = q.mean f

noncomputable def FiniteProbabilityCoupling.ofKernel {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y)
    (hK : ∀ f : Y → ℝ, p.mean (fun x => (K x).mean f) = q.mean f) :
    FiniteProbabilityCoupling p q where
  law := p.joint K
  left_mean f := by simp only [FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  right_mean f := by rw [FiniteProbabilityWeights.joint_mean]; exact hK f

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def productCouplingPairing (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean
    (fun z => f (fun i => (z i).1) * g (fun i => (z i).2))

theorem productCoupling_right_mean (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi ν).mean f :=
  productMean_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean) f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

noncomputable def productCouplingAtomMass (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi (fun i => (c i).law)).weight I (fun i => (x i, y i))

theorem productCouplingPairing_indicators (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    productCouplingPairing c (productFiberIndicator I x) (productFiberIndicator I y) =
      productCouplingAtomMass c I x y := by
  unfold productCouplingPairing productCouplingAtomMass productFiberMass FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  have he : (∀ i ∈ I, z i = (x i, y i)) ↔
      ((∀ i ∈ I, (z i).1 = x i) ∧ (∀ i ∈ I, (z i).2 = y i)) := by
    simp only [Prod.ext_iff, forall_and]
  unfold productFiberIndicator
  dsimp only
  split_ifs <;> norm_num <;> aesop

theorem productCouplingAtomMass_nonneg (I : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    0 ≤ productCouplingAtomMass c I x y :=
  productFiberMass_nonneg _ (FiniteProbabilityWeights.pi (fun i => (c i).law)).nonneg I _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_sum_left {α : Type*} (s : Finset α)
    (f : α → (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => ∑ a ∈ s, f a x) g =
      ∑ a ∈ s, productCouplingPairing c (f a) g := by
  simp only [productCouplingPairing, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]

theorem productCouplingAtomMass_sum_left (I : Finset ι)
    (base : ∀ i, X i) (y : ∀ i, Y i) :
    (∑ a : ∀ i : I, X i, productCouplingAtomMass c I (productSubtypePoint I a base) y) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I y := by
  simp_rw [← productCouplingPairing_indicators]
  rw [← productCouplingPairing_sum_left]
  simp_rw [productFiberIndicator_sum_subtype]
  simpa only [productCouplingPairing, one_mul, productFiberMass, FiniteProbabilityWeights.mean]
    using productCoupling_right_mean c (productFiberIndicator I y)

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

noncomputable def ProductCylinder.referenceMass (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (c : ProductCylinder X) : ℝ :=
  productFiberMass (FiniteProbabilityWeights.pi μ).weight c.1 (c.assignment base)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonMarkedFrequencyModel
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

theorem integral_frequency_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * (l * H ^ d) : ℕ) : ℝ) ≤
      Real.exp (((p + 2) ^ 2 + (K + 5 : ℕ)) ^ (K + 5)) := by
  have hpQ : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide)
  have hlQ : ((l * H ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ Real.exp p * Real.exp p ^ d :=
        mul_le_mul hl (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (p + (d : ℝ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hp, hd, sq_nonneg p])
  exact integral_grid_allowance_le_exp K d H (l * H ^ d) (hp.trans hpQ) (hd.trans hpQ)
    (hH.trans (Real.exp_le_exp.mpr hpQ)) hlQ

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

noncomputable def finiteResidueModeModel (residue : ∀ a, J → ZMod (D a)) (x : J → ℝ) : ℂ :=
  ∑ a, coefficient a * (star (rationalGridPhase (D a) (frequency a) (residue a)) * mode a x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedAffineModerateIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : ℤ)
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) : J → ℤ :=
  fun S => (offset + (x.1 none : ℤ)) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun r => (x.2 j r : ℤ))) S

noncomputable def weightedAffineModerateIntegerJetSum {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) : J → ℤ :=
  shift + ∑ b, weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) J (offset b) (x b)

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

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def weightedAffineModerateGridApproximation {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ)
    (S : Finset (J → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ J.card * ∑ k ∈ S,
    (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k) *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

noncomputable def weightedAffineModeratePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    weightedAffineModerateGridApproximation c s u v K M rows offset shift z F

noncomputable def weightedAffinePlateauModeCoefficient (K M : ℕ) (rows : Finset (Finset I))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card *
    ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k

noncomputable def weightedAffinePlateauModeModel (p : PMF T) (H : ℝ) (K : ℕ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) : ℂ :=
  finiteResidueModeModel (fun k : F => D k) (fun k => a k)
    (fun k => weightedAffinePlateauModeCoefficient c s u v offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift) residue x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def patchKernelGridRadius (N : ℕ) : ℝ≥0 := 1 / (2 * N)

theorem patchKernelGridRadius_pos {N : ℕ} (hN : 0 < N) : 0 < patchKernelGridRadius N := by
  have : (0 : ℝ≥0) < N := by exact_mod_cast hN
  unfold patchKernelGridRadius
  positivity

theorem patchKernelGridRadius_small {N : ℕ} (hN : 8 ≤ N) :
    2 * (patchKernelGridRadius N : ℝ) ≤ 1 / 8 := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  field_simp
  linarith

noncomputable def gridPatchKernel (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PatchKernel d where
  value x := regularizedTentPartition (uniformBoxGrid (1 / 4) N)
    (patchKernelGridRadius N) i (x + uniformBoxGrid (1 / 4) N i)
  nonneg x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).1
  le_one x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).2
  support x hx j := by
    have hnear : dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) <
        2 * (patchKernelGridRadius N : ℝ) := by
      by_contra! hfar
      exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
    have hj := dist_le_pi_dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) j
    simp only [Real.dist_eq, Pi.add_apply, add_sub_cancel_right] at hj
    exact (hj.trans hnear.le).trans ((patchKernelGridRadius_small hN).trans (by norm_num))
  lip := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  lipschitz := by
    have h := (regularizedTentPartition_lipschitz (uniformBoxGrid (ι := Fin d) (1 / 4) N)
      (patchKernelGridRadius_pos (N := N) (by omega)) i).comp
      (isometry_add_right (uniformBoxGrid (1 / 4) N i)).lipschitz
    simpa only [Fintype.card_fun, Fintype.card_fin, mul_one, Function.comp_def] using h

theorem gridPatchKernel_translate (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ) :
    (gridPatchKernel d N hN i).value (x - uniformBoxGrid (1 / 4) N i) =
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x := by
  simp only [gridPatchKernel, sub_add_cancel]

theorem gridPatchKernel_original_support {d N : ℕ} (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ)
    (hx : regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x ≠ 0)
    (j : Fin d) : |x j| ≤ 3 / 8 := by
  have hnear : dist x (uniformBoxGrid (1 / 4) N i) < 2 * (patchKernelGridRadius N : ℝ) := by
    by_contra! hfar
    exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
  have hcoord := dist_le_pi_dist x (uniformBoxGrid (1 / 4) N i) j
  rw [Real.dist_eq] at hcoord
  have hcenter := uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1 / 4) (by omega : 0 < N) i j
  have htriangle : |x j| ≤ |x j - uniformBoxGrid (1 / 4) N i j| +
      |uniformBoxGrid (1 / 4) N i j| := by
    simpa only [sub_add_cancel] using
      abs_add_le (x j - uniformBoxGrid (1 / 4) N i j) (uniformBoxGrid (1 / 4) N i j)
  linarith [patchKernelGridRadius_small hN]

theorem PatchKernel.grid_approx {d N : ℕ} (Φ : PatchKernel d) (hN : 8 ≤ N) (x : Fin d → ℝ) :
    |Φ.value x - ∑ i : Fin d → Fin (N + 1),
      Φ.value (uniformBoxGrid (1 / 4) N i) *
        regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x| ≤
      2 * Φ.lip * (patchKernelGridRadius N : ℝ) := by
  have hcover (y : Fin d → ℝ) (hy : Φ.value y ≠ 0) :=
    exists_uniformBoxGrid_approx (by norm_num : (0 : ℝ) < 1 / 4) (by omega : 0 < N) y (Φ.support y hy)
  have hr : (patchKernelGridRadius N : ℝ) = 2 * (1 / 4 : ℝ) / N := by
    simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
    ring
  have h := regularizedTentPartition_approx (uniformBoxGrid (1 / 4) N)
    (show 0 < (patchKernelGridRadius N : ℝ) from patchKernelGridRadius_pos (N := N) (by omega))
    Φ.value Φ.lipschitz (fun y hy => by rw [hr]; exact hcover y hy) x
  simpa only [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_combination_term {I : Type*} [Fintype I] [Nonempty I]
    (c a : I → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hsum : δ ≤ ∑ i, c i * a i) :
    ∃ i, δ / Fintype.card I ≤ a i := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmean : δ / Fintype.card I ≤ 𝔼 i, c i * a i := by
    rw [Fintype.expect_eq_sum_div_card]
    exact div_le_div_of_nonneg_right hsum hn.le
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have ha : 0 ≤ a i := by
    by_contra! hneg
    have hmul := mul_nonpos_of_nonneg_of_nonpos (hc i).1 hneg.le
    linarith [div_pos hδ hn]
  exact ⟨i, hi.trans (mul_le_of_le_one_left ha (hc i).2)⟩

namespace PolynomialPatch

variable {X : Type*} {s d N : ℕ}

noncomputable def gridKernelReplacement (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PolynomialPatch X s d :=
  A.shiftedKernel (uniformBoxGrid (1 / 4) N i) (gridPatchKernel d N hN i)

theorem gridKernelReplacement_value (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : X → ℝ) :
    (A.gridKernelReplacement hN i).value x = ∑' z,
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i
        ((A.form.slots x).residual z) := by
  simp only [gridKernelReplacement, shiftedKernel_value, gridPatchKernel_translate]

theorem gridKernelReplacement_approx (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (x : X → ℝ) :
    |A.value x - ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) * (A.gridKernelReplacement hN i).value x| ≤
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
  have h := (A.form.slots x).tsum_approx_finite_family A.kernel.value
    (regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N))
    (fun i => A.kernel.value (uniformBoxGrid (1 / 4) N i))
    (R := 3 / 8) (by norm_num) (by positivity)
    (fun y hy j => (A.kernel.support y hy j).trans (by norm_num))
    (fun i y hy j => gridPatchKernel_original_support hN i y hy j)
    (A.kernel.grid_approx hN)
  simp_rw [gridKernelReplacement_value]
  exact h

theorem gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1) :
    p.mean (fun x => score x * A.value (point x)) - 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤
      ∑ i : Fin d → Fin (N + 1), A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  let c := fun i : Fin d → Fin (N + 1) => A.kernel.value (uniformBoxGrid (1 / 4) N i)
  let g := fun x => ∑ i : Fin d → Fin (N + 1), c i * (A.gridKernelReplacement hN i).value (point x)
  have hpoint (x) : score x * A.value (point x) ≤ score x * g x +
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
    have hbound : |score x * (A.value (point x) - g x)| ≤
        2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore x) (abs_nonneg _)).trans
        (by simpa only [one_mul, g, c] using A.gridKernelReplacement_approx hN (point x))
    linarith [le_abs_self (score x * (A.value (point x) - g x))]
  have hmean := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const] at hmean
  have hidentity : p.mean (fun x => score x * g x) =
      ∑ i, c i * p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    rw [p.mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← p.mean_const_mul]
    congr 1
    funext x
    ring
  rw [hidentity] at hmean
  exact (sub_le_iff_le_add).mpr hmean

theorem exists_gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpositive : δ ≤ p.mean (fun x => score x * A.value (point x)))
    (hmesh : 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤ δ / 2) :
    ∃ i : Fin d → Fin (N + 1), δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  have h := A.gridKernelReplacement_score hN p point score hscore
  have hs : δ / 2 ≤ ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by linarith
  obtain ⟨i, hi⟩ := exists_positive_combination_term _ _
    (fun i => ⟨A.kernel.nonneg _, A.kernel.le_one _⟩) (by positivity : 0 < δ / 2) hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_div] using hi

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_patch_kernel_mesh (d : ℕ) {L p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 8 ≤ N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) ∧
      2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 ∧
      (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 1) * (2 * p + 11)) ∧
      (((2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N : ℝ≥0) : ℝ) ≤
        Real.exp (2 * ((p + 1) * (2 * p + 11)) + 2) := by
  let b := 2 * p + 8
  let N := ⌈Real.exp b⌉₊
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hNlo : Real.exp b ≤ (N : ℝ) := Nat.le_ceil _
  have h8 : (8 : ℝ) ≤ N := by
    have hexp : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    exact (hexp.trans (Real.exp_le_exp.mpr (by dsimp only [b]; linarith))).trans hNlo
  have hN : 8 ≤ N := by exact_mod_cast h8
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (b + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg b)).le
    have h1 := Real.one_le_exp hb
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg b)
    dsimp only [N] at *
    linarith
  have hbound : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) := by
    convert hNhi using 1; dsimp only [b]; congr 1; ring
  have herr : L / N ≤ Real.exp (-p - 8) := by
    calc
      L / N ≤ L / Real.exp b := div_le_div_of_nonneg_left hL (Real.exp_pos b) hNlo
      _ ≤ Real.exp p / Real.exp b := div_le_div_of_nonneg_right hLp (Real.exp_nonneg b)
      _ = Real.exp (-p - 8) := by
        rw [← Real.exp_sub]
        congr 1
        dsimp only [b]
        ring
  have h8exp : (2 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8exp
  have haccuracy : 2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 := by
    have heq : 2 * L * (patchKernelGridRadius N : ℝ) = L / N := by
      simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
        NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
      ring
    rw [heq]
    apply herr.trans
    rw [sub_eq_add_neg, Real.exp_add]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  let q := (p + 1) * (2 * p + 11)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hq2 : 2 * p + 11 ≤ q := by dsimp only [q]; nlinarith
  have hcount : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (by positivity) hbound d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 2 * p + 10)
    dsimp only [q]
    nlinarith
  have hradius : 1 / (patchKernelGridRadius N : ℝ) ≤ Real.exp q := by
    have heq : 1 / (patchKernelGridRadius N : ℝ) = 2 * (N : ℝ) := by
      simp [patchKernelGridRadius]
    rw [heq]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ 2 * ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (2 * p + 10) := mul_le_mul h2 hbound (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 11) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq2
  exact ⟨N, hN, hbound, haccuracy, hcount,
    metricPartition_constant_le_exp ((N + 1) ^ d) (patchKernelGridRadius N) hq hcount hradius⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeUnitBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalizedSupportedCubeSum_norm_le_one {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) :
    ‖normalizedSupportedCubeSum j Q F‖ ≤ 1 := by
  have hprod (c : SupportedCube j (Q : Set A)) :
      ‖mixedCubeProduct F c.val.1 c.val.2‖ ≤ 1 := by
    simp only [mixedCubeProduct, norm_prod, conjugationPower_norm]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun ω _ => hF ω _ (c.property ω))
  have hsum : ‖supportedCubeSum j (Q : Set A) F‖ ≤
      (Nat.card (SupportedCube j (Q : Set A)) : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hprod c)
  rw [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast]
  by_cases hc : Nat.card (SupportedCube j (Q : Set A)) = 0
  · simp only [hc, Nat.cast_zero, div_zero, zero_le_one]
  · have hpos : (0 : ℝ) < Nat.card (SupportedCube j (Q : Set A)) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using hsum)

theorem finiteSupportGowersNorm_le_one_of_embedding
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (f : A → ℂ) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) :
    finiteSupportGowersNorm (j + 1) Q f ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) zero_le_one
  rw [one_pow, ← normalizedSupportedCubeSum_self_re hφ]
  exact (Complex.re_le_norm _).trans
    (normalizedSupportedCubeSum_norm_le_one (j + 1) Q (fun _ => f) (fun _ => hf))

theorem normalizedSupportedCubeSum_le_vertex
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ)
    (hF : ∀ ω x, x ∈ Q → ‖F ω x‖ ≤ 1) (ω₀ : Fin (j + 1) → Bool) :
    ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤ finiteSupportGowersNorm (j + 1) Q (F ω₀) := by
  have hnonneg (ω) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (F ω) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hprod : (∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω)) ≤
      ∏ ω, if ω = ω₀ then finiteSupportGowersNorm (j + 1) Q (F ω₀) else 1 := by
    apply Finset.prod_le_prod (fun ω _ => hnonneg ω)
    intro ω _
    split_ifs with h
    · subst ω; exact le_rfl
    · exact finiteSupportGowersNorm_le_one_of_embedding hφ j (F ω) (hF ω)
  have hcs : ‖normalizedSupportedCubeSum (j + 1) Q F‖ ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
    simpa only [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast] using
      norm_supportedCubeSum_le_of_embedding hφ j F
  exact hcs.trans (by simpa using hprod)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rectangularScalarDiscrepancy {I J : Type*}
    [Fintype I] [Fintype J] (parent : I → ℤ) (H : I → ℕ)
    (h g : (I → ℤ) → ℂ) (epsilon level : ℝ) (D : ℕ)
    (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (z : Option J × I → ℤ) : ℝ :=
  (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
    realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (h x).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z) -
    (1 + epsilon) * level *
      realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (g x).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))

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

namespace ResidueBoxSlice
variable {J : Type*} [Fintype J] [decJ : DecidableEq J] {N : J → ℕ} {q : ℕ}

noncomputable def scalarParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ j, Finset.Ico (0 : ℤ) (S.length j : ℤ)) ≃ (∀ j, Fin (S.length j)) where
  toFun x j := ⟨(x j).val.toNat, by
    have := Finset.mem_Ico.mp (x j).property
    omega⟩
  invFun t j := ⟨((t j).val : ℤ), by
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩⟩
  left_inv x := by
    funext j
    apply Subtype.ext
    have := (Finset.mem_Ico.mp (x j).property).1
    exact Int.toNat_of_nonneg this
  right_inv t := by
    funext j
    apply Fin.ext
    simp

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
universe u v

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e

@[simp]
theorem topPositiveOrderedFace_rank
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).rank = n + 1 := by
  rfl

@[simp]
theorem topPositiveOrderedFace_lowerRank_succ
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).lowerRank.succ =
      Fin.last (n + 1) := by
  apply Fin.ext
  rfl

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  atomBoundaryDefectSq
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face)
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    upper a x

noncomputable def sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  largeAverageBaseSupport
    (orderedFullLowerBoundaryPartition P.coarse e)
    (P.sourceFullAtomDefectSq e upper a) β

@[simp]
theorem mem_sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullLargeDefectBaseSupport e upper a β ↔
      β <
        conditionalMean
          (orderedFullLowerBoundaryPartition P.coarse e)
          (P.sourceFullAtomDefectSq e upper a) x := by
  exact
    mem_largeAverageBaseSupport
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a) β x

noncomputable def sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  smallAverageBaseSupport
      (orderedBoundaryPartition
        (positiveFaceLowerLayer P.coarse e) e.face)
      (partitionAtomIndicator upper a) α ∪
    P.sourceFullLargeDefectBaseSupport e upper a β

@[simp]
theorem mem_sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullAtomBadBaseSupport e upper a α β ↔
      conditionalMean
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) x < α ∨
        β <
          conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x := by
  rw [sourceFullAtomBadBaseSupport, Finset.mem_union,
    mem_smallAverageBaseSupport,
    P.mem_sourceFullLargeDefectBaseSupport]

noncomputable def sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.sourceFullAtomBadBaseSupport e upper a α β

@[simp]
theorem mem_sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullOwnAtomBadBaseSupport e upper α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [sourceFullOwnAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ P.sourceFullAtomBadBaseSupport
          e upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical : partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [sourceFullOwnAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

noncomputable def sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  P.sourceFullOwnAtomBadBaseSupport e
    (P.coarse.partition e.lowerRank.succ e.face) α β

@[simp]
theorem mem_sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullCoarseOwnAtomBadBaseSupport e α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e
        (P.coarse.partition e.lowerRank.succ e.face)
        (partitionAtomAt
          (P.coarse.partition e.lowerRank.succ e.face) x)
        α β := by
  exact
    P.mem_sourceFullOwnAtomBadBaseSupport e
      (P.coarse.partition e.lowerRank.succ e.face) α β x

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

def AvoidsSourceFullBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    orderedFaceTuple e.face A.witness ∉
      P.sourceFullCoarseOwnAtomBadBaseSupport e
        (α e.rank) (β e.rank)

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubePlateauSite
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [DecidableEq B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)
variable (u : B → Fin (n + 1) → Option α → ℤ) (v : B → Fin (n + 1) → Option α → ℕ)

noncomputable def affineCubePlateauCoefficient (K M : ℕ) (rows : Finset (Finset α))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card * ∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedResidueBlockCells
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

theorem exists_affine_normalized_cell_of_width {ι : Type*} {N : ι → ℕ} {q Q : ℕ}
    (A : ResidueBoxSlice N q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) (hQ : 0 < Q)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hwidth : ∀ i, step * q * A.length i ≤ 2 * T i / Q) :
    ∃ z : ι → Fin (Q + 1), ∀ j : ∀ i, Fin (A.length i), ∀ i,
      |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤
        T i * (2 / Q) := by
  classical
  by_cases hlen : ∀ i, 0 < A.length i
  · exact A.exists_affine_normalized_cell hlen origin step hstep T hT hQ hparent hwidth
  · push Not at hlen
    obtain ⟨i, hi⟩ := hlen
    refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, ?_⟩
    intro j
    have hj := (j i).isLt
    omega

end ResidueBoxSlice

theorem normalized_residue_block_cell {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (H : ι → ℕ) (hq : 0 < q) (hQ : 0 < Q) (hH : ∀ i, 0 < H i)
    (hwidth : ∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ∃ z : ι → Fin (Q + 1),
      ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
      |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  apply ResidueBoxSlice.exists_affine_normalized_cell_of_width _ origin step hstep T hT hQ hparent
  intro i
  have hlen : ((ResidueBoxSlice.ofBlocks H hq hH a).length i : ℝ) ≤ H i := by
    exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
  calc
    _ ≤ step * q * H i := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = step * ((q : ℝ) * H i) := by ring
    _ ≤ step * ((N i : ℝ) / Q) := mul_le_mul_of_nonneg_left (hwidth i) hstep
    _ = (step * N i) / Q := by ring
    _ ≤ 2 * T i / Q := div_le_div_of_nonneg_right (hparentwidth i) (Nat.cast_nonneg _)

theorem exists_normalized_residue_block_cells {ι : Type*} (N : ι → ℕ) (q Q : ℕ)
    (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i) :
    ∃ (H : ι → ℕ) (hH : ∀ i, 0 < H i),
      (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ (N i : ℝ) / Q) ∧
      (∀ i, (N i : ℝ) / (2 * q * Q) ≤ H i) ∧
      ∀ a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label,
        ∃ z : ι → Fin (Q + 1),
          ∀ j : ∀ i, Fin ((ResidueBoxSlice.ofBlocks H hq hH a).length i), ∀ i,
          |origin i + step * ((ResidueBoxSlice.ofBlocks H hq hH a).point j i).val -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hρ : (0 : ℝ) < 1 / Q := by positivity
  have hρ1 : (1 : ℝ) / Q ≤ 1 := (div_le_one hQr).mpr (by exact_mod_cast hQ)
  obtain ⟨H, hH, hfit, hwidth, hlower⟩ := exists_box_block_mesh N q hq hρ hρ1 hlarge
  have hwidth' (i) : (q : ℝ) * H i ≤ (N i : ℝ) / Q := by
    calc
      _ ≤ (1 / (Q : ℝ)) * N i := hwidth i
      _ = _ := by ring
  refine ⟨H, hH, hfit, hwidth', ?_, ?_⟩
  · intro i
    have he : (1 / (Q : ℝ)) * N i / (2 * q) = (N i : ℝ) / (2 * q * Q) := by ring
    rw [← he]
    exact hlower i
  · exact normalized_residue_block_cell N q Q H hq hQ hH hwidth'
      origin step hstep T hT hparent hparentwidth

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem integerPoints_subset_integerBox (A : ResidueBoxSlice N q) :
    A.integerPoints ⊆ integerBox N := by
  classical
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  change 0 ≤ ((A.point j i).val : ℤ) ∧ ((A.point j i).val : ℤ) < (N i : ℤ)
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast (A.point j i).isLt⟩

noncomputable def subtypeSites (A : ResidueBoxSlice N q) : Finset ↥(integerBox N) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A.integerPoints)

@[simp] theorem mem_subtypeSites (A : ResidueBoxSlice N q) (x : integerBox N) :
    x ∈ A.subtypeSites ↔ x.val ∈ A.integerPoints := by
  classical
  simp only [subtypeSites, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subtypeSites_image_val (A : ResidueBoxSlice N q) :
    A.subtypeSites.image Subtype.val = A.integerPoints := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (A.mem_subtypeSites t).mp ht
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, A.integerPoints_subset_integerBox hx⟩,
      (A.mem_subtypeSites _).mpr hx, rfl⟩

theorem expect_subtypeSites (A : ResidueBoxSlice N q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 t ∈ A.subtypeSites, f t.val) = 𝔼 x ∈ A.integerPoints, f x := by
  classical
  rw [← A.subtypeSites_image_val]
  exact (Finset.expect_image Subtype.val_injective.injOn).symm

theorem subtypeSites_nonempty_of_integerPoints (A : ResidueBoxSlice N q)
    (h : A.integerPoints.Nonempty) : A.subtypeSites.Nonempty := by
  classical
  rw [← A.subtypeSites_image_val, Finset.image_nonempty] at h
  exact h

theorem subtypeSites_dense (A : ResidueBoxSlice N q) {cost : ℝ}
    (h : IsDenseCommonStrideBox N cost A.integerPoints) :
    IsDenseCommonStrideBox N cost (A.subtypeSites.image Subtype.val) := by
  classical
  rw [A.subtypeSites_image_val]
  exact h

end Erdos3.ResidueBoxSlice

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialSliceInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ V : Type*} [Finite σ] [AddCommGroup V] [Module ℚ V]
  [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem eq_of_eval₂_eq_on_residueBoxSlice
    {N : σ → ℕ} {step : ℕ} (A : ResidueBoxSlice N step) (hstep : 0 < step)
    {d : ℕ} {p q : VectorPolynomial σ ℚ V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < A.length i)
    (heval : ∀ j : ∀ i, Fin (A.length i),
      eval₂ (fun i => (A.integerPoint j i : ℝ)) p =
        eval₂ (fun i => (A.integerPoint j i : ℝ)) q) :
    p = q := by
  refine eq_of_eval₂_eq_on_grid A.length
    (fun i j => ((A.start i + step * j.val : ℕ) : ℝ)) ?_ hp hq hlen ?_
  · intro i j k h
    apply Fin.ext
    dsimp only at h
    have hnat : A.start i + step * j.val = A.start i + step * k.val := by
      exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hstep (Nat.add_left_cancel hnat)
  · intro j
    simpa only [ResidueBoxSlice.integerPoint, ResidueBoxSlice.point, Int.cast_natCast]
      using heval j

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeMarkedFreezingSliceScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_long_frozen_box {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i)
    (score W : (∀ i, Fin (N i)) → ℝ) (V : (∀ i, (P i).Label) → (∀ i, Fin (N i)) → ℝ)
    {C τ ε S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hW : ∀ x, score x * W x ≤ C)
    (hclose : ∀ x, dist (W x) (V (cell P x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x)
    (hbudget : τ + ε + C * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S) :
    ∃ a : ∀ i, (P i).Label, (∀ i, L i ≤ ((P i).length (a i) : ℝ)) ∧
      τ < 𝔼 j : (∀ i, Fin ((P i).length (a i))), score (point P a j) * V a (point P a j) := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  obtain ⟨a, ha, hs⟩ := exists_good_frozen_partition_score (cell P)
    (fun a => ∀ i, L i ≤ ((P i).length (a i) : ℝ)) score W V hC hτ hε hscoreBound hW
    (short_box_side_mass_le P hN L hL) hclose hscore hbudget
  exact ⟨a, ha, by simpa only [expect_cell] using hs⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open BoxProgressionPartition

theorem exists_long_residue_cell_frozen_score
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score W : (∀ i, Fin (N i)) → ℝ)
    (V : (ι → ZMod q) → (ι → Fin (Q + 1)) → (∀ i, Fin (N i)) → ℝ)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hcap : ∀ x, score x * W x ≤ B)
    (hclose : ∀ r z x, (∀ i, ((x i).val : ZMod q) = r i) →
      (∀ i, |origin i + step * (x i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) →
      dist (W x) (V r z x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x) (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ r : ι → ZMod q, ∃ z : ι → Fin (Q + 1),
        (∀ j : ∀ i, Fin (A.length i), ∀ i, ((A.point j i).val : ZMod q) = r i) ∧
        (∀ j : ∀ i, Fin (A.length i), ∀ i,
          |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * V r z (A.point j) := by
  classical
  obtain ⟨H, hH, hfit, hwidth, hHlower, hcells⟩ :=
    exists_normalized_residue_block_cells N q Q hq hQ origin step hstep T hT hparent
      hparentwidth hlarge
  let P := fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)
  choose z hz using hcells
  let r := fun a : ∀ i, (P i).Label => fun i => ((P i).start (a i) : ZMod q)
  let Vcell := fun a : ∀ i, (P i).Label => V (r a) (z a)
  let L := fun i => θ * H i / (2 * (Fintype.card ι + 1 : ℝ))
  have hL (i) : 0 < L i :=
    (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i) (Fintype.card ι)).2
  have hres (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i) :
      ((point P a j i).val : ZMod q) = r a i := by
    rw [point_val]
    change (((P i).start (a i) + q * (j i).val : ℕ) : ZMod q) = _
    simp [r]
  have hcellclose (x : ∀ i, Fin (N i)) : dist (W x) (Vcell (cell P x) x) ≤ ε := by
    let a := cell P x
    let j := fun i => (P i).offset (x i)
    have hid : point P a j = x := by
      funext i
      exact (P i).point_cell_offset (x i)
    apply hclose (r a) (z a) x
    · intro i
      rw [← hid]
      exact hres a j i
    · have hp : (ResidueBoxSlice.ofBlocks H hq hH a).point j = x :=
        (ResidueBoxSlice.ofBlocks_point H hq hH a j).trans hid
      simpa only [hp] using hz a j
  have hshort : (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) ≤ θ :=
    boxBlock_short_side_budget N H q hN hH hfit hθ.le
  have hbudget' : τ + ε + B * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S :=
    by linarith [mul_le_mul_of_nonneg_left hshort hB]
  obtain ⟨a, ha, hs⟩ := exists_long_frozen_box P hN L (fun i => (hL i).le)
    score W Vcell hB hτ hε hscoreBound hcap hcellclose hscore hbudget'
  let A := ResidueBoxSlice.ofBlocks H hq hH a
  have hlength (i) : 0 < A.length i := by
    have hpos : (0 : ℝ) < (P i).length (a i) := (hL i).trans_le (ha i)
    exact_mod_cast hpos
  refine ⟨A, hlength, ?_, r a, z a, ?_, hz a, ?_⟩
  · intro i
    exact (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i)
      (Fintype.card ι)).1.trans (ha i)
  · intro j i
    rw [ResidueBoxSlice.ofBlocks_point]
    exact hres a j i
  · simpa only [A, ResidueBoxSlice.ofBlocks_point] using hs

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def keepTrueSlice (S : ResidueBoxSlice N q) :
    ResidueBoxSlice (fun i : {_i : I // True} => N i.val) q :=
  S.comap Subtype.val

def keepTrueParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ i, Fin (S.length i)) ≃ (∀ i, Fin (S.keepTrueSlice.length i)) where
  toFun u i := u i.val
  invFun u i := u ⟨i, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype I] [DecidableEq I]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]
    {keep : I → Prop} [dkeep : DecidablePred keep] {N : I → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ}
  {G X : Type}
  [Fintype G]
  [Fintype X]
  {I E J : Fin m → Type}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}
  {L M : Type}
  [LieRing L]
  [LieAlgebra ℚ L]
  [LieRing M]
  [LieAlgebra ℚ M]
  {r d t : ℕ}
  {Fmark : NilpotentLieFiltration M t}
  {φ : L →ₗ⁅ℚ⁆ M}
  {weight : (X → ℤ) → ℂ}
  {cost massThreshold scoreThreshold : ℝ}
  {outputCost outputMass outputScore : ℝ}

namespace AllocatedExternalCandidateProblem.Conclusion

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityUniformResidualGood
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem exists_uniformResidualGood
    {Ω Branch : Type*} [Fintype Ω] [Fintype Branch]
    (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (error : Branch → Ω → ℝ) {ε δ : ℝ}
    (herror : ∀ b a, 0 ≤ error b a) (hmean : ∀ b, law.mean (error b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b, error b a ≤ δ := by
  classical
  let good := fun a => ∀ b, error b a ≤ δ
  let K := H.filter good
  let B := H.filter (fun a => ¬ good a)
  have htotal (a : Ω) : 0 ≤ ∑ b, error b a := Finset.sum_nonneg (fun b _ => herror b a)
  have hbad (a : Ω) (ha : a ∈ B) : δ ≤ ∑ b, error b a := by
    have hnot : ¬ ∀ b, error b a ≤ δ := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb⟩ := not_forall.mp hnot
    exact (le_of_not_ge hb).trans
      (Finset.single_le_sum (fun j _ => herror j a) (Finset.mem_univ b))
  have hmeanSum : law.mean (fun a => ∑ b, error b a) ≤
      (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ b, law.mean (error b) := by
        simp only [mean, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _b : Branch, ε := Finset.sum_le_sum (fun b _ => hmean b)
      _ = _ := by simp
  have hbadmass : δ * law.mass B ≤ (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ a ∈ B, law.weight a * δ := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a ∈ B, law.weight a * ∑ b, error b a :=
        Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hbad a ha) (law.nonneg a))
      _ ≤ law.mean (fun a => ∑ b, error b a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun a _ _ => mul_nonneg (law.nonneg a) (htotal a))
      _ ≤ _ := hmeanSum
  have hsplit : law.mass K + law.mass B = law.mass H := by
    exact Finset.sum_filter_add_sum_filter_not H good law.weight
  have hhalf : law.mass H / 2 ≤ law.mass K := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hsplitδ := congrArg (fun t : ℝ => δ * t) hsplit
    nlinarith only [hbadmass, hbudget, hsplitδ]
  exact ⟨K, Finset.filter_subset good H, hhalf, (by positivity : 0 < law.mass H / 2).trans_le hhalf,
    fun a ha => (Finset.mem_filter.mp ha).2⟩

theorem uniformResidualGood_exp_budget {Branch : Type*} [Fintype Branch]
    {mass massLog branchLog Eres u : ℝ}
    (hmass : Real.exp (-massLog) ≤ mass)
    (hcard : (Fintype.card Branch : ℝ) ≤ Real.exp branchLog)
    (hu : branchLog + Eres + massLog + 2 ≤ u) :
    (Fintype.card Branch : ℝ) * Real.exp (-u) ≤ Real.exp (-Eres) * mass / 2 := by
  calc
    _ ≤ Real.exp branchLog * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (branchLog - u) := by rw [← Real.exp_add]; rfl
    _ ≤ Real.exp (-(Eres + massLog + 2)) := Real.exp_le_exp.mpr (by linarith only [hu])
    _ ≤ Real.exp (-(Eres + massLog)) / 2 := by
      simpa using VectorPolynomial.precenter_native_selection_model_error_budget 0 (Eres + massLog)
    _ = Real.exp (-Eres) * Real.exp (-massLog) / 2 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)) (by norm_num)

theorem exists_uniformSliceResidualGood
    {Ω Branch T X : Type*} [Fintype Ω] [Fintype Branch] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ a, J a → Finset T)
    (tests : ∀ a, J a → T → ℂ) (signal : Branch → X → ℂ)
    {size ε δ : ℝ} (hS : ∀ a j, (slices a j).Nonempty)
    (hsize : ∀ a j, (Fintype.card T : ℝ) / (slices a j).card ≤ size)
    (htests : ∀ a j t, ‖tests a j t‖ ≤ 1)
    (hmean : ∀ b, sampledSliceSeminorm law physical slices tests (signal b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b (j : J a),
        ‖𝔼 t ∈ slices a j, signal b (physical a t) * tests a j t‖ ≤ δ := by
  obtain ⟨K, hKH, hmass, hpos, hgood⟩ := law.exists_uniformResidualGood H
    (fun b => centeredFiniteSliceResidualEnvelope physical slices tests (signal b))
    (fun b => centeredFiniteSliceResidualEnvelope_nonneg physical slices tests (signal b))
    hmean hH hδ hbudget
  refine ⟨K, hKH, hmass, hpos, ?_⟩
  intro a ha b j
  exact (centeredFiniteSliceResidualEnvelope_dominates physical slices tests hS hsize htests
    (signal b) a j).trans (hgood a ha b)

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

structure CenteredForecastModel (X : Type*) where
  nterms : ℕ
  positive : 0 < nterms
  models : Fin nterms → X → ℂ
  coefficient : Fin nterms → ℝ
  residual : X → ℂ

variable {X Y F : Type*} [Fintype X] [MeasurableSpace Y]

def CenteredForecastModelBounds
    (jointLaw : Measure Y) (native : Set (X → ℂ))
    (reference : FiniteProbabilityWeights X) (forecast : F → X → ℂ)
    (localSeminorm : (X → ℂ) → ℝ)
    (selectedLocal : (X → ℂ) → (Y → ℂ) → Prop)
    (input : X → ℂ) (coefficientBound residualBound termBound : ℝ)
    (model : CenteredForecastModel X) : Prop :=
  (∀ i, model.models i ∈ native) ∧
  input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
  (∑ i, |model.coefficient i|) ≤ coefficientBound ∧
  localSeminorm model.residual ≤ residualBound ∧
  (∀ f, ‖reference.correlation model.residual (forecast f)‖ ≤ residualBound) ∧
  (model.nterms : ℝ) ≤ termBound ∧
  ∀ errLocal : Y → ℂ, Measurable errLocal → selectedLocal model.residual errLocal →
    Integrable errLocal jointLaw ∧ (∫ y, ‖errLocal y‖ ∂jointLaw) ≤ residualBound

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
open MeasureTheory
open scoped BigOperators

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
open scoped BigOperators Classical

theorem exists_fixed_linear_model_partners_of_pointwise_error
    {Ω K V : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    [AddCommGroup V] [Module ℂ V]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (v e : K → V) (Q : ∀ k, I k → V) (c : ∀ k, I k → ℂ)
    (test : Ω → K → V →ₗ[ℂ] ℂ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (herr : ∀ a ∈ productive, ∀ k, ‖test a k (e k)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤ ‖test a k (v k)‖) :
    ∃ (partner : ∀ k, I k) (retained : Finset Ω),
      retained ⊆ productive ∧
      outer.mass productive / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤ ‖test a k (Q k (partner k))‖ := by
  have hex (a : Ω) (ha : a ∈ productive) (k : K) :
      ∃ i, delta / (2 * M) ≤ ‖test a k (Q k i)‖ :=
    exists_linear_model_partner (test a k) (v k) (e k) (Q k) (c k) (hmodel k)
      hdelta hM (hc k) (herr a ha k) (hscore a ha k)
  let choice : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ productive then Classical.choose (hex a ha k)
    else Classical.choice inferInstance
  have hchoice (a : Ω) (ha : a ∈ productive) (k : K) :
      delta / (2 * M) ≤ ‖test a k (Q k (choice a k))‖ := by
    dsimp only [choice]
    rw [dif_pos ha]
    exact Classical.choose_spec (hex a ha k)
  obtain ⟨partner, hmass⟩ := outer.exists_code_fiber_mass productive choice
  refine ⟨partner, productive.filter (fun a => choice a = partner),
    Finset.filter_subset _ _, ?_, ?_⟩
  · rw [Fintype.card_pi, Nat.cast_prod] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha k
    obtain ⟨hap, heq⟩ := Finset.mem_filter.mp ha
    rw [← heq]
    exact hchoice a hap k

end Erdos3

end

end OAI

end


