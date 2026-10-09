-- Prove2me | Definitions.Def_OAIErdos3B026
-- name    : OAIErdos3B026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T18:26:14.420714+00:00
-- url     : https://prove2.me/theorems/2760442a-98f7-45e4-85cb-aa33ef180559
-- title:
--   OpenAI Erdős-3 split, definitions bundle 27 of 106
-- statement:
--   Definitions bundle 27 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B025`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 27 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.exists_bounded_rank_adapted_basis`, `OAI.Erdos3.DegreeRankLieFiltration.exists_rank_adapted_basis_logHeight`, `OAI.Erdos3.FreeNilpotentLieAlgebra.coordinates`, `OAI.Erdos3.FreeNilpotentLieAlgebra.coordinates_injective`, `OAI.Erdos3.FreeNilpotentLieAlgebra.exists_bounded_structure_basis`, `OAI.Erdos3.FreeNilpotentLieAlgebra.exists_bounded_tree_basis`, `OAI.Erdos3.FreeNilpotentLieAlgebra.expansion`, `OAI.Erdos3.FreeNilpotentLieAlgebra.finite`, `OAI.Erdos3.FreeNilpotentLieAlgebra.finrank_le`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_basis_matrix_height`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_basis_matrix_logHeight`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_treeGenerator_height`, `OAI.Erdos3.FreeNilpotentLieAlgebra.lift_weightedLayer`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk_lieTreeEval`, `OAI.Erdos3.FreeNilpotentLieAlgebra.mk_tree_eq_zero_of_length_gt`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_card_le`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_coordinate_height`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_coordinate_integral`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_lie_coordinate_height`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_lie_or_zero`, `OAI.Erdos3.FreeNilpotentLieAlgebra.treeGenerators_span`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayerGenerators`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayerGenerators_card_le`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayerGenerators_subset`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayerIdeal`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_antitone`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_eq_span`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_eq_top`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_lie_mem`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_one`, `OAI.Erdos3.FreeNilpotentLieAlgebra.weightedLayer_zero`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.filtration`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.finite`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.hom_ext`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.instLieAlgebra`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.instLieRing`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layerFamily`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layerFamily_span`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layerGenerators`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layerGenerators_card_le`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layerGenerators_mem`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.layer_eq_span`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.lift`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.lift_mem_layer`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.lift_of`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.mk`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.mk_eq_zero`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.mk_surjective`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.of`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.of_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLayerBasis`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLayerBasis_height`, `OAI.Erdos3.NilpotentLieFiltration.coordinateQuotientModel`, `OAI.Erdos3.NilpotentLieFiltration.coordinateQuotientModel_geometry`, `OAI.Erdos3.NilpotentLieFiltration.exists_kernel_constant_factors`, `OAI.Erdos3.NilpotentLieFiltration.ofAdaptedBasis`, `OAI.Erdos3.NilpotentLieFiltration.ofAdaptedBasis_geometry`, `OAI.Erdos3.NilpotentLieFiltration.original_coordinate_denominator_bound`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_change_basis`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_change_basis_exp`, `OAI.Erdos3.NilpotentLieFiltration.quotientFinBasis`, `OAI.Erdos3.NilpotentLieFiltration.quotientFinBasis_layers`, `OAI.Erdos3.NilpotentLieFiltration.quotientFinWeight`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_original_grid`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_slow_original_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realificationLieHom_layer_surjective`, `OAI.Erdos3.PatchTopCoefficientIndex`, `OAI.Erdos3.PolynomialPatch.abs_shearObservable_le_one`, `OAI.Erdos3.PolynomialPatch.ofShearOrbit`, `OAI.Erdos3.PolynomialPatch.ofShearOrbit_kernel`, `OAI.Erdos3.PolynomialPatch.ofShearOrbit_weight`, `OAI.Erdos3.PolynomialPatch.shearKernelLipBound`, `OAI.Erdos3.PolynomialPatch.shearKernel_lipschitz`, `OAI.Erdos3.PolynomialPatch.shearKernel_lipschitzOn_box`, `OAI.Erdos3.PolynomialPatch.shearKernel_support_bound`, `OAI.Erdos3.PolynomialPatch.shearObservableLipBound`, `OAI.Erdos3.PolynomialPatch.shearObservable_lipschitz`, `OAI.Erdos3.PolynomialPatch.shearObservable_mem_Icc`, `OAI.Erdos3.PolynomialPatch.shearOrbitSum_eq_patchValue`, `OAI.Erdos3.PolynomialPatch.shearOrbitSum_lipschitz`, `OAI.Erdos3.PolynomialPatch.shearSummand_eq_residual`, `OAI.Erdos3.PolynomialPatch.shearSummand_lipschitz`, `OAI.Erdos3.PolynomialPatch.shearSummand_unique`, `OAI.Erdos3.PolynomialPatch.symbolicShearForm`, `OAI.Erdos3.PolynomialPatch.symbolicShearFullCenter`, `OAI.Erdos3.PolynomialPatch.symbolicShearFullCenter_degree`, `OAI.Erdos3.PolynomialPatch.symbolicShearPatch`, `OAI.Erdos3.PolynomialSlots.center_mass_le_of_normalized`, `OAI.Erdos3.PolynomialSlots.exists_fixed_kernel_patch_function`, `OAI.Erdos3.PolynomialSlots.exists_shear_observable_net`, `OAI.Erdos3.PolynomialSlots.loweringAt_patchValue`, `OAI.Erdos3.PolynomialSlots.shearPatchValue_dist`, `OAI.Erdos3.PolynomialSlots.shearTransformedSlots`, `OAI.Erdos3.PolynomialSlots.shearTransformedSlots_residual`, `OAI.Erdos3.PolynomialSlots.topPart_specializeCenter_mass_le`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_X_mass`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_inverse_X_mass`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_inverse_eval_bound`, `OAI.Erdos3.PolynomialSlots.topResidualEquiv_inverse_mass`, `OAI.Erdos3.PolynomialSlots.topResidualPoint_lipschitzOn_box`, `OAI.Erdos3.PolynomialSlots.topResidualPoint_preimage_bound`, `OAI.Erdos3.RationalFilteredNilmanifold.basis_geometry_of_forward_height`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_bounded_subalgebra_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_image_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_integral_model_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_linear_target_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_source_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_subalgebra_rational_representatives`, `OAI.Erdos3.RationalFilteredNilmanifold.linearMap_real_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.lowerCoverLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.lowerCoverLattice_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.lowerCoverLattice_forward`, `OAI.Erdos3.RationalFilteredNilmanifold.lowerCoverLattice_le`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCover`, `OAI.Erdos3.RationalFilteredNilmanifold.loweredCover_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.markedMap_basisChange_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeResetBracketGeometry`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeResetBracketGeometry_of_height`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeResetBracketGeometry_of_logBudget`, `OAI.Erdos3.RationalFilteredNilmanifold.withLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.withLattice_geometry`, `OAI.Erdos3.VectorPolynomial.PreparedFiniteNestedForwardAllDegreeSlot`, `OAI.Erdos3.VectorPolynomial.assembleFamily`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeed`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeedPolynomial`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeed_monotone`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeed_nonneg`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeed_succ`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardSeed_zero`, `OAI.Erdos3.VectorPolynomial.candidateNestedForwardWork_le_next_seed`, `OAI.Erdos3.VectorPolynomial.coefficients_assembleFamily`, `OAI.Erdos3.VectorPolynomial.exists_candidateNestedForwardLocal_budget`, `OAI.Erdos3.VectorPolynomial.exists_candidateNestedForwardSeed_polynomial_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForwardPairedResource_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForwardPairedSourcePrecision_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteForward_local_polynomial_le_later_work`, `OAI.Erdos3.VectorPolynomial.le_candidateNestedForwardSeed`, `OAI.Erdos3.VectorPolynomial.le_preparedFiniteNestedForwardAllDegreeSeed`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardInnerDetectionThreshold_bound`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardPairedSourcePrecision`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardPairedSourcePrecision_direct`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardPairedSourcePrecision_model`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForwardPairedSourcePrecision_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_local_shiftedPower_le_later_work`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor_degree`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor_model`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor_outer`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor_seed`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeAnchor_stage`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeDegree`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeDegree_le`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeDegree_slot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeIsDirect`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeIsDirect_slot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeOuter`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeOuter_slot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeSeed`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeSeed_slot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeStage`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedForwardAllDegreeStage_slot`, `OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSourceRequired`, `OAI.Erdos3.adaptedMapGeometryBudget`, `OAI.Erdos3.adaptedMapGeometryBudget_geometry`, `OAI.Erdos3.adaptedMapGeometryBudget_inverse`, `OAI.Erdos3.adaptedMapGeometryBudget_markedMap`, `OAI.Erdos3.adaptedMapGeometryBudget_nonneg`, `OAI.Erdos3.adaptedMapGeometryBudget_parameter`, `OAI.Erdos3.adaptedMarkedMapHeightBudget`, `OAI.Erdos3.bchSubgroupCoordinates_comap_ofSteps`, `OAI.Erdos3.bracket_array_equation_of_current_relation`, `OAI.Erdos3.bracket_system_matches_lift_array`, `OAI.Erdos3.coefficients_liftQuotientArray`, `OAI.Erdos3.controlled_weighted_quotient_coordinates`, `OAI.Erdos3.exists_adaptedMapGeometryBudget_fixed_power`, `OAI.Erdos3.exists_basis_image_bounds_of_height`, `OAI.Erdos3.exists_basis_intersection_correction`, `OAI.Erdos3.exists_bounded_free_nilpotent_model`, `OAI.Erdos3.exists_bounded_free_weighted_model`, `OAI.Erdos3.exists_bounded_free_weighted_quotient`, `OAI.Erdos3.exists_bracketLiftMatrix_leftInverse`, `OAI.Erdos3.exists_common_intersection_corrections`, `OAI.Erdos3.exists_controlled_coordinate_lifts`, `OAI.Erdos3.exists_controlled_kernel_split`, `OAI.Erdos3.exists_fractional_integer_kernel_correction`, `OAI.Erdos3.exists_free_nilpotent_source_basis`, `OAI.Erdos3.exists_image_intersection_corrections`, `OAI.Erdos3.exists_markedRefilteredModelInput_budget`, `OAI.Erdos3.exists_mass_bounded_shear_parameter_budget`, `OAI.Erdos3.exists_natPolynomial_fixed_power_budget`, `OAI.Erdos3.exists_patch_top_net_budget`, `OAI.Erdos3.exists_rationalTaggedSpanProjection`, `OAI.Erdos3.exists_selected_image_corrections`, `OAI.Erdos3.exists_small_patch_top_mesh`, `OAI.Erdos3.filtered_section_coefficient_loss_le_exp`, `OAI.Erdos3.filtered_section_pair_denominator_le_exp`, `OAI.Erdos3.filtered_section_single_denominator_le_exp`, `OAI.Erdos3.fixed_weight_patch_function`, `OAI.Erdos3.freeLieBoundedCoordinates`, `OAI.Erdos3.freeLieBoundedCoordinates_eq_zero_iff`, `OAI.Erdos3.horizontal_absorption_with_split`, `OAI.Erdos3.integral_basis_image_denominatorGrid`, `OAI.Erdos3.integral_basis_image_realDenominatorGrid`, `OAI.Erdos3.kernel_split_factor_le_exp`, `OAI.Erdos3.lieSubalgebraRepresentativeHeight`, `OAI.Erdos3.lieSubalgebraRepresentativeHeight_le_exp`, `OAI.Erdos3.lieSubalgebraRepresentativeHeight_le_exp_parameter`, `OAI.Erdos3.lieSubalgebraRepresentativeParameter`, `OAI.Erdos3.lieSubalgebraRepresentativeParameter_pos`, `OAI.Erdos3.lieSubalgebraRepresentative_bracket_height`, `OAI.Erdos3.liftQuotientArray`, `OAI.Erdos3.liftQuotientArray_coefficient_eq_zero`, `OAI.Erdos3.liftQuotientArray_grid`, `OAI.Erdos3.liftQuotientArray_neg`, `OAI.Erdos3.liftQuotientArray_norm_bound`, `OAI.Erdos3.lift_realSubspaceCoordinateMap`, `OAI.Erdos3.linearMap_coordinate_norm_le`, `OAI.Erdos3.linearMap_mem_scaledGrid`, `OAI.Erdos3.linear_lift_grid_of_coefficients`, `OAI.Erdos3.markedRefilteredBasisInput`, `OAI.Erdos3.markedRefilteredMapInput`, `OAI.Erdos3.markedRefilteredModelInput`, `OAI.Erdos3.markedRefilteredModelInput_bounds`, `OAI.Erdos3.matrixDenominator_le_exp_power`, `OAI.Erdos3.matrix_pair_denominator_le_exp_power`, `OAI.Erdos3.matrix_weighted_factor_le_exp_power`, `OAI.Erdos3.nativeResetBracketHeight`, `OAI.Erdos3.nativeResetBracketLog_ge_input`, `OAI.Erdos3.norm_removed_derivative_bound`, `OAI.Erdos3.patchTopCoefficientCode_card`, `OAI.Erdos3.patchTopCoefficientIndex_card`, `OAI.Erdos3.patchTopNetError`, `OAI.Erdos3.patchTopNetError_eq_div`, `OAI.Erdos3.patchTopNetError_nonneg`, `OAI.Erdos3.patchTopNetNumerator`, `OAI.Erdos3.patchTopNetNumeratorLog`, `OAI.Erdos3.patchTopNetNumeratorLog_nonneg`, `OAI.Erdos3.patchTopNetNumerator_le_exp`, `OAI.Erdos3.polynomialShearDisplacementBound`, `OAI.Erdos3.polynomialShearExp_X_displacement`, `OAI.Erdos3.polynomialShearExp_displacement`, `OAI.Erdos3.polynomialShearExp_sub_mass`, `OAI.Erdos3.polynomialShearLayerBasis`, `OAI.Erdos3.polynomialShearLayerBasis_height`, `OAI.Erdos3.polynomialShearLayerFinBasis`, `OAI.Erdos3.polynomialShearLayerFinBasis_height`, `OAI.Erdos3.polynomialShearLayerIndexEquiv`, `OAI.Erdos3.polynomialShearNilmanifold`, `OAI.Erdos3.polynomialShearNilmanifold_complexity`, `OAI.Erdos3.polynomialShearNilmanifold_complexity_budget`, `OAI.Erdos3.polynomialShearOrbitSymbolicHom`, `OAI.Erdos3.polynomialShearOrbitSymbolicHom_degree`, `OAI.Erdos3.polynomialShearRealPointAction_displacement`, `OAI.Erdos3.polynomialShearRealPointAction_eq_exp`, `OAI.Erdos3.polynomialShearRealPointAction_near_one`, `OAI.Erdos3.polynomialShearRealification_ordered_repr`, `OAI.Erdos3.rationalCoordinateSection`, `OAI.Erdos3.rationalCoordinateSection_coordinates`, `OAI.Erdos3.rationalCoordinateSection_grid`, `OAI.Erdos3.rationalCoordinateSection_rightInverse`, `OAI.Erdos3.rationalCoordinateSection_weighted`, `OAI.Erdos3.rationalKernelSeparationConstant_ceil_le_exp_power`, `OAI.Erdos3.rationalMatrix_real_ker_eq_range`, `OAI.Erdos3.rationalMatrix_real_ker_eq_span`, `OAI.Erdos3.rational_coordinate_map`, `OAI.Erdos3.rational_coordinate_map_grid`, `OAI.Erdos3.rational_coordinate_map_weighted`, `OAI.Erdos3.rational_coordinate_map_weighted_exp`, `OAI.Erdos3.rational_matrix_entry_budget`, `OAI.Erdos3.rational_section_entry_budget`, `OAI.Erdos3.realDenominatorGrid_linear_combination`, `OAI.Erdos3.realDenominatorGrid_sub`, `OAI.Erdos3.realDenominatorGrid_sub_product`, `OAI.Erdos3.realGeneratorCombination`, `OAI.Erdos3.realGeneratorCombination_coordinates`, `OAI.Erdos3.realGeneratorCombination_map_coordinates`, `OAI.Erdos3.realGeneratorCombination_mem`, `OAI.Erdos3.realPolynomialMass_weightedComponent_le`, `OAI.Erdos3.realPolynomialMass_zeroParameterEval_le`, `OAI.Erdos3.realQuotientEquiv`, `OAI.Erdos3.realQuotientEquiv_mk`, `OAI.Erdos3.realSubspaceCoordinateMap`, `OAI.Erdos3.realSubspaceCoordinateMap_apply`, `OAI.Erdos3.realSubspaceCoordinateMap_grid`, `OAI.Erdos3.realSubspaceCoordinateMap_lift`, `OAI.Erdos3.realSubspaceCoordinateMap_norm`, `OAI.Erdos3.realTransportedQuotientBasis`, `OAI.Erdos3.realTransportedQuotientBasis_repr_basis`, `OAI.Erdos3.realTransportedQuotientBasis_repr_mk`, `OAI.Erdos3.realTransportedQuotientEquiv`, `OAI.Erdos3.realTransportedQuotientEquiv_mk`, `OAI.Erdos3.real_basis_coordinates_bound`, `OAI.Erdos3.real_basis_coordinates_exp_bound`, `OAI.Erdos3.real_basis_coordinates_grid`, `OAI.Erdos3.real_basis_coordinates_transfer`, `OAI.Erdos3.real_basis_transfer_denominator`, `OAI.Erdos3.real_matrix_right_inverse`, `OAI.Erdos3.realification_fractional_integer_split`, `OAI.Erdos3.realification_mkQ_ker`, `OAI.Erdos3.realification_mkQ_surjective`, `OAI.Erdos3.realified_linear_coordinate_grid`, `OAI.Erdos3.realified_linear_coordinate_matrix`, `OAI.Erdos3.realified_linear_coordinate_norm`, `OAI.Erdos3.realified_section_correction_coordinate_norm`, `OAI.Erdos3.relativeInductionBudgetPolynomial`, `OAI.Erdos3.relativeInductionBudgetPolynomial_eval_succ`, `OAI.Erdos3.relativeInductionBudgetPolynomial_eval_zero`, `OAI.Erdos3.relativeInductionBudgetValue`, `OAI.Erdos3.relativeInductionBudgetValue_succ`, `OAI.Erdos3.relativeInductionBudgetValue_zero`, `OAI.Erdos3.scalarExtension_basis_coordinates`, `OAI.Erdos3.scalarExtension_coordinate_dist_le`, `OAI.Erdos3.scalarExtension_coordinate_norm_le`, `OAI.Erdos3.scalarExtension_coordinate_sum`, `OAI.Erdos3.scalarExtension_equiv_matrix`, `OAI.Erdos3.scalarExtension_fractional_coordinates_bound`, `OAI.Erdos3.scalarExtension_grid_of_height_one`, `OAI.Erdos3.shearActionLogBudget`, `OAI.Erdos3.shearActionLogBudget_nonneg`, `OAI.Erdos3.shearDisplacementBound_le_exp`, `OAI.Erdos3.shearKernelLipBound_le_exp`, `OAI.Erdos3.shearKernelLogBudget`, `OAI.Erdos3.shearKernelLogBudget_nonneg`, `OAI.Erdos3.shearObservable_log_bound`, `OAI.Erdos3.shearRadius_le_exp`, `OAI.Erdos3.shifted_power_le_fixed_base`, `OAI.Erdos3.symbolicShearPrefixSubstitution`, `OAI.Erdos3.symbolicShearPrefixSubstitution_degree`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B098

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ChosenBasisGeometryBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem basis_geometry_of_forward_height {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (b : Basis ι ℚ L)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    (Fintype.card ι : ℝ) ≤ p ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 4) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 4) ^ 11) := by
  have hdim : (Fintype.card ι : ℝ) ≤ p := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hD.2.2.1 i j k).trans (by linarith))
  have hp2 : 0 ≤ p + 2 := by linarith
  have hdim2 : (Fintype.card ι : ℝ) ≤ p + 2 := hdim.trans (by linarith)
  have hd2 : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  have hinverse : (rationalSolveHeight (Fintype.card ι) H : ℝ) ≤ Real.exp ((p + 4) ^ 5) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalSolveHeight_le_budget (Fintype.card ι) H hp2 hdim2 hHp
  have hbracket : (rationalLieStructureHeight (Fintype.card (Fin d))
      (max H (rationalSolveHeight (Fintype.card ι) H)) : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    simpa only [show p + 2 + 2 = p + 4 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d)) (Fintype.card ι) H hp2 hd2 hdim2 hHp
  exact ⟨hdim,
    fun i j => rationalLogHeight_le_of_height (inverse_basis_entries_height D.basis b hH hentries i j) hinverse,
    fun i j k => rationalLogHeight_le_of_height
      (basis_change_structure_height D.basis b hH hentries hstructure i j k) hbracket⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight
namespace OAI

section

namespace Erdos3

def adaptedMarkedMapHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 4) ^ 5 + (p + 2) ^ 4 + 2) ^ 4

namespace RationalFilteredNilmanifold

open Module

theorem markedMap_basisChange_logHeight
    {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (E.basis.repr (c i) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ adaptedMarkedMapHeightBudget p := by
  obtain ⟨_, hinv, _⟩ := E.basis_geometry_of_forward_height c hp hE
    (fun i j => (hc i j).trans (by linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hD.1
  have he : (Fintype.card (Fin e) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hE.1
  have hnative (i : ι) (j : Fin e) :
      rationalLogHeight (E.basis.repr (φ (b i)) j) ≤ (p + 2) ^ 4 :=
    linearMap_coordinate_logHeight D.basis E.basis φ hp hd hφ (b i) (hb i) j
  let q := p + (p + 4) ^ 5 + (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have h4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hinvq : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hnativeq : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  intro i j
  exact linearMap_coordinate_logHeight E.basis c LinearMap.id hq (he.trans hpq)
    (fun a k => (hinv a k).trans hinvq) (φ (b i))
    (fun k => (hnative i k).trans hnativeq) j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearLayerBasis (r : ℕ) :
    Basis {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  supportedSubmoduleBasis (polynomialShearOrderedBasis w) (polynomialShearLayer w r)
    {j | r ≤ polynomialShearOrderedWeight w j} (polynomialShearOrderedBasis_layers w r)

theorem polynomialShearLayerBasis_height (r : ℕ)
    (i : {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}) (j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerBasis w r i).val j) 1 := by
  rw [polynomialShearLayerBasis, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (polynomialShearOrderedBasis w) _ _

noncomputable def polynomialShearLayerIndexEquiv (r : ℕ) :
    {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j} ≃
      Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (polynomialShearLayerBasis w r)).symm

noncomputable def polynomialShearLayerFinBasis (r : ℕ) :
    Basis (Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)))
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  (polynomialShearLayerBasis w r).reindex (polynomialShearLayerIndexEquiv w r)

theorem polynomialShearLayerFinBasis_height (r : ℕ) (i j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerFinBasis w r i).val j) 1 := by
  rw [polynomialShearLayerFinBasis, Basis.reindex_apply]
  exact polynomialShearLayerBasis_height w r _ _

noncomputable def polynomialShearNilmanifold (s : ℕ) (hw : ∀ i, w i ≤ s) :
    RationalFilteredNilmanifold (PolynomialShearLieAlgebra w ℚ) s
      (Fintype.card (PolynomialShearIndex w)) where
  filtration := polynomialShearFiltration w s hw
  basis := polynomialShearOrderedBasis w
  layerBasis i := polynomialShearLayerFinBasis w (i.val + 1)
  lattice := polynomialShearLattice w s hw
  grid := s.factorial
  grid_pos := Nat.factorial_pos s
  inner_grid := polynomialShearOrderedBasis_inner_grid w s hw
  outer_grid := polynomialShearOrderedBasis_outer_grid w s hw

theorem polynomialShearNilmanifold_complexity (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ p)
    (hf : (s.factorial : ℝ) ≤ Real.exp p)
    (hH : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp p) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE p := by
  refine ⟨hd, hf, ?_, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearOrderedBasis_structure_height w s hpos hw i j k) hH
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearLayerFinBasis_height w (i.val + 1) j k)
      (by simpa using Real.one_le_exp_iff.mpr hp)

theorem polynomialShearNilmanifold_complexity_budget (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE
      ((Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1 : ℕ) : ℝ) := by
  let n := Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1
  have hn : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show Fintype.card (PolynomialShearIndex w) ≤ n by dsimp [n]; omega)
  have hf : (s.factorial : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show s.factorial ≤ n by dsimp [n]; omega)
  have hH : ((2 * s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * s + 1 ≤ n by dsimp [n]; omega)
  have he : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  exact polynomialShearNilmanifold_complexity w s hpos hw (Nat.cast_nonneg n) hn
    (hf.trans he) (hH.trans he)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialMass_weightedComponent_le (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n P) ≤ realPolynomialMass P := by
  classical
  unfold realPolynomialMass
  rw [support_weightedHomogeneousComponent]
  calc
    _ = ∑ α ∈ P.support.filter (fun α => Finsupp.weight w α = n), |P.coeff α| := by
      apply Finset.sum_congr rfl
      intro α hα
      rw [coeff_weightedHomogeneousComponent, if_pos (Finset.mem_filter.mp hα).2]
    _ ≤ ∑ α ∈ P.support, |P.coeff α| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)

theorem realPolynomialMass_zeroParameterEval_le (P : MvPolynomial (σ ⊕ τ) ℝ) :
    realPolynomialMass (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) P) ≤
      realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) (M := 1) le_rfl (by
      intro a
      cases a with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => simp only [Sum.elim_inr, realPolynomialMass_X, le_refl]) le_rfl
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  simpa only [one_pow, mul_one, MvPolynomial.coe_eval₂Hom] using h

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

theorem topPart_specializeCenter_mass_le (A : PolynomialSlots σ d w) (i : Fin d) :
    realPolynomialMass (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) ≤
      realPolynomialMass (A.center i) := by
  apply (realPolynomialMass_rename_le _ _).trans
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs]
  exact (realPolynomialMass_zeroParameterEval_le _).trans
    (realPolynomialMass_weightedComponent_le _ _ _)

theorem center_mass_le_of_normalized [Fintype σ] (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (hA : ∀ i α, |(A.center i).coeff α| ≤ 1 / 2) (i : Fin d) :
    realPolynomialMass (A.center i) ≤ ((s + 1) * (Fintype.card σ + d + 1) ^ s : ℕ) := by
  have hdegree : (A.center i).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport (patchVariableWeight w i) (by
      intro a
      cases a with
      | inl j => exact le_rfl
      | inr j => exact hpos (earlierSlot i j)) (A.degree i)).trans (hw i)
  have hmass : realPolynomialMass (A.center i) ≤ ((A.center i).support.card : ℝ) := by
    unfold realPolynomialMass
    calc
      _ ≤ ∑ _α ∈ (A.center i).support, (1 : ℝ) :=
        Finset.sum_le_sum (fun α _ => (hA i α).trans (by norm_num))
      _ = _ := by simp
  apply hmass.trans
  have hcard := polynomial_support_card_le (A.center i) hdegree
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact_mod_cast hcard.trans (Nat.mul_le_mul_left (s + 1)
    (Nat.pow_le_pow_left (by omega : Fintype.card σ + i.val + 1 ≤ Fintype.card σ + d + 1) s))

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearTransformedSlots (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) : TriangularSlots d where
  center x i := x i - aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
    (A.topResidualEquiv (X i))
  lower i x y hxy := by
    have hd := weightedLoweringSubstitution_difference e hw i x y hxy
    have htop :
        aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) =
        aeval (polynomialSubstitutionPoint e.val.toAlgHom y)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
      rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
      apply congrArg (fun f : Fin i.val → ℝ => aeval f (A.topPart.specializeCenter 0 i))
      funext j
      exact weightedLoweringSubstitution_prefix e hw i x y hxy (earlierSlot i j) j.isLt
    rw [A.topResidualEquiv_X, map_sub, map_sub, aeval_X, aeval_X, htop]
    linarith

theorem shearTransformedSlots_residual (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) (b : Fin d → ℤ) :
    (A.shearTransformedSlots hw e).residual b =
      fun i => aeval (polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ)))
        (A.topResidualEquiv (X i)) := by
  funext i
  change (b i : ℝ) - ((b i : ℝ) - _) = _
  ring

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearSummand_eq_residual (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) (b : Fin d → ℤ) :
    A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))) =
      A.kernel.value ((A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).residual b) := by
  rw [PolynomialSlots.shearTransformedSlots_residual]
  rfl

theorem shearSummand_unique (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    {b c : Fin d → ℤ}
    (hb : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (b i : ℝ))) ≠ 0)
    (hc : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (c i : ℝ))) ≠ 0) : b = c := by
  rw [A.shearSummand_eq_residual] at hb hc
  exact TriangularSlots.contributing_unique _ A.kernel hb hc

theorem shearOrbitSum_eq_patchValue (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) :
    polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g =
      (A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).patchValue A.kernel := by
  unfold polynomialShearOrbitSum TriangularSlots.patchValue
  exact tsum_congr (A.shearSummand_eq_residual g)

theorem shearObservable_mem_Icc (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : A.shearObservable x ∈ Set.Icc (0 : ℝ) 1 := by
  refine Quotient.inductionOn x ?_
  intro g
  change polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g ∈ Set.Icc (0 : ℝ) 1
  rw [A.shearOrbitSum_eq_patchValue]
  exact TriangularSlots.patchValue_mem_Icc _ A.kernel

theorem abs_shearObservable_le_one (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : |A.shearObservable x| ≤ 1 := by
  rw [abs_of_nonneg (A.shearObservable_mem_Icc x).1]
  exact (A.shearObservable_mem_Icc x).2

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

noncomputable def symbolicShearPrefixSubstitution (i : Fin d) :
    τ ⊕ Fin d → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun j => if h : j.val < i.val then X (Sum.inr ⟨j.val, h⟩) else 0)

theorem symbolicShearPrefixSubstitution_degree (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (patchVariableWeight w i) (Sum.elim (fun _ : τ => 1) w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (patchVariableWeight (σ := τ) w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

noncomputable def symbolicShearFullCenter (i : Fin d) : MvPolynomial (τ ⊕ Fin d) ℝ :=
  X (Sum.inr i) - f (rename Sum.inr (A.form.topResidualEquiv (X i)))

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)

include hdegree in
theorem symbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def symbolicShearForm : PolynomialSlots τ d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_degree A.weight i)
    (A.symbolicShearFullCenter_degree f hdegree i)

noncomputable def symbolicShearPatch : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.symbolicShearForm f hdegree
  kernel := A.kernel

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualEquiv_X_mass (A : PolynomialSlots σ d w)
    {M : ℝ} (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv (X i)) ≤ 1 + M := by
  rw [A.topResidualEquiv_X]
  exact (realPolynomialMass_sub_le _ _).trans
    (by simpa only [realPolynomialMass_X] using
      add_le_add (le_refl (1 : ℝ)) ((A.topPart_specializeCenter_mass_le i).trans (hA i)))

theorem topResidualEquiv_inverse_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (A.topResidualEquiv.symm P) ≤ realPolynomialMass P * (1 + M) ^ (n * d) := by
  apply triangularPolynomialEquiv_inverse_mass w hpos _ A.topResidualShift_degree hM _ hP
  intro i
  rw [map_neg, realPolynomialMass_neg]
  exact (A.topPart_specializeCenter_mass_le i).trans (hA i)

theorem topResidualEquiv_inverse_X_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv.symm (X i)) ≤ (1 + M) ^ (s * d) := by
  have h := A.topResidualEquiv_inverse_mass hpos hM hA (weightedSupportLE_X w i)
  rw [realPolynomialMass_X, one_mul] at h
  exact h.trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right d (hw i)))

theorem topResidualEquiv_inverse_eval_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ 1) (i : Fin d) :
    |aeval y (A.topResidualEquiv.symm (X i))| ≤ (1 + M) ^ (s * d) :=
  (mvPolynomial_eval_abs_le_sum_coeff (A.topResidualEquiv.symm (X i)) y hy).trans
    (A.topResidualEquiv_inverse_X_mass hpos s hw hM hA i)

theorem topResidualPoint_preimage_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (x : Fin d → ℝ) (hx : ∀ i, |aeval x (A.topResidualEquiv (X i))| ≤ 1) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  have hinv : aeval (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
      (A.topResidualEquiv.symm (X i)) = x i := by
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = x i
    rw [AlgEquiv.apply_symm_apply, aeval_X]
  rw [← hinv]
  exact A.topResidualEquiv_inverse_eval_bound hpos s hw hM hA _ hx i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_support_bound (A : PolynomialPatch σ s d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    (x : Fin d → ℝ) (hx : A.shearKernel x ≠ 0) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  apply A.form.topResidualPoint_preimage_bound A.weight_pos s A.weight_le hM hA x _ i
  intro j
  have h := A.kernel.support _ hx j
  exact h.trans (by norm_num)

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)

variable
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)
  (hlower : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 0) A.weight) n →
    f P - P ∈ weightedSupportLT (Sum.elim (fun _ : τ => 0) A.weight) n)

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {X Y : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem shearPatchValue_dist (A : PolynomialSlots X d w) (B : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (hB : ∀ i, realPolynomialMass (B.center i) ≤ M)
    (hclose : ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ (1 + M) ^ (s * d)) →
      dist (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
        (polynomialSubstitutionPoint B.topResidualEquiv.toAlgHom x) ≤ ε)
    (e : WeightedLoweringAut w ℝ) :
    dist ((A.shearTransformedSlots hw e).patchValue Φ)
      ((B.shearTransformedSlots hw e).patchValue Φ) ≤ Φ.lip * ε := by
  apply TriangularSlots.patchValue_dist_of_residuals_close _ _ Φ hε hsmall
  intro b hb
  let x := polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ))
  have hx : ∀ i, |x i| ≤ (1 + M) ^ (s * d) := by
    rcases hb with hb | hb
    · apply A.topResidualPoint_preimage_bound hpos s hs hM hA x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
    · apply B.topResidualPoint_preimage_bound hpos s hs hM hB x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
  rw [shearTransformedSlots_residual, shearTransformedSlots_residual]
  exact hclose x hx

end Erdos3.PolynomialSlots

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {τ : Type*} {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1)) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (polynomialShearOrbitParameterCoordinates s hw g))

theorem polynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n) :
    polynomialShearOrbitSymbolicHom hw g P ∈
      weightedSupportLE (Sum.elim (fun _ : τ => 1) w) n :=
  polynomialSymbolicShearExp_total_degree w _
    (polynomialShearOrbitParameterCoordinates_degree s hw g) hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : PolynomialPatch τ s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearPatch (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)

@[simp] theorem ofShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).weight = A.weight := rfl

@[simp] theorem ofShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofShearOrbit g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

theorem shifted_power_le_fixed_base {p : ℝ} (hp : 0 ≤ p) (C : ℕ) (hC : 2 ≤ C) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  have hbase : 0 ≤ p + 2 := by linarith
  have hpTerm : p ≤ (p + 2) ^ C := le_power_budget hp (by omega)
  have htwo : (C : ℝ) ≤ (2 : ℝ) ^ C := by
    exact_mod_cast (show C < 2 ^ C from Nat.lt_two_pow_self).le
  have hCTerm : (C : ℝ) ≤ (p + 2) ^ C :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith) C)
  have hsum : p + C ≤ (p + 2) ^ (C + 1) := by
    calc
      _ ≤ 2 * (p + 2) ^ C := by linarith
      _ ≤ (p + 2) * (p + 2) ^ C :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase _)
      _ = _ := (pow_succ' _ _).symm
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) hsum C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_natPolynomial_fixed_power_budget (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  exact (hbound p hp).trans (shifted_power_le_fixed_base hp C hC)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def relativeInductionBudgetPolynomial (b₀ c : ℕ) : ℕ → Polynomial ℕ
  | 0 => (Polynomial.X + 2) ^ b₀
  | q + 1 => (2 + (2 + Polynomial.X +
      (relativeInductionBudgetPolynomial b₀ c q).comp ((Polynomial.X + 2) ^ c)) ^ c) ^ c

@[simp] theorem relativeInductionBudgetPolynomial_eval_zero (b₀ c : ℕ) (p : ℝ) :
    (relativeInductionBudgetPolynomial b₀ c 0).eval₂ (Nat.castRingHom ℝ) p = (p + 2) ^ b₀ := by
  simp [relativeInductionBudgetPolynomial, Polynomial.eval₂_pow]

@[simp] theorem relativeInductionBudgetPolynomial_eval_succ (b₀ c q : ℕ) (p : ℝ) :
    (relativeInductionBudgetPolynomial b₀ c (q + 1)).eval₂ (Nat.castRingHom ℝ) p =
      (2 + (2 + p + (relativeInductionBudgetPolynomial b₀ c q).eval₂
        (Nat.castRingHom ℝ) ((p + 2) ^ c)) ^ c) ^ c := by
  simp only [relativeInductionBudgetPolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_X, Polynomial.eval₂_comp]

noncomputable def relativeInductionBudgetValue (b₀ c q : ℕ) (p : ℝ) : ℝ :=
  (relativeInductionBudgetPolynomial b₀ c q).eval₂ (Nat.castRingHom ℝ) p

@[simp] theorem relativeInductionBudgetValue_zero (b₀ c : ℕ) (p : ℝ) :
    relativeInductionBudgetValue b₀ c 0 p = (p + 2) ^ b₀ :=
  relativeInductionBudgetPolynomial_eval_zero b₀ c p

@[simp] theorem relativeInductionBudgetValue_succ (b₀ c q : ℕ) (p : ℝ) :
    relativeInductionBudgetValue b₀ c (q + 1) p =
      (2 + (2 + p + relativeInductionBudgetValue b₀ c q ((p + 2) ^ c)) ^ c) ^ c :=
  relativeInductionBudgetPolynomial_eval_succ b₀ c q p

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShearExp_sub_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (polynomialShearExp D P - P) ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P := by
  classical
  let B : ℝ := Fintype.card σ * A * n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpow (k : ℕ) (hk : k < n) :
      realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) ≤
        δ * (1 + B) ^ n * realPolynomialMass P := by
    have hmass := polynomialShear_pow_mass D hpos (mul_nonneg hA hδ) hD hP (k + 1)
    have he : (Fintype.card σ : ℝ) * (A * δ) * n = B * δ := by dsimp [B]; ring
    rw [he, mul_pow] at hmass
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ (realPolynomialMass_nonneg P)
    have hd : δ ^ (k + 1) ≤ δ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hδ (pow_le_one₀ hδ hδone)
    have hb : B ^ (k + 1) ≤ (1 + B) ^ n :=
      (pow_le_pow_left₀ hB (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    calc
      _ ≤ (1 + B) ^ n * δ := mul_le_mul hb hd (pow_nonneg hδ _) (by positivity)
      _ = _ := mul_comm _ _
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, δ * (1 + B) ^ n * realPolynomialMass P := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Rat.cast_smul_eq_qsmul ℝ, realPolynomialMass_smul]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
      have hc : |((k + 1).factorial : ℝ)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ ≤ 1 * realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) :=
          mul_le_mul_of_nonneg_right hc (realPolynomialMass_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hpow k (Finset.mem_range.mp hk)
    _ = _ := by simp [B]; ring

theorem polynomialShearExp_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ B : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    |aeval x (polynomialShearExp D P) - aeval x P| ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P * B ^ n := by
  rw [← map_sub]
  have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
    ((weightedSupportLE w n).sub_mem (polynomialShearExp_degree D hP) hP)
  exact (abs_aeval_le_mass_box _ x hB hx hdegree).trans
    (mul_le_mul_of_nonneg_right (polynomialShearExp_sub_mass D hpos hA hδ hδone hD hP)
      (pow_nonneg (by linarith) _))

theorem polynomialShearExp_X_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) (i : σ) :
    |aeval x (polynomialShearExp D (X i)) - x i| ≤
      s * δ * (1 + Fintype.card σ * ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * s) ^ s * B ^ s := by
  have h := polynomialShearExp_displacement D hpos (by positivity) hδ hδone hB
    (polynomialShear_X_mass_of_coordinates D hpos hw hδ hD)
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)) x hx
  simpa only [aeval_X, realPolynomialMass_X, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

def polynomialShearDisplacementBound (s d : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  s * (1 + d * ((s + 1) * (d + 1) ^ s : ℕ) * s) ^ s * B ^ s

theorem polynomialShearRealPointAction_eq_exp (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (x : σ → ℝ) (i : σ) :
    polynomialShearRealPointAction w s hw g x i =
      aeval x (polynomialShearExp (-(polynomialShearRealificationEquiv w g.coord)) (X i)) := by
  change aeval x ((polynomialShearRealAutEquiv w s hw g).val.symm (X i)) = _
  have he := congrArg (fun e : WeightedLoweringAut w ℝ => aeval x (e.val (X i)))
    (polynomialShearRealAutEquiv_apply w s hw g⁻¹)
  simpa only [map_inv, Subgroup.coe_inv, AlgEquiv.aut_inv, NilpotentLieBCHGroup.coord_inv,
    map_neg, polynomialShearExpAut_apply] using he

theorem polynomialShearRealPointAction_displacement (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (B : ℝ≥0) (hB : 1 ≤ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    dist (polynomialShearRealPointAction w s hw g x) x ≤
      (polynomialShearDisplacementBound s (Fintype.card σ) B : ℝ) * δ := by
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) hδ)).mpr
  intro i
  rw [Real.dist_eq, polynomialShearRealPointAction_eq_exp]
  have hgn (a) : |(polynomialShearBasis (R := ℝ) w).repr (-(polynomialShearRealificationEquiv w g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have h := polynomialShearExp_X_displacement (-(polynomialShearRealificationEquiv w g.coord))
    hpos hw hδ hδone (show (1 : ℝ) ≤ B from hB) hgn x hx i
  convert h using 1
  simp only [polynomialShearDisplacementBound, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  ring

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShearRealification_ordered_repr
    (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) a =
      ((polynomialShearOrderedBasis w).baseChange ℝ).repr D (polynomialShearIndexOrder w a) := by
  rw [polynomialShearRealificationEquiv_repr]
  have he : (polynomialShearOrderedBasis w).baseChange ℝ =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).reindex (polynomialShearIndexOrder w) := by
    ext j
    simp only [polynomialShearOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  rw [he, Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealPointAction_near_one (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group)
    (B : ℝ≥0) (hB : 1 ≤ B) (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
    let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
    (C : ℝ) * dist 1 g < 1 →
      dist (polynomialShearRealPointAction w s hw g x) x ≤
        (polynomialShearDisplacementBound s (Fintype.card σ) B * C : ℝ≥0) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis w).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
  dsimp only
  intro hnear
  have hc := polynomialShearOrderedBasis_structure_height w s (fun i => lt_of_lt_of_le Nat.zero_lt_one (hpos i)) hw
  have hlog : ‖basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hr := norm_coordinates_le_of_near_one
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
      (lieStructureConstants (polynomialShearOrderedBasis w))
      (fun i j k => (realLieBasis_structure (polynomialShearOrderedBasis w) i j k).symm)
      hc 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hr
    exact hr hnear
  have hg (a : PolynomialShearIndex w) :
      |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤
        (C : ℝ) * dist 1 g := by
    rw [polynomialShearRealification_ordered_repr]
    have h := (norm_le_pi_norm
      (basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g)
      (polynomialShearIndexOrder w a)).trans hlog
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h
  have h := polynomialShearRealPointAction_displacement w s hpos hw g B hB
    (mul_nonneg C.coe_nonneg dist_nonneg) hnear.le hg x hx
  simpa only [NNReal.coe_mul, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualPoint_lipschitzOn_box (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) :
    LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
      (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom)
      {x | ∀ i, |x i| ≤ B} := by
  have hmass (i : Fin d) : realPolynomialMass (A.topResidualEquiv (X i)) ≤ (1 + M : ℝ≥0) := by
    exact A.topResidualEquiv_X_mass hA i
  have hdegree (i : Fin d) : (A.topResidualEquiv (X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      (A.topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hw i)
  change LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
    (fun x : Fin d → ℝ => fun i => aeval x (A.topResidualEquiv (X i))) _
  simpa only [Fintype.card_fin] using
    lipschitzOn_realPolynomialVector_mass_box (fun i : Fin d => A.topResidualEquiv (X i))
      (1 + M) B hB hmass hdegree

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_lipschitzOn_box (A : PolynomialPatch σ s d) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzOnWith (A.kernel.lip * ((1 + M) * d * s * B ^ (s * (d + 1)))) A.shearKernel
      {x | ∀ i, |x i| ≤ B} := by
  exact A.kernel.lipschitz.comp_lipschitzOnWith
    (A.form.topResidualPoint_lipschitzOn_box A.weight_pos s A.weight_le M B hB hA)

noncomputable def shearKernelLipBound (A : PolynomialPatch σ s d) (M : ℝ≥0) : ℝ≥0 :=
  max 1 (A.kernel.lip * ((1 + M) * d * s *
    ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))

theorem shearKernel_lipschitz (A : PolynomialPatch σ s d) (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzWith (A.shearKernelLipBound M) A.shearKernel := by
  unfold shearKernelLipBound
  apply lipschitzWith_of_unit_range_support_box A.shearKernel ((1 + M) ^ (s * d))
    (A.kernel.lip * ((1 + M) * d * s * ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))
  · intro x
    exact A.kernel.nonneg _
  · intro x
    exact A.kernel.le_one _
  · intro x hx i
    simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA x hx i
  · simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_lipschitzOn_box M ((1 + M) ^ (s * d) + 1) (le_add_of_nonneg_left zero_le) hA

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

noncomputable def shearObservableLipBound (M : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  max C (A.shearKernelLipBound M *
    polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) * C)

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem shearSummand_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) (b : Fin d → ℝ) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (fun g => A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g b)) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  let R : ℝ≥0 := (1 + M) ^ (s * d)
  let T := polynomialShearDisplacementBound s d R
  let K := A.shearKernelLipBound M
  let ρ := polynomialShearRealPointAction A.weight s A.weight_le
  change LipschitzWith (max C (K * T * C)) (fun g => A.shearKernel (ρ g b))
  apply lipschitzWith_of_unit_range_near_nonzero _ C (K * T * C)
    (fun _ => A.kernel.nonneg _) (fun _ => A.kernel.le_one _)
  intro g h hg hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using
      (rightMetricSpace_isometry_mul_right ((polynomialShearOrderedBasis A.weight).baseChange ℝ) g⁻¹).dist_eq g h
  have hR : 1 ≤ R := one_le_pow₀ (le_add_of_nonneg_right zero_le)
  have hx (i : Fin d) : |ρ g b i| ≤ R := by
    simpa only [R, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA (ρ g b) hg i
  have hmove := polynomialShearRealPointAction_near_one A.weight s A.weight_pos A.weight_le
    z R hR (ρ g b) hx (by simpa only [hdist] using hnear)
  have hz : ρ z (ρ g b) = ρ h b := by
    simp only [z, map_mul, map_inv, Equiv.Perm.mul_apply]
    exact congrArg (ρ h) ((ρ g).symm_apply_apply b)
  change dist (ρ z (ρ g b)) (ρ g b) ≤
    (polynomialShearDisplacementBound s (Fintype.card (Fin d)) R * C : ℝ≥0) * dist 1 z at hmove
  rw [hz, hdist, Fintype.card_fin, dist_comm (ρ h b) (ρ g b)] at hmove
  have hkernel := (A.shearKernel_lipschitz M hA).dist_le_mul (ρ g b) (ρ h b)
  rw [Real.dist_eq] at hkernel
  apply hkernel.trans
  simpa only [NNReal.coe_mul, mul_assoc] using mul_le_mul_of_nonneg_left hmove K.coe_nonneg

theorem shearOrbitSum_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  exact separated_tsum_lipschitz
    (fun (b : Fin d → ℤ) g => A.shearKernel
      (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))))
    (fun b => A.shearSummand_lipschitz M hA (fun i => (b i : ℝ)))
    (fun _ _ => A.kernel.nonneg _)
    (fun g _ _ hb hc => A.shearSummand_unique g hb hc)

theorem shearObservable_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    LipschitzWith (A.shearObservableLipBound M) A.shearObservable := by
  let e := (polynomialShearOrderedBasis A.weight).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift (polynomialShearRealLattice s A.weight_le)
    (polynomialShearRealLattice_closed_discrete s A.weight_le).1 A.shearObservable
    (A.shearOrbitSum_lipschitz M hA)

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open scoped NNReal

def shearKernelLogBudget (s d : ℕ) (M u : ℝ) : ℝ :=
  u + M + d + s + ((s * d : ℕ) * M + 1) * (s * (d + 1) : ℕ)

def shearActionLogBudget (s d : ℕ) (M : ℝ) : ℝ :=
  s + s * ((d * ((s + 1) * (d + 1) ^ s) * s : ℕ) : ℝ) +
    s * ((s * d : ℕ) * M)

theorem shearKernelLogBudget_nonneg (s d : ℕ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    0 ≤ shearKernelLogBudget s d M u := by unfold shearKernelLogBudget; positivity

theorem shearActionLogBudget_nonneg (s d : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ shearActionLogBudget s d M := by unfold shearActionLogBudget; positivity

theorem shearRadius_le_exp (s d : ℕ) (M : ℝ≥0) :
    (((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ≤ Real.exp ((s * d : ℕ) * (M : ℝ)) := by
  simp only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
  calc
    _ ≤ (Real.exp (M : ℝ)) ^ (s * d) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (M : ℝ)]
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem shearKernelLipBound_le_exp {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    (M : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u) :
    (A.shearKernelLipBound M : ℝ) ≤ Real.exp (shearKernelLogBudget s d M u) := by
  have hM : 1 + (M : ℝ) ≤ Real.exp (M : ℝ) := by linarith [Real.add_one_le_exp (M : ℝ)]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  have hR : (((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ≤
      Real.exp ((s * d : ℕ) * (M : ℝ) + 1) := by
    have h := add_le_exp_add_one (by positivity : 0 ≤ (s * d : ℕ) * (M : ℝ))
      (le_refl (0 : ℝ)) (shearRadius_le_exp s d M) (by simp : (1 : ℝ) ≤ Real.exp 0)
    simpa only [NNReal.coe_add, NNReal.coe_one, add_zero] using h
  change max (1 : ℝ) ((A.kernel.lip : ℝ) *
    ((1 + M) * d * s * ((((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ^ (s * (d + 1))))) ≤ _
  apply max_le (Real.one_le_exp (shearKernelLogBudget_nonneg s d M.coe_nonneg hu))
  calc
    _ ≤ Real.exp u * (Real.exp (M : ℝ) * Real.exp (d : ℝ) * Real.exp (s : ℝ) *
        (Real.exp ((s * d : ℕ) * (M : ℝ) + 1)) ^ (s * (d + 1))) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      unfold shearKernelLogBudget
      ring

theorem shearDisplacementBound_le_exp (s d : ℕ) (M : ℝ≥0) :
    (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) ≤
      Real.exp (shearActionLogBudget s d M) := by
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  let J : ℝ := d * ((s + 1) * (d + 1) ^ s) * s
  have hB : 1 + J ≤ Real.exp J := by linarith [Real.add_one_le_exp J]
  have hR := shearRadius_le_exp s d M
  have he : (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) =
      (s : ℝ) * (1 + J) ^ s * ((((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ^ s) := by
    simp [polynomialShearDisplacementBound, J]
  rw [he]
  calc
    _ ≤ Real.exp (s : ℝ) * (Real.exp J) ^ s *
        (Real.exp ((s * d : ℕ) * (M : ℝ))) ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [J, shearActionLogBudget]
      push_cast
      ring

theorem shearObservable_log_bound {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)] (M : ℝ≥0) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u)
    (hC : (bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1 : ℝ) ≤ Real.exp v) :
    Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤
      shearKernelLogBudget s d M u + shearActionLogBudget s d M + v + 3 := by
  let E := shearKernelLogBudget s d M u + shearActionLogBudget s d M + v
  have hk := shearKernelLipBound_le_exp A M hu hA
  have ht := shearDisplacementBound_le_exp s d M
  have hE : 0 ≤ E := add_nonneg
    (add_nonneg (shearKernelLogBudget_nonneg s d M.coe_nonneg hu)
      (shearActionLogBudget_nonneg s d M.coe_nonneg)) hv
  have hL : (A.shearObservableLipBound M : ℝ) ≤ Real.exp E := by
    change max _ _ ≤ _
    apply max_le
    · apply hC.trans (Real.exp_le_exp.mpr ?_)
      dsimp [E]
      linarith [shearKernelLogBudget_nonneg s d M.coe_nonneg hu, shearActionLogBudget_nonneg s d M.coe_nonneg]
    · calc
        _ ≤ Real.exp (shearKernelLogBudget s d M u) * Real.exp (shearActionLogBudget s d M) * Real.exp v := by
          exact mul_le_mul (mul_le_mul hk ht (NNReal.coe_nonneg _) (Real.exp_nonneg _))
            hC (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp E := by linarith [Real.one_le_exp hE]
    _ ≤ Real.exp 3 * Real.exp E := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [E]; ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptedMapGeometryBudget
namespace OAI

section

namespace Erdos3

def adaptedMapGeometryBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 11 + (p + 4) ^ 11 + adaptedMarkedMapHeightBudget (p + 1) + p + 2

theorem adaptedMapGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ adaptedMapGeometryBudget p := by
  unfold adaptedMapGeometryBudget adaptedMarkedMapHeightBudget
  positivity

theorem adaptedMapGeometryBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 3) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_inverse {p : ℝ} (hp : 0 ≤ p) :
    (p + 4) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_markedMap {p : ℝ} (hp : 0 ≤ p) :
    adaptedMarkedMapHeightBudget (p + 1) ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_parameter {p : ℝ} (hp : 0 ≤ p) :
    p + 2 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem exists_adaptedMapGeometryBudget_fixed_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      adaptedMapGeometryBudget p + 1 ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + 3) ^ 11 + (Polynomial.X + 4) ^ 11 +
      ((Polynomial.X + 1) + ((Polynomial.X + 1) + 4) ^ 5 +
        ((Polynomial.X + 1) + 2) ^ 4 + 2) ^ 4 + Polynomial.X + 2 + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, adaptedMapGeometryBudget, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem rationalMatrix_real_ker_eq_range
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      LinearMap.range (Matrix.mulVecLin (fun i k => (A i k : ℝ))) := by
  classical
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hex : Function.Exact (A.mulVecLin.baseChange ℝ) (D.mulVecLin.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ (LinearMap.exact_iff.mpr h)
  ext x
  change Matrix.mulVecLin (fun j i => (D j i : ℝ)) x = 0 ↔
    ∃ y, Matrix.mulVecLin (fun i k => (A i k : ℝ)) y = x
  constructor
  · intro hx
    have hx' : D.mulVecLin.baseChange ℝ
        ((TensorProduct.piScalarRight ℚ ℝ ℝ I).symm x) = 0 := by
      apply (TensorProduct.piScalarRight ℚ ℝ ℝ J).injective
      rw [rationalMatrix_piScalarRight_baseChange, map_zero,
        LinearEquiv.apply_symm_apply]
      exact hx
    obtain ⟨z, hz⟩ := (hex _).mp hx'
    refine ⟨TensorProduct.piScalarRight ℚ ℝ ℝ K z, ?_⟩
    rw [← rationalMatrix_piScalarRight_baseChange, hz,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    have hz := hex.apply_apply_eq_zero
      ((TensorProduct.piScalarRight ℚ ℝ ℝ K).symm y)
    have he := congrArg (TensorProduct.piScalarRight ℚ ℝ ℝ J) hz
    simpa only [rationalMatrix_piScalarRight_baseChange,
      LinearEquiv.apply_symm_apply, map_zero] using he

theorem rationalMatrix_real_ker_eq_span
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      Submodule.span ℝ (Set.range (fun k i => (A i k : ℝ))) := by
  rw [rationalMatrix_real_ker_eq_range A D h]
  exact Matrix.range_mulVecLin (fun i k => (A i k : ℝ) : Matrix I K ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem matrixDenominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (matrixDenominator D : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hcard : (Fintype.card (ι × κ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hι.trans (by linarith)) (hκ.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  simpa only [matrixDenominator, arrayDenominator, Nat.cast_prod] using
    product_exponential_budget Finset.univ (fun ij : ι × κ => ((D ij.1 ij.2).den : ℝ))
      hp a 2 (fun _ _ => Nat.cast_nonneg _) (fun ij _ => hD ij.1 ij.2) hcard

theorem matrix_weighted_factor_le_exp_power (n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ a) + 1) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hA : 1 ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
  have hpA : p ≤ (p + 2) ^ a := le_power_budget hp ha
  have hplus : Real.exp ((p + 2) ^ a) + 1 ≤ Real.exp ((p + 2) ^ a + 1) := by
    calc
      _ ≤ Real.exp ((p + 2) ^ a) * 2 := by
        have h := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ (p + 2) ^ a)
        linarith
      _ ≤ Real.exp ((p + 2) ^ a) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a + 1) :=
      mul_le_mul (by linarith [Real.add_one_le_exp p]) hplus (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + ((p + 2) ^ a + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * (p + 2) ^ a := by linarith
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ a :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [pow_add]; ring

theorem matrix_pair_denominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hS : ∀ i j, ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator D * matrixDenominator S * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (a + 4)) := by
  have hDb := matrixDenominator_le_exp_power D hp a hκ hι hD
  have hSb := matrixDenominator_le_exp_power S hp a hι hκ hS
  have hlb := hl.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega : 1 ≤ a + 2)))
  rw [Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) * Real.exp ((p + 2) ^ (a + 2)) *
        Real.exp ((p + 2) ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hDb hSb (Nat.cast_nonneg _) (Real.exp_nonneg _)) hlb
        (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (3 * (p + 2) ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + 2) ^ (a + 4)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ (a + 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem rationalKernelSeparationConstant_ceil_le_exp_power
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℚ) {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp ((p+2)^a))
    (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    (⌈(matrixDenominator Q : ℝ) *
      (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))⌉₊ : ℝ) ≤
        Real.exp ((p+2)^(a+4)) := by
  let c : ℝ := (matrixDenominator Q : ℝ) *
    (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))
  have hden := matrixDenominator_le_exp_power Q hp a hι hκ
    (fun i j => (Nat.cast_le.mpr (hQ i j).2).trans hH)
  have hfactor : ((Fintype.card κ : ℝ)+1)*((H : ℝ)+1) ≤
      Real.exp ((p+2)^(a+2)) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ a ha)
    exact mul_le_mul_of_nonneg_left (by linarith only [hH]) (by positivity)
  have hc : c ≤ Real.exp ((p+2)^(a+3)) := by
    calc
      _ ≤ Real.exp ((p+2)^(a+2)) * Real.exp ((p+2)^(a+2)) :=
        mul_le_mul hden hfactor (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2*(p+2)^(a+2)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p+2)*(p+2)^(a+2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by rw [pow_succ]; ring
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hceil : (⌈c⌉₊ : ℝ) ≤ c+1 := (Nat.ceil_lt_add_one hc0).le
  change (⌈c⌉₊ : ℝ) ≤ _
  calc
    _ ≤ Real.exp ((p+2)^(a+3))+1 := hceil.trans (by linarith only [hc])
    _ ≤ Real.exp ((p+2)^(a+3)) * 2 := by
      have hExp := Real.one_le_exp_iff.mpr (show 0 ≤ (p+2)^(a+3) by positivity)
      linarith only [hExp]
    _ ≤ Real.exp ((p+2)^(a+3)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp ((p+2)^(a+3)+1) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hbase : 1 ≤ (p+2)^(a+3) := one_le_pow₀ (by linarith)
      calc
        _ ≤ 2*(p+2)^(a+3) := by linarith only [hbase]
        _ ≤ (p+2)*(p+2)^(a+3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix BigOperators

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (e : Basis κ ℚ V)

omit [Fintype κ] in
theorem real_basis_coordinates_transfer (x : ℝ ⊗[ℚ] V) :
    (fun i => (e.baseChange ℝ).repr x i) =
      (fun i j => (e.repr (b j) i : ℝ)) *ᵥ (fun j => (b.baseChange ℝ).repr x j) := by
  classical
  funext i
  conv_lhs => rw [← (b.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  change (∑ j, (b.baseChange ℝ).repr x j * (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i) = _
  have he (j : ι) : (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i = (e.repr (b j) i : ℝ) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simp
  simp only [he, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype κ] in
theorem real_basis_coordinates_bound {H : ℕ} {B : ℝ}
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ B) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ (Fintype.card ι : ℝ) * H * B := by
  have hcoord := congrFun (real_basis_coordinates_transfer b e x) i
  rw [hcoord]
  calc
    _ ≤ ∑ j, |(e.repr (b j) i : ℝ) * (b.baseChange ℝ).repr x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, (H : ℝ) * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hentries i j).abs_real_le (hx j) (abs_nonneg _) (Nat.cast_nonneg H)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem real_basis_coordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun j => (b.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun i => (e.baseChange ℝ).repr x i) ∈
      realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  rw [real_basis_coordinates_transfer b e x]
  exact real_matrix_denominator_grid (fun i j => e.repr (b j) i) l _ hx

theorem real_basis_transfer_denominator {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H) :
    (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
  intro i j
  exact (show ((e.repr (b j) i).den : ℝ) ≤ H by exact_mod_cast (hentries i j).2).trans
    (hHp.trans (Real.exp_le_exp.mpr (by simp)))

omit [Fintype κ] in
theorem real_basis_coordinates_exp_bound {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ Real.exp p) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (Fintype.card ι : ℝ) ≤ Real.exp p := hι.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ (Fintype.card ι : ℝ) * H * Real.exp p := real_basis_coordinates_bound b e hentries x hx i
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (mul_le_mul hdim hHp (Nat.cast_nonneg H) (Real.exp_nonneg p))
        (Real.exp_nonneg p)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

section

namespace Erdos3
open scoped Matrix

theorem exists_rationalTaggedSpanProjection
    {J : Type*} [Fintype J] {r : ℕ} (g : Fin r → J → ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hr : (r : ℝ) ≤ p) (hg : ∀ a j, rationalLogHeight (g a j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card J ∧
      ∃ Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ),
        LinearMap.ker Q = Submodule.span ℝ (Set.range (fun a j => (g a j : ℝ))) ∧
        (∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖) ∧
        ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
          ∀ x : J → ℤ, ∃ z : Fin d → ℤ,
            ∀ i, (z i : ℝ) = (D : ℝ) * Q (fun j => (x j : ℝ)) i := by
  classical
  have hheight : ∀ j a, RationalHeightLE (g a j) ⌊Real.exp p⌋₊ := by
    intro j a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff (g a j) p).mp (hg a j)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  obtain ⟨d, hd, M, S, hker, hMS, hM, hS⟩ :=
    exists_quotient_presentation_exp_height (fun j a => g a j)
      ((Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)) hheight
      hp hJ (by simpa using hr) (Nat.floor_le (Real.exp_nonneg p))
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa using (Nat.cast_le.mpr hd).trans hJ
  let Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Matrix.mulVecLin (fun i j => (M i j : ℝ))
  have hentry : ∀ i j, |(M i j : ℝ)| ≤ Real.exp ((p + 2) ^ 7) :=
    fun i j => (rational_abs_real_le_numerator (M i j)).trans (hM i j).1
  have hbound : ∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖ := by
    intro x i
    have hb := abs_matrix_mulVec_le (fun i j => (M i j : ℝ))
      ⟨Real.exp ((p + 2) ^ 7), Real.exp_nonneg _⟩ hentry x i
    exact hb.trans (mul_le_mul_of_nonneg_right
      (matrix_weighted_factor_le_exp_power (Fintype.card J) hp hJ 7 (by decide))
      (norm_nonneg x))
  refine ⟨d, hd, Q, ?_, hbound, matrixDenominator M, matrixDenominator_pos M,
    matrixDenominator_le_exp_power M hp 7 hdp hJ (fun i j => (hM i j).2), ?_⟩
  · exact rationalMatrix_real_ker_eq_span (fun j a => g a j) M hker
  · intro x
    have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
      ⟨x, by ext j; simp⟩
    obtain ⟨z, hz⟩ := real_matrix_denominator_grid M 1 (fun j => (x j : ℝ)) hx
    refine ⟨z, fun i => ?_⟩
    change (z i : ℝ) = (matrixDenominator M : ℝ) *
      ((fun i j => (M i j : ℝ)) *ᵥ (fun j => (x j : ℝ))) i
    simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using congrFun hz i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem filtered_section_coefficient_loss_le_exp (n m H a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    Real.exp ((p + 2) ^ a) +
      (((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1)) *
        ((((n : ℝ) + 1) * ((H : ℝ) + 1)) * Real.exp ((p + 2) ^ a) +
          Real.exp ((p + 2) ^ a)) ≤ Real.exp ((p + 2) ^ (a + 12)) := by
  let q := (p + 2) ^ (a + 9)
  let E := Real.exp q
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hq : 1 ≤ q := one_le_pow₀ hbase
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by dsimp [q]; positivity)
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hpow (b : ℕ) (hb : b ≤ a + 9) : (p + 2) ^ b ≤ q := pow_le_pow_right₀ hbase hb
  have hA : Real.exp ((p + 2) ^ a) ≤ E := Real.exp_le_exp.mpr (hpow a (by omega))
  have hD : ((n : ℝ) + 1) * ((H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
      _ ≤ Real.exp ((p + 2) ^ 3) := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 3 (by omega))
  have hS : ((m : ℝ) + 1) * ((rationalKernelHeight m H : ℝ) + 1) ≤ E := by
    calc
      _ ≤ ((m : ℝ) + 1) * (Real.exp ((p + 2) ^ 7) + 1) := by
        gcongr
        exact rationalKernelHeight_le_budget m H hp hm hH
      _ ≤ Real.exp ((p + 2) ^ 9) := matrix_weighted_factor_le_exp_power m hp hm 7 (by decide)
      _ ≤ E := Real.exp_le_exp.mpr (hpow 9 (by omega))
  have hE2 : E ≤ E * E := by nlinarith
  have hE3 : E * E ≤ E * E * E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (mul_nonneg hE0 hE0)
  calc
    _ ≤ E + E * (E * E + E) := by gcongr
    _ ≤ 3 * E ^ 3 := by nlinarith
    _ ≤ Real.exp 2 * (Real.exp q) ^ 3 := by
      change 3 * (Real.exp q) ^ 3 ≤ _
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by positivity)
    _ = Real.exp (2 + 3 * q) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ Real.exp ((p + 2) ^ (a + 12)) := by
      apply Real.exp_le_exp.mpr
      have hcube : (8 : ℝ) ≤ (p + 2) ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
        norm_num at h ⊢
        exact h
      calc
        2 + 3 * q ≤ 8 * q := by linarith
        _ ≤ (p + 2) ^ 3 * q := mul_le_mul_of_nonneg_right hcube (by linarith)
        _ = (p + 2) ^ (a + 12) := by
          dsimp [q]
          rw [← pow_add]
          congr 1
          omega

theorem filtered_section_pair_denominator_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * matrixDenominator D * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  have hH7 := hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 7)))
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  have h := matrix_pair_denominator_le_exp_power D S l hp 7 (by decide) hι hκ
    (fun i j => (Nat.cast_le.mpr (hD i j).2).trans hH7)
    (fun i j => (Nat.cast_le.mpr (hS i j).2).trans hK) hl
  simpa only [Nat.mul_comm (matrixDenominator S) (matrixDenominator D)] using h

end Erdos3

end

section

namespace Erdos3

theorem filtered_section_single_denominator_le_exp {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 11) := by
  have hqD : 1 ≤ matrixDenominator D := matrixDenominator_pos D
  have hnat := Nat.mul_le_mul_right l (Nat.mul_le_mul_left (matrixDenominator S) hqD)
  simp only [Nat.mul_one] at hnat
  exact (Nat.cast_le.mpr hnat).trans
    (filtered_section_pair_denominator_le_exp D S l hp hι hκ hH hD hS hl)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3

theorem rational_matrix_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ a)) ∧
    0 < matrixDenominator S ∧
    (matrixDenominator S : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) ∧
    ∀ i j, ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = z := by
  refine ⟨?_, matrixDenominator_pos S, ?_, ?_⟩
  · intro i j
    exact (rational_abs_real_le_numerator (S i j)).trans (hS i j).1
  · apply matrixDenominator_le_exp_power S hp a hι hκ
    intro i j
    exact (hS i j).2
  · exact matrixDenominator_mul_entry_real_integral S

theorem rational_section_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ 45)) ∧
    ∃ q : ℕ, q = matrixDenominator S ∧ 0 < q ∧
      (q : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
      ∀ i j, ∃ z : ℤ, (q : ℝ) * (S i j : ℝ) = z := by
  obtain ⟨hentry, hpos, hden, hint⟩ := rational_matrix_entry_budget S hp 45 hι hκ hS
  exact ⟨hentry, matrixDenominator S, rfl, hpos, hden, hint⟩

end Erdos3

end

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Matrix

def lieSubalgebraRepresentativeHeight (d r H : ℕ) : ℕ :=
  rationalLieStructureHeight d (max H (rationalSolveHeight r H))

noncomputable def lieSubalgebraRepresentativeParameter (p : ℝ) : ℝ := (p + 2) ^ 12

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]

theorem lieSubalgebraRepresentative_bracket_height (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k)
      (lieSubalgebraRepresentativeHeight (Fintype.card ι) (Fintype.card κ) H) := by
  obtain ⟨P, hP, hPH, hsource⟩ := exists_bounded_lie_embedding_retraction bk b K.incl
    (fun _ _ h => Subtype.ext h) hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hinc i j)
  exact hsource

theorem lieSubalgebraRepresentativeHeight_le_exp (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤ Real.exp ((p + 2) ^ 11) :=
  rationalLieStructureHeight_inverse_budget d r H hp hd hr hH

theorem lieSubalgebraRepresentativeParameter_pos {p : ℝ} (hp : 0 ≤ p) :
    0 < lieSubalgebraRepresentativeParameter p := by
  unfold lieSubalgebraRepresentativeParameter
  positivity

theorem lieSubalgebraRepresentativeHeight_le_exp_parameter (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤
      Real.exp (lieSubalgebraRepresentativeParameter p) := by
  apply (lieSubalgebraRepresentativeHeight_le_exp d r H hp hd hr hH).trans
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 11 ≤ 12)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedRefilteredModelBudget
namespace OAI

section

namespace Erdos3

def markedRefilteredBasisInput (p : ℝ) : ℝ :=
  p + adaptedMarkedMapHeightBudget p + 1

def markedRefilteredMapInput (p : ℝ) : ℝ :=
  markedRefilteredBasisInput p + (markedRefilteredBasisInput p + 2) ^ 4

def markedRefilteredModelInput (A : ℕ) (p : ℝ) : ℝ :=
  p + markedRefilteredMapInput p + (markedRefilteredMapInput p + A) ^ A + 1

theorem markedRefilteredModelInput_bounds (A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := markedRefilteredBasisInput p
    let t := markedRefilteredMapInput p
    let r := markedRefilteredModelInput A p
    0 ≤ q ∧ p ≤ q ∧ adaptedMarkedMapHeightBudget p ≤ q ∧
      0 ≤ t ∧ q ≤ t ∧ (q + 2) ^ 4 ≤ t ∧
      0 ≤ r ∧ p ≤ r ∧ (t + A) ^ A ≤ r := by
  dsimp only
  have hb : 0 ≤ adaptedMarkedMapHeightBudget p := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  have hq : 0 ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    positivity
  have hpq : p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hb]
  have hbq : adaptedMarkedMapHeightBudget p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hp]
  have hpow : 0 ≤ (markedRefilteredBasisInput p + 2) ^ 4 := by positivity
  have ht : 0 ≤ markedRefilteredMapInput p := add_nonneg hq hpow
  have hqt : markedRefilteredBasisInput p ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_right hpow
  have hpowt : (markedRefilteredBasisInput p + 2) ^ 4 ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_left hq
  have hmodel : 0 ≤ (markedRefilteredMapInput p + A) ^ A := by positivity
  have hr : 0 ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    positivity
  have hpr : p ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [ht, hmodel]
  have hmodelr : (markedRefilteredMapInput p + A) ^ A ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [hp, ht]
  exact ⟨hq, hpq, hbq, ht, hqt, hpowt, hr, hpr, hmodelr⟩

theorem exists_markedRefilteredModelInput_budget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      markedRefilteredModelInput A p ≤ (p + C) ^ C ∧
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
        (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X +
    (Polynomial.X + (Polynomial.X + 4) ^ 5 + (Polynomial.X + 2) ^ 4 + 2) ^ 4 + 1
  let T : Polynomial ℕ := Q + (Q + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.X + T + (T + Polynomial.C A) ^ A + 1
  let P : Polynomial ℕ := R + ((R + 2) ^ 4 + R + 4) ^ 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  have hr := (markedRefilteredModelInput_bounds A hp).2.2.2.2.2.2.1
  have hcost : 0 ≤
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 := by
    positivity
  have hsum : markedRefilteredModelInput A p +
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
      (p + C) ^ C := by
    simpa [P, R, T, Q, markedRefilteredModelInput, markedRefilteredMapInput,
      markedRefilteredBasisInput, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hcost).trans hsum, (le_add_of_nonneg_left hr).trans hsum⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

abbrev PatchTopCoefficientIndex (d s : ℕ) := Fin d × BoundedIntegerExponent (Fin d) s

theorem patchTopCoefficientIndex_card (d s : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s) ≤ d * (d + 1) ^ s := by
  simpa only [PatchTopCoefficientIndex, Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_left d (boundedIntegerExponent_card_le (Fin d) s)

theorem patchTopCoefficientCode_card (d s N : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) ≤
      (N + 1) ^ (d * (d + 1) ^ s) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by omega) (patchTopCoefficientIndex_card d s)

noncomputable def patchTopNetError (d s N : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * (4 * (1 + M) / N) * ((1 + M) ^ (s * d)) ^ s

theorem patchTopNetError_nonneg (d s N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ patchTopNetError d s N M := by unfold patchTopNetError; positivity

namespace PolynomialSlots

theorem exists_shear_observable_net {X Ω : Type*} [Nonempty Ω] {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4) :
    ∃ (code : Ω → PatchTopCoefficientIndex d s → Fin (N + 1))
      (rep : (PatchTopCoefficientIndex d s → Fin (N + 1)) → Ω),
      ∀ a e, dist (((A a).shearTransformedSlots hw e).patchValue Φ)
        (((A (rep (code a))).shearTransformedSlots hw e).patchValue Φ) ≤
        Φ.lip * patchTopNetError d s N M := by
  let coordinates : Ω → PatchTopCoefficientIndex d s → ℝ :=
    fun a j => ((A a).topResidualEquiv (MvPolynomial.X j.1)).coeff j.2.val
  have hbound (a) (j : PatchTopCoefficientIndex d s) : |coordinates a j| ≤ 1 + M :=
    (realPolynomialMass_coeff_le _ _).trans ((A a).topResidualEquiv_X_mass (hA a) j.1)
  obtain ⟨code, rep, hnet⟩ := exists_uniform_parameter_net coordinates (by linarith : 0 < 1 + M) hbound hN
  refine ⟨code, rep, fun a e => ?_⟩
  apply (A a).shearPatchValue_dist (A (rep (code a))) hw hpos s hs Φ hM
    (patchTopNetError_nonneg d s N hM) hsmall (hA a) (hA _) _ e
  intro x hx
  apply (dist_pi_le_iff (patchTopNetError_nonneg d s N hM)).mpr
  intro i
  have hdegree (a : Ω) : ((A a).topResidualEquiv (MvPolynomial.X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      ((A a).topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hs i)
  have hcoeff (m : BoundedIntegerExponent (Fin d) s) :
      |((A a).topResidualEquiv (MvPolynomial.X i)).coeff m.val -
        ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i)).coeff m.val| ≤ 4 * (1 + M) / N := by
    exact (dist_le_pi_dist (coordinates a) (coordinates (rep (code a))) (i,m)).trans (hnet a)
  have h := bounded_coefficients_evaluation_error _ _ (hdegree a) (hdegree _)
    (by positivity : 0 ≤ 4 * (1 + M) / N)
    (one_le_pow₀ (by linarith : 1 ≤ 1 + M) : 1 ≤ (1 + M) ^ (s * d)) hcoeff x hx
  change |aeval x ((A a).topResidualEquiv (MvPolynomial.X i)) -
    aeval x ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i))| ≤ patchTopNetError d s N M
  simpa only [Fintype.card_fin, patchTopNetError] using h

end PolynomialSlots
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PatchTopNetBudget
namespace OAI

section

namespace Erdos3

noncomputable def patchTopNetNumerator (d s : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * 4 * (1 + M) * ((1 + M) ^ (s * d)) ^ s

def patchTopNetNumeratorLog (s : ℕ) (p : ℝ) : ℝ :=
  s + s * p + p + 4 + s * s * p * (p + 1)

theorem patchTopNetError_eq_div (d s N : ℕ) (M : ℝ) :
    patchTopNetError d s N M = patchTopNetNumerator d s M / N := by
  unfold patchTopNetError patchTopNetNumerator
  ring

theorem patchTopNetNumeratorLog_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ patchTopNetNumeratorLog s p := by unfold patchTopNetNumeratorLog; positivity

theorem patchTopNetNumerator_le_exp (d s : ℕ) {M p : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) :
    patchTopNetNumerator d s M ≤ Real.exp (patchTopNetNumeratorLog s p) := by
  have hs : (s : ℝ) + 1 ≤ Real.exp s := Real.add_one_le_exp _
  have hd1 : (d : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hM1 : 1 + M ≤ Real.exp (p + 1) := by
    simpa only [zero_add] using add_le_exp_add_one (le_refl (0 : ℝ)) hp
      (by simp : (1 : ℝ) ≤ Real.exp 0) hMp
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    patchTopNetNumerator d s M ≤
        (Real.exp s * (Real.exp p) ^ s) * Real.exp 3 * Real.exp (p + 1) *
          ((Real.exp (p + 1)) ^ (s * d)) ^ s := by
      unfold patchTopNetNumerator
      push_cast
      gcongr
    _ = Real.exp (s + s * p + 3 + (p + 1) + s * ((s * d : ℕ) : ℝ) * (p + 1)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold patchTopNetNumeratorLog
      push_cast
      have h := mul_le_mul_of_nonneg_left hd
        (by positivity : 0 ≤ (s : ℝ) * s * (p + 1))
      nlinarith

theorem exists_small_patch_top_mesh (d s : ℕ) {M L p : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧
      ((N + 1 : ℕ) : ℝ) ≤ Real.exp (patchTopNetNumeratorLog s p + 2 * p + 6) ∧
      patchTopNetError d s N M < 1 / 4 ∧
      L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let b := patchTopNetNumeratorLog s p
  let E := b + 2 * p + 4
  let N := ⌈Real.exp E⌉₊
  have hb : 0 ≤ b := patchTopNetNumeratorLog_nonneg s hp
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hNlo : Real.exp E ≤ (N : ℝ) := Nat.le_ceil _
  have hNr : (0 : ℝ) < N := (Real.exp_pos E).trans_le hNlo
  have hN : 0 < N := by exact_mod_cast hNr
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (E + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg E)).le
    have h1 := Real.one_le_exp hE
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg E)
    dsimp only [N] at *
    linarith
  have herr : patchTopNetError d s N M ≤ Real.exp (-2 * p - 4) := by
    rw [patchTopNetError_eq_div]
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ Real.exp b := patchTopNetNumerator_le_exp d s hp hM hd hMp
      _ = Real.exp (-2 * p - 4) * Real.exp E := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [E]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNlo (Real.exp_nonneg _)
  have hfour : (4 : ℝ) < Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsmall : Real.exp (-4 : ℝ) < 1 / 4 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hfour
  have hsmall' : patchTopNetError d s N M < 1 / 4 :=
    (herr.trans (Real.exp_le_exp.mpr (by linarith))).trans_lt hsmall
  have hloss : L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * Real.exp (-2 * p - 4) :=
        (mul_le_mul_of_nonneg_left herr hL).trans
          (mul_le_mul_of_nonneg_right hLp (Real.exp_nonneg _))
      _ = Real.exp (-p) * Real.exp (-4) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (hsmall.le.trans (by norm_num)) (Real.exp_nonneg _)
      _ = _ := by ring
  have he : E + 2 = patchTopNetNumeratorLog s p + 2 * p + 6 := by dsimp only [E, b]; ring
  rw [he] at hNhi
  exact ⟨N, hN, hNhi, hsmall', hloss⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_sub {ι : Type*} (l : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid l) :
    x - y ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  change ((a i - b i : ℤ) : ℝ) = (l : ℝ) * (x i - y i)
  rw [Int.cast_sub, mul_sub]
  exact congrArg₂ (· - ·) (congrFun ha i) (congrFun hb i)

theorem realDenominatorGrid_sub_product {ι : Type*} (l m : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid m) :
    x - y ∈ realDenominatorGrid (l * m) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨fun i => (m : ℤ) * a i - (l : ℤ) * b i, ?_⟩
  funext i
  change (((m : ℤ) * a i - (l : ℤ) * b i : ℤ) : ℝ) =
    (l * m : ℕ) * (x i - y i)
  have h1 : (a i : ℝ) = (l : ℝ) * x i := congrFun ha i
  have h2 : (b i : ℝ) = (m : ℝ) * y i := congrFun hb i
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, h1, h2]
  ring

theorem realDenominatorGrid_linear_combination {ι κ : Type*} [Fintype κ]
    (l m : ℕ) (c : κ → ℝ) (v : κ → ι → ℝ)
    (hc : c ∈ realDenominatorGrid l) (hv : ∀ k, v k ∈ realDenominatorGrid m) :
    (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  classical
  obtain ⟨a, ha⟩ := hc
  choose b hb using hv
  refine ⟨fun i => ∑ k, a k * b k i, ?_⟩
  funext i
  change ((∑ k, a k * b k i : ℤ) : ℝ) = (m * l : ℕ) * (∑ k, c k • v k) i
  simp only [Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : (a k : ℝ) = (l : ℝ) * c k := congrFun ha k
  have h2 : (b k i : ℝ) = (m : ℝ) * v k i := congrFun (hb k) i
  rw [h1, h2]
  ring

theorem linear_lift_grid_of_coefficients {ι κ K : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K]
    (R : K →ₗ[ℝ] (ι → ℝ)) (v : κ → K) (c : κ → ℝ) (l m : ℕ)
    (hc : c ∈ realDenominatorGrid l) (hR : ∀ k, R (v k) ∈ realDenominatorGrid m) :
    R (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  simp only [map_sum, map_smul]
  exact realDenominatorGrid_linear_combination l m c (fun k => R (v k)) hc hR

theorem norm_removed_derivative_bound {E V : Type*}
    [AddCommGroup E] [Module ℝ E] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (N : E →ₗ[ℝ] V) (A : E →ₗ[ℝ] E) (x y : E)
    (C M D T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hA : ∀ z, ‖N (A z)‖ ≤ C * ‖N z‖)
    (hx : ‖N x‖ ≤ M / T) (hy : ‖N y‖ ≤ D / T) :
    ‖N (A (x - y))‖ ≤ C * (M + D) / T := by
  calc
    _ ≤ C * ‖N (x - y)‖ := hA _
    _ ≤ C * (‖N x‖ + ‖N y‖) := by
      rw [map_sub]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC
    _ ≤ C * (M / T + D / T) := mul_le_mul_of_nonneg_left (add_le_add hx hy) hC
    _ = _ := by field_simp [hT.ne']

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem kernel_split_factor_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18) ≤ Real.exp ((p + 2) ^ 19) := by
  have hfac : ((n : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (by simp))
      _ ≤ _ := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
  have hpow : (p + 2) ^ 3 ≤ (p + 2) ^ 18 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hsum : (p + 2) ^ 3 + (p + 2) ^ 18 ≤ (p + 2) ^ 19 := by
    calc
      _ ≤ (p + 2) ^ 18 + (p + 2) ^ 18 := add_le_add hpow (le_refl ((p + 2) ^ 18))
      _ = 2 * (p + 2) ^ 18 := by ring
      _ ≤ (p + 2) * (p + 2) ^ 18 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := (pow_succ' (p + 2) 18).symm
  calc
    _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((p + 2) ^ 18) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
    _ = Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

theorem exists_controlled_kernel_split {ι κ ν τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K)
    (b : ν → K) (hb : ∀ j, (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : (ι → ℝ) →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖split x‖ ≤ Real.exp ((p + 2) ^ 19) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  classical
  obtain ⟨m, hm, hmp, u, v, hdecomp, hnorm, hgrid⟩ :=
    exists_controlled_sum_coordinates A B hH hl hA hB hp hι hcols hHp hlp
  have hν : (Fintype.card ν : ℝ) ≤ p := by
    have hsum : (Fintype.card κ : ℝ) + Fintype.card ν ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  let C : (ν → ℝ) →ₗ[ℝ] K := {
    toFun := fun c => ∑ j, c j • b j
    map_add' := by intros; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hC (c : ν → ℝ) : (C c).val = B.map (Rat.castHom ℝ) *ᵥ c := by
    change K.subtype (∑ j, c j • b j) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ j, c j • (b j).val) = _
    simp only [hb]
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨m, hm, hmp, C.comp v, ?_, ?_, ?_⟩
  · intro x hx
    have hd := hdecomp x (by simpa only [hAspan, hBspan] using hx)
    have hu : A.map (Rat.castHom ℝ) *ᵥ u x ∈ U := by
      rw [← hAspan]
      exact (real_column_span_mem_iff A _).mpr ⟨u x, rfl⟩
    change x - (C (v x)).val ∈ U
    have he : x - B.map (Rat.castHom ℝ) *ᵥ v x = A.map (Rat.castHom ℝ) *ᵥ u x :=
      (eq_sub_iff_add_eq.mpr hd).symm
    rw [hC, he]
    exact hu
  · intro x
    change ‖(C (v x)).val‖ ≤ _
    rw [hC]
    have hmat := norm_matrix_mulVec_le (B.map (Rat.castHom ℝ)) (H : ℝ≥0)
      (fun i j => (hB i j).abs_real_le) (v x)
    calc
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * ‖v x‖ := hmat
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * (Real.exp ((p + 2) ^ 18) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hnorm x).2 (by positivity)
      _ = (((Fintype.card ν : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18)) * ‖x‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (kernel_split_factor_le_exp (Fintype.card ν) H hp hν hHp) (norm_nonneg x)
  · intro x hx
    exact linear_lift_grid_of_coefficients R b (v x) m n (hgrid x hx).2 hR

theorem horizontal_absorption_with_split {H E : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    (U K : Submodule ℝ H) (P : E →ₗ[ℝ] H)
    (f : E →ₗ[ℝ] E) (hf : P.comp f = P) (S R : K →ₗ[ℝ] E)
    (hSR : S = f.comp R) (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (split : H →ₗ[ℝ] K) (hsplit : ∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U)
    (y small rational : E) (k : K) (hsystem : y = small + f rational + S k)
    (hy : P y ∈ U) (hsmall : P small ∈ U ⊔ K) (hrational : P rational ∈ U ⊔ K) :
    let ks := split (P small)
    let kr := split (P rational)
    P (small - S ks) ∈ U ∧ P (rational - R kr) ∈ U ∧ (k + ks + kr).val ∈ U ∧
      y = (small - S ks) + f (rational - R kr) + S (k + ks + kr) := by
  let ks := split (P small)
  let kr := split (P rational)
  have hs : P (small - S ks) ∈ U := by
    rw [map_sub, show P (S ks) = ks.val from DFunLike.congr_fun hS ks]
    exact hsplit (P small) hsmall
  have hr : P (rational - R kr) ∈ U := by
    rw [map_sub, show P (R kr) = kr.val from DFunLike.congr_fun hR kr]
    exact hsplit (P rational) hrational
  have hnew := linear_derivative_absorb f S R hSR y small rational k ks kr hsystem
  refine ⟨hs, hr, ?_, hnew⟩
  have he : P y = P (small - S ks) + P (rational - R kr) + (k + ks + kr).val := by
    rw [hnew, map_add, map_add,
      show P (f (rational - R kr)) = P (rational - R kr) from DFunLike.congr_fun hf _,
      show P (S (k + ks + kr)) = (k + ks + kr).val from DFunLike.congr_fun hS _]
  have hm := U.sub_mem (U.sub_mem hy hs) hr
  have he' : P y - P (small - S ks) - P (rational - R kr) = (k + ks + kr).val := by
    rw [he]
    abel
  exact he' ▸ hm

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_image_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b u v : ι → ℝ),
        u ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        u - v = a + b → ∃ e q : ι → ℝ,
          e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          u - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, m, hm, hmp, hsolve⟩ :=
    exists_controlled_linear_splitting C hH hl hC hp hι hcols hHp hlp T hT
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ν)]
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hι hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b u v hu hv ha hb hdiff
    have hspan : Submodule.span ℝ (Set.range (fun j i => (C i j : ℝ))) =
        Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ⊔
          Submodule.span ℝ (Set.range (fun j i => (B i j : ℝ))) :=
      real_column_span_fromCols A B
    have hdiffmem : u - v ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      apply (real_column_span_mem_iff C _).mp
      rw [hspan]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ((real_column_span_mem_iff A _).mpr hu))
        (Submodule.mem_sup_right ((real_column_span_mem_iff B _).mpr hv))
    obtain ⟨z, hz⟩ := hdiffmem
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb (hz.trans hdiff)
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cb := (fun i j => (S i j : ℝ)) *ᵥ b
    let e := (fun i j => (A i j : ℝ)) *ᵥ (ca ∘ Sum.inl)
    let q := (fun i j => (A i j : ℝ)) *ᵥ (cb ∘ Sum.inl)
    let eB := (fun i j => (B i j : ℝ)) *ᵥ (ca ∘ Sum.inr)
    let qB := (fun i j => (B i j : ℝ)) *ᵥ (cb ∘ Sum.inr)
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := ⟨_, rfl⟩
    have heB : eB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hqB : qB ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := ⟨_, rfl⟩
    have hea : e + eB = a := by
      change (C.map (Rat.castHom ℝ)) *ᵥ ca = a at hSa
      dsimp only [C] at hSa
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSa
      exact hSa
    have hqb : q + qB = b := by
      change (C.map (Rat.castHom ℝ)) *ᵥ cb = b at hSb
      dsimp only [C] at hSb
      rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at hSb
      exact hSb
    refine ⟨e, q, he, hq, ?_,
      real_matrix_denominator_grid A m _ (realDenominatorGrid_comp m _ hgrid Sum.inl),
      Submodule.sub_mem _ (Submodule.sub_mem _ hu he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca ∘ Sum.inl‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left ((pi_norm_restriction_le ca Sum.inl).trans hslow)
            (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · have heq : u - e - q = v + eB + qB := by
        rw [← hea, ← hqb] at hdiff
        have hu' : u = (e + eB) + (q + qB) + v := (sub_eq_iff_eq_add).mp hdiff
        rw [hu']
        abel
      rw [heq]
      exact Submodule.add_mem _ (Submodule.add_mem _ hv heB) hqB

end Erdos3

end

section

namespace Erdos3

theorem exists_common_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        β - e₂ - q₂ ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ⊓
            LinearMap.range (Matrix.mulVecLin (fun i j => (B i j : ℝ))) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_image_intersection_corrections A B hH hl hA hB hp
    hι hcols hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα β e₁ e₂ q₁ q₂ h₁ h₂ he₁ he₂ hq₁ hq₂
    have hdiff : (β - e₁ - q₁) - (β - e₂ - q₂) = (e₂ - e₁) + (q₂ - q₁) := by abel
    obtain ⟨e, q, _, _, he, hq, hrem⟩ := hsolve α hα (e₂ - e₁) (q₂ - q₁)
      (β - e₁ - q₁) (β - e₂ - q₂) h₁ h₂ he₂
      (realDenominatorGrid_sub l q₂ q₁ hq₂ hq₁) hdiff
    refine ⟨e₁ + e, q₁ + q, ?_, ?_, ?_⟩
    · calc
        ‖e₁ + e‖ ≤ ‖e₁‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add he₁ he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using
        realDenominatorGrid_sub_product l m q₁ (-q) hq₁ (realDenominatorGrid_neg m hq)
    · have heq : β - (e₁ + e) - (q₁ + q) = (β - e₁ - q₁) - e - q := by abel
      rwa [heq]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_basis_intersection_correction
    {μ κ ν σ L : Type*} [Fintype μ] [Fintype κ] [Fintype ν]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (U V : Submodule ℚ L) (v : κ → L) (w : ν → L)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (b.repr (v a) i) H)
    (hwH : ∀ a i, RationalHeightLE (b.repr (w a) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x e q : ℝ ⊗[ℚ] L),
        x - e - q ∈ U.baseChange ℝ → x ∈ V.baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun e‖ ≤ Real.exp p / monomialScale T α →
        (b.baseChange ℝ).equivFun q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] L,
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          x - E - Q ∈ (U ⊓ V).baseChange ℝ := by
  let B := (b.baseChange ℝ).equivFun
  let A : Matrix μ κ ℚ := fun i a => b.repr (v a) i
  let C : Matrix μ ν ℚ := fun i a => b.repr (w a) i
  have hU (x : ℝ ⊗[ℚ] L) : x ∈ U.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    rw [← real_span_rational_family U v hv, real_span_family_mem_iff_coordinates b v,
      real_column_span_mem_iff A]
  have hV (x : ℝ ⊗[ℚ] L) : x ∈ V.baseChange ℝ ↔
      B x ∈ LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    rw [← real_span_rational_family V w hw, real_span_family_mem_iff_coordinates b w,
      real_column_span_mem_iff C]
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_common_intersection_corrections A C hH hl
    (fun i a => hvH a i) (fun i a => hwH a i) hp hμ hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x e q hxU hxV he hq
  have hu : B x - B e - B q ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (A i a : ℝ))) := by
    simpa only [map_sub] using (hU (x - e - q)).mp hxU
  have hz : B x - 0 - 0 ∈
      LinearMap.range (Matrix.mulVecLin (fun i a => (C i a : ℝ))) := by
    simpa only [sub_zero] using (hV x).mp hxV
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα (B x) (B e) 0 (B q) 0 hu hz he
    (by simpa only [zero_sub, norm_neg] using he) hq (realDenominatorGrid_zero l)
  refine ⟨B.symm E, B.symm Q, ?_, ?_, ?_⟩
  · change ‖B (B.symm E)‖ ≤ _
    rw [B.apply_symm_apply]
    exact hE
  · change B (B.symm Q) ∈ _
    rw [B.apply_symm_apply]
    exact hQ
  · rw [realification_inf]
    constructor
    · apply (hU _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.1
    · apply (hV _).mpr
      rw [map_sub, map_sub, B.apply_symm_apply, B.apply_symm_apply]
      exact hmem.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_matrix_right_inverse {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (hDS : D * S = 1) :
    D.map (Rat.castHom ℝ) * S.map (Rat.castHom ℝ) = 1 := by
  rw [← Matrix.map_mul, hDS]
  exact Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℝ W]
  (U : Submodule ℚ V)

theorem realification_mkQ_ker : LinearMap.ker (U.mkQ.baseChange ℝ) = U.baseChange ℝ := by
  rw [← realification_ker, Submodule.ker_mkQ]

theorem realification_mkQ_surjective : Function.Surjective (U.mkQ.baseChange ℝ) :=
  LinearMap.lTensor_surjective ℝ U.mkQ_surjective

noncomputable def realQuotientEquiv :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] V) ⧸ U.baseChange ℝ) :=
  (U.mkQ.baseChange ℝ).quotKerEquivOfSurjective
    (realification_mkQ_surjective U) |>.symm |>.trans
      (Submodule.quotEquivOfEq _ _ (realification_mkQ_ker U))

theorem realQuotientEquiv_mk (x : ℝ ⊗[ℚ] V) :
    realQuotientEquiv U (U.mkQ.baseChange ℝ x) = (U.baseChange ℝ).mkQ x := by
  dsimp only [realQuotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

noncomputable def realTransportedQuotientEquiv (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (realQuotientEquiv U).trans (Submodule.Quotient.equiv _ _ E rfl)

theorem realTransportedQuotientEquiv_mk (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (x : ℝ ⊗[ℚ] V) :
    realTransportedQuotientEquiv U E (U.mkQ.baseChange ℝ x) =
      ((U.baseChange ℝ).map E.toLinearMap).mkQ (E x) := by
  change Submodule.Quotient.equiv _ _ E rfl (realQuotientEquiv U (U.mkQ.baseChange ℝ x)) = _
  rw [realQuotientEquiv_mk]
  rfl

noncomputable def realTransportedQuotientBasis {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) :
    Basis κ ℝ (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (b.baseChange ℝ).map (realTransportedQuotientEquiv U E)

theorem realTransportedQuotientBasis_repr_mk {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) (x : ℝ ⊗[ℚ] V) (i : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E x)) i =
      (b.baseChange ℝ).repr (U.mkQ.baseChange ℝ x) i := by
  rw [← realTransportedQuotientEquiv_mk]
  simp only [realTransportedQuotientBasis, Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem realTransportedQuotientBasis_repr_basis {ι κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (e : Basis ι ℚ V) (b : Basis κ ℚ (V ⧸ U)) (i : ι) (j : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E ((e.baseChange ℝ) i))) j =
      (b.repr (U.mkQ (e i)) j : ℝ) := by
  rw [realTransportedQuotientBasis_repr_mk]
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix NNReal

variable {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
  (D : Matrix κ ι ℚ) (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))

include hD

theorem rational_coordinate_map (x : V) :
    f.equivFun (q x) = D.map (Rat.castHom ℝ) *ᵥ e.equivFun x := by
  have h := LinearMap.toMatrix_mulVec_repr e f q x
  rw [hD] at h
  exact h.symm

theorem rational_coordinate_map_grid (l : ℕ) (x : V)
    (hx : e.equivFun x ∈ realDenominatorGrid l) :
    f.equivFun (q x) ∈ realDenominatorGrid (matrixDenominator D * l) := by
  rw [rational_coordinate_map e f q D hD]
  exact real_matrix_denominator_grid D l _ hx

theorem rational_coordinate_map_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0)
    (H : ℝ≥0) (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ H)
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * M / scale (r i) := by
  rw [rational_coordinate_map e f q D hD]
  exact weighted_matrix_mulVec_bound r c (D.map (Rat.castHom ℝ))
    (fun i j h => by change (D i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    H (fun i j => (rational_abs_real_le_numerator (D i j)).trans (hH i j))
    scale hscale hM (e.equivFun x) hx i

theorem rational_coordinate_map_weighted_exp (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 2)) * M / scale (r i) := by
  have h := rational_coordinate_map_weighted e f q D hD c r hblock
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩ hH scale hscale hM x hx i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hι a ha) hM)
    (hscale _).le)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

noncomputable def rationalCoordinateSection : (κ → ℝ) →ₗ[ℝ] V :=
  e.equivFun.symm.toLinearMap.comp (S.map (Rat.castHom ℝ)).mulVecLin

theorem rationalCoordinateSection_coordinates (y : κ → ℝ) :
    e.equivFun (rationalCoordinateSection e S y) = S.map (Rat.castHom ℝ) *ᵥ y :=
  e.equivFun.apply_symm_apply _

theorem rationalCoordinateSection_grid (l : ℕ) (y : κ → ℝ)
    (hy : y ∈ realDenominatorGrid l) :
    e.equivFun (rationalCoordinateSection e S y) ∈
      realDenominatorGrid (matrixDenominator S * l) := by
  rw [rationalCoordinateSection_coordinates]
  exact real_matrix_denominator_grid S l y hy

theorem rationalCoordinateSection_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (y : κ → ℝ) (hy : ∀ j, |y j| ≤ M / scale (r j)) (i : ι) :
    |e.equivFun (rationalCoordinateSection e S y) i| ≤
      Real.exp ((p + 2) ^ (a + 2)) * M / scale (c i) := by
  rw [rationalCoordinateSection_coordinates]
  have h := weighted_matrix_mulVec_bound c r (S.map (Rat.castHom ℝ))
    (fun i j h => by change (S i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩
    (fun i j => (rational_abs_real_le_numerator (S i j)).trans (hH i j))
    scale hscale hM y hy i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hκ a ha) hM)
    (hscale _).le)

theorem rationalCoordinateSection_rightInverse [DecidableEq ι] [DecidableEq κ]
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : Basis κ ℝ W)
    (q : V →ₗ[ℝ] W) (D : Matrix κ ι ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))
    (hDS : D * S = 1) (y : κ → ℝ) :
    q (rationalCoordinateSection e S y) = f.equivFun.symm y :=
  (quotient_basis_representative e f q (D.map (Rat.castHom ℝ)) (S.map (Rat.castHom ℝ))
    hD (real_matrix_right_inverse D S hDS) y).symm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V W E : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup E] [Module ℝ E]

theorem scalarExtension_basis_coordinates (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (q : V →ₗ[ℚ] W) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (q.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (q (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem scalarExtension_equiv_matrix [Fintype ι] [DecidableEq ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (b : Basis κ ℝ E)
    (q : V →ₗ[ℚ] W) (u : (ℝ ⊗[ℚ] W) ≃ₗ[ℝ] E)
    (hu : ∀ x i, b.repr (u x) i = (f.baseChange ℝ).repr x i) :
    LinearMap.toMatrix (e.baseChange ℝ) b (u.toLinearMap.comp (q.baseChange ℝ)) =
      (LinearMap.toMatrix e f q).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    hu, scalarExtension_basis_coordinates, Matrix.map_apply, Rat.coe_castHom]

theorem scalarExtension_grid_of_height_one [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W)
    (hq : ∀ i j, RationalHeightLE (f.repr (q (e j)) i) 1)
    (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun i => (e.baseChange ℝ).repr x i) ∈ realDenominatorGrid l) :
    (fun i => (f.baseChange ℝ).repr (q.baseChange ℝ x) i) ∈ realDenominatorGrid l := by
  classical
  let D := LinearMap.toMatrix e f q
  have hD : LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ) =
      D.map (Rat.castHom ℝ) := by
    ext i j
    simp only [D, LinearMap.toMatrix_apply, Matrix.map_apply,
      scalarExtension_basis_coordinates, Rat.coe_castHom]
  have hden : matrixDenominator D = 1 := by
    apply Nat.le_antisymm
    · have hb : ∀ i j, RationalHeightLE (D i j) 1 := by
        simpa only [D, LinearMap.toMatrix_apply] using hq
      simpa using matrixDenominator_le D hb
    · exact matrixDenominator_pos D
  have h := rational_coordinate_map_grid (e.baseChange ℝ) (f.baseChange ℝ)
    (q.baseChange ℝ) D hD l x hx
  simpa only [hden, one_mul, Basis.equivFun_apply] using h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem controlled_weighted_quotient_coordinates
    {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
    (c : ι → δ) (r : κ → δ) (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ)) (hDS : D * S = 1)
    (hDb : ∀ i j, r i ≠ c j → D i j = 0) (hSb : ∀ i j, c i ≠ r j → S i j = 0)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hDh : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hSh : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ (a + 4)) ∧ l ∣ m ∧
      (∀ x : V, e.equivFun x ∈ realDenominatorGrid l →
        f.equivFun (q x) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, y ∈ realDenominatorGrid l →
        e.equivFun (rationalCoordinateSection e S y) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, q (rationalCoordinateSection e S y) = f.equivFun.symm y) ∧
      ∀ (scale : δ → ℝ), (∀ d, 0 < scale d) → ∀ M : ℝ, 0 ≤ M →
        (∀ x : V, (∀ j, |e.equivFun x j| ≤ M / scale (c j)) →
          ∀ i, |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 4)) * M / scale (r i)) ∧
        (∀ y : κ → ℝ, (∀ j, |y j| ≤ M / scale (r j)) →
          ∀ i, |e.equivFun (rationalCoordinateSection e S y) i| ≤
            Real.exp ((p + 2) ^ (a + 4)) * M / scale (c i)) := by
  let m := matrixDenominator D * matrixDenominator S * l
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos D) (matrixDenominator_pos S)) hl
  have hmD : matrixDenominator D * l ∣ m := ⟨matrixDenominator S, by dsimp [m]; ring⟩
  have hmS : matrixDenominator S * l ∣ m := ⟨matrixDenominator D, by dsimp [m]; ring⟩
  refine ⟨m, hm, matrix_pair_denominator_le_exp_power D S l hp a ha hι hκ
    (fun i j => (hDh i j).2) (fun i j => (hSh i j).2) hlp,
    ⟨matrixDenominator D * matrixDenominator S, by dsimp [m]; ring⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos D) hl) hmD
      (rational_coordinate_map_grid e f q D hD l x hx)
  · intro y hy
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos S) hl) hmS
      (rationalCoordinateSection_grid e S l y hy)
  · exact rationalCoordinateSection_rightInverse e S f q D hD hDS
  · intro scale hscale M hM
    have hbudget : Real.exp ((p + 2) ^ (a + 2)) ≤ Real.exp ((p + 2) ^ (a + 4)) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
    constructor
    · intro x hx i
      have h := rational_coordinate_map_weighted_exp e f q D hD c r hDb hp hι a ha
        (fun i j => (hDh i j).1) scale hscale hM x hx i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)
    · intro y hy i
      have h := rationalCoordinateSection_weighted e S c r hSb hp hκ a ha
        (fun i j => (hSh i j).1) scale hscale hM y hy i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem linearMap_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W) (A : ℝ≥0)
    (hentries : ∀ i j, |f.repr (q (e j)) i| ≤ A) (x : V) :
    ‖f.equivFun (q x)‖ ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have h := abs_linearMap_le_basis_bound e ((f.coord i).comp q) A (hentries i) x
  simpa only [LinearMap.comp_apply, Basis.coord_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h

theorem scalarExtension_coordinate_norm_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x : ℝ ⊗[ℚ] V) :
    ‖(f.baseChange ℝ).equivFun (q.baseChange ℝ x)‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  have h := linearMap_coordinate_norm_le (e.baseChange ℝ) (f.baseChange ℝ) (q.baseChange ℝ)
    ⟨Real.exp p, Real.exp_nonneg p⟩ (fun i j => by
      rw [scalarExtension_basis_coordinates]
      exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp (hentries i j)).1) x
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    (Fintype.card ι : ℝ) * Real.exp p ≤ Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (hd.trans (by linarith [Real.add_one_le_exp p])) (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring

theorem scalarExtension_coordinate_dist_le {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (q : V →ₗ[ℚ] W) {p : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (f.repr (q (e j)) i) ≤ p) (x y : ℝ ⊗[ℚ] V) :
    dist ((f.baseChange ℝ).equivFun (q.baseChange ℝ x))
      ((f.baseChange ℝ).equivFun (q.baseChange ℝ y)) ≤
      Real.exp (2 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using scalarExtension_coordinate_norm_le e f q hd hentries (x - y)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]

theorem realified_linear_coordinate_matrix (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) :
    LinearMap.toMatrix (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ) =
      (LinearMap.toMatrix b c φ).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply,
    scalarExtension_basis_coordinates, Rat.coe_castHom]

theorem realified_linear_coordinate_norm (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖(c.baseChange ℝ).equivFun (φ.baseChange ℝ x)‖ ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [rational_coordinate_map (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ)]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hφ i j).abs_real_le) _

theorem realified_linear_coordinate_grid (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (l : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (c.baseChange ℝ).equivFun (φ.baseChange ℝ x) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  exact rational_coordinate_map_grid (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ) l x hx

theorem realified_section_correction_coordinate_norm [DecidableEq κ]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ}
    (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (x : ℝ ⊗[ℚ] L) (y : ℝ ⊗[ℚ] M) :
    ‖(b.baseChange ℝ).equivFun (x - S.baseChange ℝ (φ.baseChange ℝ x - y))‖ ≤
      ‖(b.baseChange ℝ).equivFun x‖ +
        (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
          ((((Fintype.card ι : ℝ) + 1) * (H + 1)) *
            ‖(b.baseChange ℝ).equivFun x‖ + ‖(c.baseChange ℝ).equivFun y‖) := by
  have hp := realified_linear_coordinate_norm b c φ hφ x
  have hs := realified_linear_coordinate_norm c b S hS (φ.baseChange ℝ x - y)
  have ht := norm_sub_le ((c.baseChange ℝ).equivFun (φ.baseChange ℝ x))
    ((c.baseChange ℝ).equivFun y)
  have hc := norm_sub_le ((b.baseChange ℝ).equivFun x)
    ((b.baseChange ℝ).equivFun (S.baseChange ℝ (φ.baseChange ℝ x - y)))
  rw [← map_sub] at ht hc
  have hdiff := ht.trans (add_le_add hp (le_refl ‖(c.baseChange ℝ).equivFun y‖))
  have hcorrect := hs.trans (mul_le_mul_of_nonneg_left hdiff
    (by positivity : 0 ≤ ((Fintype.card κ : ℝ) + 1) * (K + 1)))
  exact hc.trans (add_le_add (le_refl ‖(b.baseChange ℝ).equivFun x‖) hcorrect)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

theorem exists_bracketLiftMatrix_leftInverse [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H : ℕ} (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) :
    ∃ Q : Matrix κ μ ℚ, Q * bracketLiftMatrix b e = 1 ∧
      ∀ i j, RationalHeightLE (Q i j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let f : E →ₗ[ℚ] (μ → ℚ) := b.equivFun.toLinearMap.comp E.subtype
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (b.equivFun.injective h)
  have hli : LinearIndependent ℚ (bracketLiftMatrix b e).col :=
    e.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  exact exists_bounded_rational_left_inverse (bracketLiftMatrix b e) hli hH he

noncomputable def realSubspaceCoordinateMap (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ → ℝ) :=
  (Matrix.mulVecLin (fun i j => (Q i j : ℝ))).comp (b.baseChange ℝ).equivFun.toLinearMap

omit [Fintype κ] in
@[simp] theorem realSubspaceCoordinateMap_apply (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (x : ℝ ⊗[ℚ] L) :
    realSubspaceCoordinateMap b Q x =
      (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := rfl

theorem realSubspaceCoordinateMap_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1) (x : κ → ℝ) :
    realSubspaceCoordinateMap b Q (bracketSystemLift e x) = x := by
  classical
  rw [realSubspaceCoordinateMap_apply, bracketSystemLift_coordinates]
  change Q.map (Rat.castHom ℝ) *ᵥ ((bracketLiftMatrix b e).map (Rat.castHom ℝ) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, real_matrix_right_inverse Q (bracketLiftMatrix b e) hQ,
    Matrix.one_mulVec]

theorem lift_realSubspaceCoordinateMap [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    bracketSystemLift e (realSubspaceCoordinateMap b Q x) = x := by
  obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
  rw [realSubspaceCoordinateMap_lift b e Q hQ]

theorem realSubspaceCoordinateMap_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H) (x : ℝ ⊗[ℚ] L) :
    ‖realSubspaceCoordinateMap b Q x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realSubspaceCoordinateMap_apply]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hQ i j).abs_real_le) _

theorem realSubspaceCoordinateMap_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realSubspaceCoordinateMap b Q x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  rw [realSubspaceCoordinateMap_apply]
  exact real_matrix_denominator_grid Q l _ hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentSourceBounds
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

noncomputable def freeLieBoundedCoordinates : FreeLieAlgebra ℚ X →ₗ[ℚ] (BoundedFreeWord X s → ℚ) where
  toFun p w := (freeLieWordExpansion p).coeff w.val
  map_add' p q := by ext w; simp
  map_smul' c p := by ext w; simp

theorem freeLieBoundedCoordinates_eq_zero_iff (p : FreeLieAlgebra ℚ X) :
    freeLieBoundedCoordinates X s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  rw [freeLie_lowerCentralSeries_iff_low_coeff_zero]
  constructor
  · intro hp w hw
    exact congrFun hp ⟨w, hw⟩
  · intro hp
    ext w
    exact hp w.val w.property

namespace FreeNilpotentLieAlgebra

noncomputable def coordinates : FreeNilpotentLieAlgebra X s →ₗ[ℚ] (BoundedFreeWord X s → ℚ) :=
  (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule.liftQ
    (freeLieBoundedCoordinates X s)
    (fun p hp => (freeLieBoundedCoordinates_eq_zero_iff X s p).mpr hp)

theorem coordinates_injective : Function.Injective (coordinates X s) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := mk_surjective X s x
  obtain ⟨b, rfl⟩ := mk_surjective X s y
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (mk_eq_zero X s (a - b)).mpr
  apply (freeLieBoundedCoordinates_eq_zero_iff X s (a - b)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

instance finite [Fintype X] : Module.Finite ℚ (FreeNilpotentLieAlgebra X s) :=
  Module.Finite.of_injective (coordinates X s) (coordinates_injective X s)

theorem finrank_le [Fintype X] :
    Module.finrank ℚ (FreeNilpotentLieAlgebra X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have h := LinearMap.finrank_le_finrank_of_injective (coordinates_injective X s)
  calc
    _ ≤ Module.finrank ℚ (BoundedFreeWord X s → ℚ) := h
    _ = Fintype.card (BoundedFreeWord X s) := by simp
    _ ≤ _ := boundedFreeWord_card_le

end FreeNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3

namespace FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

noncomputable def expansion : FreeNilpotentLieAlgebra X s →ₗ[ℚ] WordPolynomial X :=
  (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule.liftQ
    ((wordTruncation s).comp freeLieWordExpansion.toLinearMap)
    (fun p hp => (wordTruncation_eq_zero_iff s _).mpr
      ((freeLie_lowerCentralSeries_iff_low_coeff_zero s p).mp hp))

end FreeNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_tree_eq_zero_of_length_gt (a : FreeMagma X) (ha : s < a.length) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = 0 := by
  apply (mk_eq_zero X s _).mpr
  apply (freeLie_lowerCentralSeries_iff_low_coeff_zero s _).mpr
  intro w hw
  rw [freeLieWordExpansion_tree]
  by_contra h
  have he := commutatorTree_homogeneous a w h
  omega

noncomputable def treeGenerators [Fintype X] : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem treeGenerators_span [Fintype X] :
    Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction
    (fun p => mk X s p ∈ Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)))
  · simpa only [map_zero] using (Submodule.zero_mem
      (Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))))
  · intro p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro c p hp
    rw [map_smul]
    exact Submodule.smul_mem _ c hp
  · intro a
    by_cases ha : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a ha, ha⟩, rfl⟩
    · rw [mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge ha)]
      exact Submodule.zero_mem _

theorem treeGenerators_card_le [Fintype X] :
    (treeGenerators X s).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans
    (finiteLieTrees_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_coordinate_height (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s x w) ((2 * (s + 1)) ^ s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  change RationalHeightLE ((freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val) _
  rw [freeLieWordExpansion_tree]
  exact (commutatorTree_coefficient_height s a w.val w.property).mono
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem treeGenerators_coordinate_integral (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    ∃ z : ℤ, (z : ℚ) = coordinates X s x w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_integral s a w.val w.property
  refine ⟨z, ?_, hbound.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
  change (z : ℚ) = (freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val
  rwa [freeLieWordExpansion_tree]

theorem exists_bounded_tree_basis :
    ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) ((2 * (s + 1)) ^ s)) ∧
      ∀ i w, ∃ z : ℤ, (z : ℚ) = coordinates X s (b i) w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))
  rw [treeGenerators_span, finrank_top] at hex
  obtain ⟨v, hv, hspan, hlin⟩ := hex
  let b := Basis.mk hlin (le_of_eq hspan.symm)
  have hb (i) : b i ∈ treeGenerators X s := by
    simpa only [b, Basis.mk_apply, Finset.mem_coe] using hv i
  exact ⟨b, hb, fun i w => treeGenerators_coordinate_height X s (b i) (hb i) w,
    fun i w => treeGenerators_coordinate_integral X s (b i) (hb i) w⟩

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable {X ι L : Type*} [Fintype X] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} (e : Basis ι ℚ L) (f : X → L)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem lift_treeGenerator_height
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H)
    (x : FreeNilpotentLieAlgebra X s) (hx : x ∈ treeGenerators X s) (i : ι) :
    RationalHeightLE (e.repr (lift f hnil x) i) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  rw [lift_mk, lift_lieTreeEval]
  exact finiteLieTrees_coordinate_height e f hc hf s a (Finset.mem_filter.mp ha).1 i

theorem lift_basis_matrix_height
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H) (i j) :
    RationalHeightLE (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  rw [LinearMap.toMatrix_apply]
  exact lift_treeGenerator_height e f hnil hc hf (b j) (hb j) i

theorem lift_basis_matrix_logHeight
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hf : ∀ x i, rationalLogHeight (e.repr (f x) i) ≤ p) (i j) :
    rationalLogHeight (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j) ≤
      (p + 3) ^ (6 * s + 2) := by
  have hraw := lift_basis_matrix_height e f hnil b hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun x i => rationalHeightLE_ceil_exp (hf x i)) i j
  apply rationalLogHeight_le_of_height hraw
  have h := lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module
attribute [local instance] LieRing.ofAssociativeRing

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_lie_or_zero {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) :
    ⁅x, y⁆ = 0 ∨ ⁅x, y⁆ ∈ treeGenerators X s := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  have he : ⁅mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a),
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) b)⁆ =
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) (a * b)) := (LieHom.map_lie _ _ _).symm
  rw [he]
  by_cases hab : (a * b).length ≤ s
  · right
    exact Finset.mem_image.mpr ⟨a * b, Finset.mem_filter.mpr
      ⟨mem_finiteLieTrees_of_length_le X (a * b) hab, hab⟩, rfl⟩
  · exact Or.inl (mk_tree_eq_zero_of_length_gt X s (a * b) (Nat.lt_of_not_ge hab))

theorem treeGenerators_lie_coordinate_height {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s ⁅x, y⁆ w) ((2 * (s + 1)) ^ s) := by
  rcases treeGenerators_lie_or_zero X s hx hy with hzero | hmem
  · rw [hzero, map_zero, Pi.zero_apply]
    have hH : 1 ≤ (2 * (s + 1)) ^ s := one_le_pow₀ (by omega)
    simpa only [RationalHeightLE, Rat.num_zero, Int.natAbs_zero, Rat.den_zero, Nat.zero_le,
      true_and] using hH
  · exact treeGenerators_coordinate_height X s _ hmem w

theorem exists_bounded_structure_basis :
    let n := Fintype.card (BoundedFreeWord X s)
    let d := finrank ℚ (FreeNilpotentLieAlgebra X s)
    let H := (2 * (s + 1)) ^ s
    ∃ b : Basis (Fin d) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) H) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        ((n + 1) * (rationalSolveHeight d H * H) ^ n) := by
  dsimp only
  obtain ⟨b, hb, hcoord, _⟩ := exists_bounded_tree_basis X s
  refine ⟨b, hb, hcoord, ?_⟩
  intro i j k
  have h := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (coordinates X s) (coordinates_injective X s)
    (show 1 ≤ (2 * (s + 1)) ^ s from one_le_pow₀ (by omega))
    (fun w l => by simpa only [Pi.basisFun_repr] using hcoord l w)
    ⁅b i, b j⁆ (fun w => by simpa only [Pi.basisFun_repr] using
      treeGenerators_lie_coordinate_height X s (hb i) (hb j) w) k
  simpa only [Fintype.card_fin, lieStructureConstants] using h

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3

open Module

theorem exists_bounded_free_nilpotent_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i w, rationalLogHeight (FreeNilpotentLieAlgebra.coordinates X s (b i) w) ≤ (p + C) ^ C) ∧
        ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.C H + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let A := ((s : ℝ) + 1) * (p + 1) ^ s
  let T := A + (H : ℝ) + p + 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAT : A ≤ T := by
    exact (le_add_of_nonneg_right (Nat.cast_nonneg H)).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hT : 0 ≤ T := hA.trans hAT
  have hHT : (H : ℝ) ≤ T := by
    exact (le_add_of_nonneg_left hA).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, A, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hBC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  have hsize : ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ A :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (1 : ℝ))) s) (by positivity)
  have hn : (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (boundedFreeWord_card_le (X := X) (s := s))
      _ ≤ _ := hsize
  have hd : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (FreeNilpotentLieAlgebra.finrank_le X s)
      _ ≤ _ := hsize
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  obtain ⟨b, hb, hcoord, hstructure⟩ := FreeNilpotentLieAlgebra.exists_bounded_structure_basis X s
  refine ⟨hd.trans (hAT.trans hTC), hn.trans (hAT.trans hTC), b, hb, ?_, ?_⟩
  · intro i w
    exact rationalLogHeight_le_of_height (hcoord i w)
      (hHexp.trans (Real.exp_le_exp.mpr hTC))
  · intro i j k
    have hcost := embedding_coordinate_height_budget
      (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
      hT (hn.trans hAT) (hd.trans hAT) hHexp hHexp
    exact rationalLogHeight_le_of_height (hstructure i j k)
      (hcost.trans (Real.exp_le_exp.mpr hBC))

end Erdos3

end

section

namespace Erdos3

open Module
attribute [local instance] LieRing.ofAssociativeRing

theorem exists_free_nilpotent_source_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr x i) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_nilpotent_model s
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + 2) ^ (3 ^ s) + Polynomial.C H + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let B := (p + a) ^ a
  let V := (p + 2) ^ (3 ^ s)
  let T := B + V + (H : ℝ) + 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hBT : B ≤ T := by
    exact (le_add_of_nonneg_right hV).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := by
    exact (le_add_of_nonneg_left hB).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hHT : (H : ℝ) ≤ T :=
    (le_add_of_nonneg_left (add_nonneg hB hV)).trans (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, B, V, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hPC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hd, hn, b, hb, _, hstructure⟩ := hmodel X p hp hX
  have hgen : ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ V := by
    calc
      _ ≤ ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) := by
        exact_mod_cast FreeNilpotentLieAlgebra.treeGenerators_card_le X s
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (2 : ℝ))) _
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  refine ⟨hd.trans (hBT.trans hTC), hgen.trans (hVT.trans hTC), b, hb,
    fun i j k => (hstructure i j k).trans (hBT.trans hTC), ?_⟩
  intro x hx i
  have hraw := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (FreeNilpotentLieAlgebra.coordinates X s) (FreeNilpotentLieAlgebra.coordinates_injective X s)
    (show 1 ≤ H from one_le_pow₀ (by omega))
    (fun w j => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s (b j) (hb j) w)
    x (fun w => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s x hx w) i
  have hcost := embedding_coordinate_height_budget
    (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
    hT (hn.trans hBT) (hd.trans hBT) hHexp hHexp
  apply rationalLogHeight_le_of_height hraw
  simpa only [Fintype.card_fin] using hcost.trans (Real.exp_le_exp.mpr hPC)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedLayerBounds
namespace OAI

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_lieTreeEval (a : FreeMagma X) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = lieTreeEval (of X s) a :=
  map_lieTreeEval (mk X s) (FreeLieAlgebra.of ℚ) a

noncomputable def weightedLayer (w : X → ℕ) (d : ℕ) : Submodule ℚ (FreeNilpotentLieAlgebra X s) :=
  weightedLieUpperSpan (of X s) w d

theorem weightedLayer_antitone (w : X → ℕ) : Antitone (weightedLayer X s w) :=
  weightedLieUpperSpan_antitone (of X s) w

theorem weightedLayer_lie_mem (w : X → ℕ) {d e : ℕ} {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ weightedLayer X s w d) (hy : y ∈ weightedLayer X s w e) :
    ⁅x, y⁆ ∈ weightedLayer X s w (d + e) :=
  weightedLieUpperSpan_lie_mem (of X s) w hx hy

theorem weightedLayer_eq_top (w : X → ℕ) (d : ℕ) (hd : ∀ a : FreeMagma X, d ≤ lieTreeWeight w a) :
    weightedLayer X s w d = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction (fun p => mk X s p ∈ weightedLayer X s w d)
  · simpa only [map_zero] using (weightedLayer X s w d).zero_mem
  · intro p q hp hq
    rw [map_add]
    exact (weightedLayer X s w d).add_mem hp hq
  · intro c p hp
    rw [map_smul]
    exact (weightedLayer X s w d).smul_mem c hp
  · intro a
    rw [mk_lieTreeEval]
    exact Submodule.subset_span ⟨a, hd a, rfl⟩

theorem weightedLayer_zero (w : X → ℕ) : weightedLayer X s w 0 = ⊤ :=
  weightedLayer_eq_top X s w 0 (fun _ => Nat.zero_le _)

theorem weightedLayer_one (w : X → ℕ) (hw : ∀ i, 0 < w i) : weightedLayer X s w 1 = ⊤ :=
  weightedLayer_eq_top X s w 1 (fun a => a.length_pos.trans_le (lieTree_length_le_weight w hw a))

noncomputable def weightedLayerIdeal (w : X → ℕ) (d : ℕ) : LieIdeal ℚ (FreeNilpotentLieAlgebra X s) :=
  { weightedLayer X s w d with
    lie_mem := by
      intro x y hy
      have hx : x ∈ weightedLayer X s w 0 := by rw [weightedLayer_zero]; exact Submodule.mem_top
      change ⁅x, y⁆ ∈ weightedLayer X s w d
      simpa only [Nat.zero_add] using weightedLayer_lie_mem X s w hx hy }

variable [Fintype X]

noncomputable def weightedLayerGenerators (w : X → ℕ) (d : ℕ) : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s ∧ d ≤ lieTreeWeight w a)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem weightedLayer_eq_span (w : X → ℕ) (d : ℕ) :
    weightedLayer X s w d = Submodule.span ℚ (weightedLayerGenerators X s w d : Set _) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, rfl⟩
    by_cases hlen : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a hlen, hlen, ha⟩, mk_lieTreeEval X s a⟩
    · rw [← mk_lieTreeEval, mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge hlen)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Submodule.subset_span ⟨a, (Finset.mem_filter.mp ha).2.2, (mk_lieTreeEval X s a).symm⟩

theorem weightedLayerGenerators_subset (w : X → ℕ) (d : ℕ) :
    weightedLayerGenerators X s w d ⊆ treeGenerators X s := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩, rfl⟩

theorem weightedLayerGenerators_card_le (w : X → ℕ) (d : ℕ) :
    (weightedLayerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) :=
  (Finset.card_le_card (weightedLayerGenerators_subset X s w d)).trans (treeGenerators_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module
attribute [local instance] LieRing.ofAssociativeRing

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ) (d : ℕ)

end Erdos3.FreeNilpotentLieAlgebra

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

def FreeWeightedNilpotentLieAlgebra (X : Type*) (s : ℕ) (w : X → ℕ) :=
  FreeNilpotentLieAlgebra X s ⧸ FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) (s : ℕ) (w : X → ℕ)

noncomputable instance instLieRing : LieRing (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieRing (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieAlgebra ℚ (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable def mk : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeWeightedNilpotentLieAlgebra X s w :=
  lieQuotientMap (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))

theorem mk_surjective : Function.Surjective (mk X s w) := lieQuotientMap_surjective _

theorem mk_eq_zero (x : FreeNilpotentLieAlgebra X s) :
    mk X s w x = 0 ↔ x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w (s + 1) :=
  lieQuotientMap_eq_zero _ x

noncomputable def of (x : X) : FreeWeightedNilpotentLieAlgebra X s w :=
  mk X s w (FreeNilpotentLieAlgebra.of X s x)

noncomputable def filtration (hw : ∀ i, 0 < w i) :
    NilpotentLieFiltration (FreeWeightedNilpotentLieAlgebra X s w) s where
  layer d := (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap
  antitone := fun _ _ h => Submodule.map_mono (FreeNilpotentLieAlgebra.weightedLayer_antitone X s w h)
  one_eq_top := by
    rw [FreeNilpotentLieAlgebra.weightedLayer_one X s w hw, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (mk_surjective X s w)
  lie_mem := by
    rintro d e x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, FreeNilpotentLieAlgebra.weightedLayer_lie_mem X s w ha hb, (mk X s w).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (mk_eq_zero X s w a).mpr ha

theorem of_mem_layer (hw : ∀ i, 0 < w i) (x : X) :
    of X s w x ∈ (filtration X s w hw).layer (w x) :=
  ⟨FreeNilpotentLieAlgebra.of X s x,
    weightedLieUpperSpan_leaf (FreeNilpotentLieAlgebra.of X s) w x, rfl⟩

instance finite [Fintype X] : Module.Finite ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  Module.Finite.of_surjective (mk X s w).toLinearMap (mk_surjective X s w)

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedEvaluationBounds
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

include hf in
theorem FreeNilpotentLieAlgebra.lift_weightedLayer {d : ℕ} {x : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w d) :
    FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot x ∈ F.layer d :=
  weightedLieUpperSpan_le_comap F (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w
    (fun i => by rw [FreeNilpotentLieAlgebra.lift_of]; exact hf i) d hx

namespace FreeWeightedNilpotentLieAlgebra

noncomputable def lift : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (fun x hx => by
      have h := FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf hx
      simpa only [F.terminal, Submodule.mem_bot] using h)

@[simp] theorem lift_of (x : X) : lift F w f hf (of X s w x) = f x :=
  FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot x

theorem lift_mem_layer (hw : ∀ i, 0 < w i) {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) : lift F w f hf x ∈ F.layer d := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf ha

theorem hom_ext {φ ψ : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s w x) = ψ (of X s w x)) : φ = ψ := by
  have heq : φ.comp (mk X s w) = ψ.comp (mk X s w) := FreeNilpotentLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s w x
  exact LieHom.congr_fun heq a

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedModelBounds
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def layerGenerators (d : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact (FreeNilpotentLieAlgebra.weightedLayerGenerators X s w d).image (mk X s w)

theorem layer_eq_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    (filtration X s w hw).layer d = Submodule.span ℚ (layerGenerators X s w d : Set _) := by
  classical
  change (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap = _
  rw [FreeNilpotentLieAlgebra.weightedLayer_eq_span, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

theorem layerGenerators_mem (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ layerGenerators X s w d) :
    x ∈ (filtration X s w hw).layer d := by
  rw [layer_eq_span]
  exact Submodule.subset_span hx

noncomputable def layerFamily (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : layerGenerators X s w d) : (filtration X s w hw).layer d :=
  ⟨x.val, layerGenerators_mem X s w hw d x.val x.property⟩

theorem layerFamily_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s w hw d)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s w d →
      FreeWeightedNilpotentLieAlgebra X s w) = (layerGenerators X s w d : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s w hw d).symm

theorem layerGenerators_card_le (d : ℕ) :
    (layerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact Finset.card_image_le.trans (FreeNilpotentLieAlgebra.weightedLayerGenerators_card_le X s w d)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_quotient (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (e.repr x i) ≤ (p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) ∧ (d : ℝ) ≤ (p + C) ^ C ∧
          ∃ b : Basis (Fin d) ℚ (FreeWeightedNilpotentLieAlgebra X s w),
            ∃ D : Matrix (Fin d) (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ,
              ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) (Fin d) ℚ,
                LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap = D ∧
                D * S = 1 ∧
                (∀ i j, rationalLogHeight (D i j) ≤ (p + C) ^ C) ∧
                (∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C) ∧
                ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_free_nilpotent_source_basis s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 51)
  refine ⟨C, hC, ?_⟩
  intro X _ w p hp hX
  classical
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : B + (B + 3) ^ 51 ≤ (p + C) ^ C := by
    simpa [Q, B, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (B + 3) ^ 51)).trans hsum
  have h51 : (B + 3) ^ 51 ≤ (p + C) ^ C := (le_add_of_nonneg_left hB).trans hsum
  have hsmall (k : ℕ) (hk : k ≤ 51) : (B + 1 + 2) ^ k ≤ (p + C) ^ C := by
    rw [show B + 1 + 2 = B + 3 by ring]
    exact (pow_le_pow_right₀ (by linarith only [hB]) hk).trans h51
  obtain ⟨hdim, hcount, e, he, hstructure, hgen⟩ := hsource X p hp hX
  let T := FreeNilpotentLieAlgebra.weightedLayerGenerators X s w (s + 1)
  let I := FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)
  let v : T → FreeNilpotentLieAlgebra X s := Subtype.val
  have hrange : Set.range v = (T : Set (FreeNilpotentLieAlgebra X s)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact (FreeNilpotentLieAlgebra.weightedLayer_eq_span X s w (s + 1)).symm
  have hcountT : (Fintype.card T : ℝ) ≤ B := by
    have hsub := Finset.card_le_card (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1))
    exact (Nat.cast_le.mpr (by simpa only [T, Fintype.card_coe] using hsub)).trans hcount
  obtain ⟨d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp B)
      (fun i j => rationalHeightLE_ceil_exp (hgen j.val
        (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1) j.property) i))
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (show 0 ≤ B + 1 by linarith only [hB])
      (by simpa only [Fintype.card_fin] using hdim.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (hcountT.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (ceil_exp_le_exp_add_one hB)
  have hd' : d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) := by simpa only [Fintype.card_fin] using hd
  refine ⟨hdim.trans hBC, e, he, fun x hx i => (hgen x hx i).trans hBC,
    d, hd', (Nat.cast_le.mpr hd').trans (hdim.trans hBC), b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hS i j)).trans (hsmall 45 (by omega))
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans (hsmall 51 (by omega))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ (p + C) ^ C ∧
      ∃ (b : Basis (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ
          (FreeWeightedNilpotentLieAlgebra X s w))
        (u : Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w)) → ℕ),
        Monotone u ∧ (∀ j, u j ≤ s + 1) ∧ IsCentralLieBasis b ∧
        (∀ d, (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).layer d =
          Submodule.span ℚ (b '' {j | d ≤ u j})) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
            (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ,
            LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hquotient⟩ := exists_bounded_free_weighted_quotient s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 2) ^ 4
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 2) ^ 4
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBP : B ≤ P := le_power_budget hB (by norm_num : 1 ≤ (4 : ℕ))
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans
      (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans
      (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, e, he, hgen, d, hd, hdimq, q, D, _, hmatrix, _, hD, _, hc⟩ :=
    hquotient X w p hp hX
  have hdimq' : (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ B := by
    simpa only [finrank_eq_card_basis q, Fintype.card_fin] using hdimq
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j : Fin d) :
      rationalLogHeight (q.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ P := by
    apply linearMap_coordinate_logHeight e q
      (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap hB
      (by simpa only [Fintype.card_fin] using hdim) ?_ x (hgen x hx)
    intro i j
    have h := hD j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let F := FreeWeightedNilpotentLieAlgebra.filtration X s w hw
  let v (i : Fin (s + 1)) := FreeWeightedNilpotentLieAlgebra.layerFamily X s w hw (i.val + 1)
  have hv (i : Fin (s + 1)) (x : FreeWeightedNilpotentLieAlgebra.layerGenerators X s w (i.val + 1))
      (j : Fin d) : rationalLogHeight (q.repr (v i x : FreeWeightedNilpotentLieAlgebra X s w) j) ≤ P := by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.property
    change rationalLogHeight (q.repr x.val j) ≤ P
    rw [← hxy]
    exact htree y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (i.val + 1) hy) j
  obtain ⟨b, u, hu, hub, hcentral, hlayer, _, hinverse, hstructure⟩ :=
    F.exists_bounded_sorted_adapted_basis_logHeight q v
      (fun i => FreeWeightedNilpotentLieAlgebra.layerFamily_span X s w hw (i.val + 1))
      hP (by simpa only [Fintype.card_fin] using hdimq.trans hBP) hv
      (fun i j k => (hc i j k).trans hBP)
  have htree' (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b (LinearMap.id) hQ
      (by simpa only [Fintype.card_fin] using hdimq.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ)
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (htree x hx i).trans hPQ) j
  let A := LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree' (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
      (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq'.trans
      (hBR.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq'.trans (hBR.trans hRC), b, u, hu, hub, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx j => (htree' x hx j).trans hRC, e, he, hdim.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 by ring] using hSC

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankAdaptedBasis
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis ι ℚ L)

theorem exists_bounded_rank_adapted_basis
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤) {H : ℕ}
    (hv : ∀ i j a k, RationalHeightLE (e.repr (v i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (e.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c := by
  let := e.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => F.rankFlag n.val
  have hP : Antitone P := fun _ _ h => F.rankFlag_antitone h
  have hSP (n : Fin (N + 1)) : Submodule.span ℚ (S ∩ (P n : Set L)) = P n := by
    by_cases hn : n.val < (s + 1) * (s + 1)
    · obtain ⟨hi, hj⟩ := rankFlag_decode_lt hn
      let i : Fin (s + 1) := ⟨n.val / (s + 1), Nat.lt_succ_of_le hi⟩
      let j : Fin (s + 1) := ⟨n.val % (s + 1), Nat.lt_succ_of_le hj⟩
      exact span_inter_eq_of_spanning_family _ (v i j) (hspan i j) S (hv i j)
    · have heq : n.val = (s + 1) * (s + 1) := by dsimp only [N] at n; omega
      change Submodule.span ℚ (S ∩ (F.rankFlag n.val : Set L)) = F.rankFlag n.val
      rw [heq, F.rankFlag_terminal]
      exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  refine ⟨b, centralLieBasis_of_finite_flag F.rankFlag b w F.rankFlag_zero F.rankFlag_terminal
    (fun _ {_ _} hy => F.rankFlag_lie_mem hy) hw hflag, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := F.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

theorem exists_rank_adapted_basis_logHeight
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j a k, rationalLogHeight (e.repr (v i j a : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, hcentral, hb, hlayer⟩ := F.exists_bounded_rank_adapted_basis e v hspan
    (fun i j a k => rationalHeightLE_ceil_exp (hv i j a k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, hcentral, hlayer, fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AdaptedBasisNilmanifold
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def adaptedLayerBasis (j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer j))) ℚ (F.layer j) := by
  classical
  let c := supportedSubmoduleBasis b (F.layer j) {i | j ≤ w i} (hlayers j)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem adaptedLayerBasis_height (j : ℕ) (i : Fin (finrank ℚ (F.layer j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.adaptedLayerBasis b w hlayers j i) k) 1 := by
  classical
  unfold adaptedLayerBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ k

noncomputable def ofAdaptedBasis (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d where
  filtration := F
  basis := b
  layerBasis i := F.adaptedLayerBasis b w hlayers (i.val + 1)
  lattice := Γ
  grid := N
  grid_pos := hN
  inner_grid := hin
  outer_grid := hout

theorem ofAdaptedBasis_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  refine ⟨hd, hNp, hc, ?_⟩
  intro i j k
  exact rationalLogHeight_le_of_height (F.adaptedLayerBasis_height b w hlayers _ j k)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

noncomputable def quotientFinBasis :
    Basis (Fin (Fintype.card {i // i ∉ S})) ℚ (L ⧸ I) :=
  (supportedQuotientBasis b I.toSubmodule S hspan).reindex (Fintype.equivFin _)

noncomputable def quotientFinWeight : Fin (Fintype.card {i // i ∉ S}) → ℕ :=
  fun i => w ((Fintype.equivFin {i // i ∉ S}).symm i)

include hlayers in
theorem quotientFinBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (quotientFinBasis b I S hspan '' {i | j ≤ quotientFinWeight w S i}) := by
  rw [F.supportedQuotientBasis_layers b w hlayers I hI S hspan]
  exact (basis_reindex_span_weights (L := L ⧸ I)
    (supportedQuotientBasis b I.toSubmodule S hspan) (Fintype.equivFin _)
    (fun i => w i) j).symm

noncomputable def coordinateQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ I) t (Fintype.card {i // i ∉ S}) :=
  (F.quotientLie I hI).ofAdaptedBasis (quotientFinBasis b I S hspan)
    (quotientFinWeight w S) (F.quotientFinBasis_layers b w hlayers I hI S hspan)
    (Γ.map (F.quotientStepHom I hI)) N hN
    (bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_inner_grid_supported b I hI S hspan Γ hin))
    (bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_outer_grid_supported b I hI S hspan Γ hout))

theorem coordinateQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.coordinateQuotientModel b w hlayers I hI S hspan Γ N hN hin hout).GeometryComplexityLE p := by
  apply (F.quotientLie I hI).ofAdaptedBasis_geometry _ _ _ _ _ _ _ _ hp
  · exact (Nat.cast_le.mpr (Fintype.card_subtype_le (fun i => i ∉ S))).trans hd
  · exact hNp
  · intro i j k
    simp only [quotientFinBasis, lieStructureConstants_reindex, supportedQuotientBasis_lieStructure]
    exact hc _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SourceLatticeCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def withLattice {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d :=
  { D with lattice := Λ, grid := N, grid_pos := hN, inner_grid := hin, outer_grid := hout }

theorem withLattice_geometry {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p q : ℝ} (hD : D.GeometryComplexityLE p) (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.withLattice Λ N hN hin hout).GeometryComplexityLE q :=
  ⟨hD.1.trans hpq, hNb, fun i j k => (hD.2.2.1 i j k).trans hpq,
    fun i j k => (hD.2.2.2 i j k).trans hpq⟩

theorem exists_native_image_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          (E.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ.map realificationHom ⊓
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
            (D.lattice.map realificationHom).map
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨c, _, hbudget⟩ := exists_image_cover_reconstruction_budget (bchIntegralDenominatorBound s) 0
  let P : Polynomial ℕ := Polynomial.X + 1 + (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ
  let t := p + 1
  have ht : 0 ≤ t := add_nonneg hp zero_le_one
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hdt : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have het : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  have hlt : (D.grid : ℝ) ≤ Real.exp t := hD.2.1.trans (Real.exp_le_exp.mpr hpt)
  have hmt : (E.grid : ℝ) ≤ Real.exp t := hE.2.1.trans (Real.exp_le_exp.mpr hpt)
  obtain ⟨A, Λ, hA, hAb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, hcover⟩ :=
    E.filtration.exists_image_lattice_cover D.basis E.basis φ D.lattice E.lattice
      D.grid E.grid H D.grid_pos E.grid_pos hH D.inner_grid E.inner_grid E.outer_grid
      (fun i j => rationalHeightLE_ceil_exp (hφ i j))
      (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  let a := imageLatticeLogBudget (bchIntegralDenominatorBound s) t
  have ha : 0 ≤ a := imageLatticeLogBudget_nonneg _ ht
  have hAt : (A : ℝ) ≤ Real.exp a :=
    (Nat.cast_le.mpr hAb).trans (imageLatticeBound_le_exp _ _ _ H D.grid E.grid ht hdt het hHt hlt hmt)
  have hprod : ((E.grid * A : ℕ) : ℝ) ≤ Real.exp (t + a) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hmt hAt (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hN : 0 < (E.grid * A) * E.grid := Nat.mul_pos (Nat.mul_pos E.grid_pos hA) E.grid_pos
  have hNg : (((E.grid * A) * E.grid : ℕ) : ℝ) ≤ Real.exp (2 * t + a) := by
    calc
      _ = ((E.grid * A : ℕ) : ℝ) * (E.grid : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp (t + a) * Real.exp t := mul_le_mul hprod hmt (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hidx : (Λ.relIndex E.lattice : ℝ) ≤ Real.exp (t * (t + a)) := by
    apply (Nat.cast_le.mpr hindex).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right het (add_nonneg ht ha)
  obtain ⟨hq, hi, _⟩ := hbudget t ht
  have hsum : t + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hfinal p hp
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg _)) _)).trans hsum
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hi.trans hcC)), (E.grid * A) * E.grid, hN, hin, hout, ?_, hcover⟩
  exact E.withLattice_geometry Λ _ hN hin hout hE (hpt.trans htC)
    (hNg.trans (Real.exp_le_exp.mpr (hq.trans hcC)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group)

noncomputable def lowerCoverLattice : Subgroup D.filtration.Group :=
  Λ.map (changeStep (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot
    D.filtration.lowerCentralSeries_eq_bot).toMonoidHom

theorem lowerCoverLattice_coordinates :
    bchSubgroupCoordinates D.basis (D.lowerCoverLattice hst Λ) =
      bchSubgroupCoordinates D.basis Λ :=
  bchSubgroupCoordinates_changeStep _ _ D.basis Λ

theorem lowerCoverLattice_forward :
    D.lowerCoverLattice hst Λ ≤ Λ.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hy

theorem lowerCoverLattice_le (hΛ : Λ ≤ (D.raiseStep hst).lattice) :
    D.lowerCoverLattice hst Λ ≤ D.lattice := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact D.raiseStep_lattice_back hst (hΛ hy)

variable (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCover : RationalFilteredNilmanifold L s d :=
  D.withLattice (D.lowerCoverLattice hst Λ) N hN
    (by rw [D.lowerCoverLattice_coordinates]; exact hin)
    (by rw [D.lowerCoverLattice_coordinates]; exact hout)

theorem loweredCover_geometry {p q : ℝ} (hD : D.GeometryComplexityLE p)
    (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.loweredCover hst Λ N hN hin hout).GeometryComplexityLE q :=
  D.withLattice_geometry _ _ _ _ _ hD hpq hNb

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix

theorem bchSubgroupCoordinates_comap_ofSteps
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup M t hM)) :
    bchSubgroupCoordinates b (Γ.comap (mapOfSteps (hL := hL) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup M t hM) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup M t hM) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

namespace RationalFilteredNilmanifold

theorem exists_native_source_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 2 * R ^ 2 + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := E.grid * matrixDenominator A
  let Λ₀ := E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN₀ : 0 < N₀ := Nat.mul_pos E.grid_pos (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis Λ₀ := by
    rw [bchSubgroupCoordinates_comap_ofSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) D.basis E.basis φ E.lattice]
    intro x hx
    exact E.inner_grid (matrix_mulVec_fine_grid A E.grid hx)
  let r := p + (p + 2) ^ 3
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp.trans hpr
  have hN₀b : (N₀ : ℝ) ≤ Real.exp r := by
    rw [show (N₀ : ℝ) = (E.grid : ℝ) * matrixDenominator A by exact Nat.cast_mul _ _]
    exact (mul_le_mul hE.2.1 hAb (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice Λ₀
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hr
      (by simpa only [Fintype.card_fin] using hD.1.trans hpr)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpr)) hN₀b
  have htotal : r + 2 * r ^ 2 + (r + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by nlinarith [sq_nonneg r, sq_nonneg (r + 2)]
  have hiC : 2 * r ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hgC : (r + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg r]
  exact ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hiC),
    N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpr.trans hrC)
      (hNb.trans (Real.exp_le_exp.mpr hgC)), htarget⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include hφ in

theorem realificationLieHom_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : ℝ ⊗[ℚ] M) (hy : y ∈ G.realification.layer j) :
    ∃ x ∈ F.realification.layer j, realificationLieHom φ x = y := by
  have hmap : (F.layer j).map φ.toLinearMap = G.layer j := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hφ j x hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj j y hy
      exact ⟨x, hx, hxy⟩
  have hreal : ((F.layer j).baseChange ℝ).map (φ.toLinearMap.baseChange ℝ) =
      (G.layer j).baseChange ℝ := by
    rw [← realification_map, hmap]
  change y ∈ (G.layer j).baseChange ℝ at hy
  rw [← hreal] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3
open Module
open scoped TensorProduct BigOperators

theorem realification_fractional_integer_split {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    ∃ (e : ℝ ⊗[ℚ] V) (r : V),
      x = e + (1 : ℝ) ⊗ₜ[ℚ] r ∧
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      ∀ i, ∃ z : ℤ, b.repr r i = z := by
  let B := b.baseChange ℝ
  let r := b.equivFun.symm (fun i => (⌊B.repr x i⌋ : ℚ))
  let e := x - (1 : ℝ) ⊗ₜ[ℚ] r
  have hr (i) : b.repr r i = (⌊B.repr x i⌋ : ℚ) := by
    change b.equivFun (b.equivFun.symm _) i = _
    rw [LinearEquiv.apply_symm_apply]
  have he (i) : B.repr e i = Int.fract (B.repr x i) := by
    change B.repr (x - (1 : ℝ) ⊗ₜ[ℚ] r) i = _
    rw [map_sub, Finsupp.sub_apply, Module.Basis.baseChange_repr_tmul (S := ℝ), hr]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one]
    rfl
  refine ⟨e, r, by dsimp [e]; abel, ?_, fun i => ⟨⌊B.repr x i⌋, hr i⟩⟩
  intro i
  change 0 ≤ B.repr e i ∧ B.repr e i < 1
  rw [he]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem exists_fractional_integer_kernel_correction
    {ι L M : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    [AddCommGroup M] [Module ℚ M] (φ : L →ₗ[ℚ] M)
    (H : Submodule ℚ L) (b : Basis ι ℚ (LinearMap.ker φ))
    (x : ℝ ⊗[ℚ] L) (hx : φ.baseChange ℝ x ∈ (H.map φ).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ) (r : LinearMap.ker φ),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      x - (LinearMap.ker φ).subtype.baseChange ℝ e -
        (1 : ℝ) ⊗ₜ[ℚ] (r : L) ∈ H.baseChange ℝ := by
  rw [realification_map] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hk : x - y ∈ (LinearMap.ker φ).baseChange ℝ := by
    rw [realification_ker, LinearMap.mem_ker, map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := hk
  obtain ⟨e, r, heq, he, hr⟩ := realification_fractional_integer_split b k
  refine ⟨e, r, he, hr, ?_⟩
  have heq' := congrArg ((LinearMap.ker φ).subtype.baseChange ℝ) heq
  rw [hk, map_add, LinearMap.baseChange_tmul] at heq'
  change x - y = (LinearMap.ker φ).subtype.baseChange ℝ e + (1 : ℝ) ⊗ₜ[ℚ] (r : L) at heq'
  have hfinal : x - (LinearMap.ker φ).subtype.baseChange ℝ e -
      (1 : ℝ) ⊗ₜ[ℚ] (r : L) = y := by
    rw [show x = (x - y) + y by abel, heq']
    abel
  rwa [hfinal]

namespace NilpotentLieFiltration

variable {ι L M : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (b : Basis ι ℚ (LinearMap.ker φ.toLinearMap))

include hH

theorem exists_kernel_constant_factors (g : F.realification.Group)
    (hg : realificationLieHom φ g.coord ∈ (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap) (r : LinearMap.ker φ.toLinearMap),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      let kE : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e⟩
      let kR : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (r : L)⟩
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kE = 1 ∧
      NilpotentLieBCHGroup.realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ kR = 1 ∧
      (kE⁻¹ * g * kR⁻¹).coord ∈ H.baseChange ℝ := by
  obtain ⟨e, r, he, hr, hlin⟩ :=
    exists_fractional_integer_kernel_correction φ.toLinearMap H b g.coord hg
  refine ⟨e, r, he, hr, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ
      ((LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e) = 0
    have hm : (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e ∈
        (LinearMap.ker φ.toLinearMap).baseChange ℝ := ⟨e, rfl⟩
    rwa [realification_ker, LinearMap.mem_ker] at hm
  · apply NilpotentLieBCHGroup.ext
    change φ.toLinearMap.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] (r : L)) = 0
    rw [LinearMap.baseChange_tmul, show φ.toLinearMap (r : L) = 0 from r.property,
      TensorProduct.tmul_zero]
  · let a := (LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ e
    let c := (1 : ℝ) ⊗ₜ[ℚ] (r : L)
    have hbch := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord (-c)
      (by rw [F.realification.one_eq_top]; trivial)
      (by rw [F.realification.one_eq_top]; trivial)
    have hm : lieBCH s (lieBCH s (-a) g.coord) (-c) - (-a + g.coord + -c) ∈
        H.baseChange ℝ := Submodule.baseChange_mono ℝ hH hbch
    have hlin' : -a + g.coord + -c ∈ H.baseChange ℝ := by
      convert hlin using 1
      dsimp [a, c]
      abel
    have hh := (H.baseChange ℝ).add_mem hm hlin'
    simpa only [sub_add_cancel, NilpotentLieBCHGroup.coord_mul,
      NilpotentLieBCHGroup.coord_inv] using hh

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

section Linear

variable {ι κ V L : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup L] [Module ℚ L]

theorem scalarExtension_coordinate_sum (b : Basis ι ℚ L) (bk : Basis κ ℚ V)
    (f : V →ₗ[ℚ] L) (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (f.baseChange ℝ x) i =
      ∑ j, (bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ) := by
  classical
  conv_lhs => rw [← (bk.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, scalarExtension_basis_coordinates]

theorem scalarExtension_fractional_coordinates_bound
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℝ)
    (hentries : ∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H)
    (x : ℝ ⊗[ℚ] V)
    (hx : ∀ j, 0 ≤ (bk.baseChange ℝ).repr x j ∧ (bk.baseChange ℝ).repr x j < 1)
    (i : ι) :
    |(b.baseChange ℝ).repr (f.baseChange ℝ x) i| ≤ (Fintype.card κ : ℝ) * H := by
  rw [scalarExtension_coordinate_sum b bk f x i]
  calc
    _ ≤ ∑ j, |(bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hx j).1]
      exact (mul_le_mul (hx j).2.le (hentries i j) (abs_nonneg _) (by norm_num)).trans
        (by rw [one_mul])
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integral_basis_image_denominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => b.repr (f r) i) ∈ denominatorGrid q := by
  classical
  choose z hz using hr
  choose a ha using hentries
  refine ⟨fun i => ∑ j, z j * a j i, ?_⟩
  intro i
  change (q : ℚ) * b.repr (f r) i = ((∑ j, z j * a j i : ℤ) : ℚ)
  conv_lhs => rw [← bk.sum_repr r]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (q : ℚ) * b.repr (f (bk j)) i = (a j i : ℚ) := ha j i
  rw [hz, ← hj]
  ring

theorem integral_basis_image_realDenominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] f r) i) ∈ realDenominatorGrid q := by
  have h := integral_basis_image_denominatorGrid b bk f q hentries r hr
  have hreal := (real_cast_mem_denominatorGrid_iff q (fun i => b.repr (f r) i)).mpr h
  simpa only [Basis.baseChange_repr_tmul (S := ℝ), Rat.smul_def, mul_one] using hreal

theorem exists_basis_image_bounds_of_height [Fintype ι]
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℕ) (hentries : ∀ i j, RationalHeightLE (b.repr (f (bk j)) i) H) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card ι * Fintype.card κ) ∧
      (∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H) ∧
      ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (f (bk j)) i
  refine ⟨matrixDenominator A, matrixDenominator_pos A,
    matrixDenominator_le A hentries, fun i j => (hentries i j).abs_real_le, ?_⟩
  intro j
  refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
  exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm

end Linear

namespace NilpotentLieFiltration

variable {ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}

end NilpotentLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolRepresentativeTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ M : Type*} [Fintype ι] [Fintype κ] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration M s) (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : Basis κ ℚ M)

omit [Fintype κ] in
theorem realSymbolRepresentative_slow_original_coordinates (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ j, 0 < T j) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (E : F.RealPolynomialSymbolGroup w) (hE : F.SymbolSlowBound b ω hF w T (Real.exp p) E)
    (α : σ →₀ ℕ) (i : κ) :
    |(e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w E.coord) α) i| ≤
      Real.exp ((p + 3) ^ 2) / monomialScale T α := by
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hdim' : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hbound : (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p ≤ Real.exp ((p + 3) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => F.realSymbolRepresentative_slow_coefficients b ω hF w T hT
          (Real.exp_pos p).le E hE α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

theorem realSymbolRepresentative_original_grid (w : σ → ℕ) (l : ℕ)
    (R : F.RealPolynomialSymbolGroup w) (hR : F.SymbolRationalGrid b ω hF w l R)
    (α : σ →₀ ℕ) :
    (fun i => (e.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hF w R.coord) α) i)
      ∈ realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  obtain ⟨z, hz⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l R hR
  apply real_basis_coordinates_grid b e l
  exact ⟨fun j => z (α, j), funext (fun j => congrFun hz (α, j))⟩

theorem original_coordinate_denominator_bound {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (l : ℕ) (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator (fun i j => e.repr (b j) i) * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3 + p) := by
  have hD : (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
    intro i j
    exact ((rationalLogHeight_le_iff _ _).mp (hentries j i)).2.trans
      (Real.exp_le_exp.mpr (by simp))
  rw [Nat.cast_mul]
  exact (mul_le_mul hD hl (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialBasisTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (e : Basis κ ℚ L)
  (w : σ → ℕ)

theorem polynomialRationalGrid_change_basis (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid e w
      (matrixDenominator (fun i j => e.repr (b j) i) * l) g := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hgrid (α : σ →₀ ℕ) :
      (fun i => (e.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i) ∈
        realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
    apply real_basis_coordinates_grid b e l
    exact ⟨fun j => z (α, j), funext fun j => congrFun hz (α, j)⟩
  choose a ha using hgrid
  exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

omit [Fintype κ] in
theorem polynomialSlowBound_change_basis_exp (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T (Real.exp p) g) :
    F.PolynomialSlowBound e w T (Real.exp ((p + 3) ^ 2)) g := by
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hdim' : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hbound : (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p ≤ Real.exp ((p + 3) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  intro α i
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => hg α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

theorem loweringAt_patchValue {X : Type*} {d : ℕ} {w : Fin d → ℕ}
    (A : PolynomialSlots X d w) (hw : Monotone w) (Φ : PatchKernel d) (t : X → ℝ) :
    ((A.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ) = (A.slots t).patchValue Φ := by
  unfold TriangularSlots.patchValue
  apply tsum_congr
  intro b
  congr 1
  rw [shearTransformedSlots_residual]
  exact A.top_factorization_residual t b

theorem exists_fixed_kernel_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    {δ : ℝ} (_hδ : 0 < δ)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue Φ))
    (herror : Φ.lip * patchTopNetError d s N M ≤ δ / 2) :
    ∃ (B : PolynomialSlots X d w) (retained : Finset Ω),
      (∀ i, realPolynomialMass (B.center i) ≤ M) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / 2 ≤ (localLaw a).mean (fun t => score a t *
        (B.shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) := by
  obtain ⟨code, rep, hnet⟩ := exists_shear_observable_net A hw hpos hs Φ hM hA hN hsmall
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  refine ⟨A (rep i), productive.filter (fun a => code a = i), hA _, Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤
        outer.mass productive / Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) := by
      apply div_le_div_of_nonneg_left (outer.mass_nonneg productive)
      · exact_mod_cast Fintype.card_pos (α := PatchTopCoefficientIndex d s → Fin (N + 1))
      · exact_mod_cast patchTopCoefficientCode_card d s N
    apply hcard.trans
    convert hi using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    obtain ⟨ha, hcode⟩ := Finset.mem_filter.mp ha
    have hclose (t : T) :
        dist (((A a).slots (point a t)).patchValue Φ)
          (((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) ≤
            Φ.lip * patchTopNetError d s N M := by
      have h := hnet a ((A a).loweringAt (point a t))
      rw [hcode, loweringAt_patchValue] at h
      exact h
    let u := fun t => score a t * ((A a).slots (point a t)).patchValue Φ
    let v := fun t => score a t *
      ((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ
    have he : |(localLaw a).mean (fun t => u t - v t)| ≤ Φ.lip * patchTopNetError d s N M := by
      apply (localLaw a).abs_mean_le_on_support
      intro t _
      change |score a t * _ - score a t * _| ≤ _
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore a t) (abs_nonneg _)).trans
        (by simpa only [one_mul, Real.dist_eq] using hclose t)
    rw [(localLaw a).mean_sub] at he
    have hp := hpositive a ha
    change δ ≤ (localLaw a).mean u at hp
    change δ / 2 ≤ (localLaw a).mean v
    linarith [le_abs_self ((localLaw a).mean u - (localLaw a).mean v)]

end PolynomialSlots
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem fixed_weight_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N J : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    {M L δ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hΦ : ∀ a, ((Φ a).lip : ℝ) ≤ L)
    (hN : 8 ≤ N) (hkernel : 2 * L * (patchKernelGridRadius N : ℝ) ≤ δ / 2)
    (hJ : 0 < J) (hsmall : patchTopNetError d s J (M + 1 / 4) < 1 / 4)
    (hhomogeneous : ((2 * ((N + 1) ^ d : ℕ) + 1 : ℝ≥0) / patchKernelGridRadius N : ℝ≥0) *
      patchTopNetError d s J (M + 1 / 4) ≤ δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d))
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) :
    ∃ (i : Fin d → Fin (N + 1)) (B : PolynomialSlots X d w)
      (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
      (∀ j, realPolynomialMass (B.center j) ≤ M + 1 / 4) ∧
      retained ⊆ productive ∧
      outer.mass productive /
        (((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
        (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue
            (gridPatchKernel d N hN i)) := by
  let P : Ω → PolynomialPatch X s d := fun a =>
    ⟨w, hpos, hs, hw, A a, Φ a⟩
  have hk (a) : 2 * ((Φ a).lip : ℝ) * (patchKernelGridRadius N : ℝ) ≤ δ / 2 :=
    (mul_le_mul (mul_le_mul_of_nonneg_left (hΦ a) (by norm_num))
      le_rfl (patchKernelGridRadius N).coe_nonneg
      (mul_nonneg (by norm_num) hL)).trans hkernel
  have hchoose (a : Ω) : ∃ i : Fin d → Fin (N + 1), a ∈ productive →
      δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤ (localLaw a).mean (fun t => score a t *
        ((P a).gridKernelReplacement hN i).value (point a t)) := by
    by_cases ha : a ∈ productive
    · obtain ⟨i, hi⟩ := (P a).exists_gridKernelReplacement_score hN (localLaw a) (point a)
        (score a) (hscore a) hδ (hpositive a ha) (hk a)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨fun _ => 0, fun h => (ha h).elim⟩
  choose code hcode using hchoose
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  let Q := productive.filter (fun a => code a = i)
  let A' : Ω → PolynomialSlots X d w := fun a => ((P a).gridKernelReplacement hN i).form
  have hA' (a) (j) : realPolynomialMass ((A' a).center j) ≤ M + 1 / 4 := by
    change realPolynomialMass ((A a).center j + MvPolynomial.C (uniformBoxGrid (1 / 4) N i j)) ≤ _
    apply (realPolynomialMass_add_le _ _).trans
    rw [realPolynomialMass_C]
    exact add_le_add (hA a j) (uniformBoxGrid_mem (by norm_num) (by omega : 0 < N) i j)
  have hδ' : 0 < δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hpositive' (a) (ha : a ∈ Q) : δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      (localLaw a).mean (fun t => score a t * ((A' a).slots (point a t)).patchValue
        (gridPatchKernel d N hN i)) := by
    obtain ⟨ha, hai⟩ := Finset.mem_filter.mp ha
    have h := hcode a ha
    rw [hai] at h
    exact h
  have he : (gridPatchKernel d N hN i).lip * patchTopNetError d s J (M + 1 / 4) ≤
      (δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d)) / 2 := by
    simp only [gridPatchKernel]
    convert hhomogeneous using 1; ring
  obtain ⟨B, retained, hB, hretained, hmass, hlocal⟩ :=
    PolynomialSlots.exists_fixed_kernel_patch_function A' hw hpos hs (gridPatchKernel d N hN i)
      (by linarith : 0 ≤ M + 1 / 4) hA' hJ hsmall outer Q localLaw point score hscore hδ' hpositive' he
  refine ⟨i, B, A', retained, hB, fun a ha => (Finset.mem_filter.mp (hretained ha)).1, ?_, ?_⟩
  · have hi' : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ d ≤ outer.mass Q := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hi
      convert hi using 1; try rfl
      congr 1
      ext a
      simp only [Q, Finset.mem_filter]
    apply le_trans _ hmass
    rw [← div_div]
    exact div_le_div_of_nonneg_right hi' (by positivity)
  · intro a ha
    convert hlocal a ha using 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MassBoundedShearBudget
namespace OAI

section

namespace Erdos3

theorem exists_mass_bounded_shear_parameter_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d D : ℕ) (M p : ℝ),
      0 ≤ p → 0 ≤ M → M ≤ p → (d : ℝ) ≤ p → D ≤ d * (d + 1) ^ s →
      ∃ t : ℝ, 0 ≤ t ∧
        (D + s.factorial + 2 * s + 1 : ℕ) ≤ t ∧
        t + shearKernelLogBudget s d M p + shearActionLogBudget s d M + (t + a) ^ a + 4 ≤
          (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := 1 + X + Polynomial.C (s.factorial + 2 * s + 1) + X * (X + 1) ^ s
  let K := Q + Q + Q + Polynomial.C s +
    (Polynomial.C s * Q * Q + 1) * (Polynomial.C s * (Q + 1))
  let T := Polynomial.C s + Polynomial.C s *
    (Q * (Polynomial.C (s + 1) * (Q + 1) ^ s) * Polynomial.C s) +
    Polynomial.C s * (Polynomial.C s * Q * Q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (Q + K + T + (Q + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro d D M p hp hM hMp hd hD
  let t : ℝ := 1 + p + (s.factorial + 2 * s + 1 : ℕ) + p * (p + 1) ^ s
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    have hprod : 0 ≤ p * (p + 1) ^ s := by positivity
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (s.factorial + 2 * s + 1)]
  have hdt := hd.trans hpt
  have hMt := hMp.trans hpt
  have hDb : (D : ℝ) ≤ p * (p + 1) ^ s := by
    apply (Nat.cast_le.mpr hD).trans
    push_cast
    gcongr
  have hgeo : ((D + s.factorial + 2 * s + 1 : ℕ) : ℝ) ≤ t := by
    dsimp [t]
    push_cast at *
    linarith
  have hK : shearKernelLogBudget s d M p ≤
      t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1)) := by
    unfold shearKernelLogBudget
    push_cast
    gcongr
  have hT : shearActionLogBudget s d M ≤
      s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t) := by
    unfold shearActionLogBudget
    push_cast
    gcongr
  have htotal : t +
      (t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1))) +
      (s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t)) + (t + a) ^ a + 4 ≤ (p + 2) ^ C := by
    simpa [X, Q, K, T, t, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbound p hp
  refine ⟨t, ht, hgeo, ?_⟩
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PatchTopNetPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem exists_patch_top_net_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ) (M L p : ℝ),
      0 ≤ p → 0 ≤ M → 0 ≤ L → (d : ℝ) ≤ p → M ≤ Real.exp p → L ≤ Real.exp p →
      ∃ N : ℕ, 0 < N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (((N + 1) ^ (d * (d + 1) ^ s) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        patchTopNetError d s N M < 1 / 4 ∧
        L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := Polynomial.C s + Polynomial.C s * X + X + 4 +
    Polynomial.C s * Polynomial.C s * X * (X + 1) + 2 * X + 6
  let I : Polynomial ℕ := X * (X + 1) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (Q + I * Q)
  refine ⟨C, hC, ?_⟩
  intro d M L p hp hM hL hd hMp hLp
  let q := patchTopNetNumeratorLog s p + 2 * p + 6
  have hq : 0 ≤ q := by
    have := patchTopNetNumeratorLog_nonneg s hp
    dsimp only [q]
    positivity
  have hcount : 0 ≤ p * (p + 1) ^ s := by positivity
  have ht : q + p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by
    simpa [Q, I, X, q, patchTopNetNumeratorLog, Polynomial.eval₂_pow] using hbudget p hp
  have hqp : q ≤ (p + 2) ^ C := by nlinarith
  have hcp : p * (p + 1) ^ s * q ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, hNbound, hsmall, hloss⟩ := exists_small_patch_top_mesh d s hp hM hL hd hMp hLp
  refine ⟨N, hN, hNbound.trans (Real.exp_le_exp.mpr hqp), ?_, hsmall, hloss⟩
  have hdc : ((d * (d + 1) ^ s : ℕ) : ℝ) ≤ p * (p + 1) ^ s := by
    push_cast
    gcongr
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp q) ^ (d * (d + 1) ^ s) := pow_le_pow_left₀ (by positivity) hNbound _
    _ = Real.exp (((d * (d + 1) ^ s : ℕ) : ℝ) * q) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (p + 1) ^ s * q) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hq)
    _ ≤ _ := Real.exp_le_exp.mpr hcp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealGeneratorCombinations
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

variable {ι κ V : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def realGeneratorCombination (v : κ → V) (a : κ → ℝ) : ℝ ⊗[ℚ] V :=
  ∑ j, a j ⊗ₜ[ℚ] v j

theorem realGeneratorCombination_mem (U : Submodule ℚ V) (v : κ → V)
    (hv : ∀ j, v j ∈ U) (a : κ → ℝ) : realGeneratorCombination v a ∈ U.baseChange ℝ := by
  classical
  exact Submodule.sum_mem _ (fun j _ => Submodule.tmul_mem_baseChange_of_mem (a j) (hv j))

theorem realGeneratorCombination_coordinates [Fintype ι] (b : Basis ι ℚ V)
    (v : κ → V) (a : κ → ℝ) :
    (b.baseChange ℝ).equivFun (realGeneratorCombination v a) =
      (fun i j => (b.repr (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Basis.equivFun_apply, Finset.sum_apply,
    Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, Rat.smul_def]

theorem realGeneratorCombination_map_coordinates [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (v : κ → V) (a : κ → ℝ) :
    realRationalCoordinateEquiv (φ.baseChange ℝ (realGeneratorCombination v a)) =
      (fun i j => (φ (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Finset.sum_apply, LinearMap.baseChange_tmul,
    realRationalCoordinateEquiv_tmul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem exists_controlled_coordinate_lifts
    {μ ι κ σ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a q : ι → ℝ),
        a + q ∈ realRationalCoordinateSpan (U.map φ) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ E) = a ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ Q) = q ∧
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan := realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting A hH hl
    (fun i j => hφH j i) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) := hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (x : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 3) * ‖x‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) x).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg x))
  have hBm : 0 < matrixDenominator B * m := Nat.mul_pos (matrixDenominator_pos B) hm
  have hBmp : ((matrixDenominator B * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  refine ⟨l * (matrixDenominator B * m), Nat.mul_pos hl hBm, ?_, dvd_mul_right _ _, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hBmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  · intro α hα a q hsum ha hq
    rw [hspan] at hsum
    obtain ⟨x, hx⟩ := hsum
    obtain ⟨hSa, hSq, hslow, hgrid, _⟩ := hsolve α hα a q x ha hq hx
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cq := (fun i j => (S i j : ℝ)) *ᵥ q
    refine ⟨realGeneratorCombination v ca, realGeneratorCombination v cq,
      realGeneratorCombination_mem U v hvU ca, realGeneratorCombination_mem U v hvU cq,
      ?_, ?_, ?_, ?_⟩
    · rw [realGeneratorCombination_map_coordinates]
      exact hSa
    · rw [realGeneratorCombination_map_coordinates]
      exact hSq
    · rw [realGeneratorCombination_coordinates]
      calc
        ‖(fun i j => (b.repr (v j) i : ℝ)) *ᵥ ca‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca‖ := hnorm ca
        _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring
    · rw [realGeneratorCombination_coordinates]
      exact realDenominatorGrid_subset_of_dvd hBm (dvd_mul_left _ _)
        (real_matrix_denominator_grid B m cq hgrid)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearMapIntegralCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_integral_model_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨c, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + 1 + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hp1 : p ≤ p + 1 := by linarith
  have hbud : p + (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcC : (p + 1 + c) ^ c ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by
    have hn : 0 ≤ (p + 1 + c) ^ c := by positivity
    linarith
  obtain ⟨B, Λ, hB, _, hBb, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid ⌈Real.exp p⌉₊
      (p + 1) D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) D.inner_grid
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hp1)
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hp1))
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBb.trans (Real.exp_le_exp.mpr hcC)
  exact ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem linearMap_mem_scaledGrid {L M ι κ : Type*}
    [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]
    [Fintype ι] [Fintype κ] [DecidableEq ι] (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {a b : ℕ}
    (hab : b * matrixDenominator (LinearMap.toMatrix e f φ) ∣ a)
    {x : L} (hx : e.equivFun x ∈ scaledIntegerGrid a) :
    f.equivFun (φ x) ∈ scaledIntegerGrid b := by
  classical
  have h := matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ) b
    (scaledIntegerGrid_subset_of_dvd hab hx)
  change LinearMap.toMatrix e f φ *ᵥ e.equivFun x ∈ scaledIntegerGrid b at h
  have hmap : LinearMap.toMatrix e f φ *ᵥ e.equivFun x = f.equivFun (φ x) := by
    simpa only [Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr e f φ x
  rwa [hmap] at h

namespace RationalFilteredNilmanifold

theorem linearMap_real_lattice {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ[ℚ] M)
    (hφ : ∀ z : D.filtration.Group, z ∈ D.lattice →
      (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    (⟨φ.baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨⟨φ x.coord⟩, hφ x hx, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change (1 : ℝ) ⊗ₜ[ℚ] φ x.coord = φ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x.coord)
  exact (LinearMap.baseChange_tmul _ _ _).symm

theorem exists_native_linear_target_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {t d e k : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ[ℚ] M) (ψ : L →ₗ[ℚ] (Fin k → ℚ)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → (k : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (ψ (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ → (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        ∀ z : D.filtration.Group, z ∈ Λ → IntegralVector (ψ z.coord) := by
  obtain ⟨a, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := 2 * X + 2 * (X + 2) ^ 3 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ t d e k D E φ ψ p hp hD hE hk hφ hψ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ
  let Z := LinearMap.toMatrix D.basis (Pi.basisFun ℚ (Fin k)) ψ
  let l := D.grid * ((E.grid * matrixDenominator A) * matrixDenominator Z)
  let P := 2 * p + 2 * (p + 2) ^ 3 + 1
  have hp1 : p + 1 ≤ P := by dsimp [P]; nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) 3]
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hp1
  have hP : 0 ≤ P := hp.trans hpP
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hZ : (matrixDenominator Z : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power Z hp 1
      (by simpa only [Fintype.card_fin] using hk)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hψ i j)).2
    dsimp only [Z]
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hl : 0 < l := Nat.mul_pos D.grid_pos
    (Nat.mul_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A)) (matrixDenominator_pos Z))
  have hDl : D.grid ∣ l := dvd_mul_right _ _
  have hAl : E.grid * matrixDenominator A ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hZl : matrixDenominator Z ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hlP : (l : ℝ) ≤ Real.exp P := by
    have h := mul_le_mul hD.2.1
      (mul_le_mul (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _)) hZ
        (Nat.cast_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    change (D.grid : ℝ) * ((E.grid : ℝ) * matrixDenominator A * matrixDenominator Z) ≤ _ at h
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add] at h
    have h' : (l : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3 + (p + 2) ^ 3)) := by
      simpa only [l, Nat.cast_mul] using h
    apply h'.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    ring_nf
    linarith
  have hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis D.lattice :=
    fun _ hx => D.inner_grid (scaledIntegerGrid_subset_of_dvd hDl hx)
  obtain ⟨B, Λ, hB, hlB, hBP, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice l ⌈Real.exp p⌉₊ P hl
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hinner hP
      (by simpa only [Fintype.card_fin] using hD.1.trans hpP)
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1)) hlP
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have htotal : P + (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P₀, X, P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (P + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  have hpC : p ≤ (p + C) ^ C := hpP.trans
    ((le_add_of_nonneg_right (by positivity : 0 ≤ (P + a) ^ a)).trans htotal)
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBP.trans (Real.exp_le_exp.mpr haC)
  refine ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC, ?_, ?_⟩
  · intro z hz
    apply (bchSubgroupCoordinates_repr E.basis E.lattice ⟨φ z.coord⟩).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ (hAl.trans hlB)
    rw [← hcoords]
    exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
  · intro z hz
    have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
      rw [← hcoords]
      exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
    have h := linearMap_mem_scaledGrid D.basis (Pi.basisFun ℚ (Fin k)) ψ (b := 1)
      (by simpa only [one_mul] using hZl.trans hlB) hgrid
    obtain ⟨v, hv⟩ := h
    exact ⟨v, fun i => by simpa only [Nat.cast_one, one_smul, Basis.equivFun_apply,
      Pi.basisFun_repr] using congrFun hv i⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedSubalgebraRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_native_subalgebra_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (l H : ℕ) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      0 < l →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates bk
        (D.lattice.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot
          D.filtration.lowerCentralSeries_eq_bot K) K.incl)) →
      (∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) H) →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j, |(D.basis.repr (bk j : L) i : ℝ)| ≤ Real.exp p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup, r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a + 2 * X + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk l H p hp hD hκ hl hinner hc hH hlp hentries q hq hqp
  classical
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let H0 := ⌈Real.exp p⌉₊
  have hH0 : (H0 : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ t by dsimp [t]; linarith)
  have hc0 : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H0 :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H0 t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH0 hc0 (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (p + a) ^ a + 2 * p + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a + 2 * p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + a) ^ a + 2 * p)).trans hsum
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hgK hg
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let hnilK := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot K
  let f := realificationMap (hnil := hnilK) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  obtain ⟨gK, hgK⟩ := (show g ∈ f.range from by
    rwa [realificationMap_incl_range])
  obtain ⟨rK, hrK, γK, hγK, hfac⟩ := hrep bk hnilK
    (D.lattice.comap (map K.incl)) l H p hl hinner hc hp hκ hH hlp gK
  have hγ : f γK ∈ D.realLattice := by
    change γK ∈ D.realLattice.comap f
    dsimp only [realLattice, f]
    rw [realification_subgroup_comap_incl]
    exact hγK
  have heq : g = f rK * f γK := by rw [← hgK, hfac, map_mul]
  refine ⟨f rK, realificationMap_incl_mem K rK, ?_, ?_, f γK, hγ, heq⟩
  · intro i
    change |(D.basis.baseChange ℝ).repr (K.incl.toLinearMap.baseChange ℝ rK.coord) i| ≤ _
    rw [scalarExtension_coordinate_sum D.basis bk K.incl.toLinearMap rK.coord i]
    calc
      _ ≤ ∑ j, |(bk.baseChange ℝ).repr rK.coord j * (D.basis.repr (K.incl (bk j)) i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : κ, Real.exp ((p + a) ^ a) * Real.exp p := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hrK j) (hentries i j) (abs_nonneg _) (Real.exp_pos _).le
      _ = (Fintype.card κ : ℝ) * (Real.exp ((p + a) ^ a) * Real.exp p) := by simp
      _ ≤ Real.exp p * (Real.exp ((p + a) ^ a) * Real.exp p) := by
        exact mul_le_mul_of_nonneg_right (hκ.trans (by linarith [Real.add_one_le_exp p])) (by positivity)
      _ = Real.exp ((p + a) ^ a + 2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr haC
  · have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (f γK)⁻¹ (D.realLattice.inv_mem hγ)
    have h := hmul g (f γK)⁻¹
      (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
      (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
    simpa only [heq, mul_inv_cancel_right] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_bounded_subalgebra_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_subalgebra_rational_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 12 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk p hp hD hκ hinc q hq hqp
  classical
  let H := ⌈Real.exp p⌉₊
  let p0 := p + 1
  let t := lieSubalgebraRepresentativeParameter p0
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hpt : p ≤ t := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 12))
  have ht : 0 ≤ t := (lieSubalgebraRepresentativeParameter_pos hp0).le
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hincH : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hinc i j)
  let HC := lieSubalgebraRepresentativeHeight (Fintype.card (Fin d)) (Fintype.card κ) H
  have hHC : (HC : ℝ) ≤ Real.exp t :=
    lieSubalgebraRepresentativeHeight_le_exp_parameter _ _ _ hp0 hd0 hκ0 hH
  have hcK : ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) HC :=
    lieSubalgebraRepresentative_bracket_height D.basis K bk (one_le_ceil_exp p) hc hincH
  let A : Matrix (Fin d) κ ℚ := fun i j => D.basis.repr (bk j : L) i
  let qI := matrixDenominator A
  have hqI : 0 < qI := matrixDenominator_pos A
  have hcolumns : ∀ j, D.basis.equivFun (bk j : L) ∈ denominatorGrid qI := by
    intro j
    refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
    exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm
  have hqIb : (qI : ℝ) ≤ Real.exp ((p0 + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp0 1 hd0 hκ0
    intro i j
    exact ((Nat.cast_le.mpr (hincH i j).2).trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 1)))
  have hlb : ((D.grid * qI : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p0 * Real.exp ((p0 + 2) ^ 3) :=
        mul_le_mul (hD.2.1.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith)))
          hqIb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (p0 + (p0 + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p0 + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hpow := le_power_budget hp0 (by decide : 1 ≤ 3)
        have hnon : 0 ≤ (p0 + 2) ^ 3 := by positivity
        rw [pow_succ]
        nlinarith
      _ ≤ _ := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p0 + 2) (by decide : 4 ≤ 12))
  have hinner := lieSubalgebra_comap_inner_grid_of_columns K bk D.basis D.lattice
    D.grid qI D.inner_grid hcolumns
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D K bk (D.grid * qI) HC t ht (GeometryComplexityLE.mono D hD hpt)
    (hκ.trans hpt) (Nat.mul_pos D.grid_pos hqI) hinner hcK hHC hlb
    (fun i j => ((hincH i j).abs_real_le.trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 12))))
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, lieSubalgebraRepresentativeParameter, p0, Polynomial.eval₂_pow, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
      using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftArrays
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

noncomputable def assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) :
    VectorPolynomial σ R (κ → V) := by
  classical
  exact ∑ k, map (LinearMap.single R (fun _ : κ => V) k) (P k)

@[simp] theorem coefficients_assembleFamily {σ κ R V : Type*} [Fintype κ] [CommRing R]
    [AddCommGroup V] [Module R V] (P : κ → VectorPolynomial σ R V) (α : σ →₀ ℕ) (k : κ) :
    coefficients (assembleFamily P) α k = coefficients (P k) α := by
  classical
  simp [assembleFamily, LinearMap.single_apply, Pi.single_apply]

end VectorPolynomial

open VectorPolynomial

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

noncomputable def liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : VectorPolynomial σ ℚ (κ × ι → ℝ) :=
  assembleFamily (fun bi : κ × ι => map
    (((LinearMap.proj bi.2).comp (realQuotientCoordinateMap f)).restrictScalars ℚ) (S bi.1))

@[simp] theorem coefficients_liftQuotientArray (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (bi : κ × ι) :
    coefficients (liftQuotientArray f S) α bi = realQuotientCoordinateMap f (coefficients (S bi.1) α) bi.2 := by
  rw [liftQuotientArray, coefficients_assembleFamily, coefficients_map]
  rfl

theorem liftQuotientArray_coefficient_eq_zero (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    (hS : ∀ t, coefficients (S t) α = 0) : coefficients (liftQuotientArray f S) α = 0 := by
  funext bi
  rw [coefficients_liftQuotientArray, hS, map_zero]
  rfl

theorem bracket_system_matches_lift_array (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : map ((realBracketSystem f k).restrictScalars ℚ) A = liftQuotientArray f S) :
    ∀ t α, coefficients (S t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ := by
  intro t α
  apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
  funext i
  have hi := congrArg (fun P : VectorPolynomial σ ℚ (κ × ι → ℝ) => coefficients P α (t, i)) h
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    coefficients_liftQuotientArray, realBracketSystem_apply] at hi
  rw [map_sub, Finsupp.sub_apply, coefficients_lie_constant, map_sub, Pi.sub_apply]
  exact sub_eq_zero.mpr hi.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BracketArrayEquation
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

theorem liftQuotientArray_neg (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => -S t) = -liftQuotientArray f S := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  funext bi
  simp only [coefficients_liftQuotientArray, map_neg, Finsupp.neg_apply, Pi.neg_apply]

theorem liftQuotientArray_norm_bound (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ t, ‖realQuotientCoordinateMap f (coefficients (S t) α)‖ ≤ M) :
    ‖coefficients (liftQuotientArray f S) α‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro bi
  rw [coefficients_liftQuotientArray]
  exact (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (S bi.1) α)) bi.2).trans (hS bi.1)

theorem liftQuotientArray_grid (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (l : ℕ)
    (hS : ∀ t, realQuotientCoordinateMap f (coefficients (S t) α) ∈ realDenominatorGrid l) :
    coefficients (liftQuotientArray f S) α ∈ realDenominatorGrid l := by
  classical
  have hex : ∀ t, ∃ z : ι → ℤ,
      (fun i => (z i : ℝ)) = (l : ℝ) • realQuotientCoordinateMap f (coefficients (S t) α) := hS
  choose z hz using hex
  refine ⟨fun bi => z bi.1 bi.2, ?_⟩
  funext bi
  change (z bi.1 bi.2 : ℝ) = (l : ℝ) * coefficients (liftQuotientArray f S) α bi
  rw [coefficients_liftQuotientArray]
  exact congrFun (hz bi.1) bi.2

theorem bracket_array_equation_of_current_relation
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (π : (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hcurrent : ∀ t α, ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ -
      (π (coefficients (S t) α) - π (coefficients (R t) α)) ∈ V.baseChange ℝ) :
    ∀ α, realBracketSystem f k (coefficients P α) =
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α +
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α := by
  intro α
  funext bi
  have hi := congrFun ((realQuotientCoordinateMap_eq_zero_iff f _).mpr (hcurrent bi.1 α)) bi.2
  simp only [map_sub, Pi.sub_apply, Pi.zero_apply] at hi
  change realQuotientCoordinateMap f ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆ bi.2 = _
  simp only [Pi.add_apply, coefficients_liftQuotientArray, coefficients_map,
    LinearMap.restrictScalars_apply, map_neg, map_sub, Finsupp.sub_apply,
    Finsupp.neg_apply, Pi.sub_apply, Pi.neg_apply]
  linear_combination hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedImageCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_selected_image_corrections
    {η ι κ σ : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    (A : Matrix η κ ℚ) (ρ : ι → η) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧
      (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (x : η → ℝ),
        x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ i, x (ρ i) = a i + b i) →
        let e := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a)
        let q := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b)
        e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        (∀ i, e (ρ i) = a i) ∧ (∀ i, q (ρ i) = b i) ∧
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
        q ∈ realDenominatorGrid m ∧
        x - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        ∀ i, (x - e - q) (ρ i) = 0 := by
  let C : Matrix ι κ ℚ := fun i j => A (ρ i) j
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting C hH hl
    (fun i j => hA (ρ i) j) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hη hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨S, matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b x hx ha hb hselect e q
    obtain ⟨z, hz⟩ := hx
    have hC : (fun i j => (C i j : ℝ)) *ᵥ z = a + b := by
      funext i
      exact (congrFun hz (ρ i)).trans (hselect i)
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb hC
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ a, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ b, rfl⟩
    have heq (i : ι) : e (ρ i) = a i := congrFun hSa i
    have hqq (i : ι) : q (ρ i) = b i := congrFun hSb i
    refine ⟨he, hq, heq, hqq, ?_, real_matrix_denominator_grid A m _ hgrid,
      Submodule.sub_mem _ (Submodule.sub_mem _ ⟨z, hz⟩ he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · intro i
      change x (ρ i) - e (ρ i) - q (ρ i) = 0
      rw [hselect i, heq i, hqq i]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteForwardPairedSourcePrecision
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    (x gainLog stageLog : ℝ) : ℝ :=
  preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    if isDirect then
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect
    else 0

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_model
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n false x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
  simp only [preparedFiniteForwardPairedSourcePrecision, Bool.false_eq_true, ↓reduceIte, add_zero]

@[simp] theorem preparedFiniteForwardPairedSourcePrecision_direct
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (x gainLog stageLog : ℝ) :
    preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog =
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
          preparedFiniteForwardWork A stageCountConstant n x + Cdirect) ^ Cdirect := by
  simp only [preparedFiniteForwardPairedSourcePrecision, ↓reduceIte]

theorem preparedFiniteForwardPairedSourcePrecision_nonneg
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    0 ≤ preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog := by
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect <;> simp only [preparedFiniteForwardPairedSourcePrecision_model,
    preparedFiniteForwardPairedSourcePrecision_direct] <;> positivity

theorem exists_preparedFiniteForwardPairedSourcePrecision_budget
    (depth A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ n ≤ depth, ∀ isDirect : Bool,
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, _, hb⟩ := exists_preparedFiniteForwardStage_budget depth A stageCountConstant
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C Cdirect) ^ Cdirect)
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs n hn isDirect
  have hstage := hb x gainLog stageLog hx hg hs n hn
  have hwork := hstage.2.1
  have hsource := hstage.2.2.2.2.2.2.2.2
  have hbound : (x + B) ^ B + (2 * (x + B) ^ B + Cdirect) ^ Cdirect ≤ (x + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hpoly x hx
  refine ⟨preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant n isDirect hx hg hs, ?_⟩
  cases isDirect with
  | false =>
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    apply hsource.2.trans
    apply le_trans _ hbound
    have hnonneg : 0 ≤ (2 * (x + B) ^ B + Cdirect) ^ Cdirect := by positivity
    linarith only [hnonneg]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    apply le_trans _ hbound
    apply add_le_add hsource.2
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg hsource.1 hwork.1) (Nat.cast_nonneg Cdirect))
    linarith only [hsource.2, hwork.2]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedForwardSeedPolynomial
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | outer + 1 => (preparedFiniteForwardWorkPolynomial A constants innerDepth).comp
      (candidateNestedForwardSeedPolynomial A constants innerDepth outer)

noncomputable def candidateNestedForwardSeed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) (x : ℝ) : ℝ :=
  (candidateNestedForwardSeedPolynomial A constants innerDepth outer).eval₂ (Nat.castRingHom ℝ) x

@[simp] theorem candidateNestedForwardSeed_zero (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) (x : ℝ) : candidateNestedForwardSeed A constants innerDepth 0 x = x := by
  simp [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial]

@[simp] theorem candidateNestedForwardSeed_succ (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) (x : ℝ) :
    candidateNestedForwardSeed A constants innerDepth (outer + 1) x =
      preparedFiniteForwardWork A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outer x) := by
  simp only [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial,
    Polynomial.eval₂_comp, preparedFiniteForwardWork]

theorem candidateNestedForwardSeed_nonneg (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ candidateNestedForwardSeed A constants innerDepth outer x :=
  natPolynomial_eval_nonneg _ hx

theorem candidateNestedForwardSeed_monotone (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    Monotone (fun outer => candidateNestedForwardSeed A constants innerDepth outer x) := by
  apply monotone_nat_of_le_succ
  intro outer
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq]
  let y := candidateNestedForwardSeed A constants innerDepth outer x
  have hy : 0 ≤ y := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hparam := le_preparedFiniteForwardParameter A constants innerDepth hy
  have hp0 := preparedFiniteForwardParameter_nonneg A constants innerDepth hy
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  calc
    y ≤ preparedFiniteForwardParameter A constants innerDepth y + A := by linarith only [hparam, hAreal]
    _ = (preparedFiniteForwardParameter A constants innerDepth y + A) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hp0, hAreal]) (by omega)

theorem le_candidateNestedForwardSeed (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer : ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x) :
    x ≤ candidateNestedForwardSeed A constants innerDepth outer x := by
  simpa only [candidateNestedForwardSeed_zero] using
    candidateNestedForwardSeed_monotone A constants innerDepth hA hx (Nat.zero_le outer)

theorem candidateNestedForwardWork_le_next_seed
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hi : inner ≤ innerDepth) :
    preparedFiniteForwardWork A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer x) ≤
        candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  rw [candidateNestedForwardSeed_succ, preparedFiniteForwardWork_eq, preparedFiniteForwardWork_eq]
  have hy := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hp := preparedFiniteForwardParameter_nonneg A constants inner hy
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (preparedFiniteForwardParameter_monotone A constants hy hi) le_rfl) A

theorem exists_candidateNestedForwardSeed_polynomial_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (Q : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x : ℝ}, 0 ≤ x → ∀ outer ≤ outerDepth,
      Q.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤ (x + 2) ^ C := by
  let polys := fun o => Q.comp (candidateNestedForwardSeedPolynomial A constants innerDepth o)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (∑ o ∈ Finset.range (outerDepth + 1), polys o)
  refine ⟨C, hC, ?_⟩
  intro x hx outer ho
  apply le_trans _ (hbound x hx)
  rw [Polynomial.eval₂_finsetSum]
  have hentry := Finset.single_le_sum (f := fun o => (polys o).eval₂ (Nat.castRingHom ℝ) x)
    (fun o _ => natPolynomial_eval_nonneg (polys o) hx) (Finset.mem_range.mpr (Nat.lt_succ_of_le ho))
  simpa only [polys, Polynomial.eval₂_comp, candidateNestedForwardSeed] using hentry

theorem exists_candidateNestedForwardLocal_budget
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ outer ≤ outerDepth, ∀ inner ≤ innerDepth,
      let seed := candidateNestedForwardSeed A constants innerDepth outer x
      seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardWork A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardCumulative A constants inner seed ∈ Set.Icc 0 ((x + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants inner seed gainLog stageLog ∈
        Set.Icc 0 ((x + 2) ^ C) ∧
      ∀ direct : Bool, preparedFiniteForwardPairedSourcePrecision A Cdirect constants
        inner direct seed gainLog stageLog ∈ Set.Icc 0 ((x + 2) ^ C) := by
  obtain ⟨B, _, hstage⟩ := exists_preparedFiniteForwardStage_budget innerDepth A constants
  obtain ⟨D, _, hpaired⟩ :=
    exists_preparedFiniteForwardPairedSourcePrecision_budget innerDepth A Cdirect constants
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B +
    (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbound⟩ :=
    exists_candidateNestedForwardSeed_polynomial_budget A constants innerDepth outerDepth Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs outer ho inner hi seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hxs : x ≤ seed := le_candidateNestedForwardSeed A constants innerDepth outer hA hx
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hxs⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hxs⟩
  have htotal : seed + (seed + B) ^ B + (seed + D) ^ D ≤ (x + 2) ^ C := by
    simpa [Q, seed, Polynomial.eval₂_pow] using hbound hx outer ho
  have hB0 : 0 ≤ (seed + B) ^ B := by positivity
  have hD0 : 0 ≤ (seed + D) ^ D := by positivity
  have hBup : (seed + B) ^ B ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hD0]
  have hDup : (seed + D) ^ D ≤ (x + 2) ^ C := by linarith only [htotal, hseed, hB0]
  obtain ⟨hparam, hwork, _, _, _, hcum, _, hmodel, _⟩ :=
    hstage seed gainLog stageLog hseed hg' hs' inner hi
  refine ⟨⟨hseed, by linarith only [htotal, hB0, hD0]⟩,
    ⟨hparam.1, hparam.2.trans hBup⟩, ⟨hwork.1, hwork.2.trans hBup⟩,
    ⟨hcum.1, hcum.2.trans hBup⟩, ⟨hmodel.1, hmodel.2.trans hBup⟩, ?_⟩
  intro direct
  have h := hpaired hseed hg' hs' inner hi direct
  exact ⟨h.1, h.2.trans hDup⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardInnerDetectionThreshold_bound
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) ≤
        Real.exp (-gainLog) / 2 := by
  have hp := (preparedFiniteForward_prefix_bounds A stageCountConstant n hx).2.1
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hfloor : gainLog + 1 ≤
      2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8 := by
    dsimp only [preparedFiniteForwardModelPrecision]
    linarith only [hp, hw, hg.1, hs.1]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : 2 * Real.exp (-(gainLog + 1)) ≤ Real.exp (-gainLog) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(gainLog + 1)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hthreshold := Real.exp_le_exp.mpr (neg_le_neg hfloor)
  linarith only [hthreshold, hhalf]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceRequired
    {Slot : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ) : ℝ :=
  1 + max 0 anchorGoodRequired + max 0 conditionalRequired +
    (∑ slot, max 0 (detectorRequired slot)) +
    ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))

variable {Slot : Type*} [Fintype Slot]
variable (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
variable (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardLaterWorkBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_local_shiftedPower_le_later_work
    (A C Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hA : 2 ≤ A) (hC : C ≤ A) (hn : 1 ≤ n) :
    let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
      0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
    (t + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  intro t
  have hcap : (t + C) ^ C ≤ preparedFiniteForwardCap A stageCountConstant 0 x := by
    simpa only [t, preparedFiniteForwardPairedSourcePrecision_model] using
      preparedFiniteForward_phase_cap A stageCountConstant 0 C hx hg hs hC
  have hnext : preparedFiniteForwardCap A stageCountConstant 0 x ≤
      preparedFiniteForwardParameter A stageCountConstant 1 x := by
    rw [preparedFiniteForwardParameter_succ]
    have hparameter := preparedFiniteForwardParameter_nonneg A stageCountConstant 0 hx
    have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant 0 hx
    linarith only [hparameter, hbranch]
  have hlater := preparedFiniteForwardParameter_monotone A stageCountConstant hx hn
  have hwork := (preparedFiniteForward_model_scalar_bounds A stageCountConstant n 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)).2.1
  exact hcap.trans (hnext.trans (hlater.trans hwork))

theorem exists_preparedFiniteForward_local_polynomial_le_later_work
    (Cbase : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog f : ℝ},
      0 ≤ x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → C ≤ A → 1 ≤ n →
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        0 false x gainLog stageLog + preparedFiniteForwardWork A stageCountConstant 0 x
      f ∈ Set.Icc 0 ((t + Cbase) ^ Cbase) →
      P.eval₂ (Nat.castRingHom ℝ) f ≤ preparedFiniteForwardWork A stageCountConstant n x := by
  let Q := P.comp ((Polynomial.X + Polynomial.C Cbase) ^ Cbase)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant n x gainLog stageLog f hx hg hs hCA hn t hf
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant 0 false hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant 0 hx)
  have heval : P.eval₂ (Nat.castRingHom ℝ) f ≤
      P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) := by
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.1 hf.2 k) (Nat.cast_nonneg _)
  have hbound : P.eval₂ (Nat.castRingHom ℝ) ((t + Cbase) ^ Cbase) ≤ (t + C) ^ C := by
    simpa [Q, Polynomial.eval₂_comp, Polynomial.eval₂_pow] using hpoly t ht
  exact heval.trans (hbound.trans
    (preparedFiniteForward_local_shiftedPower_le_later_work A C Cdirect stageCountConstant n
      hx hg hs (hC.trans hCA) hCA hn))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardPairedResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardPairedResource_budget (Cdirect Cresource : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      (preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + Cresource) ^ Cresource ≤
      (preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
        preparedFiniteForwardWork A stageCountConstant n x + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + (X + Polynomial.C Cdirect) ^ Cdirect +
    Polynomial.C Cresource) ^ Cresource
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant n x gainLog stageLog hx hg hs
  let t := preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog +
    preparedFiniteForwardWork A stageCountConstant n x
  have ht : 0 ≤ t := add_nonneg
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)
  have heq : preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n true x gainLog stageLog +
      preparedFiniteForwardWork A stageCountConstant n x + Cresource =
      t + (t + Cdirect) ^ Cdirect + Cresource := by
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    dsimp only [t]
    ring
  rw [heq]
  simpa [P, X, Polynomial.eval₂_pow, t] using hpoly t ht

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResetBracketGeometry
namespace OAI

section

namespace Erdos3

open Module

noncomputable def nativeResetBracketHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((p + 4) ^ 11)⌉₊

theorem nativeResetBracketLog_ge_input {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + 4) ^ 11 := by
  have hpow : p + 4 ≤ (p + 4) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 4)
      (by norm_num : (1 : ℕ) ≤ 11)
  linarith only [hpow]

namespace RationalFilteredNilmanifold

variable {κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f) (c : Basis κ ℚ M)

theorem nativeResetBracketGeometry {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k)
      (nativeResetBracketHeight p)) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k)
      (nativeResetBracketHeight p)) := by
  obtain ⟨hdim, _, hbracket⟩ := Fmark.basis_geometry_of_forward_height c hp hF
    (fun i j => (hc i j).trans (by linarith))
  exact ⟨hD.1, hdim,
    fun i j k => rationalHeightLE_ceil_exp
      ((hD.2.2.1 i j k).trans (nativeResetBracketLog_ge_input hp)),
    fun i j k => rationalHeightLE_ceil_exp (hbracket i j k)⟩

theorem nativeResetBracketGeometry_of_height {p : ℝ} {H : ℕ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hH : nativeResetBracketHeight p ≤ H) :
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) := by
  obtain ⟨hd, hf, hbracketD, hbracketF⟩ := D.nativeResetBracketGeometry Fmark c hp hD hF hc
  exact ⟨hd, hf, fun i j k => (hbracketD i j k).mono hH,
    fun i j k => (hbracketF i j k).mono hH⟩

theorem nativeResetBracketGeometry_of_logBudget {p q : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hF : Fmark.GeometryComplexityLE p)
    (hc : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hbudget : (p + 4) ^ 11 ≤ q) :
    1 ≤ ⌈Real.exp q⌉₊ ∧ (⌈Real.exp q⌉₊ : ℝ) ≤ Real.exp (q + 1) ∧
    (d : ℝ) ≤ p ∧ (Fintype.card κ : ℝ) ≤ p ∧
    (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) ⌈Real.exp q⌉₊) ∧
    (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) ⌈Real.exp q⌉₊) := by
  refine ⟨one_le_ceil_exp _, ceil_exp_le_exp_add_one ?_,
    D.nativeResetBracketGeometry_of_height Fmark c hp hD hF hc ?_⟩
  · exact (show 0 ≤ (p + 4) ^ 11 by positivity).trans hbudget
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hbudget)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

abbrev PreparedFiniteNestedForwardAllDegreeSlot (outerDepth innerDepth cutoff : ℕ) :=
  Fin (outerDepth + 1) × Fin (innerDepth + 1) × Fin (cutoff + 1) × Bool

def preparedFiniteNestedForwardAllDegreeOuter {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (outerDepth + 1) := k.1

def preparedFiniteNestedForwardAllDegreeStage {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    Fin (innerDepth + 1) := k.2.1

def preparedFiniteNestedForwardAllDegreeIsDirect {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : Bool :=
  k.2.2.2

def preparedFiniteNestedForwardAllDegreeDegree {outerDepth innerDepth cutoff : ℕ}
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℕ :=
  k.2.2.1.val

noncomputable def preparedFiniteNestedForwardAllDegreeSeed
    {outerDepth innerDepth cutoff : ℕ} (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) : ℝ :=
  candidateNestedForwardSeed A constants innerDepth k.1.val x

def preparedFiniteNestedForwardAllDegreeAnchor (outerDepth innerDepth cutoff : ℕ) :
    PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff :=
  (⟨outerDepth, Nat.lt_succ_self outerDepth⟩,
    ⟨innerDepth, Nat.lt_succ_self innerDepth⟩, 0, false)

@[simp] theorem preparedFiniteNestedForwardAllDegreeOuter_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeOuter (outer, inner, degree, direct) = outer := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeStage_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeStage (outer, inner, degree, direct) = inner := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeIsDirect_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeIsDirect (outer, inner, degree, direct) = direct := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeDegree_slot {outerDepth innerDepth cutoff : ℕ}
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeDegree (outer, inner, degree, direct) = degree.val := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeSeed_slot {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) (x : ℝ)
    (outer : Fin (outerDepth + 1)) (inner : Fin (innerDepth + 1))
    (degree : Fin (cutoff + 1)) (direct : Bool) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x (outer, inner, degree, direct) =
      candidateNestedForwardSeed A constants innerDepth outer.val x := rfl

theorem preparedFiniteNestedForwardAllDegreeDegree_le {outerDepth innerDepth cutoff m : ℕ}
    (hcutoff : cutoff ≤ m)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    preparedFiniteNestedForwardAllDegreeDegree k ≤ m :=
  (Nat.le_of_lt_succ k.2.2.1.isLt).trans hcutoff

theorem le_preparedFiniteNestedForwardAllDegreeSeed {outerDepth innerDepth cutoff : ℕ}
    (A : ℕ) (constants : ℕ → ℕ) {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    x ≤ preparedFiniteNestedForwardAllDegreeSeed A constants x k :=
  le_candidateNestedForwardSeed A constants innerDepth k.1.val hA hx

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_outer
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeOuter
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨outerDepth, Nat.lt_succ_self outerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_stage
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeStage
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      ⟨innerDepth, Nat.lt_succ_self innerDepth⟩ := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_model
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeIsDirect
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = false := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_degree
    (outerDepth innerDepth cutoff : ℕ) :
    preparedFiniteNestedForwardAllDegreeDegree
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) = 0 := rfl

@[simp] theorem preparedFiniteNestedForwardAllDegreeAnchor_seed
    (outerDepth innerDepth cutoff A : ℕ) (constants : ℕ → ℕ) (x : ℝ) :
    preparedFiniteNestedForwardAllDegreeSeed A constants x
      (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff) =
      candidateNestedForwardSeed A constants innerDepth outerDepth x := rfl

end Erdos3.VectorPolynomial

end

end OAI

end


