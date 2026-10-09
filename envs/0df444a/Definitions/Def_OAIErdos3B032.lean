-- Prove2me | Definitions.Def_OAIErdos3B032
-- name    : OAIErdos3B032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:09:16.257908+00:00
-- url     : https://prove2.me/theorems/233cd5b2-c9b9-48a1-8b84-afe68e2b1393
-- title:
--   OpenAI Erdős-3 split, definitions bundle 33 of 128
-- statement:
--   Definitions bundle 33 of 128 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B031`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 33 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.affineCoveredSiteSample`, `OAI.Erdos3.BooleanCubeKernel.affineCoveredSiteSample_eq_values`, `OAI.Erdos3.BooleanCubeKernel.affine_site_substitution_eval`, `OAI.Erdos3.BooleanCubeKernel.cubeModePolynomialBudget`, `OAI.Erdos3.BooleanCubeKernel.exists_bounded_ambient_mode_witness`, `OAI.Erdos3.BooleanCubeKernel.exists_bounded_integer_mode_rows`, `OAI.Erdos3.BooleanCubeKernel.exists_bounded_integer_mode_witness`, `OAI.Erdos3.BooleanCubeKernel.exists_vertex_bounded_integer_mode`, `OAI.Erdos3.BooleanCubeKernel.integerCubeWitnessBound_le_polynomial`, `OAI.Erdos3.BooleanCubeKernel.integerCubeWitnessBound_le_vertex_budget`, `OAI.Erdos3.BooleanCubeKernel.integer_cube_difference_bound`, `OAI.Erdos3.BooleanCubeKernel.integer_cube_root_bound`, `OAI.Erdos3.BooleanCubeKernel.physicalEuclideanSitePoint`, `OAI.Erdos3.FiniteSitePhaseRemoval`, `OAI.Erdos3.MultidegreeLieFiltration.exists_bounded_ordinaryLayer_basis`, `OAI.Erdos3.MultidegreeLieFiltration.ordinaryLayer_eq_span_multidegree_bases`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.terminal_coefficients_mem_rational_stepDrop`, `OAI.Erdos3.NilpotentLieFiltration.FormalInductionRun.terminal_coefficients_mem_stepDropSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.exists_rational_formal_stage_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positive_coefficient_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_squarefree_coefficient_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positiveCoefficientBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positiveCoefficientBasis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeCoefficientBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeCoefficientBasis_height`, `OAI.Erdos3.RelativePatchSliceConclusion.exists_fiber_law_with_slice`, `OAI.Erdos3.RelativePatchSliceConclusion.tighten_rank`, `OAI.Erdos3.RelativeReturnedFiberLaw`, `OAI.Erdos3.ResidueBoxSlice.fiberIntegerPoint_mem_integerBox`, `OAI.Erdos3.ResidueBoxSlice.fiberPointInBox`, `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw`, `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw_mean`, `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw_score`, `OAI.Erdos3.SamplerLongVariables`, `OAI.Erdos3.StepDropRow`, `OAI.Erdos3.SubspaceArrayTorus`, `OAI.Erdos3.VectorPolynomial.AllocatedCongruenceIntegerAxis`, `OAI.Erdos3.VectorPolynomial.AllocatedCongruenceRankOutput`, `OAI.Erdos3.VectorPolynomial.AllocatedDegreeActiveAxis`, `OAI.Erdos3.VectorPolynomial.AllocatedDegreeRankOutput`, `OAI.Erdos3.VectorPolynomial.AllocatedTaggedRankOutput`, `OAI.Erdos3.VectorPolynomial.LayerSamplerAxis`, `OAI.Erdos3.VectorPolynomial.LayerSamplerLongVariables`, `OAI.Erdos3.VectorPolynomial.LayerSamplerScale.rec`, `OAI.Erdos3.VectorPolynomial.LayerSamplerVariables`, `OAI.Erdos3.VectorPolynomial.SpatialDegreeOutput`, `OAI.Erdos3.VectorPolynomial.affineLiftFrequency`, `OAI.Erdos3.VectorPolynomial.affineLiftFrequency_bound`, `OAI.Erdos3.VectorPolynomial.affineModeLift`, `OAI.Erdos3.VectorPolynomial.affineModeLift_coefficientFunctional`, `OAI.Erdos3.VectorPolynomial.affineModeLift_comp_map`, `OAI.Erdos3.VectorPolynomial.affineModeLift_exists_factorization_iff`, `OAI.Erdos3.VectorPolynomial.affineModeLift_factorization_iff`, `OAI.Erdos3.VectorPolynomial.affineModeLift_integerFrequency`, `OAI.Erdos3.VectorPolynomial.affineModeLift_substitute`, `OAI.Erdos3.VectorPolynomial.affineParameterSubstitution`, `OAI.Erdos3.VectorPolynomial.affineParameterSubstitution_degree`, `OAI.Erdos3.VectorPolynomial.affineParameterSubstitution_eval`, `OAI.Erdos3.VectorPolynomial.allocatedBoundedCoefficient_selected_long_top`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceIntegerEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceOutputEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceOutputEmbedding_deck`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceOutputEmbedding_integer`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceOutputEmbedding_spatial`, `OAI.Erdos3.VectorPolynomial.allocatedDegreeLongAxis`, `OAI.Erdos3.VectorPolynomial.allocatedDegreeRankBlock`, `OAI.Erdos3.VectorPolynomial.allocatedKernelReplacementLog`, `OAI.Erdos3.VectorPolynomial.allocatedLongEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalConstantRadius`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSiteRadius`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSiteRadius_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSupportRadius`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSupportRadius_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalChartRadius`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalChartRadius_inv_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalChartRadius_pos`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRootAllowance`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalGridScale`, `OAI.Erdos3.VectorPolynomial.allocatedSiteJetSize`, `OAI.Erdos3.VectorPolynomial.allocatedSiteJetSize_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedGridHeightCutoff`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialRankBlock`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialRankBlock_product`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankBlock`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial_degreeLE`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial_top_diagonal`, `OAI.Erdos3.VectorPolynomial.coefficientModePolynomial_top_integer_row`, `OAI.Erdos3.VectorPolynomial.coefficientMode_diagonal_polynomial`, `OAI.Erdos3.VectorPolynomial.coefficient_mode_with_lower_site_cauchySchwarz`, `OAI.Erdos3.VectorPolynomial.degreeLE_dehomogenize`, `OAI.Erdos3.VectorPolynomial.dehomogenize_rowPolynomial`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScale`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScaleOfExp`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScaleOfExp_value`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScaleOfFloor`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScaleOfFloor_value`, `OAI.Erdos3.VectorPolynomial.emptyLayerSamplerScale_value`, `OAI.Erdos3.VectorPolynomial.exists_absorbed_integer_site_tests`, `OAI.Erdos3.VectorPolynomial.exists_highest_affine_nonfactor`, `OAI.Erdos3.VectorPolynomial.exists_highest_affine_subspace_nonfactor`, `OAI.Erdos3.VectorPolynomial.exists_layerSamplerScale`, `OAI.Erdos3.VectorPolynomial.factorialContractedRow`, `OAI.Erdos3.VectorPolynomial.factorialContractedRow_bound`, `OAI.Erdos3.VectorPolynomial.factorialContractedRow_eval`, `OAI.Erdos3.VectorPolynomial.factorialContractedRow_nonzero`, `OAI.Erdos3.VectorPolynomial.homogeneous_factorization_to_bounded_site`, `OAI.Erdos3.VectorPolynomial.homogeneous_mode_diagonal_difference`, `OAI.Erdos3.VectorPolynomial.homogeneous_substitute_scaled`, `OAI.Erdos3.VectorPolynomial.integerContractedRow`, `OAI.Erdos3.VectorPolynomial.integerContractedRow_apply`, `OAI.Erdos3.VectorPolynomial.integerContractedRow_cast`, `OAI.Erdos3.VectorPolynomial.integerContractedRow_coefficientFunctional`, `OAI.Erdos3.VectorPolynomial.layerContinuousPrincipalSlots`, `OAI.Erdos3.VectorPolynomial.layerContinuousPrincipalSlots_not_constant`, `OAI.Erdos3.VectorPolynomial.layerIntegerPrincipalSlots`, `OAI.Erdos3.VectorPolynomial.layerIntegerPrincipalSlots_card`, `OAI.Erdos3.VectorPolynomial.layerIntegerPrincipalSlots_not_constant`, `OAI.Erdos3.VectorPolynomial.layerSamplerBox`, `OAI.Erdos3.VectorPolynomial.layerSamplerBox_le`, `OAI.Erdos3.VectorPolynomial.layerSamplerBox_one_le`, `OAI.Erdos3.VectorPolynomial.layerSamplerDegree`, `OAI.Erdos3.VectorPolynomial.layerSamplerDenominators`, `OAI.Erdos3.VectorPolynomial.layerSamplerGapWidth`, `OAI.Erdos3.VectorPolynomial.layerSamplerScaleBound`, `OAI.Erdos3.VectorPolynomial.layerSamplerSides`, `OAI.Erdos3.VectorPolynomial.layerSamplerSides_integer_principal`, `OAI.Erdos3.VectorPolynomial.layerSamplerSides_le`, `OAI.Erdos3.VectorPolynomial.layerSamplerSides_pos`, `OAI.Erdos3.VectorPolynomial.layerSamplerTailScaleFloor`, `OAI.Erdos3.VectorPolynomial.layerSamplerTailScaleFloor_le_exp`, `OAI.Erdos3.VectorPolynomial.layerSamplerTailWidth`, `OAI.Erdos3.VectorPolynomial.layerSamplerTailWidth_of_scaleFloor`, `OAI.Erdos3.VectorPolynomial.layerSamplerWidths`, `OAI.Erdos3.VectorPolynomial.layerSamplerWitnessScaleBound`, `OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope`, `OAI.Erdos3.VectorPolynomial.rowPolynomial_integer_site`, `OAI.Erdos3.VectorPolynomial.selectedLayerSamplerScale`, `OAI.Erdos3.VectorPolynomial.slicedGridGeometryLog`, `OAI.Erdos3.allocatedKernelLog`, `OAI.Erdos3.arrayCoordinateEquiv`, `OAI.Erdos3.arrayCoordinateEquiv_continuous`, `OAI.Erdos3.arrayCoordinateLinear`, `OAI.Erdos3.arrayCoordinateTorus`, `OAI.Erdos3.arrayCoordinateTorus_bijective`, `OAI.Erdos3.arrayCoordinateTorus_mk`, `OAI.Erdos3.basisGradeProjection_one_lie_eq_zero`, `OAI.Erdos3.basisSurjectionSection`, `OAI.Erdos3.basisSurjectionSection_rightInverse`, `OAI.Erdos3.bounded_submodule_spanning_mem_candidates`, `OAI.Erdos3.canonicalBoundedCoefficient_selected_long_top`, `OAI.Erdos3.canonicalPrincipalSubblockSlot`, `OAI.Erdos3.canonicalPrincipalSubblockSlot_degree`, `OAI.Erdos3.canonicalPrincipalSubblockSlot_injective`, `OAI.Erdos3.canonicalRankBlock`, `OAI.Erdos3.canonicalRankBlockEmbedding`, `OAI.Erdos3.canonicalSelectedLongTopResidual`, `OAI.Erdos3.canonicalSelectedTopResidual`, `OAI.Erdos3.chosenBasis_smul_coordinate_height`, `OAI.Erdos3.chosenBoundedSubmoduleBasis`, `OAI.Erdos3.chosenBoundedSubmoduleBasis_height`, `OAI.Erdos3.clearedMatrix_real`, `OAI.Erdos3.cleared_image_section_entry_bound`, `OAI.Erdos3.complementaryPeriod`, `OAI.Erdos3.complementaryPeriod_le_product`, `OAI.Erdos3.coordinateArraySpan`, `OAI.Erdos3.dependentCoordinateBudget`, `OAI.Erdos3.dependentCoordinateBudget_nonneg`, `OAI.Erdos3.dependentQuotientHeight_le_exp`, `OAI.Erdos3.euclideanDualLattice`, `OAI.Erdos3.euclideanDualLattice_discrete`, `OAI.Erdos3.euclideanDualLattice_eq_span`, `OAI.Erdos3.euclideanDualLattice_eq_span_dualBasis`, `OAI.Erdos3.euclideanDualLattice_isZLattice`, `OAI.Erdos3.euclideanSubspace`, `OAI.Erdos3.euclideanSubspaceArrayEquiv`, `OAI.Erdos3.euclideanSubspaceArrayEquiv_apply`, `OAI.Erdos3.euclideanSubspaceArrayEquiv_map_lattice`, `OAI.Erdos3.euclideanSubspaceArrayEquiv_mem_lattice`, `OAI.Erdos3.euclideanSubspaceLattice_closed`, `OAI.Erdos3.euclideanSubspaceLattice_discrete`, `OAI.Erdos3.euclideanSubspaceTorusEquiv`, `OAI.Erdos3.euclideanSubspaceTorusEquiv_continuous`, `OAI.Erdos3.euclideanSubspaceTorusEquiv_mk`, `OAI.Erdos3.euclideanSubspaceTorusEquiv_symm_continuous`, `OAI.Erdos3.euclideanSubspaceTorusHomeomorph`, `OAI.Erdos3.exists_anchored_sparse_corrections`, `OAI.Erdos3.exists_anchored_sparse_family`, `OAI.Erdos3.exists_bounded_common_site_residual`, `OAI.Erdos3.exists_bounded_functional_extension`, `OAI.Erdos3.exists_bounded_functional_preserving_subspace`, `OAI.Erdos3.exists_bounded_integer_site_residual`, `OAI.Erdos3.exists_bounded_linear_retraction`, `OAI.Erdos3.exists_bounded_quotient_functional`, `OAI.Erdos3.exists_bounded_rank_quotient_data`, `OAI.Erdos3.exists_bounded_sparse_generators`, `OAI.Erdos3.exists_bounded_submodule_ambient_spanning`, `OAI.Erdos3.exists_bounded_submodule_basis_from_spanning`, `OAI.Erdos3.exists_bounded_submodule_quotient_basis`, `OAI.Erdos3.exists_coordinate_intersection_corrections`, `OAI.Erdos3.exists_denseSliceThreshold`, `OAI.Erdos3.exists_dependent_coordinate_basis`, `OAI.Erdos3.exists_dependent_coordinate_corrections`, `OAI.Erdos3.exists_homogeneousIntersection_basis`, `OAI.Erdos3.exists_orthogonal_lattice_split_basis`, `OAI.Erdos3.exists_preimage_basis_logHeight`, `OAI.Erdos3.exists_quotient_functional_preserving_subspace`, `OAI.Erdos3.exists_relative_finite_returned_fiber_normalization`, `OAI.Erdos3.exists_slicedGridParameters`, `OAI.Erdos3.exists_sparse_coordinate_corrections`, `OAI.Erdos3.exists_sparse_generators_exp_height`, `OAI.Erdos3.exists_stepDrop_basis_exp_height`, `OAI.Erdos3.exists_stepDrop_basis_uniform_budget`, `OAI.Erdos3.exists_stepDrop_bounded_basis`, `OAI.Erdos3.exists_submodule_intersection_basis_logHeight`, `OAI.Erdos3.exists_submodule_quotient_basis_exp`, `OAI.Erdos3.exists_uniform_slicedGridParameters`, `OAI.Erdos3.finiteSitePhaseRemoval_of_annihilates`, `OAI.Erdos3.finiteSitePhaseRemoval_polynomial`, `OAI.Erdos3.finite_card_heightBoundedLieSubalgebras`, `OAI.Erdos3.finite_card_heightBoundedSubspaces`, `OAI.Erdos3.fixedKernelInverseBound`, `OAI.Erdos3.formalBracketMatrixHeight`, `OAI.Erdos3.formalCurrentMatrixHeight`, `OAI.Erdos3.formalGeometryHeight`, `OAI.Erdos3.fourCoordinateKernel`, `OAI.Erdos3.fourDependentProjection`, `OAI.Erdos3.fourDependentProjection_le`, `OAI.Erdos3.fourDependentProjection_map`, `OAI.Erdos3.fourFirstProjection`, `OAI.Erdos3.fourFirstProjection_map`, `OAI.Erdos3.fourLinearMap`, `OAI.Erdos3.fourSparseFirstProjection`, `OAI.Erdos3.fourSparseFirstProjection_le`, `OAI.Erdos3.fourSparseFirstProjection_map`, `OAI.Erdos3.four_dependent_inputs_vanish`, `OAI.Erdos3.four_sparse_lifts_vanish`, `OAI.Erdos3.fullShiftExponent_multinomial`, `OAI.Erdos3.full_coefficient_linear_pow`, `OAI.Erdos3.groupedSiteApprox`, `OAI.Erdos3.groupedSiteCoefficient`, `OAI.Erdos3.groupedSiteFactor`, `OAI.Erdos3.heightBoundedLieSubalgebras`, `OAI.Erdos3.heightBoundedSubspaces`, `OAI.Erdos3.heterogeneousSamplerSides`, `OAI.Erdos3.heterogeneousSamplerSides_integer_principal`, `OAI.Erdos3.heterogeneousSamplerSides_le`, `OAI.Erdos3.heterogeneousSamplerSides_pos`, `OAI.Erdos3.homogeneousComponent_conditionPolynomial_top`, `OAI.Erdos3.homogeneousComponent_killCompl`, `OAI.Erdos3.homogeneousComponent_polynomialTranslate_top`, `OAI.Erdos3.homogeneousComponent_restricted_translate_top`, `OAI.Erdos3.homogeneousIntersection`, `OAI.Erdos3.homogeneousIntersectionBasisHeight`, `OAI.Erdos3.homogeneousIntersectionSystem`, `OAI.Erdos3.homogeneousIntersectionSystem_basis_height`, `OAI.Erdos3.homogeneousIntersectionSystem_ker`, `OAI.Erdos3.homogeneousIntersection_baseChange`, `OAI.Erdos3.homogeneousIntersection_finrank_le`, `OAI.Erdos3.integerBasisOfReal`, `OAI.Erdos3.integerBasisOfReal_apply`, `OAI.Erdos3.integerBasisOfReal_synthesis`, `OAI.Erdos3.integerMatrixTorusMap`, `OAI.Erdos3.integerMatrixTorusMap_mk`, `OAI.Erdos3.integerMatrix_preserves_array_lattice`, `OAI.Erdos3.kernelRankBlock`, `OAI.Erdos3.kernelRankBlockEmbedding`, `OAI.Erdos3.kernelRankBlockEmbedding_apply`, `OAI.Erdos3.kernelRankCoefficientSlot`, `OAI.Erdos3.kernelRankCoefficientSlot_apply`, `OAI.Erdos3.kernelRankCoefficientSlot_degree`, `OAI.Erdos3.kernelRankCoefficientSlot_eq_block_sum`, `OAI.Erdos3.kernelRankCoefficientSlot_injective`, `OAI.Erdos3.kernelRankCoefficientSlot_monomial`, `OAI.Erdos3.latticeBasisEquiv`, `OAI.Erdos3.latticeBasisEquiv_coordinates`, `OAI.Erdos3.latticeBasisEquiv_synthesis`, `OAI.Erdos3.latticeDualBasis`, `OAI.Erdos3.latticeDualEquiv`, `OAI.Erdos3.latticeDualEquiv_coe`, `OAI.Erdos3.latticeDualPoint`, `OAI.Erdos3.latticeDualPoint_injective`, `OAI.Erdos3.latticeDualPoint_mem`, `OAI.Erdos3.latticeDualPoint_neg`, `OAI.Erdos3.latticeDualPoint_surjective`, `OAI.Erdos3.latticeIntegerLift`, `OAI.Erdos3.latticeIntegerLift_projection`, `OAI.Erdos3.latticeLiftSection`, `OAI.Erdos3.latticeLiftSection_rightInverse`, `OAI.Erdos3.latticeSection`, `OAI.Erdos3.latticeSection_discrete`, `OAI.Erdos3.latticeSheetPoint`, `OAI.Erdos3.latticeSheetPoint_projection`, `OAI.Erdos3.latticeSheetPoint_projection_orthogonal`, `OAI.Erdos3.latticeSheetPoint_reconstruction`, `OAI.Erdos3.latticeSheetPoint_sub_mem_of_quotient_eq`, `OAI.Erdos3.latticeSheetQuotient`, `OAI.Erdos3.latticeSheetQuotient_injective_on_region`, `OAI.Erdos3.latticeSignedCoordinates`, `OAI.Erdos3.layerKernelIndexBound`, `OAI.Erdos3.layerKernelIndexBound_le_exp`, `OAI.Erdos3.linear_pow_totalDegree_le`, `OAI.Erdos3.linear_power_full_difference`, `OAI.Erdos3.linear_power_full_difference_algebra`, `OAI.Erdos3.matrixModuleAction_cleared`, `OAI.Erdos3.matrixModuleAction_int_smul`, `OAI.Erdos3.mem_euclideanDualLattice`, `OAI.Erdos3.mem_fourCoordinateKernel`, `OAI.Erdos3.mem_fourFirstProjection`, `OAI.Erdos3.mem_fourSparseFirstProjection`, `OAI.Erdos3.mem_heightBoundedSubspaces`, `OAI.Erdos3.mem_homogeneousIntersection`, `OAI.Erdos3.mem_realSparseFirstProjection_of_zero`, `OAI.Erdos3.mem_standardEuclideanLattice`, `OAI.Erdos3.mem_stepDropSubmodule`, `OAI.Erdos3.normalizedCoveredReference`, `OAI.Erdos3.normalizedLatticeSheet_point`, `OAI.Erdos3.orthogonalLatticeImage`, `OAI.Erdos3.orthogonalLatticeImage_discrete`, `OAI.Erdos3.orthogonalLatticeImage_full`, `OAI.Erdos3.orthogonalLatticeImage_le_dual_section`, `OAI.Erdos3.orthogonalLatticeKernelEquiv`, `OAI.Erdos3.orthogonalLatticeProjection`, `OAI.Erdos3.orthogonalLatticeProjection_surjective`, `OAI.Erdos3.orthogonalSectionKernelEquiv`, `OAI.Erdos3.period_mul_complementary`, `OAI.Erdos3.polynomialTopSymbol_add`, `OAI.Erdos3.polynomialTopSymbol_add_lower`, `OAI.Erdos3.polynomialTopSymbol_eq_zero_of_degree_lt`, `OAI.Erdos3.preimageBasisBudget`, `OAI.Erdos3.preimageBasisBudget_nonneg`, `OAI.Erdos3.principalCoefficientSlot_eq_block_sum`, `OAI.Erdos3.principalCoefficientSlot_monomial`, `OAI.Erdos3.projectedLatticeLift`, `OAI.Erdos3.projectedLatticeLift_projection`, `OAI.Erdos3.projectedLatticeShift`, `OAI.Erdos3.rankQuotientFrequencyHeight`, `OAI.Erdos3.rankQuotientHeight`, `OAI.Erdos3.rankQuotientHeight_le_exp`, `OAI.Erdos3.rankQuotientLayerHeight`, `OAI.Erdos3.realInner_nondegenerate`, `OAI.Erdos3.realRationalCoordinateSpan_inf`, `OAI.Erdos3.real_fourCoordinateKernel_mem_iff`, `OAI.Erdos3.rightLieLinear`, `OAI.Erdos3.rightLieLinear_apply`, `OAI.Erdos3.rightLieLinear_baseChange`, `OAI.Erdos3.rowPolynomial_homogeneous`, `OAI.Erdos3.row_polynomial_site_cauchySchwarz`, `OAI.Erdos3.samplerLongEmbedding`, `OAI.Erdos3.samplerLongEmbedding_common`, `OAI.Erdos3.samplerLongEmbedding_dedicated`, `OAI.Erdos3.samplerLongEmbedding_principalExponent`, `OAI.Erdos3.samplerLong_killCompl_principal_monomial`, `OAI.Erdos3.scaledLinearResidual`, `OAI.Erdos3.scaledLinearResidual_apply`, `OAI.Erdos3.scaledLinearResidual_evaluation`, `OAI.Erdos3.scaledLinearResidual_factor_iff`, `OAI.Erdos3.scaledSiteResidual_preserves_lattice`, `OAI.Erdos3.sparseGeneratorBudget`, `OAI.Erdos3.sparseGeneratorBudget_nonneg`, `OAI.Erdos3.sparseGeneratorHeight_bound`, `OAI.Erdos3.standardEuclideanEquiv`, `OAI.Erdos3.standardEuclideanLattice`, `OAI.Erdos3.standardEuclideanLattice_discrete`, `OAI.Erdos3.standardEuclideanLattice_full`, `OAI.Erdos3.standardEuclideanLattice_self_dual`, `OAI.Erdos3.standardEuclideanLinearEquiv`, `OAI.Erdos3.standardEuclideanPoint`, `OAI.Erdos3.standardEuclideanPoint_apply`, `OAI.Erdos3.standardEuclideanPoint_bijective`, `OAI.Erdos3.standardLatticeSmallBox`, `OAI.Erdos3.standardLatticeSmallBox_isOpen`, `OAI.Erdos3.standardLatticeSmallBox_separates`, `OAI.Erdos3.stepDropBracketHeight`, `OAI.Erdos3.stepDropBracketHeight_le_exp`, `OAI.Erdos3.stepDropBracketKernel`, `OAI.Erdos3.stepDropBracketKernel_baseChange`, `OAI.Erdos3.stepDropBracketKernel_eq_iInf`, `OAI.Erdos3.stepDropSubalgebra`, `OAI.Erdos3.stepDropSubmodule`, `OAI.Erdos3.stepDropSubmodule_baseChange`, `OAI.Erdos3.stepDropSubmodule_graded`, `OAI.Erdos3.stepDropSubmodule_lie_mem`, `OAI.Erdos3.stepDropSubmodule_mem_higher_grade`, `OAI.Erdos3.stepDropSubmodule_top_frequency`, `OAI.Erdos3.stepDropSystem`, `OAI.Erdos3.stepDropSystem_basis_height`, `OAI.Erdos3.stepDropSystem_ker`, `OAI.Erdos3.stepDrop_basis_height_budget`, `OAI.Erdos3.stepDrop_bracket_height`, `OAI.Erdos3.stepDrop_quotient_mem_iff`, `OAI.Erdos3.subspaceAmbientTorus`, `OAI.Erdos3.subspaceAmbientTorus_continuous`, `OAI.Erdos3.subspaceAmbientTorus_mk`, `OAI.Erdos3.subspaceArrayCharacter`, `OAI.Erdos3.subspaceArrayFunctional_integral`, `OAI.Erdos3.subspaceArrayIntegerLattice`, `OAI.Erdos3.unitSubspaceCoordinate`, `OAI.Erdos3.vectorIntervalSiteWeight`, `OAI.Erdos3.vectorIntervalSiteWeight_bound`, `OAI.Erdos3.vectorIntervalSiteWeight_lipschitz`, `OAI.Erdos3.vectorResidueSiteWeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
namespace OAI

section

namespace Erdos3

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def fourCoordinateKernel (S : Finset (Fin 4)) : Submodule ℚ (Fin 4 → V) :=
  ⨅ k ∈ S, LinearMap.ker (LinearMap.proj k)

theorem mem_fourCoordinateKernel (S : Finset (Fin 4)) (v : Fin 4 → V) :
    v ∈ fourCoordinateKernel S ↔ ∀ k ∈ S, v k = 0 := by
  simp [fourCoordinateKernel]

def fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  J.map (LinearMap.proj 0)

theorem mem_fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) (v : V) :
    v ∈ fourFirstProjection J ↔ ∃ w ∈ J, w 0 = v := Iff.rfl

def fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) : Submodule ℚ V :=
  (J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)

theorem mem_fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V))
    (S : Finset (Fin 4)) (v : V) :
    v ∈ fourSparseFirstProjection J S ↔ ∃ w ∈ J, w 0 = v ∧ ∀ k ∈ S, w k = 0 := by
  change (∃ w, w ∈ J ⊓ fourCoordinateKernel S ∧ w 0 = v) ↔ _
  constructor
  · rintro ⟨w, ⟨hw, hS⟩, hv⟩
    exact ⟨w, hw, hv, (mem_fourCoordinateKernel S w).mp hS⟩
  · rintro ⟨w, hw, hv, hS⟩
    exact ⟨w, ⟨hw, (mem_fourCoordinateKernel S w).mpr hS⟩, hv⟩

theorem fourSparseFirstProjection_le (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection J S ≤ fourFirstProjection J :=
  Submodule.map_mono inf_le_left

def fourDependentProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  fourSparseFirstProjection J {1, 2} ⊓ fourSparseFirstProjection J {1, 3}

theorem fourDependentProjection_le (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection J ≤ fourFirstProjection J :=
  inf_le_left.trans (fourSparseFirstProjection_le J {1, 2})

end Erdos3

end

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def fourLinearMap (f : V →ₗ[ℚ] W) : (Fin 4 → V) →ₗ[ℚ] (Fin 4 → W) :=
  LinearMap.pi (fun k => f.comp (LinearMap.proj k))

theorem fourFirstProjection_map (f : V →ₗ[ℚ] W) (J : Submodule ℚ (Fin 4 → V)) :
    fourFirstProjection (J.map (fourLinearMap f)) = (fourFirstProjection J).map f := by
  ext y
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl⟩

theorem fourSparseFirstProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection (J.map (fourLinearMap f)) S = (fourSparseFirstProjection J S).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, ⟨v, hv, rfl⟩, hzero, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hy
    refine ⟨v 0, (mem_fourSparseFirstProjection _ _ _).mpr ⟨v, hv, rfl, ?_⟩, hzero⟩
    intro k hk
    exact hf ((hS k hk).trans (map_zero f).symm)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hx
    refine (mem_fourSparseFirstProjection _ _ _).mpr
      ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl, ?_⟩
    intro k hk
    change f (v k) = 0
    rw [hS k hk, map_zero]

theorem fourDependentProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection (J.map (fourLinearMap f)) = (fourDependentProjection J).map f := by
  rw [fourDependentProjection, fourSparseFirstProjection_map f hf, fourSparseFirstProjection_map f hf]
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := hf (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
  · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hz, rfl⟩⟩

end Erdos3

end

section

namespace Erdos3

theorem four_sparse_lifts_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourSparseFirstProjection (J a) {1, 2})
    (hvb : v b ∈ fourSparseFirstProjection (J b) {1, 3}) : η (B v) = 0 := by
  classical
  have hlift (i : I) : ∃ w ∈ J i, w 0 = v i := (mem_fourFirstProjection (J i) (v i)).mp (hv i)
  choose w hwJ hw0 using hlift
  obtain ⟨xa, hxa, hxa0, hxaz⟩ := (mem_fourSparseFirstProjection (J a) {1, 2} (v a)).mp hva
  obtain ⟨xb, hxb, hxb0, hxbz⟩ := (mem_fourSparseFirstProjection (J b) {1, 3} (v b)).mp hvb
  let z : ∀ i, Fin 4 → V i := Function.update (Function.update w a xa) b xb
  have hza : z a = xa := by simp [z, hab]
  have hzb : z b = xb := by simp [z]
  have hzJ (i : I) : z i ∈ J i := by
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hwJ i
  have hzfirst : (fun i => z i 0) = v := by
    funext i
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb0
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa0
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hw0 i
  have hz1 : B (fun i => z i 1) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 1 (by simp))
  have hz2 : B (fun i => z i 2) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 2 (by simp))
  have hz3 : B (fun i => z i 3) = 0 := hzero _ b hb (by rw [hzb]; exact hxbz 3 (by simp))
  have h := hJ z hzJ
  simpa only [hzfirst, hz1, hz2, hz3, hη, add_zero, sub_zero] using h

theorem four_dependent_inputs_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourDependentProjection (J a))
    (hvb : v b ∈ fourDependentProjection (J b)) : η (B v) = 0 :=
  four_sparse_lifts_vanish S B hzero η hη J hJ v hv a b hab ha hb hva.1 hvb.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSparseGenerators
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bounded_sparse_generators
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (Σ _ : K, ι) ∧ ∃ w : κ → ι → ℚ,
      Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
      ∀ a i, RationalHeightLE (w a i)
        ((Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ) := by
  let P : (Fin 4 → ι → ℚ) →ₗ[ℚ] ((Σ _ : K, ι) → ℚ) := {
    toFun := fun x j => x j.1 j.2
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker P = fourCoordinateKernel K := by
    ext x
    rw [LinearMap.mem_ker, mem_fourCoordinateKernel]
    constructor
    · intro hx k hk
      funext i
      exact congrFun hx ⟨⟨k, hk⟩, i⟩
    · intro hx
      funext j
      exact congrFun (hx j.1 j.1.property) j.2
  obtain ⟨r, hr, z, hz, hzH⟩ := exists_bounded_span_kernel_generators
    (Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)) (Pi.basisFun ℚ (Σ _ : K, ι)) P v hH
    (fun a j => by simpa only [Pi.basis_repr, Pi.basisFun_repr] using hvH a j.1 j.2)
    (fun a j => hvH a j.1 j.2)
  refine ⟨r, hr, fun a => z a 0, ?_, ?_⟩
  · change Submodule.span ℚ (Set.range (fun a => z a 0)) =
      (J ⊓ fourCoordinateKernel K).map (LinearMap.proj 0)
    rw [← hv, ← hker, ← hz, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro a i
    simpa only [Pi.basis_repr, Pi.basisFun_repr] using hzH a ⟨0, i⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
namespace OAI

section

namespace Erdos3

noncomputable def sparseGeneratorBudget (p : ℝ) : ℝ := p + p * ((p + 2) ^ 7 + p)

theorem sparseGeneratorBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ sparseGeneratorBudget p := by
  unfold sparseGeneratorBudget
  positivity

theorem sparseGeneratorHeight_bound {p : ℝ} (hp : 0 ≤ p) (r n H : ℕ)
    (hr : (r : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalKernelHeight r H * H) ^ n : ℕ) : ℝ) ≤
      Real.exp (sparseGeneratorBudget p) := by
  have hfront : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn le_rfl).trans (Real.add_one_le_exp p)
  have hbase : (rationalKernelHeight r H : ℝ) * H ≤ Real.exp ((p + 2) ^ 7 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul (rationalKernelHeight_le_budget r H hp hr hH) hH
      (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (rationalKernelHeight r H : ℝ) * H) hbase n
  rw [← Real.exp_nat_mul] at hpower
  push_cast
  calc
    ((n : ℝ) + 1) * ((rationalKernelHeight r H : ℝ) * H) ^ n ≤
        Real.exp p * Real.exp ((n : ℝ) * ((p + 2) ^ 7 + p)) :=
      mul_le_mul hfront hpower (by positivity) (Real.exp_pos _).le
    _ = Real.exp (p + (n : ℝ) * ((p + 2) ^ 7 + p)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (sparseGeneratorBudget p) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hn (by positivity))

theorem exists_sparse_generators_exp_height
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ Real.exp (sparseGeneratorBudget p) ∧
      ∃ w : κ → ι → ℚ, Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
        ∀ a i, RationalHeightLE (w a i) M := by
  obtain ⟨r, hr, w, hw, hwH⟩ := exists_bounded_sparse_generators J K v hv hH hvH
  refine ⟨(Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ, ?_,
    sparseGeneratorHeight_bound hp r (Fintype.card κ) H
      ((Nat.cast_le.mpr hr).trans hrows) hcols hHp, w, hw, hwH⟩
  have hkernel := rationalKernelHeight_pos r hH
  exact Nat.mul_pos (Nat.zero_lt_succ _) (pow_pos (Nat.mul_pos hkernel hH) _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealSparseFourProjection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι : Type*} [Fintype ι]

theorem real_fourCoordinateKernel_mem_iff (S : Finset (Fin 4))
    (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) :
    x ∈ (fourCoordinateKernel (V := ι → ℚ) S).baseChange ℝ ↔
      ∀ k ∈ S, ∀ i, DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ = 0 := by
  have hker : fourCoordinateKernel (V := ι → ℚ) S =
      ⨅ k : S, LinearMap.ker (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)) := by
    ext v
    constructor
    · intro hv
      apply (Submodule.mem_iInf _).mpr
      intro k
      exact (mem_fourCoordinateKernel S v).mp hv k k.property
    · intro hv
      apply (mem_fourCoordinateKernel S v).mpr
      intro k hk
      exact (Submodule.mem_iInf _).mp hv ⟨k, hk⟩
  rw [hker, real_baseChange_iInf]
  constructor
  · intro hx k hk i
    have hz := (Submodule.mem_iInf _).mp hx ⟨k, hk⟩
    rw [realification_ker] at hz
    have hzero : (LinearMap.proj k : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0 := hz
    rw [← realCoordinate_projection]
    simpa only [map_zero, Pi.zero_apply] using
      congrFun (congrArg realRationalCoordinateEquiv hzero) i
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro k
    rw [realification_ker]
    change (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0
    apply realRationalCoordinateEquiv.injective
    funext i
    simpa only [map_zero, Pi.zero_apply, realCoordinate_projection] using hx k k.property i

theorem mem_realSparseFirstProjection_of_zero
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (S : Finset (Fin 4))
    (y : (Σ _ : Fin 4, ι) → ℝ) (hy : y ∈ realFourCoordinateSpan J)
    (hzero : ∀ k ∈ S, ∀ i, y ⟨k, i⟩ = 0) :
    (fun i => y ⟨0, i⟩) ∈ realRationalCoordinateSpan (fourSparseFirstProjection J S) := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hxK := (real_fourCoordinateKernel_mem_iff S x).mpr hzero
  have hxJK : x ∈ (J ⊓ fourCoordinateKernel S).baseChange ℝ := by
    rw [realification_inf]
    exact ⟨hx, hxK⟩
  have hproj : (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈
      (fourSparseFirstProjection J S).baseChange ℝ := by
    change _ ∈ ((J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)).baseChange ℝ
    rw [realification_map]
    exact ⟨x, hxJK, rfl⟩
  have hmem : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) ∈
      realRationalCoordinateSpan (fourSparseFirstProjection J S) := ⟨_, hproj, rfl⟩
  have heq : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) =
      fun i => DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨0, i⟩ := by
    funext i
    exact realCoordinate_projection x 0 i
  rwa [heq] at hmem

theorem realRationalCoordinateSpan_inf (U V : Submodule ℚ (ι → ℚ)) :
    realRationalCoordinateSpan (U ⊓ V) =
      realRationalCoordinateSpan U ⊓ realRationalCoordinateSpan V := by
  unfold realRationalCoordinateSpan
  rw [realification_inf]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hv, rfl⟩⟩
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := realRationalCoordinateEquiv.injective (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SparseCoordinateCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_sparse_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (a b : (Σ _ : K, ι) → ℝ) (x : (Σ _ : Fin 4, ι) → ℝ),
        x ∈ realFourCoordinateSpan J →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ j : Σ _ : K, ι, x ⟨j.1, j.2⟩ = a j + b j) →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          e ∈ realFourCoordinateSpan J ∧ q ∈ realFourCoordinateSpan J ∧
          (∀ j : Σ _ : K, ι, e ⟨j.1, j.2⟩ = a j) ∧
          (∀ j : Σ _ : K, ι, q ⟨j.1, j.2⟩ = b j) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          x - e - q ∈ realFourCoordinateSpan J ∧
          (fun i => (x - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  let A : Matrix (Σ _ : Fin 4, ι) κ ℚ := fun j a => v a j.1 j.2
  let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  have hspan : realFourCoordinateSpan J =
      LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    ext x
    rw [← hv, realFourCoordinateSpan_span]
    exact real_column_span_mem_iff A x
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_selected_image_corrections A ρ hH hl
    (fun i a => hvH a i.1 i.2) hp hι hK hκ hHp hlp T hT
  refine ⟨m, hm, hmp, ?_⟩
  intro α hα a b x hx ha hb hselect
  obtain ⟨he, hq, heq, hqq, hslow, hgrid, hrem, hzero⟩ :=
    hsolve α hα a b x (hspan ▸ hx) ha hb hselect
  refine ⟨_, _, hspan.symm ▸ he, hspan.symm ▸ hq, heq, hqq, hslow, hgrid,
    hspan.symm ▸ hrem, ?_⟩
  apply mem_realSparseFirstProjection_of_zero J K _ (hspan.symm ▸ hrem)
  intro k hk i
  exact hzero ⟨⟨k, hk⟩, i⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredSparseFamilies
namespace OAI

section

namespace Erdos3

theorem exists_anchored_sparse_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u u₀ E E₀ Q Q₀ : (Σ _ : Fin 4, ι) → ℝ),
        u - E - Q ∈ realFourCoordinateSpan J →
        u₀ - E₀ - Q₀ ∈ realFourCoordinateSpan J →
        (∀ j : Σ _ : K, ι, u ⟨j.1, j.2⟩ = u₀ ⟨j.1, j.2⟩) →
        ‖E - E₀‖ ≤ Real.exp p / monomialScale T α →
        Q ∈ realDenominatorGrid l → Q₀ ∈ realDenominatorGrid l →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          (fun i => (u - u₀ - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hsolve⟩ := exists_sparse_coordinate_corrections J K v hv hH hl hvH
    hp hι hK hκ hHp hlp T hT
  refine ⟨l * m, Nat.mul_pos hl hm, ?_, dvd_mul_right l m, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα u u₀ E E₀ Q Q₀ hu hu₀ hanchor hE hQ hQ₀
    let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
    let x := (u - E - Q) - (u₀ - E₀ - Q₀)
    let a := (E₀ - E) ∘ ρ
    let b := (Q₀ - Q) ∘ ρ
    have hx : x ∈ realFourCoordinateSpan J := Submodule.sub_mem _ hu hu₀
    have ha : ‖a‖ ≤ Real.exp p / monomialScale T α := by
      apply (pi_norm_restriction_le (E₀ - E) ρ).trans
      simpa only [norm_sub_rev] using hE
    have hb : b ∈ realDenominatorGrid l :=
      realDenominatorGrid_comp l _ (realDenominatorGrid_sub l Q₀ Q hQ₀ hQ) ρ
    have hselect (j : Σ _ : K, ι) : x ⟨j.1, j.2⟩ = a j + b j := by
      change (u ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩) -
        (u₀ ⟨j.1, j.2⟩ - E₀ ⟨j.1, j.2⟩ - Q₀ ⟨j.1, j.2⟩) =
        (E₀ ⟨j.1, j.2⟩ - E ⟨j.1, j.2⟩) + (Q₀ ⟨j.1, j.2⟩ - Q ⟨j.1, j.2⟩)
      rw [hanchor j]
      ring
    obtain ⟨e, q, _, _, _, _, he, hq, _, hrem⟩ := hsolve α hα a b x hx ha hb hselect
    refine ⟨E - E₀ + e, Q - Q₀ + q, ?_, ?_, ?_⟩
    · calc
        ‖E - E₀ + e‖ ≤ ‖E - E₀‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Real.exp p / monomialScale T α +
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α :=
          add_le_add hE he
        _ = _ := (add_div _ _ _).symm
    · simpa only [sub_neg_eq_add] using realDenominatorGrid_sub_product l m
        (Q - Q₀) (-q) (realDenominatorGrid_sub l Q Q₀ hQ hQ₀) (realDenominatorGrid_neg m hq)
    · have heq : u - u₀ - (E - E₀ + e) - (Q - Q₀ + q) = x - e - q := by
        funext j
        change u j - u₀ j - (E j - E₀ j + e j) - (Q j - Q₀ j + q j) =
          ((u j - E j - Q j) - (u₀ j - E₀ j - Q₀ j)) - e j - q j
        ring
      simpa only [heq] using hrem

end Erdos3

end

section

namespace Erdos3

theorem exists_anchored_sparse_family
    {ι κ σ η : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p) (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (u : η → (Σ _ : Fin 4, ι) → ℝ) (β : η → ι → ℝ) (a₀ : η) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ a i, u a ⟨0, i⟩ = β a i) →
        (∀ a (j : Σ _ : K, ι), u a ⟨j.1, j.2⟩ = u a₀ ⟨j.1, j.2⟩) →
        (∀ a, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          u a - E - Q ∈ realFourCoordinateSpan J) →
        ∀ a, ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β a - β a₀ - e - q ∈ realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_anchored_sparse_corrections J K v hv hH hl hvH
    hp hfour hK hcols hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα u β a₀ M hM hfirst hanchor hcorrect a
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hu₀⟩ := hcorrect a₀
  obtain ⟨E, Q, hE, hQ, hu⟩ := hcorrect a
  have hscale : 0 < monomialScale T α :=
    monomialScale_pos T (fun i => (Real.exp_pos _).trans_le (hT i)) α
  have hdiff : ‖E - E₀‖ ≤ Real.exp p / monomialScale T α := by
    calc
      ‖E - E₀‖ ≤ ‖E‖ + ‖E₀‖ := norm_sub_le _ _
      _ ≤ M / monomialScale T α + M / monomialScale T α := add_le_add hE hE₀
      _ = (2 * M) / monomialScale T α := by ring
      _ ≤ Real.exp p / monomialScale T α := div_le_div_of_nonneg_right hM hscale.le
  obtain ⟨e, q, he, hq, hrem⟩ :=
    hsolve α hα (u a) (u a₀) E E₀ Q Q₀ hu hu₀ (hanchor a) hdiff hQ hQ₀
  refine ⟨(fun i => e ⟨0, i⟩), (fun i => q ⟨0, i⟩),
    (pi_norm_restriction_le e (fun i => ⟨0, i⟩)).trans he,
    realDenominatorGrid_comp m q hq (fun i => ⟨0, i⟩), ?_⟩
  have heq : (fun i => (u a - u a₀ - e - q) ⟨0, i⟩) =
      β a - β a₀ - (fun i => e ⟨0, i⟩) - (fun i => q ⟨0, i⟩) := by
    funext i
    simp only [Pi.sub_apply, hfirst]
  rwa [heq] at hrem

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedAmbientModeWitness
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_ambient_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : VectorPolynomial (Option K) ℝ (J → ℝ) →ₗ[ℝ] ℝ) (h : ℕ)
    (hbound : VectorPolynomial.MonomialRowBound Λ h C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        Λ (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |VectorPolynomial.contractedRow Λ (map (Int.castRingHom ℝ) (∏ i, P i)) j| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, VectorPolynomial.contractedRow Λ
        (map (Int.castRingHom ℝ) (∏ i, P i)) j * w.val j) ≠ 0 := by
  obtain ⟨selection, hdet⟩ := integer_difference_exists_pivot difference hlin
  obtain ⟨forms, hlen, hforms, hz, w, hw⟩ := exists_integral_vector_mode_witness
    root difference selection hdet hH hD hroot hdiff
    (Λ.comp (VectorPolynomial.map W.subtype)) h hnonfactor
  simp only [Fintype.card_fin] at hforms
  subst h
  let P : Fin forms.length → MvPolynomial (Option K) ℤ := forms.get
  have hmem (i : Fin forms.length) : P i ∈ forms := List.get_mem _ _
  have hprod : (∏ i, P i) = forms.prod := by
    rw [← Fin.prod_ofFn, List.ofFn_get]
  refine ⟨P, (fun i => hforms _ (hmem i)), ?_, ?_, w, ?_⟩
  · intro s
    exact List.exists_mem_iff_get.mp (hz s)
  · intro j
    rw [map_prod]
    exact VectorPolynomial.contractedRow_prod_bound Λ
      (fun i => map (Int.castRingHom ℝ) (P i))
      (fun i => (hforms _ (hmem i)).1.map _) (fun i => (hforms _ (hmem i)).2) hC hbound j
  · rw [VectorPolynomial.contractedRow_apply, hprod]
    exact hw

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledLinearResidual
namespace OAI

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

noncomputable def scaledLinearResidual (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) :
    V →ₗ[ℝ] V := q • LinearMap.id - T.comp E

theorem scaledLinearResidual_apply (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) (x : V) :
    scaledLinearResidual E T q x = q • x - T (E x) := rfl

theorem scaledLinearResidual_evaluation (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ)
    (hT : ∀ x, E (T (E x)) = q • E x) (x : V) :
    E (scaledLinearResidual E T q x) = 0 := by
  rw [scaledLinearResidual_apply, map_sub, map_smul, hT, sub_self]

theorem scaledLinearResidual_factor_iff (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V)
    {q : ℝ} (hq : q ≠ 0) (hT : ∀ x, E (T (E x)) = q • E x) (L : V →ₗ[ℝ] ℝ) :
    L.comp (scaledLinearResidual E T q) = 0 ↔ ∃ M : W →ₗ[ℝ] ℝ, L = M.comp E := by
  constructor
  · intro h
    refine ⟨q⁻¹ • L.comp T, ?_⟩
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [LinearMap.comp_apply, scaledLinearResidual_apply, map_sub, map_smul,
      smul_eq_mul, LinearMap.zero_apply, sub_eq_zero] at hx
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hx, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  · rintro ⟨M, rfl⟩
    ext x
    simp only [LinearMap.comp_apply, scaledLinearResidual_evaluation E T q hT,
      map_zero, LinearMap.zero_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisSurjectionSection
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F]

noncomputable def basisSurjectionSection (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) : F →ₗ[R] E :=
  b.constr R (fun i => (hq (b i)).choose)

theorem basisSurjectionSection_rightInverse (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) (x : F) : q (basisSurjectionSection q hq b x) = x := by
  have he : q.comp (basisSurjectionSection q hq b) = LinearMap.id := by
    apply b.ext
    intro i
    change q (b.constr R (fun j => (hq (b j)).choose) (b i)) = b i
    rw [b.constr_basis]
    exact (hq (b i)).choose_spec
  exact LinearMap.congr_fun he x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeBasisEquiv (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : (I → ℤ) ≃ Λ :=
  (b.restrictScalars ℤ).equivFun.symm.toEquiv.trans
    (LinearEquiv.ofEq _ _ hb).toEquiv

theorem latticeBasisEquiv_coordinates (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) (i : I) :
    b.equivFun (latticeBasisEquiv Λ b hb z).val i = (z i : ℝ) := by
  change b.repr (((b.restrictScalars ℤ).equivFun.symm z) : E) i = _
  have h := b.restrictScalars_repr_apply ℤ ((b.restrictScalars ℤ).equivFun.symm z) i
  change (algebraMap ℤ ℝ)
    ((b.restrictScalars ℤ).equivFun ((b.restrictScalars ℤ).equivFun.symm z) i) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  simpa using h.symm

theorem latticeBasisEquiv_synthesis (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    (latticeBasisEquiv Λ b hb z).val = b.equivFun.symm (fun i => (z i : ℝ)) := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact latticeBasisEquiv_coordinates Λ b hb z i

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanDualLattice (Λ : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ

theorem mem_euclideanDualLattice (Λ : Submodule ℤ E) (ξ : E) :
    ξ ∈ euclideanDualLattice Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ) := by
  simp only [euclideanDualLattice, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, innerₗ_apply_apply]
  exact forall_congr' (fun _ => forall_congr' (fun _ => exists_congr (fun _ => eq_comm)))

theorem realInner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

variable [FiniteDimensional ℝ E]

theorem euclideanDualLattice_eq_span_dualBasis (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate
        ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ))) := by
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E) realInner_nondegenerate
    ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h

instance euclideanDualLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : DiscreteTopology (euclideanDualLattice Λ) := by
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  infer_instance

instance euclideanDualLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : IsZLattice ℝ (euclideanDualLattice Λ) := by
  constructor
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  exact IsZLattice.span_top (K := ℝ)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def latticeSection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := ZLattice.comap ℝ Λ W.subtype

instance latticeSection_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (W : Submodule ℝ E) : DiscreteTopology (latticeSection Λ W) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

noncomputable def orthogonalLatticeImage (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := Λ.map (W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

theorem orthogonalLatticeImage_le_dual_section (Λ : Submodule ℤ E)
    (W : Submodule ℝ E) :
    orthogonalLatticeImage Λ W ≤ euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_euclideanDualLattice _ _).mpr
  intro y hy
  have hy' : (y : E) ∈ euclideanDualLattice Λ := hy
  obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ y.val).mp hy' x hx
  refine ⟨n, ?_⟩
  change inner ℝ (W.orthogonalProjectionOnto x) y = (n : ℝ)
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, real_inner_comm]
  exact hn

theorem orthogonalLatticeImage_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection (euclideanDualLattice Λ) W)] :
    DiscreteTopology (orthogonalLatticeImage Λ W) := by
  have hdis : DiscreteTopology (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W)) :=
    euclideanDualLattice_discrete _
  have hd : IsDiscrete (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) : Set W) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr hdis
  exact isDiscrete_iff_discreteTopology.mp (hd.mono (orthogonalLatticeImage_le_dual_section Λ W))

theorem orthogonalLatticeImage_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E) [DiscreteTopology (orthogonalLatticeImage Λ W)] :
    IsZLattice ℝ (orthogonalLatticeImage Λ W) := by
  constructor
  change span ℝ (W.orthogonalProjectionOnto.toLinearMap '' (Λ : Set E)) = ⊤
  rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact W.starProjection_eq_self_iff.mpr w.property

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

noncomputable def standardEuclideanLattice : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)

instance standardEuclideanLattice_discrete : DiscreteTopology (standardEuclideanLattice ι) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

instance standardEuclideanLattice_full : IsZLattice ℝ (standardEuclideanLattice ι) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

theorem mem_standardEuclideanLattice (x : EuclideanSpace ℝ ι) :
    x ∈ standardEuclideanLattice ι ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  change x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) ↔ _
  rw [(EuclideanSpace.basisFun ι ℝ).toBasis.mem_span_iff_repr_mem ℤ x]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

noncomputable def standardEuclideanPoint (z : ι → ℤ) : standardEuclideanLattice ι :=
  ⟨WithLp.toLp 2 (fun i => (z i : ℝ)), (mem_standardEuclideanLattice ι _).mpr (fun i => ⟨z i, rfl⟩)⟩

@[simp]
theorem standardEuclideanPoint_apply (z : ι → ℤ) (i : ι) :
    (standardEuclideanPoint ι z : EuclideanSpace ℝ ι) i = (z i : ℝ) := rfl

theorem standardEuclideanPoint_bijective : Function.Bijective (standardEuclideanPoint ι) := by
  constructor
  · intro z w h
    funext i
    have hi := congrArg (fun x : standardEuclideanLattice ι => (x : EuclideanSpace ℝ ι) i) h
    exact Int.cast_injective (α := ℝ) hi
  · intro x
    choose z hz using (mem_standardEuclideanLattice ι (x : EuclideanSpace ℝ ι)).mp x.property
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext i
    exact hz i

noncomputable def standardEuclideanEquiv : (ι → ℤ) ≃ standardEuclideanLattice ι :=
  Equiv.ofBijective (standardEuclideanPoint ι) (standardEuclideanPoint_bijective ι)

theorem standardEuclideanLattice_self_dual :
    euclideanDualLattice (standardEuclideanLattice ι) = standardEuclideanLattice ι := by
  ext x
  rw [mem_euclideanDualLattice, mem_standardEuclideanLattice]
  constructor
  · intro hx i
    have hi : EuclideanSpace.basisFun ι ℝ i ∈ standardEuclideanLattice ι :=
      Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hx _ hi
    exact ⟨n, by simpa only [EuclideanSpace.inner_basisFun_real] using hn.symm⟩
  · intro hx y hy
    choose a ha using hx
    choose b hb using (mem_standardEuclideanLattice ι y).mp hy
    refine ⟨∑ i, a i * b i, ?_⟩
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp only [Int.cast_sum, Int.cast_mul, ha, hb]
    apply Finset.sum_congr rfl
    intro i _
    ring

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalLatticeProjection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Λ →ₗ[ℤ] orthogonalLatticeImage Λ W :=
  ((W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ).comp Λ.subtype).codRestrict
    (orthogonalLatticeImage Λ W) (fun x => ⟨x.val, x.property, rfl⟩)

theorem orthogonalLatticeProjection_surjective (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Function.Surjective (orthogonalLatticeProjection Λ W) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def orthogonalLatticeKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ Wᗮ ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ W) where
  toFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext
    (W.orthogonalProjectionOnto_eq_zero_iff.mpr x.val.property)⟩
  invFun x := ⟨⟨x.val.val, W.orthogonalProjectionOnto_eq_zero_iff.mp
    (congrArg Subtype.val (show orthogonalLatticeProjection Λ W x.val = 0 from x.property))⟩,
    x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_orthogonal_lattice_split_basis {I J : Type*}
    (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bK : Basis I ℤ (latticeSection Λ Wᗮ)) (bP : Basis J ℤ (orthogonalLatticeImage Λ W)) :
    ∃ b : Basis (I ⊕ J) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, W.orthogonalProjectionOnto (b (Sum.inr j) : E) = (bP j).val) := by
  let : Free ℤ (orthogonalLatticeImage Λ W) := Free.of_basis bP
  obtain ⟨b, hK, hP⟩ := exists_basis_of_surjection (orthogonalLatticeProjection Λ W)
    (orthogonalLatticeProjection_surjective Λ W) (bK.map (orthogonalLatticeKernelEquiv Λ W)) bP
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hK]
    rfl
  · intro j
    exact congrArg Subtype.val (hP j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integerBasisOfReal (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : Basis I ℤ Λ :=
  (b.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ hb)

theorem integerBasisOfReal_apply (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (i : I) : (integerBasisOfReal Λ b hb i).val = b i := by
  simp only [integerBasisOfReal, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply]

theorem integerBasisOfReal_synthesis [Fintype I] (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) :
    ((integerBasisOfReal Λ b hb).equivFun.symm z).val =
      b.equivFun.symm (fun i => (z i : ℝ)) := by
  simp only [integerBasisOfReal, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact latticeBasisEquiv_synthesis (span ℤ (Set.range b)) b rfl z

noncomputable def standardEuclideanLinearEquiv (J : Type*) [Fintype J] :
    (J → ℤ) ≃ₗ[ℤ] standardEuclideanLattice J :=
  ((EuclideanSpace.basisFun J ℝ).toBasis.restrictScalars ℤ).equivFun.symm

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

def standardLatticeSmallBox : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| < 1 / 2}

theorem standardLatticeSmallBox_isOpen : IsOpen (standardLatticeSmallBox J) := by
  unfold standardLatticeSmallBox
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem standardLatticeSmallBox_separates
    {x y : EuclideanSpace ℝ J} (hx : x ∈ standardLatticeSmallBox J)
    (hy : y ∈ standardLatticeSmallBox J) (hxy : x - y ∈ standardEuclideanLattice J) : x = y := by
  ext i
  obtain ⟨n, hn⟩ := (mem_standardEuclideanLattice J (x - y)).mp hxy i
  change (n : ℝ) = x i - y i at hn
  have hxi := abs_lt.mp (hx i)
  have hyi := abs_lt.mp (hy i)
  have hnlo : (-1 : ℝ) < n := by linarith
  have hnhi : (n : ℝ) < 1 := by linarith
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  exact sub_eq_zero.mp (by simpa only [hn0, Int.cast_zero] using hn.symm)

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalSectionKernelEquiv (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    latticeSection Λ W ≃ₗ[ℤ] LinearMap.ker (orthogonalLatticeProjection Λ Wᗮ) where
  toFun x := ⟨⟨x.val.val, x.property⟩,
    Subtype.ext (W.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.val.property)⟩
  invFun x := ⟨⟨x.val.val, by
    have h := Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mp
      (congrArg Subtype.val (show orthogonalLatticeProjection Λ Wᗮ x.val = 0 from x.property))
    change x.val.val ∈ Wᗮᗮ at h
    rwa [W.orthogonal_orthogonal] at h⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def latticeLiftSection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    orthogonalLatticeImage Λ Wᗮ →ₗ[ℤ] Λ :=
  basisSurjectionSection (orthogonalLatticeProjection Λ Wᗮ)
    (orthogonalLatticeProjection_surjective Λ Wᗮ) bP

theorem latticeLiftSection_rightInverse (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : orthogonalLatticeImage Λ Wᗮ) :
    orthogonalLatticeProjection Λ Wᗮ (latticeLiftSection Λ W bP x) = x :=
  basisSurjectionSection_rightInverse _ _ _ _

variable [Fintype I] [Fintype J]

noncomputable def latticeIntegerLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) : (J → ℤ) →ₗ[ℤ] Λ :=
  (latticeLiftSection Λ W bP).comp bP.equivFun.symm.toLinearMap

theorem latticeIntegerLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (z : J → ℤ) :
    Wᗮ.orthogonalProjectionOnto (latticeIntegerLift Λ W bP z).val = (bP.equivFun.symm z).val :=
  congrArg Subtype.val (latticeLiftSection_rightInverse Λ W bP (bP.equivFun.symm z))

noncomputable def latticeSignedCoordinates (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    Λ ≃ₗ[ℤ] (J → ℤ) × (I → ℤ) :=
  signedSplitCoordinates (orthogonalLatticeProjection Λ Wᗮ) (latticeLiftSection Λ W bP)
    (latticeLiftSection_rightInverse Λ W bP) (bW.map (orthogonalSectionKernelEquiv Λ W)) bP

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def projectedLatticeLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : Λ :=
  (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose

theorem projectedLatticeLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) :
    Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val = z.val :=
  congrArg Subtype.val (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose_spec

noncomputable def latticeSheetPoint (W : Submodule ℝ E) (z : Wᗮ) (u : W) : E :=
  u.val + z.val

theorem latticeSheetPoint_projection (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    W.orthogonalProjectionOnto (latticeSheetPoint W z u) = u := by
  change W.orthogonalProjectionOnto (u.val + z.val) = u
  rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal z.property, add_zero]
  exact Subtype.ext (W.starProjection_eq_self_iff.mpr u.property)

theorem latticeSheetPoint_projection_orthogonal (W : Submodule ℝ E) (z : Wᗮ) (u : W) :
    Wᗮ.orthogonalProjectionOnto (latticeSheetPoint W z u) = z := by
  change Wᗮ.orthogonalProjectionOnto (u.val + z.val) = z
  rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero u.property, zero_add]
  exact Subtype.ext (Wᗮ.starProjection_eq_self_iff.mpr z.property)

noncomputable def projectedLatticeShift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : W :=
  W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val

noncomputable def latticeSheetQuotient (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) : W ⧸ (latticeSection Λ W).toAddSubgroup :=
  QuotientAddGroup.mk (u - projectedLatticeShift Λ W z)

theorem latticeSheetPoint_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) :
    latticeSheetPoint W z.val u =
      (u - projectedLatticeShift Λ W z).val + (projectedLatticeLift Λ W z).val := by
  have hs := W.starProjection_add_starProjection_orthogonal (projectedLatticeLift Λ W z).val
  change (projectedLatticeShift Λ W z).val +
    (Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val = _ at hs
  rw [projectedLatticeLift_projection] at hs
  change u.val + z.val.val = (u.val - (projectedLatticeShift Λ W z).val) + _
  calc
    _ = (u.val - (projectedLatticeShift Λ W z).val) +
        ((projectedLatticeShift Λ W z).val + z.val.val) := by abel
    _ = _ := by rw [hs]

theorem latticeSheetPoint_sub_mem_of_quotient_eq (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) :
    latticeSheetPoint W z.val u - latticeSheetPoint W w.val v ∈ Λ := by
  have hm := QuotientAddGroup.eq_iff_sub_mem.mp h
  change ((u - projectedLatticeShift Λ W z) - (v - projectedLatticeShift Λ W w)).val ∈ Λ at hm
  have hl := Λ.sub_mem (projectedLatticeLift Λ W z).property (projectedLatticeLift Λ W w).property
  rw [latticeSheetPoint_reconstruction, latticeSheetPoint_reconstruction]
  convert Λ.add_mem hm hl using 1
  simp only [Submodule.coe_sub]
  abel

theorem latticeSheetQuotient_injective_on_region (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {Ω : Set E}
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, x - y ∈ Λ → x = y)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (hu : latticeSheetPoint W z.val u ∈ Ω) (hv : latticeSheetPoint W w.val v ∈ Ω)
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) : z = w ∧ u = v := by
  have he := hΩ _ hu _ hv (latticeSheetPoint_sub_mem_of_quotient_eq Λ W h)
  constructor
  · apply Subtype.ext
    simpa only [latticeSheetPoint_projection_orthogonal] using
      congrArg Wᗮ.orthogonalProjectionOnto he
  · simpa only [latticeSheetPoint_projection] using congrArg W.orthogonalProjectionOnto he

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open MeasureTheory

theorem normalizedLatticeSheet_point {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (Λ : Submodule ℤ Wᗮ) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = Λ) (z : Fin n → ℤ) (u : W) :
    latticeSheetPoint W (latticeBasisEquiv Λ b hb z).val u =
      (normalizedOrthogonalChart W b).symm (u, fun i => (z i : ℝ) / (basisAxisScale b i : ℝ)) := by
  apply (normalizedOrthogonalChart W b).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, normalizedOrthogonalChart_apply,
    latticeSheetPoint_projection, latticeSheetPoint_projection_orthogonal]
  refine Prod.ext rfl ?_
  funext i
  change b.equivFun (latticeBasisEquiv Λ b hb z).val i / (basisAxisScale b i : ℝ) =
    (z i : ℝ) / (basisAxisScale b i : ℝ)
  rw [latticeBasisEquiv_coordinates]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def subspaceArrayIntegerLattice (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    AddSubgroup (I → U) where
  carrier := {x | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  zero_mem' i a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i a
    obtain ⟨n, hn⟩ := hx i a
    obtain ⟨m, hm⟩ := hy i a
    refine ⟨n + m, ?_⟩
    change (x i).val a + (y i).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx i a
    obtain ⟨n, hn⟩ := hx i a
    refine ⟨-n, ?_⟩
    change -(x i).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev SubspaceArrayTorus (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :=
  (I → U) ⧸ subspaceArrayIntegerLattice I U

theorem subspaceArrayFunctional_integral {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    ∃ n : ℤ, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x = n := by
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  refine ⟨∑ i, ∑ a, frequency i a * z i a, ?_⟩
  change (∑ i, ∑ a, (frequency i a : ℝ) * (x i).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

noncomputable def subspaceArrayCharacter {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ) : SubspaceArrayTorus I U → ℂ :=
  quotientLinearCharacter (subspaceArrayIntegerLattice I U)
    (subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)))
    (subspaceArrayFunctional_integral U frequency)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

def arrayCoordinateLinear {I J : Type*} (U : Submodule ℝ (J → ℝ)) (i : I) :
    (I → U) →ₗ[ℝ] (Unit → U) where
  toFun x _ := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def arrayCoordinateTorus {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U →+ (I → SubspaceArrayTorus Unit U) :=
  AddMonoidHom.pi (fun i => QuotientAddGroup.map (subspaceArrayIntegerLattice I U)
    (subspaceArrayIntegerLattice Unit U) (arrayCoordinateLinear U i).toAddMonoidHom
    (fun _x hx _ a => hx i a))

theorem arrayCoordinateTorus_mk {I J : Type*} (U : Submodule ℝ (J → ℝ)) (x : I → U) (i : I) :
    arrayCoordinateTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) i =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) (fun _ => x i) := rfl

theorem arrayCoordinateTorus_bijective {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    Function.Bijective (arrayCoordinateTorus (I := I) U) := by
  constructor
  · intro x y h
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) y
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    intro i a
    exact (QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h i)) () a
  · intro y
    choose v hv using fun i => QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) (y i)
    refine ⟨QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) (fun i => v i ()), ?_⟩
    funext i
    rw [arrayCoordinateTorus_mk]
    have he : (fun _ : Unit => v i ()) = v i := funext (fun u => by cases u; rfl)
    rw [he, hv i]

noncomputable def arrayCoordinateEquiv {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U ≃+ (I → SubspaceArrayTorus Unit U) :=
  AddEquiv.ofBijective (arrayCoordinateTorus U) (arrayCoordinateTorus_bijective U)

theorem arrayCoordinateEquiv_continuous {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) : Continuous (arrayCoordinateEquiv (I := I) U) := by
  apply continuous_pi
  intro i
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (arrayCoordinateLinear U i).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerMatrix_preserves_array_lattice {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U)
    (hx : x ∈ subspaceArrayIntegerLattice I U) :
    matrixModuleAction (fun s i => (E s i : ℝ)) x ∈ subspaceArrayIntegerLattice S U := by
  classical
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  intro s a
  refine ⟨∑ i, E s i * z i a, ?_⟩
  change (∑ i, (E s i : ℝ) • x i).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

noncomputable def integerMatrixTorusMap {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    SubspaceArrayTorus I U →+ SubspaceArrayTorus S U :=
  QuotientAddGroup.map (subspaceArrayIntegerLattice I U) (subspaceArrayIntegerLattice S U)
    (matrixModuleAction (fun s i => (E s i : ℝ))).toAddMonoidHom
    (fun x hx => integerMatrix_preserves_array_lattice U E x hx)

theorem integerMatrixTorusMap_mk {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U) :
    integerMatrixTorusMap U E (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
        (matrixModuleAction (fun s i => (E s i : ℝ)) x) := rfl

end Erdos3

end

section

namespace Erdos3

def unitSubspaceCoordinate {J : Type*} (U : Submodule ℝ (J → ℝ)) (a : J) :
    (Unit → U) →ₗ[ℝ] ℝ where
  toFun x := (x ()).val a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def subspaceAmbientTorus {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus Unit U →+ (J → UnitAddCircle) :=
  AddMonoidHom.pi (fun a => quotientLinearPhase (subspaceArrayIntegerLattice Unit U)
    (unitSubspaceCoordinate U a) (fun _x hx => hx () a))

theorem subspaceAmbientTorus_mk {J : Type*} (U : Submodule ℝ (J → ℝ)) (x : Unit → U) (a : J) :
    subspaceAmbientTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) x) a =
      ((x ()).val a : UnitAddCircle) := rfl

theorem subspaceAmbientTorus_continuous {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) :
    Continuous (subspaceAmbientTorus U) := by
  apply continuous_pi
  intro a
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (unitSubspaceCoordinate U a).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

noncomputable def euclideanSubspace : Submodule ℝ (EuclideanSpace ℝ D) :=
  U.comap (PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).toLinearMap

noncomputable def euclideanSubspaceArrayEquiv : euclideanSubspace U ≃L[ℝ] (Unit → U) where
  toFun x _ := ⟨WithLp.ofLp x.val, x.property⟩
  invFun x := ⟨WithLp.toLp 2 (x ()).val, (x ()).property⟩
  left_inv _ := rfl
  right_inv x := by funext u; cases u; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    apply continuous_pi
    intro u
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).symm.continuous.comp
      (continuous_subtype_val.comp (continuous_apply ()))).subtype_mk _

omit [Fintype D] in
theorem euclideanSubspaceArrayEquiv_apply (x : euclideanSubspace U) (u : Unit) (i : D) :
    (euclideanSubspaceArrayEquiv U x u).val i = x.val i := rfl

theorem euclideanSubspaceArrayEquiv_mem_lattice (x : euclideanSubspace U) :
    euclideanSubspaceArrayEquiv U x ∈ subspaceArrayIntegerLattice Unit U ↔
      x ∈ latticeSection (standardEuclideanLattice D) (euclideanSubspace U) := by
  change (∀ u i, ∃ n : ℤ, x.val i = n) ↔ x.val ∈ standardEuclideanLattice D
  rw [mem_standardEuclideanLattice]
  constructor
  · intro h i
    obtain ⟨n, hn⟩ := h () i
    exact ⟨n, hn.symm⟩
  · intro h u i
    obtain ⟨n, hn⟩ := h i
    exact ⟨n, hn.symm⟩

theorem euclideanSubspaceArrayEquiv_map_lattice :
    (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup.map
      (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv.toAddMonoidHom =
        subspaceArrayIntegerLattice Unit U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  · intro hy
    refine ⟨(euclideanSubspaceArrayEquiv U).symm y, ?_,
      (euclideanSubspaceArrayEquiv U).apply_symm_apply y⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U _).mp (by simpa using hy)

noncomputable def euclideanSubspaceTorusEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃+
        SubspaceArrayTorus Unit U :=
  QuotientAddGroup.congr _ _ (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv
    (euclideanSubspaceArrayEquiv_map_lattice U)

instance euclideanSubspaceLattice_discrete :
    DiscreteTopology (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :=
  latticeSection_discrete (standardEuclideanLattice D) (euclideanSubspace U)

instance euclideanSubspaceLattice_closed :
    IsClosed ((latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :
      Set (euclideanSubspace U)) := AddSubgroup.isClosed_of_discrete

theorem euclideanSubspaceTorusEquiv_mk (x : euclideanSubspace U) :
    euclideanSubspaceTorusEquiv U (QuotientAddGroup.mk' _ x) =
      QuotientAddGroup.mk' _ (euclideanSubspaceArrayEquiv U x) := rfl

theorem euclideanSubspaceTorusEquiv_continuous : Continuous (euclideanSubspaceTorusEquiv U) := by
  apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).continuous

theorem euclideanSubspaceTorusEquiv_symm_continuous :
    Continuous (euclideanSubspaceTorusEquiv U).symm := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).symm.continuous

noncomputable def euclideanSubspaceTorusHomeomorph :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ₜ
        SubspaceArrayTorus Unit U where
  toEquiv := (euclideanSubspaceTorusEquiv U).toEquiv
  continuous_toFun := euclideanSubspaceTorusEquiv_continuous U
  continuous_invFun := euclideanSubspaceTorusEquiv_symm_continuous U

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem clearedMatrix_real {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (i : I) (s : S) :
    (clearedMatrix T i s : ℝ) = (matrixDenominator T : ℝ) * (T i s : ℝ) := by
  have h := congrFun (congrFun (clearedMatrix_cast T) i) s
  change (clearedMatrix T i s : ℚ) = (matrixDenominator T : ℚ) * T i s at h
  exact_mod_cast h

theorem matrixModuleAction_cleared {I S W : Type*} [Fintype I] [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℚ) (x : S → W) :
    matrixModuleAction (fun i s => (clearedMatrix T i s : ℝ)) x =
      (matrixDenominator T : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (clearedMatrix T i s : ℝ) • x s) =
    (matrixDenominator T : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [clearedMatrix_real, mul_smul, Finset.smul_sum]

theorem scaledSiteResidual_preserves_lattice {I S J : Type*} [Fintype I] [Fintype S]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (T : Matrix I S ℤ) (q : ℕ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    scaledLinearResidual (matrixModuleAction (fun s i => (E s i : ℝ)))
      (matrixModuleAction (fun i s => (T i s : ℝ))) (q : ℝ) x ∈ subspaceArrayIntegerLattice I U := by
  apply (subspaceArrayIntegerLattice I U).sub_mem ?_
    (integerMatrix_preserves_array_lattice U T _ (integerMatrix_preserves_array_lattice U E x hx))
  intro i a
  obtain ⟨z, hz⟩ := hx i a
  refine ⟨(q : ℤ) * z, ?_⟩
  change (q : ℝ) * (x i).val a = _
  rw [hz, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix Classical

theorem cleared_image_section_entry_bound {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (H : ℕ)
    (hT : ∀ i s, RationalHeightLE (T i s) (rationalKernelHeight (Fintype.card S) H))
    {P : ℝ} (hP : 0 ≤ P) (hI : (Fintype.card I : ℝ) ≤ P)
    (hS : (Fintype.card S : ℝ) ≤ P) (hH : (H : ℝ) ≤ Real.exp P) (i : I) (s : S) :
    |(clearedMatrix T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36) := by
  have hden : (matrixDenominator T : ℝ) ≤ Real.exp ((P + 2) ^ 36) := by
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hT hP hS hI hH
      (by simpa using Real.one_le_exp hP)
  have hentry := (hT i s).abs_real_le.trans
    (rationalKernelHeight_le_budget (Fintype.card S) H hP hS hH)
  have hpow : (P + 2) ^ 7 ≤ (P + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  rw [clearedMatrix_real, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp ((P + 2) ^ 36) * Real.exp ((P + 2) ^ 7) :=
      mul_le_mul hden hentry (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((P + 2) ^ 36 + (P + 2) ^ 7) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * (P + 2) ^ 36) := Real.exp_le_exp.mpr (by linarith)

theorem exists_bounded_integer_site_residual {I S : Type*} [Fintype I] [Fintype S]
    (E : Matrix S I ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hE : ∀ s i, RationalHeightLE (E s i : ℚ) H) :
    ∃ (d : ℕ) (T : Matrix I S ℤ), 0 < d ∧
      (∀ {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I → W),
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P → (Fintype.card S : ℝ) ≤ P →
        (H : ℝ) ≤ Real.exp P →
        (d : ℝ) ≤ Real.exp ((P + 2) ^ 36) ∧
          ∀ i s, |(T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36)) := by
  obtain ⟨T, hT, hTH⟩ := exists_bounded_rational_image_section (fun s i => (E s i : ℚ)) hH hE
  refine ⟨matrixDenominator T, clearedMatrix T, matrixDenominator_pos T, ?_, ?_⟩
  · intro W _ _ x
    rw [matrixModuleAction_cleared, map_smul]
    congr 1
    have he := matrixModuleAction_image_section
      (Matrix.of (fun s i => ((E s i : ℚ) : ℝ)))
      (Matrix.of (fun i s => (T i s : ℝ))) (real_matrix_image_section _ T hT) x
    funext s
    simpa only [matrixModuleAction, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Rat.cast_intCast] using congrFun he s
  · intro P hP hI hS hHP
    refine ⟨?_, cleared_image_section_entry_bound T H hTH hP hI hS hHP⟩
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hTH hP hS hI hHP
      (by simpa using Real.one_le_exp hP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem matrixModuleAction_int_smul {I S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℤ) (d : ℕ) (x : S → W) :
    matrixModuleAction (fun i s => (((d : ℤ) * T i s : ℤ) : ℝ)) x =
      (d : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (((d : ℤ) * T i s : ℤ) : ℝ) • x s) =
    (d : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [Int.cast_mul, Int.cast_natCast, mul_smul, Finset.smul_sum]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCommonSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def complementaryPeriod {I : Type*} [Fintype I] (q : I → ℕ) (i : I) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

theorem period_mul_complementary {I : Type*} [Fintype I] (q : I → ℕ) (i : I) :
    q i * complementaryPeriod q i = ∏ j, q j :=
  Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

theorem complementaryPeriod_le_product {I : Type*} [Fintype I] (q : I → ℕ)
    (hq : ∀ i, 0 < q i) (i : I) : complementaryPeriod q i ≤ ∏ j, q j := by
  rw [← period_mul_complementary q i]
  exact Nat.le_mul_of_pos_left _ (hq i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_bounded_common_site_residual {J S : Type*} [Fintype J] [Fintype S]
    {I : J → Type*} [∀ j, Fintype (I j)] (E : ∀ j, Matrix S (I j) ℤ)
    (H : J → ℕ) (hH : ∀ j, 1 ≤ H j)
    (hE : ∀ j s i, RationalHeightLE (E j s i : ℚ) (H j)) :
    ∃ (d : ℕ) (T : ∀ j, Matrix (I j) S ℤ), 0 < d ∧
      (∀ j {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I j → W),
        matrixModuleAction (fun s i => (E j s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E j s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E j s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (∀ j, (Fintype.card (I j) : ℝ) ≤ P) →
        (Fintype.card S : ℝ) ≤ P → (∀ j, (H j : ℝ) ≤ Real.exp P) →
        (d : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) ∧
          ∀ j i s, |(T j i s : ℝ)| ≤ Real.exp (((Fintype.card J : ℝ) + 2) * (P + 2) ^ 36)) := by
  choose d T hd hT hbound using fun j => exists_bounded_integer_site_residual (E j) (hH j) (hE j)
  let D := ∏ j, d j
  refine ⟨D, fun j i s => (complementaryPeriod d j : ℤ) * T j i s,
    Finset.prod_pos (fun j _ => hd j), ?_, ?_⟩
  · intro j W _ _ x
    rw [matrixModuleAction_int_smul, map_smul, hT j, smul_smul]
    congr 1
    exact_mod_cast (by simpa only [Nat.mul_comm] using period_mul_complementary d j :
      complementaryPeriod d j * d j = D)
  · intro P hP hI hS hHP
    have hD : (D : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) := by
      calc
        (D : ℝ) = ∏ j, (d j : ℝ) := Nat.cast_prod _ _
        _ ≤ ∏ _j : J, Real.exp ((P + 2) ^ 36) :=
          Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
            (fun j _ => (hbound j hP (hI j) hS (hHP j)).1)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    refine ⟨hD, ?_⟩
    intro j i s
    rw [Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (complementaryPeriod d j) : (0 : ℝ) ≤ complementaryPeriod d j)]
    have hc : (complementaryPeriod d j : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) :=
      (Nat.cast_le.mpr (complementaryPeriod_le_product d hd j)).trans hD
    calc
      _ ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) * Real.exp (2 * (P + 2) ^ 36) :=
        mul_le_mul hc ((hbound j hP (hI j) hS (hHP j)).2 i s) (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def integerContractedRow {σ J : Type*}
    (frequency : (σ →₀ ℕ) → J → ℤ) (P : MvPolynomial σ ℤ) : J → ℤ :=
  fun j => ∑ d ∈ P.support, P.coeff d * frequency d j

theorem integerContractedRow_cast {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ)
    (frequency : (σ →₀ ℕ) → J → ℤ) {h : ℕ}
    (hfrequency : ∀ d : σ →₀ ℕ, d.degree = h → ∀ j,
      Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1) = (frequency d j : ℝ))
    {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow Λ (MvPolynomial.map (Int.castRingHom ℝ) P) j := by
  change _ = ((TensorProduct.curry Λ).flip (Pi.single j 1)) (MvPolynomial.map (Int.castRingHom ℝ) P)
  rw [polynomialFunctional_map_expansion]
  simp only [integerContractedRow, Int.cast_sum, Int.cast_mul, Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (MvPolynomial.mem_support_iff.mp hd)
  change _ = ((P.coeff d : ℤ) : ℝ) * Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)
  rw [hfrequency d hdeg j]

theorem integerContractedRow_coefficientFunctional {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow
      (coefficientFunctional (fun d j => (frequency d j : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) P) j :=
  integerContractedRow_cast _ frequency (fun d _ j => coefficientFunctional_unit _ d j) hP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem integer_cube_root_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ k, |(root k : ℝ)| ≤ L := by
  intro k
  simpa only [affineSite, Finset.sum_empty, add_zero] using hsite ∅ k

theorem integer_cube_difference_bound {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) {L : ℝ}
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L) :
    ∀ i k, |(difference i k : ℝ)| ≤ 2 * L := by
  intro i k
  have he : (difference i k : ℝ) =
      ((affineSite root difference {i} (some k) : ℤ) : ℝ) - (root k : ℝ) := by
    simp [affineSite]
  rw [he]
  have ht := hsite {i} k
  have hr := integer_cube_root_bound root difference hsite k
  exact (abs_sub _ _).trans (by linarith)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem integerCubeWitnessBound_le_polynomial (q : ℕ) {H D : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) :
    integerCubeWitnessBound q H D ≤
      (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + H + D) ^ (q + 2) := by
  let M := 1 + H + D
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hDq : D ^ q ≤ M ^ q := pow_le_pow_left₀ hD (by dsimp [M]; linarith) q
  have hDm : D ^ (q - 1) ≤ M ^ q :=
    (pow_le_pow_left₀ hD (by dsimp [M]; linarith) (q - 1)).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  have hHM : 1 + H ≤ M := by dsimp [M]; linarith
  have hA : (q.factorial : ℝ) * D ^ q ≤ (q.factorial : ℝ) * M ^ q :=
    mul_le_mul_of_nonneg_left hDq (Nat.cast_nonneg _)
  have hB : (q : ℝ) * ((q.factorial : ℝ) * D ^ (q - 1) * (1 + H)) ≤
      (q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1) := by
    calc
      _ ≤ (q : ℝ) * ((q.factorial : ℝ) * M ^ q * M) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hfactor : (q : ℝ) * D + 1 ≤ ((q : ℝ) + 1) * M := by
    have hd : D ≤ M := by dsimp [M]; linarith
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hbase : 2 + H ≤ 2 * M := by dsimp [M]; linarith
  have hpow : M ^ (q + 1) ≤ M ^ (q + 2) := pow_le_pow_right₀ hM (by omega)
  unfold integerCubeWitnessBound integerFormMassBound
  calc
    _ ≤ (q.factorial : ℝ) * M ^ q * (2 * M) +
        (((q : ℝ) + 1) * M) * ((q : ℝ) * (q.factorial : ℝ) * M ^ (q + 1)) := by
      exact add_le_add (mul_le_mul hA hbase (by positivity) (by positivity))
        (mul_le_mul hfactor hB (by positivity) (by positivity))
    _ = 2 * (q.factorial : ℝ) * M ^ (q + 1) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by
      simp only [pow_succ]
      ring
    _ ≤ 2 * (q.factorial : ℝ) * M ^ (q + 2) +
        ((q : ℝ) * (q + 1) * (q.factorial : ℝ)) * M ^ (q + 2) := by gcongr
    _ = _ := by dsimp [M]; ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_integer_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, w, hw⟩ := exists_bounded_ambient_mode_witness W root difference hlin
    hH hD hC hroot hdiff (VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ)))
    h (VectorPolynomial.coefficientFunctional_rowBound _ hbound) hnonfactor
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => (hP i).1)
  have hcast (j : J) := VectorPolynomial.integerContractedRow_coefficientFunctional frequency hp j
  refine ⟨P, hP, hz, ?_, w, ?_⟩
  · intro j
    rw [hcast j]
    exact hb j
  · simp_rw [hcast]
    exact hw

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem rowPolynomial_homogeneous {σ R : Type*} [Fintype σ] [CommRing R] (a : σ → R) :
    (rowPolynomial a).IsHomogeneous 1 :=
  IsHomogeneous.sum Finset.univ _ 1 (fun i _ => isHomogeneous_C_mul_X (a i) i)

theorem VectorPolynomial.integerContractedRow_apply {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (w : J → ℝ) :
    (∑ j, (integerContractedRow frequency P j : ℝ) * w j) =
      coefficientFunctional (fun d j => (frequency d j : ℝ))
        ((MvPolynomial.map (Int.castRingHom ℝ) P) ⊗ₜ[ℝ] w) := by
  simp_rw [integerContractedRow_coefficientFunctional frequency hP]
  exact contractedRow_apply _ _ w

namespace BooleanCubeKernel

theorem exists_bounded_integer_mode_rows {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, hw⟩ := exists_bounded_integer_mode_witness W root difference hlin
    hH hD hC hroot hdiff frequency h hbound hnonfactor
  let rows := fun i => polynomialLinearRow (P i)
  have hp (i : Fin h) : rowPolynomial (rows i) = P i :=
    (homogeneous_eq_rowPolynomial _ (hP i).1).symm
  have hprod : (∏ i, rowPolynomial (rows i)) = ∏ i, P i := by simp_rw [hp]
  refine ⟨rows, ?_, ?_, ?_, ?_⟩
  · intro i k
    exact (integer_coefficient_le_mass (P i) (Finsupp.single k 1)).trans (hP i).2
  · intro s
    obtain ⟨i, hi⟩ := hz s
    refine ⟨i, ?_⟩
    change (∑ k, polynomialLinearRow (P i) k * affineSite root difference s k) = 0
    rw [← homogeneous_eval_eq_row _ (hP i).1]
    exact hi
  · rw [hprod]
    exact hb
  · rw [hprod]
    exact hw

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineParameterSubstitution {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : MvPolynomial K ℝ :=
  MvPolynomial.C (b none j) + rowPolynomial (fun k => b (some k) j)

theorem dehomogenize_rowPolynomial {K : Type*} [Fintype K] (a : Option K → ℝ) :
    MvPolynomial.aeval dehomogenizingSubstitution (rowPolynomial a) =
      MvPolynomial.C (a none) + rowPolynomial (fun k => a (some k)) := by
  simp [rowPolynomial, dehomogenizingSubstitution, Fintype.sum_option]

theorem affineParameterSubstitution_degree {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : (affineParameterSubstitution b j).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  exact max_le (by simp) (rowPolynomial_homogeneous (fun k => b (some k) j)).totalDegree_le

theorem affineParameterSubstitution_eval {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (t : K → ℝ) (j : I) :
    MvPolynomial.aeval t (affineParameterSubstitution b j) =
      b none j + ∑ k, b (some k) j * t k := by
  change MvPolynomial.eval t (affineParameterSubstitution b j) = _
  rw [affineParameterSubstitution, map_add, MvPolynomial.eval_C, rowPolynomial_eval]

noncomputable def affineModeLift {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ :=
  Λ.comp (substitute dehomogenizingSubstitution)

theorem affineModeLift_substitute {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (b : Option K → I → ℝ) :
    affineModeLift Λ (substitute (fun j => rowPolynomial (fun k => b k j)) p) =
      Λ (substitute (affineParameterSubstitution b) p) := by
  rw [affineModeLift, LinearMap.comp_apply, substitute_comp]
  simp only [dehomogenize_rowPolynomial]
  rfl

theorem coefficientModePolynomial_degreeLE {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : DegreeLE (1 : I → ℕ) h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem rowPolynomial_integer_site {I K : Type*} [Fintype K]
    (site : K → ℤ) (b : K → I → ℝ) :
    (fun i => MvPolynomial.aeval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i))) =
      integerSiteValue site b := by
  funext i
  change MvPolynomial.eval (fun k => (site k : ℝ)) (rowPolynomial (fun k => b k i)) = _
  rw [rowPolynomial_eval]
  change (∑ k, b k i * (site k : ℝ)) = (∑ k, site k • b k) i
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change b k i * (site k : ℝ) = site k • b k i
  rw [zsmul_eq_mul, mul_comm]

theorem exists_absorbed_integer_site_tests {A I K S : Type*} {W : A → Type*}
    [Fintype A] [Fintype K] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℤ)
    (L : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (h a) q →
        L a q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (low : (K → I → ℝ) → ℝ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
      character ((low b + ∑ a, L a (substitute (fun i => rowPolynomial (fun k => b k i)) (p a)) : ℝ) :
        CircleFourier.Circle) * (∏ s, test s (integerSiteValue (site s) b)) =
      character (low b : CircleFourier.Circle) * (∏ s, test' s (integerSiteValue (site s) b)) := by
  have hf (a : A) : ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → L a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) q) := by
    obtain ⟨M, hM⟩ := hfactor a
    exact ⟨M, (homogeneous_site_factorization_iff (h a)
      (fun s k => (site s k : ℝ)) (L a) M).mpr hM⟩
  obtain ⟨test', ht, he⟩ := exists_absorbed_polynomial_site_tests h
    (fun s k => (site s k : ℝ)) L hf p hp
    (fun (b : K → I → ℝ) i => rowPolynomial (fun k => b k i))
    (fun b i => (rowPolynomial_homogeneous (fun k => b k i)).totalDegree_le) low test htest
  refine ⟨test', ht, ?_⟩
  intro b
  simpa only [rowPolynomial_integer_site] using he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

def cubeModePolynomialBudget (q : ℕ) (L : ℝ) : ℝ :=
  (q.factorial : ℝ) * (2 + (q : ℝ) * (q + 1)) * (1 + 3 * L) ^ (q + 2)

theorem integerCubeWitnessBound_le_vertex_budget (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    integerCubeWitnessBound q L (2 * L) ≤ cubeModePolynomialBudget q L := by
  have he : 1 + L + 2 * L = 1 + 3 * L := by ring
  simpa only [cubeModePolynomialBudget, he] using
    integerCubeWitnessBound_le_polynomial q hL (show 0 ≤ 2 * L by positivity)

theorem exists_vertex_bounded_integer_mode {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_bounded_integer_mode_rows W root difference hlin
    hL (show 0 ≤ 2 * L by positivity) hC
    (integer_cube_root_bound root difference hsite)
    (integer_cube_difference_bound root difference hsite) frequency h hbound hnonfactor
  have hbudget := integerCubeWitnessBound_le_vertex_budget q hL
  refine ⟨rows, (fun i k => (hr i k).trans hbudget), hz, ?_, hw⟩
  intro j
  exact (hb j).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integerCubeWitnessBound_nonneg q hL (by positivity)) hbudget h) hC)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_dehomogenize {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {h : ℕ} {p : VectorPolynomial (Option K) ℝ W}
    (hp : DegreeLE (1 : Option K → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute dehomogenizingSubstitution p) := by
  apply degreeLE_substitute_affine _ _ p hp
  intro k
  cases k <;> simp [dehomogenizingSubstitution]

theorem affineModeLift_factorization_iff {K S W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (M : (S → W) →ₗ[ℝ] ℝ) :
    (∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) := by
  constructor
  · intro hf q hq
    have ho := (homogeneous_site_factorization_iff h site L M).mp hf
    change L (substitute dehomogenizingSubstitution q) = _
    rw [← siteEvaluation_dehomogenize]
    exact ho _ (degreeLE_dehomogenize hq)
  · intro hf q hq
    exact hf q (homogeneous_degreeLE hq)

theorem affineModeLift_exists_factorization_iff {K S W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :=
  exists_congr (fun M => affineModeLift_factorization_iff h site L M)

theorem exists_highest_affine_nonfactor {K S : Type*} {m : ℕ} {W : Fin m → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (site : S → K → ℝ) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q → affineModeLift (L j) q =
          M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  obtain ⟨i, hi, hh⟩ := exists_highest_exceptional_layer _ hbad
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (affineModeLift_exists_factorization_iff (j.val + 1) site (L j)).mp (hh j hj)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open CircleFourier _root_.MvPolynomial
open scoped BigOperators Classical

def FiniteSitePhaseRemoval {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [AddCommGroup V]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ) : Prop :=
  ∀ (base : K → V) (shift : X → V) (phase : (K → V) → ℝ) (test : S → V → ℂ),
    (∀ s v, ‖test s v‖ ≤ 1) →
    ‖𝔼 x, character (phase (rowShiftedTuple base rows shift x) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character ((additiveBoxDifference h
        (fun x (_ : Unit) => phase (rowShiftedTuple base rows shift x)) u v () : ℝ) : CircleFourier.Circle)‖

theorem finiteSitePhaseRemoval_of_annihilates {h : ℕ} {S K X V : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] [AddCommGroup V]
    (hh : 0 < h) (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0) :
    FiniteSitePhaseRemoval (X := X) (V := V) site rows := by
  intro base shift phase test htest
  exact row_shifted_site_phase_cauchySchwarz hh site base rows shift hzero phase test htest

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem affineModeLift_comp_map {K V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    affineModeLift (L.comp (map f)) = (affineModeLift L).comp (map f) := by
  apply LinearMap.ext
  intro q
  simp only [affineModeLift, LinearMap.comp_apply, map_substitute]

theorem exists_highest_affine_subspace_nonfactor {K S : Type*} {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    (U : ∀ j, Submodule ℝ (V j)) (site : S → K → ℝ)
    (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q →
          affineModeLift (L j) (map (U j).subtype q) =
            M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  have hh := exists_highest_affine_nonfactor site (fun j => (L j).comp (map (U j).subtype))
    (by simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hbad)
  simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hh

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineFrequencyLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineLiftFrequency {K J A : Type*}
    (frequency : (K →₀ ℕ) → J → A) (d : Option K →₀ ℕ) : J → A := frequency d.some

theorem affineModeLift_coefficientFunctional {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) :
    affineModeLift (coefficientFunctional frequency) =
      coefficientFunctional (affineLiftFrequency frequency) := by
  apply LinearMap.ext
  intro p
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, affineModeLift, LinearMap.comp_apply,
    dehomogenize_monomial, coefficientFunctional_monomial, affineLiftFrequency]

theorem affineModeLift_integerFrequency {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℤ) :
    affineModeLift (coefficientFunctional (fun d j => (frequency d j : ℝ))) =
      coefficientFunctional (fun d j => ((affineLiftFrequency frequency d j : ℤ) : ℝ)) :=
  affineModeLift_coefficientFunctional _

theorem affineLiftFrequency_bound {K J : Type*} [Fintype K]
    (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ} {C : ℝ}
    (hbound : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C) :
    ∀ d, d.degree = h → ∀ j, |((affineLiftFrequency frequency d j : ℤ) : ℝ)| ≤ C := by
  intro d hd j
  exact hbound d.some ((some_degree_le d).trans hd.le) j

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSiteRemoval
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial CircleFourier
open scoped BigOperators Classical

theorem finiteSitePhaseRemoval_polynomial {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hremove : FiniteSitePhaseRemoval (X := X) (V := J → ℝ) site rows)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hc := hremove base shift (fun tuple => eval (fun z => tuple z.1 z.2) P) test htest
  simpa only [row_shift_difference_eq_topSymbol base rows shift P hP] using hc

theorem row_polynomial_site_cauchySchwarz {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ :=
  finiteSitePhaseRemoval_polynomial site rows
    (finiteSitePhaseRemoval_of_annihilates hh site rows hzero) base shift P hP test htest

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem fullShiftExponent_multinomial (n : ℕ) : (fullShiftExponent n).multinomial = n.factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Nat.factorial_one, Finset.prod_const_one, Nat.div_one]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialTopSymbol_add {I : Type*} (h : ℕ) (P Q : MvPolynomial I ℝ)
    (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction =
      polynomialTopSymbol h P direction + polynomialTopSymbol h Q direction := by
  simp only [polynomialTopSymbol, map_add, MvPolynomial.coeff_add]

theorem polynomialTopSymbol_eq_zero_of_degree_lt {I : Type*} {h : ℕ}
    (Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h Q direction = 0 := by
  simp only [polynomialTopSymbol, homogeneousComponent_eq_zero h Q hQ, map_zero,
    MvPolynomial.coeff_zero]

theorem polynomialTopSymbol_add_lower {I : Type*} {h : ℕ}
    (P Q : MvPolynomial I ℝ) (hQ : Q.totalDegree < h) (direction : Fin h → I → ℝ) :
    polynomialTopSymbol h (P + Q) direction = polynomialTopSymbol h P direction := by
  rw [polynomialTopSymbol_add, polynomialTopSymbol_eq_zero_of_degree_lt Q hQ, add_zero]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem full_coefficient_linear_pow {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).coeff (fullShiftExponent n) =
      (n.factorial : R) * ∏ i, a i := by
  rw [coeff_linearCombination_X_pow_of_fintype, fullShiftExponent_sum]
  simp only [ite_true, fullShiftExponent_multinomial]
  rw [(fullShiftExponent n).prod_fintype _ (fun _ => pow_zero _)]
  simp only [fullShiftExponent_apply, pow_one]

theorem linear_pow_totalDegree_le {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n).totalDegree ≤ n := by
  have hsum : (∑ i, a i • X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    rw [smul_eq_C_mul]
    have hX : (X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
      simpa only [X, Finsupp.sum_single_index, id_eq] using
        (totalDegree_monomial_le (Finsupp.single i 1) (1 : R))
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hX)
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left n hsum).trans_eq (Nat.mul_one n))

theorem linear_power_full_difference {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : R) * ∏ i, a i := by
  have he : (fun (x : Fin n → R) (_ : Unit) => (∑ i, a i * x i) ^ n) =
      (fun x (_ : Unit) => eval x ((∑ i, a i • X i : MvPolynomial (Fin n) R) ^ n)) := by
    funext x _
    simp only [smul_eq_C_mul, map_pow, map_sum, map_mul, eval_C, eval_X]
  rw [he, full_mixed_difference_of_totalDegree _ (linear_pow_totalDegree_le n a),
    full_coefficient_linear_pow]
  simp

theorem linear_power_full_difference_algebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (n : ℕ) (a : Fin n → S) :
    additiveBoxDifference n (fun (x : Fin n → R) (_ : Unit) => (∑ i, x i • a i) ^ n)
      (fun _ => 1) (fun _ => 0) () = (n.factorial : S) * ∏ i, a i := by
  have hm := additiveBoxDifference_map n (fun _ => algebraMap R S)
    (fun (x : Fin n → S) (_ : Unit) => (∑ i, a i * x i) ^ n)
    (fun _ => 1) (fun _ => 0) ()
  simp only [map_one, map_zero] at hm
  simpa only [Algebra.smul_def, mul_comm] using hm.trans (linear_power_full_difference n a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem homogeneous_substitute_scaled {I J R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p)
    (w : I → R) (Q : MvPolynomial J R) :
    substitute (fun i => MvPolynomial.C (w i) * Q) p = (Q ^ h) ⊗ₜ[R] eval w p := by
  let f := substitute (V := W) (fun i => MvPolynomial.C (w i) * Q)
  let g : VectorPolynomial I R W →ₗ[R] VectorPolynomial J R W :=
    (TensorProduct.mk R (MvPolynomial J R) W (Q ^ h)).comp (eval w)
  change f p = g p
  apply eq_of_homogeneous_tmul f g h _ hp
  intro P hP v
  change MvPolynomial.aeval (fun i => MvPolynomial.C (w i) * Q) P ⊗ₜ[R] v =
    (Q ^ h) ⊗ₜ[R] (MvPolynomial.eval w P • v)
  rw [Erdos3.homogeneous_aeval_scaled P hP w Q]
  simp only [← MvPolynomial.smul_eq_C_mul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem homogeneous_mode_diagonal_difference {I T R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (p : VectorPolynomial I R W) (hp : Homogeneous h p) (w : I → R)
    (A : Fin h → MvPolynomial T R) (L : VectorPolynomial T R W →ₗ[R] R) :
    additiveBoxDifference h
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p))
      (fun _ => 1) (fun _ => 0) () =
        (h.factorial : R) * L ((∏ i, A i) ⊗ₜ[R] eval w p) := by
  let F : MvPolynomial T R →ₗ[R] R := (TensorProduct.curry L).flip (eval w p)
  have he :
      (fun (x : Fin h → R) (_ : Unit) =>
        L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • A i) p)) =
      (fun x (_ : Unit) => F ((∑ i, x i • A i) ^ h)) := by
    funext x _
    rw [homogeneous_substitute_scaled p hp w]
    rfl
  rw [he]
  have hm := additiveBoxDifference_hom F.toAddMonoidHom h
    (fun (x : Fin h → R) (_ : Unit) => (∑ i, x i • A i) ^ h)
    (fun _ => 1) (fun _ => 0) ()
  refine hm.trans ?_
  rw [linear_power_full_difference_algebra]
  change F ((h.factorial : MvPolynomial T R) * ∏ i, A i) = _
  have hc : (h.factorial : MvPolynomial T R) * ∏ i, A i =
      (h.factorial : R) • ∏ i, A i := by
    rw [MvPolynomial.smul_eq_C_mul, map_natCast]
  rw [hc, map_smul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem coefficientModePolynomial_top_diagonal {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (a : Fin h → K → ℝ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial L p) (fun i z => a i z.1 * w z.2) =
      (h.factorial : ℝ) * L ((∏ i, rowPolynomial (a i)) ⊗ₜ[ℝ] eval w p) := by
  have hphase (x : Fin h → ℝ) :
      MvPolynomial.eval (fun z => 0 + ∑ i, (a i z.1 * w z.2) * x i)
        (coefficientModePolynomial L p) =
      L (substitute (fun j => MvPolynomial.C (w j) * ∑ i, x i • rowPolynomial (a i)) p) := by
    have hv : (fun z : K × I => 0 + ∑ i, (a i z.1 * w z.2) * x i) =
        (fun z => ∑ i, a i z.1 * (x i * w z.2)) := by
      funext z
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hv, coefficientModePolynomial_eval L p (fun k j => ∑ i, a i k * (x i * w j))]
    apply congrArg (fun f : I → MvPolynomial K ℝ => L (substitute f p))
    funext j
    exact rowPolynomial_diagonal a x (w j)
  have hd := affineShift_difference_eq_topSymbol (fun _ : K × I => 0)
    (fun i z => a i z.1 * w z.2) (coefficientModePolynomial L p)
    (coefficientModePolynomial_degree L p hp) (fun _ => 1) (fun _ => 0)
  simp only [hphase, sub_zero, Finset.prod_const_one, mul_one] at hd
  exact hd.symm.trans (homogeneous_mode_diagonal_difference p hp w (fun i => rowPolynomial (a i)) L)

theorem coefficientModePolynomial_top_integer_row {I K J : Type*} [Fintype K] [Fintype J]
    {h : ℕ} (frequency : (K →₀ ℕ) → J → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p)
    (a : Fin h → K → ℤ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial
      (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
      (fun i z => (a i z.1 : ℝ) * w z.2) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  have hprod : (∏ i, rowPolynomial (a i)).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => rowPolynomial (a i))
      (fun _ => 1) (fun i _ => rowPolynomial_homogeneous (a i))
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (∏ i, rowPolynomial (a i)) =
      ∏ i, rowPolynomial (fun k => (a i k : ℝ)) := by
    simp only [map_prod, rowPolynomial_map, Int.coe_castRingHom]
  rw [coefficientModePolynomial_top_diagonal
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) p hp
    (fun i k => (a i k : ℝ)) w, ← hmap, integerContractedRow_apply frequency hprod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators TensorProduct Classical

theorem coefficient_mode_with_lower_site_cauchySchwarz {h : ℕ} {S K I X W : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X]
    [AddCommGroup W] [Module ℝ W] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → I → ℝ) (shift : X → I → ℝ)
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ W) (hp : Homogeneous h p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < h)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base rows shift x k j)) p) +
          MvPolynomial.eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) Q : ℝ) :
            CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X,
        character ((polynomialTopSymbol h (coefficientModePolynomial L p)
          (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hdegree : (coefficientModePolynomial L p + Q).totalDegree ≤ h :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (coefficientModePolynomial_degree L p hp) hQ.le)
  simpa only [map_add, coefficientModePolynomial_eval, polynomialTopSymbol_add_lower _ Q hQ] using
    row_polynomial_site_cauchySchwarz hh site rows hzero base shift
      (coefficientModePolynomial L p + Q) hdegree test htest

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientModeDiagonalPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def factorialContractedRow {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) : J → ℤ :=
  fun j => (h.factorial : ℤ) * integerContractedRow frequency (∏ i, rowPolynomial (a i)) j

theorem factorialContractedRow_eval {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  simp [integerRowPolynomial_eval, factorialContractedRow, Finset.mul_sum, mul_assoc]

theorem coefficientMode_diagonal_polynomial {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      polynomialTopSymbol h (coefficientModePolynomial
        (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
        (fun i z => (a i z.1 : ℝ) * w z.2) := by
  rw [factorialContractedRow_eval]
  exact (coefficientModePolynomial_top_integer_row frequency p hp a w).symm

theorem factorialContractedRow_bound {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) {B : ℝ}
    (hb : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B) :
    ∀ j, |(factorialContractedRow frequency a j : ℝ)| ≤ (h.factorial : ℝ) * B := by
  intro j
  simpa only [factorialContractedRow, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)] using
    mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)

theorem factorialContractedRow_nonzero {K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) (w : J → ℝ)
    (hw : (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j) ≠ 0) :
    (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) ≠ 0 := by
  have he : (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j := by
    simp [factorialContractedRow, Finset.mul_sum, mul_assoc]
  rw [he]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)) hw

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedHomogeneousFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem homogeneous_factorization_to_bounded_site {K S J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℝ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial (Option K) ℝ U, Homogeneous h p →
      affineModeLift (coefficientFunctional frequency) (map U.subtype p) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p)) :
    ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation site p) := by
  let L := (coefficientFunctional frequency).comp (map U.subtype)
  have hlift : ∀ p, Homogeneous h p → affineModeLift L p =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p) := by
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hf
  exact (homogeneous_site_factorization_iff h site L M).mp hlift

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientSubspaceFunctional
namespace OAI

section

namespace Erdos3

theorem exists_quotient_functional_preserving_subspace
    {K V A : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    (U I : Submodule K V) (η : V →ₗ[K] A) (hη : U ⊓ I ≤ η.ker) :
    ∃ ξ : (V ⧸ I) →ₗ[K] A, ∀ x ∈ U, ξ (I.mkQ x) = η x := by
  let q : U →ₗ[K] V ⧸ I := I.mkQ.comp U.subtype
  let f : U →ₗ[K] A := η.comp U.subtype
  have hk : q.ker ≤ f.ker := by
    intro x hx
    have hxI : x.val ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hx
    exact hη ⟨x.property, hxI⟩
  let fbar := q.ker.liftQ f hk
  let φ : q.range →ₗ[K] A := fbar.comp q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ξ, hξ⟩ := φ.exists_extend
  refine ⟨ξ, ?_⟩
  intro x hx
  let u : U := ⟨x, hx⟩
  have he := LinearMap.congr_fun hξ (q.rangeRestrict u)
  change ξ (q u) = fbar (q.quotKerEquivRange.symm (q.rangeRestrict u)) at he
  have hq : q.quotKerEquivRange.symm (q.rangeRestrict u) = q.ker.mkQ u :=
    q.quotKerEquivRange_symm_apply_image u _
  rw [hq] at he
  exact he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedQuotientFunctional
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix BigOperators

variable {ι κ V U : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]

theorem exists_bounded_linear_retraction (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H) :
    ∃ ρ : V →ₗ[ℚ] U, (∀ x, ρ (φ x) = x) ∧
      ∀ i j, RationalHeightLE (a.repr (ρ (b j)) i)
        (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix a b φ
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have heq (z : κ → ℚ) : A *ᵥ z = b.equivFun (φ (a.equivFun.symm z)) := by
      have hz := LinearMap.toMatrix_mulVec_repr a b φ (a.equivFun.symm z)
      simpa only [A, ← a.equivFun_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply] using hz
    rw [heq, heq] at hxy
    exact a.equivFun.symm.injective (hφ (b.equivFun.injective hxy))
  obtain ⟨P, hPA, hP⟩ := exists_bounded_rational_left_inverse A
    (Matrix.mulVec_injective_iff.mp hinj) hH
    (by simpa only [A, LinearMap.toMatrix_apply] using ha)
  refine ⟨Matrix.toLin b a P, ?_, ?_⟩
  · intro x
    have hcomp : (Matrix.toLin b a P).comp φ = LinearMap.id := by
      calc
        _ = (Matrix.toLin b a P).comp (Matrix.toLin a b A) := by
          rw [Matrix.toLin_toMatrix]
        _ = Matrix.toLin a a (P * A) := (Matrix.toLin_mul a b a P A).symm
        _ = LinearMap.id := by rw [hPA, Matrix.toLin_one]
    exact LinearMap.congr_fun hcomp x
  · intro i j
    have hij := LinearMap.toMatrix_toLin b a P
    have hv := congrArg (fun M => M i j) hij
    rw [LinearMap.toMatrix_apply] at hv
    rw [hv]
    exact hP i j

theorem exists_bounded_functional_extension (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) (η : U →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H)
    (hη : ∀ j, RationalHeightLE (η (a j)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x, ξ (φ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((Fintype.card κ + 1) *
          (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card κ) := by
  classical
  obtain ⟨ρ, hρ, hheight⟩ := exists_bounded_linear_retraction a b φ hφ hH ha
  refine ⟨η.comp ρ, fun x => by simp only [LinearMap.comp_apply, hρ], ?_⟩
  intro i
  have he : η (ρ (b i)) = ∑ j, a.repr (ρ (b i)) j * η (a j) := by
    conv_lhs => rw [← a.sum_repr (ρ (b i))]
    simp only [map_sum, map_smul, smul_eq_mul]
  change RationalHeightLE (η (ρ (b i))) _
  rw [he]
  exact rationalHeightLE_sum _ (fun j => (hheight j i).mul (hη j))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bounded_functional_preserving_subspace
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (W : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = W) (η : V →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x ∈ W, ξ x = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ W + 1) * (rationalSolveHeight (finrank ℚ W) H * K) ^ finrank ℚ W) := by
  classical
  let : FiniteDimensional ℚ V := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let a : Basis (Fin (finrank ℚ W)) ℚ W :=
    (Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan)
  have ha (i) : (a i : V) = z i := by
    simp only [a, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  have hcoords (i j) : RationalHeightLE (b.repr (W.subtype (a j)) i) H := by
    change RationalHeightLE (b.repr (a j : V) i) H
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hv k i
  have hvalues (j) : RationalHeightLE ((η.comp W.subtype) (a j)) K := by
    change RationalHeightLE (η (a j : V)) K
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hη k
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_extension a b W.subtype
    Subtype.val_injective (η.comp W.subtype) hH hcoords hvalues
  refine ⟨ξ, fun x hx => hξ ⟨x, hx⟩, ?_⟩
  simpa only [Fintype.card_fin] using hbound

theorem exists_bounded_quotient_functional
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (U I : Submodule ℚ V) (b : Basis ι ℚ (V ⧸ I))
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    (η : V →ₗ[ℚ] ℚ) (hann : U ⊓ I ≤ η.ker)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (I.mkQ (v i)) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : (V ⧸ I) →ₗ[ℚ] ℚ, (∀ x ∈ U, ξ (I.mkQ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ (U.map I.mkQ) + 1) *
          (rationalSolveHeight (finrank ℚ (U.map I.mkQ)) H * K) ^
            finrank ℚ (U.map I.mkQ)) := by
  obtain ⟨η₀, hη₀⟩ := exists_quotient_functional_preserving_subspace U I η hann
  have hmem (i) : v i ∈ U := hspan ▸ Submodule.subset_span (Set.mem_range_self i)
  have hproject : Submodule.span ℚ (Set.range (I.mkQ ∘ v)) = U.map I.mkQ := by
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_preserving_subspace b
    (U.map I.mkQ) (I.mkQ ∘ v) hproject η₀ hH hv
    (fun i => by simpa only [Function.comp_apply, hη₀ (v i) (hmem i)] using hη i)
  refine ⟨ξ, ?_, hbound⟩
  intro x hx
  rw [hξ (I.mkQ x) (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)]
  exact hη₀ x hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def stepDropBracketKernel (K V : Submodule R L) : Submodule R L where
  carrier := {x | ∀ k ∈ K, ⁅x, k⁆ ∈ V}
  zero_mem' := by intro k _; rw [zero_lie]; exact V.zero_mem
  add_mem' := by
    intro x y hx hy k hk
    rw [add_lie]
    exact V.add_mem (hx k hk) (hy k hk)
  smul_mem' := by
    intro a x hx k hk
    rw [smul_lie]
    exact V.smul_mem a (hx k hk)

noncomputable def stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) : Submodule R L :=
  U.toSubmodule ⊓ (K.comap (basisGradeProjection b w 1) ⊓
    ((stepDropBracketKernel K V).comap (basisGradeProjection b w 1) ⊓
      V.comap (LinearMap.id - basisGradeProjection b w 1)))

theorem mem_stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) (x : L) :
    x ∈ stepDropSubmodule b w U V K ↔
      x ∈ U ∧ basisGradeProjection b w 1 x ∈ K ∧
      (∀ k ∈ K, ⁅basisGradeProjection b w 1 x, k⁆ ∈ V) ∧
      x - basisGradeProjection b w 1 x ∈ V := Iff.rfl

theorem basisGradeProjection_one_lie_eq_zero [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (x y : L) :
    basisGradeProjection b w 1 ⁅x, y⁆ = 0 := by
  classical
  have hb (i j : ι) : basisGradeProjection b w 1 ⁅b i, b j⁆ = 0 := by
    apply b.repr.injective
    ext k
    simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hk
    · exact hgraded i j k (by have := hw i; have := hw j; omega)
    · rfl
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_lie_sum, smul_lie, lie_smul, map_sum, map_smul, hb, smul_zero,
    Finset.sum_const_zero]

theorem stepDropSubmodule_lie_mem [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    {x y : L} (hx : x ∈ stepDropSubmodule b w U V K) (hy : y ∈ stepDropSubmodule b w U V K) :
    ⁅x, y⁆ ∈ stepDropSubmodule b w U V K := by
  obtain ⟨hxU, _, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  obtain ⟨hyU, hyK, _, hyV⟩ := (mem_stepDropSubmodule b w U V K y).mp hy
  have hbr : ⁅x, y⁆ ∈ V := by
    have h₁ := hxbr (basisGradeProjection b w 1 y) hyK
    have h₂ := hUV _ (hU 1 x hxU) _ hyV
    have h₃ : ⁅x - basisGradeProjection b w 1 x, y⁆ ∈ V := by
      rw [← lie_skew]
      exact V.neg_mem (hUV y hyU _ hxV)
    have he : ⁅x, y⁆ =
        ⁅basisGradeProjection b w 1 x, basisGradeProjection b w 1 y⁆ +
        ⁅basisGradeProjection b w 1 x, y - basisGradeProjection b w 1 y⁆ +
        ⁅x - basisGradeProjection b w 1 x, y⁆ := by
      rw [lie_sub, sub_lie]
      abel
    rw [he]
    exact V.add_mem (V.add_mem h₁ h₂) h₃
  have hz := basisGradeProjection_one_lie_eq_zero b w hw hgraded x y
  apply (mem_stepDropSubmodule b w U V K _).mpr
  refine ⟨U.lie_mem hxU hyU, ?_, ?_, ?_⟩
  · rw [hz]
    exact K.zero_mem
  · intro k _
    rw [hz, zero_lie]
    exact V.zero_mem
  · rwa [hz, sub_zero]

noncomputable def stepDropSubalgebra [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra R L :=
  { stepDropSubmodule b w U V K with
    lie_mem' := stepDropSubmodule_lie_mem b w hw hgraded U V K hU hUV }

theorem stepDropSubmodule_graded (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V) :
    BasisGradedSubmodule b w (stepDropSubmodule b w U V K) := by
  intro j x hx
  obtain ⟨hxU, hxK, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  apply (mem_stepDropSubmodule b w U V K _).mpr
  by_cases hj : j = 1
  · subst j
    have hi := basisCoordinateProjection_idempotent b {i | w i = 1} x
    refine ⟨hU 1 x hxU, ?_, ?_, ?_⟩
    · simpa only [basisGradeProjection, hi] using hxK
    · intro k hk
      simpa only [basisGradeProjection, hi] using hxbr k hk
    · rw [show basisGradeProjection b w 1 (basisGradeProjection b w 1 x) =
        basisGradeProjection b w 1 x from hi, sub_self]
      exact V.zero_mem
  · have hz := basisGradeProjection_other b w (Ne.symm hj) x
    have hback := basisGradeProjection_other b w hj x
    have hv := hV j _ hxV
    rw [map_sub, hback, sub_zero] at hv
    refine ⟨hU j x hxU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

theorem stepDropSubmodule_mem_higher_grade (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) {j : ℕ} (hj : j ≠ 1)
    {x : L} (hx : basisGradeProjection b w j x = x) :
    x ∈ stepDropSubmodule b w U V K ↔ x ∈ U ∧ x ∈ V := by
  have hz : basisGradeProjection b w 1 x = 0 := by
    rw [← hx]
    exact basisGradeProjection_other b w (Ne.symm hj) x
  rw [mem_stepDropSubmodule]
  constructor
  · rintro ⟨hU, _, _, hV⟩
    exact ⟨hU, by simpa only [hz, sub_zero] using hV⟩
  · rintro ⟨hU, hV⟩
    refine ⟨hU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

def rightLieLinear {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L] (k : L) : L →ₗ[R] L where
  toFun x := ⁅x, k⁆
  map_add' x y := add_lie x y k
  map_smul' a x := smul_lie a x k

@[simp] theorem rightLieLinear_apply {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (k x : L) : rightLieLinear (R := R) k x = ⁅x, k⁆ := rfl

theorem stepDropBracketKernel_eq_iInf {R L κ : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    [Fintype κ] (K V : Submodule R L) (e : Basis κ R K) :
    stepDropBracketKernel K V = ⨅ z, V.comap (rightLieLinear (e z : L)) := by
  classical
  ext x
  change (∀ k ∈ K, ⁅x, k⁆ ∈ V) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap, rightLieLinear_apply]
  constructor
  · intro h z
    exact h (e z) (e z).property
  · intro h k hk
    have he : (∑ z, e.repr ⟨k, hk⟩ z • (e z : L)) = k := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg K.subtype (e.sum_repr ⟨k, hk⟩)
    rw [← he, lie_sum]
    apply V.sum_mem
    intro z _
    rw [lie_smul]
    exact V.smul_mem _ (h z)

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightLieLinear_baseChange (k : L) :
    (rightLieLinear (R := ℚ) k).baseChange ℝ = rightLieLinear (R := ℝ) ((1 : ℝ) ⊗ₜ[ℚ] k) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, rightLieLinear_apply,
      LieAlgebra.ExtendScalars.bracket_tmul, mul_one]

theorem stepDropBracketKernel_baseChange [Fintype κ]
    (K V : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropBracketKernel K V).baseChange ℝ = stepDropBracketKernel (K.baseChange ℝ) (V.baseChange ℝ) := by
  apply le_antisymm
  · intro x hx k hk
    exact lie_mem_real_baseChange (stepDropBracketKernel K V) K V
      (fun _ ha _ hb => ha _ hb) hx hk
  · intro x hx
    rw [stepDropBracketKernel_eq_iInf K V e, real_baseChange_iInf]
    rw [Submodule.mem_iInf]
    intro z
    rw [realification_comap]
    change (rightLieLinear (R := ℚ) (e z : L)).baseChange ℝ x ∈ V.baseChange ℝ
    rw [rightLieLinear_baseChange, rightLieLinear_apply]
    exact hx _ (Submodule.tmul_mem_baseChange_of_mem 1 (e z).property)

theorem stepDropSubmodule_baseChange [Fintype κ]
    (b : Basis ι ℚ L) (w : ι → ℕ) (U : LieSubalgebra ℚ L)
    (V K : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropSubmodule b w U V K).baseChange ℝ =
      stepDropSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U) (V.baseChange ℝ) (K.baseChange ℝ) := by
  simp only [stepDropSubmodule, realification_inf, realification_comap,
    stepDropBracketKernel_baseChange K V e, basisGradeProjection,
    basisCoordinateProjection_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_id,
    realificationLieSubalgebra_toSubmodule]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {R L μ : Type*} [Field R] [AddCommGroup L] [Module R L]

noncomputable def homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) : Submodule R L :=
  U ⊓ (V ⊓ LinearMap.ker (basisGradeProjection b w j - LinearMap.id))

theorem mem_homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) (x : L) :
    x ∈ homogeneousIntersection b w j U V ↔
      x ∈ U ∧ x ∈ V ∧ basisGradeProjection b w j x = x := by
  simp only [homogeneousIntersection, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem homogeneousIntersection_finrank_le [Fintype μ]
    (b : Basis μ R L) (w : μ → ℕ) (j : ℕ) (U V : Submodule R L) :
    Module.finrank R (homogeneousIntersection b w j U V) ≤ Fintype.card μ := by
  let : FiniteDimensional R L := b.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (homogeneousIntersection b w j U V).subtype) (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis b] using h

theorem homogeneousIntersection_baseChange {L μ : Type*} [AddCommGroup L] [Module ℚ L]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L) :
    (homogeneousIntersection b w j U V).baseChange ℝ =
      homogeneousIntersection (b.baseChange ℝ) w j (U.baseChange ℝ) (V.baseChange ℝ) := by
  simp only [homogeneousIntersection, realification_inf, realification_ker,
    LinearMap.baseChange_sub, LinearMap.baseChange_id, basisGradeProjection,
    basisCoordinateProjection_baseChange]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

abbrev StepDropRow (υ χ κ ν : Type*) := υ ⊕ χ ⊕ (κ × ν) ⊕ ν

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepDropSystem (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    L →ₗ[ℚ] (StepDropRow υ χ κ ν → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.toSubmodule.mkQ
    | .inr (.inl i) => (fK.coord i).comp (K.mkQ.comp (basisGradeProjection b w 1))
    | .inr (.inr (.inl z)) => (fV.coord z.2).comp
        (V.mkQ.comp ((rightLieLinear (eK z.1 : L)).comp (basisGradeProjection b w 1)))
    | .inr (.inr (.inr i)) => (fV.coord i).comp
        (V.mkQ.comp (LinearMap.id - basisGradeProjection b w 1))

theorem stepDrop_quotient_mem_iff {ρ : Type*} (V : Submodule ℚ L)
    (f : Basis ρ ℚ (L ⧸ V)) (x : L) :
    x ∈ V ↔ ∀ i, f.repr (V.mkQ x) i = 0 := by
  simp only [Submodule.mkQ_apply]
  constructor
  · intro hx i
    rw [(Submodule.Quotient.mk_eq_zero V).mpr hx, map_zero]
    rfl
  · intro h
    apply (Submodule.Quotient.mk_eq_zero V).mp
    apply f.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i

theorem stepDropSystem_ker [Fintype κ] (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    LinearMap.ker (stepDropSystem b w U V K fU fK fV eK) = stepDropSubmodule b w U V K := by
  ext x
  rw [LinearMap.mem_ker, mem_stepDropSubmodule]
  constructor
  · intro hx
    have hU := (stepDrop_quotient_mem_iff U.toSubmodule fU x).mpr
      (fun i => congrFun hx (.inl i))
    have hK := (stepDrop_quotient_mem_iff K fK (basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inl i)))
    have hbr : basisGradeProjection b w 1 x ∈ stepDropBracketKernel K V := by
      rw [stepDropBracketKernel_eq_iInf K V eK, Submodule.mem_iInf]
      intro z
      exact (stepDrop_quotient_mem_iff V fV _).mpr
        (fun i => congrFun hx (.inr (.inr (.inl (z, i)))))
    have hV := (stepDrop_quotient_mem_iff V fV (x - basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inr (.inr i))))
    exact ⟨hU, hK, hbr, hV⟩
  · rintro ⟨hU, hK, hbr, hV⟩
    funext i
    rcases i with i | i | ⟨z, i⟩ | i
    · exact (stepDrop_quotient_mem_iff U.toSubmodule fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff K fK _).mp hK i
    · exact (stepDrop_quotient_mem_iff V fV _).mp (hbr (eK z) (eK z).property) i
    · exact (stepDrop_quotient_mem_iff V fV _).mp hV i

theorem stepDropSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B)
    (i : StepDropRow υ χ κ ν) (j : μ) :
    RationalHeightLE (stepDropSystem b w U V K fU fK fV eK (b j) i) (max H B) := by
  classical
  have hp : basisGradeProjection b w 1 (b j) = if w j = 1 then b j else 0 :=
    basisCoordinateProjection_basis b {i | w i = 1} j
  have hzero := rationalHeightLE_zero (hH.trans (Nat.le_max_left H B))
  rcases i with i | i | ⟨z, i⟩ | i
  · exact (hU i j).mono (Nat.le_max_left H B)
  · change RationalHeightLE (fK.repr (K.mkQ (basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · exact (hK i j).mono (Nat.le_max_left H B)
    · simpa only [map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ ⁅basisGradeProjection b w 1 (b j), (eK z : L)⁆) i) _
    rw [hp]
    split_ifs
    · exact (hbr i j z).mono (Nat.le_max_right H B)
    · simpa only [zero_lie, map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ (b j - basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using hzero
    · simpa only [sub_zero] using (hV i j).mono (Nat.le_max_left H B)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem stepDropSubmodule_top_frequency
    {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (b : Basis ι R L) (w : ι → ℕ) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[R] R) {s : ℕ} (hs : 2 ≤ s)
    (hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    {x : L} (hx : x ∈ stepDropSubmodule b w U V K) :
    η (basisGradeProjection b w s x) = 0 := by
  have hmem := stepDropSubmodule_graded b w U V K hU hV s x hx
  have hpure : basisGradeProjection b w s (basisGradeProjection b w s x) =
      basisGradeProjection b w s x := basisCoordinateProjection_idempotent b {i | w i = s} x
  exact hη _ ((stepDropSubmodule_mem_higher_grade b w U V K (by omega) hpure).mp hmem).2 hpure

namespace NilpotentLieFiltration

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_coefficients_mem_stepDropSubmodule
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈
      stepDropSubmodule (b.baseChange ℝ) w U (V.baseChange ℝ) (K.baseChange ℝ) := by
  apply (mem_stepDropSubmodule _ _ _ _ _ _).mpr
  refine ⟨W.state.mem_U α, W.state.horizontal α, ?_, ?_⟩
  · rintro k ⟨x, rfl⟩
    apply real_bracket_mem_of_basis (eK.baseChange ℝ) (K.subtype.baseChange ℝ) (V.baseChange ℝ)
      (basisGradeProjection (b.baseChange ℝ) w 1 (coefficients W.state.P.coord α)) _ x
    intro z
    simpa only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply] using
      W.terminal_lower_bracket hs 1 (by omega) z α
  · have h := F.real_sub_horizontal_mem_of_lower_grades b w hF (V.baseChange ℝ)
      (j := s + 1) (by omega) (coefficients W.state.P.coord α)
      (fun d hd hds => W.terminal_lower_log hs α d hd (by omega))
    rw [F.realLayer_terminal] at h
    simpa only [LieSubmodule.bot_toSubmodule, sup_bot_eq] using h

theorem FormalInductionRun.terminal_coefficients_mem_rational_stepDrop
    {U₀ : LieSubalgebra ℚ L}
    (W : F.FormalInductionRun b w (realificationLieSubalgebra U₀) V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈ (stepDropSubmodule b w U₀ V K).baseChange ℝ := by
  rw [stepDropSubmodule_baseChange b w U₀ V K eK]
  exact W.terminal_coefficients_mem_stepDropSubmodule hs hF α

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]

theorem exists_bounded_submodule_quotient_basis (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) (rationalKernelHeight t H) := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (v j) i
  have hA : LinearMap.range A.mulVecLin = U.map b.equivFun.toLinearMap := by
    rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ :=
    exists_bounded_image_equations A hH (fun i j => hv j i)
  have hkerD := hker.trans hA
  let f := submoduleQuotientCoordinateBasis b U D hkerD hsurj
  have hf : LinearMap.toMatrix b f U.mkQ = D :=
    submoduleQuotientCoordinateBasis_matrix b U D hkerD hsurj
  refine ⟨t, ht, d, hd, f, fun i j => ?_⟩
  have hij := congrFun (congrFun hf i) j
  rw [LinearMap.toMatrix_apply] at hij
  rw [hij]
  exact hD i j

theorem exists_submodule_quotient_basis_exp (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hm : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) H' := by
  obtain ⟨t, ht, d, hd, f, hf⟩ := exists_bounded_submodule_quotient_basis b U v hspan hH hv
  exact ⟨rationalKernelHeight t H, rationalKernelHeight_pos t hH,
    rationalKernelHeight_le_budget t H hp ((Nat.cast_le.mpr ht).trans hm) hHp,
    d, hd, f, hf⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]
  (e : Basis ν ℚ L) (H : ℕ)

noncomputable def chosenBoundedSubmoduleBasis (U : Submodule ℚ L) :
    Basis (Fin (finrank ℚ U)) ℚ U := by
  classical
  exact if h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H then h.choose else Module.finBasis ℚ U

theorem chosenBoundedSubmoduleBasis_height (U : Submodule ℚ L)
    (h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H) (j k) :
    RationalHeightLE (e.repr (chosenBoundedSubmoduleBasis e H U j).val k) H := by
  classical
  unfold chosenBoundedSubmoduleBasis
  rw [dif_pos h]
  exact h.choose_spec j k

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_submodule_basis_from_spanning
    {L μ κ : Type*} [AddCommGroup L] [Module ℚ L] [Fintype μ]
    (b : Basis μ ℚ L) (V : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = V) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ V)) ℚ V,
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact hv k j

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

theorem exists_stepDrop_bounded_basis (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B) :
    ∃ r : ℕ, r ≤ Fintype.card (StepDropRow υ χ κ ν) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
        ℚ (stepDropSubmodule b w U V K),
        ∀ i j, RationalHeightLE (b.repr (e i : L) j)
          ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
  classical
  let P := stepDropSystem b w U V K fU fK fV eK
  have hP : ∀ i j, RationalHeightLE ((Pi.basisFun ℚ (StepDropRow υ χ κ ν)).repr (P (b i)) j) (max H B) := by
    intro i j
    change RationalHeightLE (P (b i) j) _
    exact stepDropSystem_basis_height b w U V K fU fK fV eK hH hU hK hV hbr j i
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (StepDropRow υ χ κ ν)) P b
    (hH.trans (Nat.le_max_left H B)) (basis_repr_height_one b) hP
  have hspan' : Submodule.span ℚ (Set.range v) = stepDropSubmodule b w U V K := by
    simpa only [b.span_eq, top_inf_eq, P, stepDropSystem_ker] using hspan
  have hv' : ∀ i j, RationalHeightLE (b.repr (v i) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
    simpa only [mul_one] using hv
  obtain ⟨e, he⟩ := exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'
  exact ⟨r, hr, e, he⟩

def stepDropBracketHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H) ^ n

omit [Fintype κ] [Fintype ν] in
theorem stepDrop_bracket_height (b : Basis μ ℚ L) (V K : Submodule ℚ L)
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ}
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) (i : ν) (j : μ) (z : κ) :
    RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) (stepDropBracketHeight (Fintype.card μ) H) := by
  have hbr := lie_bracket_coordinate_height b hstructure (b j) (eK z : L)
    (basis_repr_height_one b j) (fun k => heK k z)
  have h := linearMap_coordinate_height b fV V.mkQ (fun a c => hV c a) _ hbr i
  simpa only [stepDropBracketHeight, mul_one] using h

theorem stepDrop_basis_height_budget (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  have hkernel := rationalKernelHeight_le_budget r H hp hr hH
  have hfront : (n + 1 : ℝ) ≤ Real.exp n := Real.add_one_le_exp n
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (rationalKernelHeight r H)) hkernel n
  rw [← Real.exp_nat_mul] at hpower
  have h : (((n + 1) * rationalKernelHeight r H ^ n : ℕ) : ℝ) ≤
      Real.exp ((n : ℝ) + n * (p + 2) ^ 7) := by
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (Real.exp_nonneg _)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have ht : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : p + 2 ≤ (p + 2) ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 8)
  calc
    (n : ℝ) + n * (p + 2) ^ 7 ≤ p + p * (p + 2) ^ 7 := by gcongr
    _ ≤ (p + 2) + (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
    _ = (p + 2) + (p + 2) ^ 8 := by ring
    _ ≤ 2 * (p + 2) ^ 8 := by linarith
    _ ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (p + 2) ^ 9 := by ring

theorem exists_stepDrop_basis_exp_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 9)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + 2) ^ 9)) := by
  obtain ⟨r, hr, e, he⟩ := exists_stepDrop_bounded_basis b w U V K fU fK fV eK hH hU hK hV hbr
  have hrp : (r : ℝ) ≤ p := (Nat.cast_le.mpr hr).trans hrows
  have hb := stepDrop_basis_height_budget (Fintype.card μ) r H hp hμ hrp hHp
  refine ⟨e, fun i j => ?_⟩
  have hij : RationalHeightLE (b.repr (e i : L) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r H ^ Fintype.card μ) := by
    simpa only [max_self] using he i j
  exact ⟨(Nat.cast_le.mpr hij.1).trans hb, (Nat.cast_le.mpr hij.2).trans hb⟩

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def preimageBasisBudget (p : ℝ) : ℝ :=
  sparseGeneratorBudget (p + (p + (p + 3) ^ 7 + 2) ^ 4 + 1)

theorem preimageBasisBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ preimageBasisBudget p := by
  apply sparseGeneratorBudget_nonneg
  positivity

theorem exists_preimage_basis_logHeight
    {V W μ ν ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype μ] [Fintype ν] [Fintype ι] [Fintype κ]
    (e : Basis μ ℚ V) (f : Basis ν ℚ W) (U : Submodule ℚ V) (K : Submodule ℚ W)
    (T : V →ₗ[ℚ] W) (u : ι → V) (v : κ → W)
    (hu : Submodule.span ℚ (Set.range u) = U)
    (hv : Submodule.span ℚ (Set.range v) = K)
    {p : ℝ} (hp : 0 ≤ p) (hν : (Fintype.card ν : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (huH : ∀ a i, rationalLogHeight (e.repr (u a) i) ≤ p)
    (hvH : ∀ a i, rationalLogHeight (f.repr (v a) i) ≤ p)
    (hTu : ∀ a i, rationalLogHeight (f.repr (T (u a)) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ K.comap T : Submodule ℚ V))) ℚ
        (U ⊓ K.comap T : Submodule ℚ V),
      ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ preimageBasisBudget p := by
  obtain ⟨H, _, hH, d, hd, g, hg⟩ := exists_submodule_quotient_basis_exp f K v hv
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hvH a i))
    (show 0 ≤ p + 1 by linarith) (hκ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  have hgH (i : ν) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (f i)) j) ≤ (p + 3) ^ 7 := by
    have h := rationalLogHeight_le_of_height (hg j i) hH
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  let q := p + (p + 3) ^ 7
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hquot (a : ι) (j : Fin d) :
      rationalLogHeight (g.repr (K.mkQ (T (u a))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight f g K.mkQ hq (hν.trans hpq)
      (fun i j => (hgH i j).trans (le_add_of_nonneg_left hp))
      (T (u a)) (fun i => (hTu a i).trans hpq) j
  let Q := p + (q + 2) ^ 4
  have hpQ : p ≤ Q := le_add_of_nonneg_right (by positivity)
  have hQ : 0 ≤ Q := hp.trans hpQ
  let B := ⌈Real.exp Q⌉₊
  obtain ⟨t, ht, z, hz, hzH⟩ := exists_bounded_span_kernel_generators e g
    (K.mkQ.comp T) u (one_le_ceil_exp Q)
    (fun a i => rationalHeightLE_ceil_exp ((huH a i).trans hpQ))
    (fun a i => rationalHeightLE_ceil_exp
      ((hquot a i).trans (le_add_of_nonneg_left hp)))
  have hker : LinearMap.ker (K.mkQ.comp T) = K.comap T := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hu, hker] at hz
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e _ z hz hzH
  have ht' : (t : ℝ) ≤ p := by
    exact (Nat.cast_le.mpr ((show t ≤ d by simpa only [Fintype.card_fin] using ht).trans hd)).trans hν
  have hcost : (((Fintype.card ι + 1) * (rationalKernelHeight t B * B) ^
      Fintype.card ι : ℕ) : ℝ) ≤ Real.exp (preimageBasisBudget p) :=
    sparseGeneratorHeight_bound (show 0 ≤ Q + 1 by linarith) t (Fintype.card ι) B
      (ht'.trans (hpQ.trans (by linarith))) (hι.trans (hpQ.trans (by linarith)))
      (ceil_exp_le_exp_add_one hQ)
  exact ⟨b, fun a i => rationalLogHeight_le_of_height (hb a i) hcost⟩

end Erdos3

end

section

namespace Erdos3

open Module

def rankQuotientLayerHeight (n m H : ℕ) : ℕ :=
  (n + 1) * (H * rationalKernelHeight m H) ^ n

def rankQuotientFrequencyHeight (n m u H : ℕ) : ℕ :=
  (u + 1) * (rationalSolveHeight u (rankQuotientLayerHeight n m H) *
    ((n + 1) * (H * H) ^ n)) ^ u

def rankQuotientHeight (n m q u H : ℕ) : ℕ :=
  max 1 (max (rationalKernelHeight m H)
    (max (rationalLieStructureHeight n (max H (max (rationalKernelHeight m H)
      (rationalSolveHeight q (rationalKernelHeight m H)))))
      (max (rankQuotientLayerHeight n m H) (rankQuotientFrequencyHeight n m u H))))

theorem exists_bounded_rank_quotient_data
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n t : ℕ}
    (F : DegreeRankLieFiltration L s r) (e : Basis (Fin n) ℚ L)
    (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
      ℚ (F.associatedDegree.layer (i.val + 1)))
    (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
      ℚ (F.layer i.val j.val))
    (I : LieIdeal ℚ L) (a : Basis (Fin t) ℚ I)
    (η : L →ₗ[ℚ] ℚ) (hann : F.layer s r ⊓ I.toSubmodule ≤ η.ker)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (ha : ∀ i j, RationalHeightLE (e.repr (a i).val j) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hη : ∀ i, RationalHeightLE (η (e i)) H) :
    ∃ m : ℕ, m ≤ t ∧ ∃ q : ℕ, q ≤ n ∧ ∃ u : ℕ, u ≤ q ∧
      ∃ f : Basis (Fin q) ℚ (L ⧸ I),
        (∀ i j, RationalHeightLE (f.repr (lieQuotientMap I (e j)) i)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k)
          (rankQuotientHeight n m q u H)) ∧
        (∀ i : Fin (s + 1), ∃ b' : Basis
            (Fin (finrank ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.associatedDegree.layer (i.val + 1)).map (lieQuotientMap I).toLinearMap),
          ∀ a j, RationalHeightLE (f.repr (b' a).val j) (rankQuotientHeight n m q u H)) ∧
        (∀ i j : Fin (s + 1), ∃ c' : Basis
            (Fin (finrank ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap)))
            ℚ ((F.layer i.val j.val).map (lieQuotientMap I).toLinearMap),
          ∀ a k, RationalHeightLE (f.repr (c' a).val k) (rankQuotientHeight n m q u H)) ∧
        ∃ ξ : (L ⧸ I) →ₗ[ℚ] ℚ,
          (∀ x ∈ F.layer s r, ξ (lieQuotientMap I x) = η x) ∧
          ∀ i, RationalHeightLE (ξ (f i)) (rankQuotientHeight n m q u H) := by
  classical
  obtain ⟨m, hm, q, hq, f, A, _, hmatrix, _, hA, _, hstructure⟩ :=
    exists_bounded_lie_quotient_with_structure e I (fun i => (a i).val)
      (span_submodule_basis I.toSubmodule a) hH (fun i j => ha j i) hbracket
  have hm' : m ≤ t := by simpa only [Fintype.card_fin] using hm
  have hq' : q ≤ n := by simpa only [Fintype.card_fin] using hq
  let π := (lieQuotientMap I).toLinearMap
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hH
  have hE : 1 ≤ E := by
    have : 0 < H := by omega
    have : 0 < Q := by omega
    change 1 ≤ (n + 1) * (H * Q) ^ n
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hproj (i j) : RationalHeightLE (f.repr (π (e j)) i) Q := by
    have h := hA i j
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  have himage (P : Submodule ℚ L)
      (bP : Basis (Fin (finrank ℚ P)) ℚ P)
      (hP : ∀ i j, RationalHeightLE (e.repr (bP i).val j) H) :
      ∃ b' : Basis (Fin (finrank ℚ (P.map π))) ℚ (P.map π),
        ∀ i j, RationalHeightLE (f.repr (b' i).val j) E := by
    have hspan : Submodule.span ℚ (Set.range (fun i => π (bP i).val)) = P.map π := by
      change Submodule.span ℚ (Set.range (π ∘ (fun i => (bP i).val))) = _
      rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (bP i).val) hspan
    intro i j
    simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using
      linearMap_coordinate_height e f π (fun i j => hproj j i) (bP i).val (hP i) j
  let u := finrank ℚ ((F.layer s r).map π)
  let _ : FiniteDimensional ℚ (L ⧸ I) := f.finiteDimensional_of_finite
  have hu : u ≤ q := by
    have hfq : finrank ℚ (L ⧸ I) = q := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis f
    exact (Submodule.finrank_le _).trans_eq hfq
  let cs := c ⟨s, Nat.lt_succ_self s⟩ ⟨r, Nat.lt_succ_of_le F.rank_le_degree⟩
  obtain ⟨ξ, hξ, hξH⟩ := exists_bounded_quotient_functional (F.layer s r) I.toSubmodule f
    (fun i => (cs i).val) (span_submodule_basis _ cs) η hann hE
    (fun i j => by
      change RationalHeightLE (f.repr (π (cs i).val) j) E
      simpa only [Fintype.card_fin, E, Q, rankQuotientLayerHeight] using linearMap_coordinate_height e f π
        (fun i j => hproj j i) (cs i).val (hc _ _ i) j)
    (fun i => by
      simpa only [Fintype.card_fin] using
        linearFunctional_coordinate_height e η hη (cs i).val (hc _ _ i))
  let K := rankQuotientHeight n m q u H
  have hQK : Q ≤ K := by dsimp only [K, rankQuotientHeight, Q]; omega
  have hEK : E ≤ K := by dsimp only [K, rankQuotientHeight, E]; omega
  have hSK : rationalLieStructureHeight n
      (max H (max Q (rationalSolveHeight q Q))) ≤ K := by
    dsimp only [K, rankQuotientHeight, Q]; omega
  have hFK : rankQuotientFrequencyHeight n m u H ≤ K := by
    dsimp only [K, rankQuotientHeight]; omega
  refine ⟨m, hm', q, hq', u, hu, f, fun i j => (hproj i j).mono hQK,
    ?_, ?_, ?_, ξ, hξ, fun i => (hξH i).mono hFK⟩
  · intro i j k
    have h : RationalHeightLE (lieStructureConstants f i j k)
        (rationalLieStructureHeight n (max H (max Q (rationalSolveHeight q Q)))) := by
      simpa only [Fintype.card_fin] using hstructure i j k
    exact h.mono hSK
  · intro i
    obtain ⟨b', hb'⟩ := himage _ (b i) (hb i)
    exact ⟨b', fun a j => (hb' a j).mono hEK⟩
  · intro i j
    obtain ⟨c', hc'⟩ := himage _ (c i j) (hc i j)
    exact ⟨c', fun a k => (hc' a k).mono hEK⟩

end Erdos3

end

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]

theorem chosenBasis_smul_coordinate_height (e : Basis ν ℚ L) (H : ℕ)
    (U V : Submodule ℚ L) (hUV : U = V)
    (j : Fin (finrank ℚ U)) (v : V) (q : ℚ) {K : ℕ}
    (hq : RationalHeightLE q K)
    (hv : v.val = q • (chosenBoundedSubmoduleBasis e H U j).val)
    (k : Fin (finrank ℚ V)) :
    RationalHeightLE ((chosenBoundedSubmoduleBasis e H V).repr v k) K := by
  subst V
  have he : v = q • chosenBoundedSubmoduleBasis e H U j := Subtype.ext hv
  rw [he, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hb : RationalHeightLE ((chosenBoundedSubmoduleBasis e H U).repr
      (chosenBoundedSubmoduleBasis e H U j) k) 1 := by
    classical
    rw [Basis.repr_self]
    by_cases hkj : k = j <;> simp [hkj, RationalHeightLE]
  simpa only [Nat.mul_one] using hq.mul hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {L μ υ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def homogeneousIntersectionSystem (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    L →ₗ[ℚ] (υ ⊕ ν ⊕ μ → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.mkQ
    | .inr (.inl i) => (fV.coord i).comp V.mkQ
    | .inr (.inr i) => (b.coord i).comp (basisGradeProjection b w j - LinearMap.id)

theorem homogeneousIntersectionSystem_ker (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) :
    LinearMap.ker (homogeneousIntersectionSystem b w j U V fU fV) = homogeneousIntersection b w j U V := by
  ext x
  rw [LinearMap.mem_ker, mem_homogeneousIntersection]
  constructor
  · intro hx
    refine ⟨(stepDrop_quotient_mem_iff U fU x).mpr (fun i => congrFun hx (.inl i)),
      (stepDrop_quotient_mem_iff V fV x).mpr (fun i => congrFun hx (.inr (.inl i))), ?_⟩
    apply sub_eq_zero.mp
    apply b.repr.injective
    ext i
    have hi := congrFun hx (.inr (.inr i))
    change b.repr (basisGradeProjection b w j x - x) i = 0 at hi
    simpa only [map_zero, Finsupp.zero_apply] using hi
  · rintro ⟨hU, hV, hj⟩
    funext i
    rcases i with i | i | i
    · exact (stepDrop_quotient_mem_iff U fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff V fV x).mp hV i
    · change b.repr (basisGradeProjection b w j x - x) i = 0
      rw [hj, sub_self, map_zero]
      rfl

theorem homogeneousIntersectionSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule ℚ L) (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V))
    {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H)
    (i : υ ⊕ ν ⊕ μ) (k : μ) :
    RationalHeightLE (homogeneousIntersectionSystem b w j U V fU fV (b k) i) H := by
  classical
  rcases i with i | i | i
  · exact hU i k
  · exact hV i k
  · change RationalHeightLE (b.repr (basisGradeProjection b w j (b k) - b k) i) H
    have hp : basisGradeProjection b w j (b k) = if w k = j then b k else 0 :=
      basisCoordinateProjection_basis b {i | w i = j} k
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    · simpa only [zero_sub, map_neg, Finsupp.neg_apply] using (basis_repr_height_one b k i).neg.mono hH

def homogeneousIntersectionBasisHeight (n r H : ℕ) : ℕ :=
  (n + 1) * rationalKernelHeight r H ^ n

theorem exists_homogeneousIntersection_basis [Fintype μ] [Fintype υ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U)) (fV : Basis ν ℚ (L ⧸ V)) {H r : ℕ}
    (hH : 1 ≤ H) (hr : Fintype.card υ + Fintype.card ν + Fintype.card μ ≤ r)
    (hU : ∀ i k, RationalHeightLE (fU.repr (U.mkQ (b k)) i) H)
    (hV : ∀ i k, RationalHeightLE (fV.repr (V.mkQ (b k)) i) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ (homogeneousIntersection b w j U V)))
      ℚ (homogeneousIntersection b w j U V), ∀ i k,
      RationalHeightLE (b.repr (e i : L) k) (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
  classical
  let P := homogeneousIntersectionSystem b w j U V fU fV
  have hP : ∀ i k, RationalHeightLE ((Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)).repr (P (b i)) k) H := by
    intro i k
    change RationalHeightLE (P (b i) k) H
    exact homogeneousIntersectionSystem_basis_height b w j U V fU fV hH hU hV k i
  obtain ⟨t, ht, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (υ ⊕ ν ⊕ μ)) P b hH (basis_repr_height_one b) hP
  have htr : t ≤ r := by
    simp only [Fintype.card_sum] at ht
    omega
  have hspan' : Submodule.span ℚ (Set.range v) = homogeneousIntersection b w j U V := by
    simpa only [b.span_eq, top_inf_eq, P, homogeneousIntersectionSystem_ker] using hspan
  have hv' : ∀ i k, RationalHeightLE (b.repr (v i) k)
      (homogeneousIntersectionBasisHeight (Fintype.card μ) r H) := by
    intro i k
    apply (hv i k).mono
    simp only [homogeneousIntersectionBasisHeight, mul_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (rationalKernelHeight_mono hH htr) _)
  exact exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'

end Erdos3

end

section

namespace Erdos3

theorem rankQuotientHeight_le_exp (n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) := by
  let Q := rationalKernelHeight m H
  let E := rankQuotientLayerHeight n m H
  let V := (n + 1) * (H * H) ^ n
  let P := (p + 2) ^ 51
  have hpP : p ≤ P := le_power_budget hp (by decide : 1 ≤ 51)
  have hP : 0 ≤ P := hp.trans hpP
  have hbase : 1 ≤ p + 2 := by linarith
  have hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ 7) := rationalKernelHeight_le_budget m H hp hm hH
  have hH7 : (H : ℝ) ≤ Real.exp ((p + 2) ^ 7) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide)))
  have hprod {A B : ℕ} (hA : (A : ℝ) ≤ Real.exp ((p + 2) ^ 7))
      (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ 7)) :
      ((A * B : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 7) * Real.exp ((p + 2) ^ 7) :=
        mul_le_mul hA hB (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ 7) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          _ ≤ (p + 2) * (p + 2) ^ 7 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by ring)
  have hE10 : (E : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * Q) hp 8 1 (hprod hH7 hQ)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hV10 : (V : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    exact rational_sum_cost_le_exp n (H * H) hp 8 1 (hprod hH7 hH7)
      (by simpa only [pow_one] using hn.trans (show p ≤ p + 2 by linarith))
  have hEP : (E : ℝ) ≤ Real.exp P :=
    hE10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hVP : (V : ℝ) ≤ Real.exp P :=
    hV10.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 10 ≤ 51)))
  have hfreq0 := embedding_coordinate_height_budget u u E V hP
    (hu.trans hpP) (hu.trans hpP) hEP hVP
  have hfreq : (rankQuotientFrequencyHeight n m u H : ℝ) ≤ Real.exp ((p + 2) ^ 424) :=
    exponential_budget_comp hp hP 51 8 le_rfl hfreq0
  have h51 : P ≤ (p + 2) ^ 424 := pow_le_pow_right₀ hbase (by decide : 51 ≤ 424)
  have hstructure := rationalLieQuotientStructureHeight_le_exp n m q H hp hn hm hq hH
  simp only [rankQuotientHeight, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ (max_le ?_ (max_le ?_ hfreq)))
  · exact hQ.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 7 ≤ 424)))
  · exact hstructure.trans (Real.exp_le_exp.mpr h51)
  · exact hEP.trans (Real.exp_le_exp.mpr h51)

theorem dependentQuotientHeight_le_exp (s n m q u H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hu : (u : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rankQuotientHeight n m q u (lieTreeHeight n H s) : ℝ) ≤
      Real.exp ((p + 2) ^ ((6 * s + 4) * 424)) := by
  let P := (p + 2) ^ (6 * s + 2)
  have hpP : p ≤ P := le_power_budget hp (by omega : 1 ≤ 6 * s + 2)
  have hP : 0 ≤ P := hp.trans hpP
  have h := rankQuotientHeight_le_exp n m q u (lieTreeHeight n H s) hP
    (hn.trans hpP) (hm.trans hpP) (hq.trans hpP) (hu.trans hpP)
    (lieTreeHeight_le_exp n H s hp hn hH)
  have hc := exponential_budget_comp hp hP (6 * s + 2) 424 le_rfl h
  simpa only [show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (b : Basis ι ℚ L)

noncomputable def coordinateArraySpan (m : ℕ) (c : Fin m × ι → ℚ) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range fun a : Fin m => b.equivFun.symm (fun i => c (a, i)))

noncomputable def heightBoundedSubspaces (m H : ℕ) : Set (Submodule ℚ L) :=
  coordinateArraySpan b m '' {c : Fin m × ι → ℚ | ∀ z, RationalHeightLE (c z) H}

theorem mem_heightBoundedSubspaces (m H : ℕ) (U : Submodule ℚ L) :
    U ∈ heightBoundedSubspaces b m H ↔
      ∃ v : Fin m → L, Submodule.span ℚ (Set.range v) = U ∧
        ∀ a i, RationalHeightLE (b.repr (v a) i) H := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a => b.equivFun.symm (fun i => c (a, i)), rfl, ?_⟩
    intro a i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hc (a, i)
  · rintro ⟨v, hv, hh⟩
    refine ⟨fun z => b.repr (v z.1) z.2, (fun z => hh z.1 z.2), ?_⟩
    have he : (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i)) = v := by
      funext a
      apply b.equivFun.injective
      simp only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply]
    change Submodule.span ℚ (Set.range (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i))) = U
    rw [he, hv]

theorem finite_card_heightBoundedSubspaces (m H : ℕ) :
    (heightBoundedSubspaces b m H).Finite ∧
      (heightBoundedSubspaces b m H).ncard ≤ ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  let S : Set (Fin m × ι → ℚ) := {c | ∀ z, RationalHeightLE (c z) H}
  obtain ⟨hfin, hcard⟩ := finite_card_bounded_height_arrays S H (fun _ hc => hc)
  refine ⟨hfin.image (coordinateArraySpan b m), ?_⟩
  have hh := (Set.ncard_image_le (f := coordinateArraySpan b m) hfin).trans hcard
  rw [Fintype.card_prod, Fintype.card_fin] at hh
  exact hh

section Lie

variable {A : Type*} [LieRing A] [LieAlgebra ℚ A] (e : Basis ι ℚ A)

noncomputable def heightBoundedLieSubalgebras (m H : ℕ) : Set (LieSubalgebra ℚ A) :=
  {K | K.toSubmodule ∈ heightBoundedSubspaces e m H}

theorem finite_card_heightBoundedLieSubalgebras (m H : ℕ) :
    (heightBoundedLieSubalgebras e m H).Finite ∧
      (heightBoundedLieSubalgebras e m H).ncard ≤
        ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  classical
  obtain ⟨hfin, hcard⟩ := finite_card_heightBoundedSubspaces e m H
  let f : heightBoundedLieSubalgebras e m H → heightBoundedSubspaces e m H :=
    fun K => ⟨K.val.toSubmodule, K.property⟩
  have hf : Function.Injective f := by
    intro K J h
    exact Subtype.ext (LieSubalgebra.toSubmodule_injective (congrArg Subtype.val h))
  let : Fintype (heightBoundedSubspaces e m H) := hfin.fintype
  let : Finite (heightBoundedLieSubalgebras e m H) := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  refine ⟨Set.toFinite _, ?_⟩
  exact (show (heightBoundedLieSubalgebras e m H).ncard ≤ (heightBoundedSubspaces e m H).ncard by
    simpa only [Nat.card_coe_set_eq] using hc).trans hcard

end Lie
end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (e : Basis ι ℚ L) (K : Submodule ℚ L)

theorem exists_bounded_submodule_ambient_spanning (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e K v hspan hv
  have hr : finrank ℚ K ≤ Fintype.card ι := by
    simpa only [finrank_eq_card_basis e] using K.finrank_le
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (finrank ℚ K)) :
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
          (Submodule.span ℚ (Set.range w)).comap K.subtype := by
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

theorem bounded_submodule_spanning_mem_candidates (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    K ∈ heightBoundedSubspaces e (Fintype.card ι) H := by
  obtain ⟨w, hw, hh⟩ := exists_bounded_submodule_ambient_spanning e K v hspan hH hv
  exact (mem_heightBoundedSubspaces e (Fintype.card ι) H K).mpr ⟨w, hw, hh⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_submodule_intersection_basis_logHeight
    {ι κ J V : Type*} [Fintype ι] [Fintype κ] [Fintype J]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : J → Submodule ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ n : ℕ, n ≤ Fintype.card ι ∧ ∃ bw : Basis (Fin n) ℚ ↥(⨅ j, U j : Submodule ℚ V),
      ∀ a i, rationalLogHeight (b.repr (bw a : V) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).map b.equivFun.toLinearMap := by
    rw [← hv j, Submodule.map_span, ← Set.range_comp]
    exact Matrix.range_mulVecLin _
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    simp only [Wc, W, Submodule.mem_iInf]
    constructor
    · intro hx j
      obtain ⟨y, hy, he⟩ := hA j ▸ hx j
      exact b.equivFun.injective he ▸ hy
    · intro hx j
      rw [hA j]
      exact ⟨x, hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  refine ⟨finrank ℚ Wc, ?_, bc.map e.symm, ?_⟩
  · simpa using Submodule.finrank_le Wc
  · intro a i
    change rationalLogHeight (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) ≤ _
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact (rationalLogHeight_le_iff _ _).mpr (hbc a i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquarefreeCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_squarefree_coefficient_basis (a : SquarefreeIndex (ReplicatedIndex bound))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : a.val = 0
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a = ⊥ := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a =
        M.filtration.layer (blockDegree (fun j : ReplicatedIndex bound => j.1) a.val) := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis _ (replicated_blockDegree_le bound a) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

noncomputable def squarefreeCoefficientBasis (p : ℝ) (a : SquarefreeIndex (ReplicatedIndex bound)) :
    Basis (Fin (finrank ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem squarefreeCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : SquarefreeIndex (ReplicatedIndex bound)) (j k) :
    RationalHeightLE (D.basis.repr (M.squarefreeCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_squarefree_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3

noncomputable def heterogeneousSamplerSides {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) : SamplerTupleIndex G B h → ℕ
  | .inl _ => L
  | .inr ⟨d, _, _⟩ => match K d with
    | none => L
    | some k => integerAxisSideLength (h d) k L (γ d)

theorem heterogeneousSamplerSides_pos {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : 0 < heterogeneousSamplerSides h K L γ v := by
  rcases v with g | ⟨d, b, v⟩
  · exact hL
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact hL
    | some k => exact integerAxisSideLength_pos (hh d) hL (γ d)

theorem heterogeneousSamplerSides_le {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : heterogeneousSamplerSides h K L γ v ≤ L := by
  rcases v with g | ⟨d, b, v⟩
  · exact le_rfl
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact le_rfl
    | some k => exact integerAxisSideLength_le (hh d) hL (γ d)

theorem heterogeneousSamplerSides_integer_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) (d : D) [Fintype (B d)]
    {k : ℕ} (hk : K d = some k) (e) (he : e ∈ principalCoefficientSlots (G := G) (B := B) h d) :
    monomialScale (fun v : SamplerTupleIndex G B h => (heterogeneousSamplerSides h K L γ v : ℝ)) e.val =
      (integerAxisSideLength (h d) k L (γ d) : ℝ) ^ h d := by
  obtain ⟨b, rfl⟩ := (mem_principalCoefficientSlots h d e).mp he
  change monomialScale _ (canonicalPrincipalExponent h d b) = _
  rw [monomialScale_canonicalPrincipal]
  simp only [heterogeneousSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

abbrev LayerSamplerAxis (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ j : Fin m, I j ⊕ Fin (n j)

def layerSamplerDegree (I : Fin m → Type*) (n : Fin m → ℕ) : LayerSamplerAxis I n → ℕ :=
  fun a => a.1.val + 1

abbrev LayerSamplerVariables (G : Type*) (I : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) := SamplerTupleIndex G B (layerSamplerDegree I n)

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerContinuousPrincipalSlots (j : Fin m) (i : I j) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inl i⟩

noncomputable def layerIntegerPrincipalSlots (j : Fin m) (i : Fin (n j)) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inr i⟩

theorem layerIntegerPrincipalSlots_card (j : Fin m) (i : Fin (n j)) :
    (layerIntegerPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inr i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

theorem layerContinuousPrincipalSlots_not_constant (j : Fin m) (i : I j) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerContinuousPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

theorem layerIntegerPrincipalSlots_not_constant (j : Fin m) (i : Fin (n j)) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerIntegerPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerDenominators : LayerSamplerAxis I n → Option ℕ :=
  fun a => Sum.elim (fun _ => none) (fun i => some (basisAxisScale (b a.1) i)) a.2

noncomputable def layerSamplerWidths (R : Fin m → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => principalProfileSize (R a.1) (Fintype.card (B a))

noncomputable def layerSamplerSides (R : Fin m → ℝ) (L : ℕ) : LayerSamplerVariables G I n B → ℕ :=
  heterogeneousSamplerSides (layerSamplerDegree I n) (layerSamplerDenominators U b) L
    (layerSamplerWidths B R)

theorem layerSamplerSides_pos (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : 0 < layerSamplerSides B U b R L v :=
  heterogeneousSamplerSides_pos _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

theorem layerSamplerSides_le (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : layerSamplerSides B U b R L v ≤ L :=
  heterogeneousSamplerSides_le _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

theorem layerSamplerSides_integer_principal (R : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) (e) (he : e ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (fun v : LayerSamplerVariables G I n B => (layerSamplerSides B U b R L v : ℝ)) e.val =
      (integerAxisSideLength (j.val + 1) (basisAxisScale (b j) i) L
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ) ^ (j.val + 1) := by
  rw [layerIntegerPrincipalSlots_card]
  exact heterogeneousSamplerSides_integer_principal _ _ L (layerSamplerWidths B R)
    ⟨j, Sum.inr i⟩ rfl e he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerTailWidth (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  tailProfileSize (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))

noncomputable def layerSamplerGapWidth (R : Fin m → ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  principalProfileSize (R a.1) (layerIntegerPrincipalSlots (G := G) B a.1 a.2).card

noncomputable def layerSamplerScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (layerSamplerGapWidth (G := G) B R) ^ Fintype.card (Σ j, Fin (n j))

structure LayerSamplerScale (R σ : Fin m → ℝ) where
  value : ℕ
  positive : 0 < value
  width : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ layerSamplerTailWidth (G := G) B R σ j * value
  gap : ∀ j i, value ^ (j.val + 1) < basisAxisScale (b j) i →
    (principalSamplingGapRatio (layerSamplerGapWidth (G := G) B R ⟨j, i⟩) * value) ^ (j.val + 1) ≤
      basisAxisScale (b j) i

theorem exists_layerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) : ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerScaleBound (G := G) B R σ L₀ := by
  obtain ⟨L, hL, hlo, hhi, hw, hg⟩ := exists_common_polynomial_scale
    (fun a : Σ j, Fin (n j) => basisAxisScale (b a.1) a.2) (fun a => a.1.val + 1)
    (layerSamplerGapWidth (G := G) B R) (layerSamplerTailWidth (G := G) B R σ)
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) L₀
  exact ⟨⟨L, hL, hw, fun j i => hg ⟨j, i⟩⟩, hlo, hhi⟩

noncomputable def selectedLayerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (hσ : ∀ j, 0 < σ j) (L₀ : ℕ) : LayerSamplerScale (G := G) B U b R σ :=
  (exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀).choose

noncomputable def layerSamplerBox {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : ℝ := layerSamplerSides B U b R S.value v

theorem layerSamplerBox_one_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : 1 ≤ layerSamplerBox B U b S v := by
  have h : 1 ≤ layerSamplerSides B U b R S.value v :=
    Nat.succ_le_of_lt (layerSamplerSides_pos B U b R S.positive v)
  unfold layerSamplerBox
  exact_mod_cast h

theorem layerSamplerBox_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : layerSamplerBox B U b S v ≤ S.value := by
  unfold layerSamplerBox
  exact_mod_cast layerSamplerSides_le B U b R S.positive v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerWitnessScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) (W : ℝ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (fun a => layerSamplerGapWidth (G := G) B R a / W) ^
      Fintype.card (Σ j, Fin (n j))

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoveredSiteValues
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def affineCoveredSiteSample {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) (restrictCoefficients (U j) (p j) (hm j))))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_site_substitution_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (p : VectorPolynomial I ℝ W) (x : Option K → I → ℝ) :
    VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) p) =
      fun s => eval (integerSiteValue (affineSite root difference s) x) p := by
  funext s
  change eval _ (substitute _ p) = _
  rw [eval_substitute]
  apply congrArg (fun t : I → ℝ => eval t p)
  funext i
  rw [affineParameterSubstitution_eval]
  simp [integerSiteValue, Fintype.sum_option, affineSite, Finset.sum_apply,
    zsmul_eq_mul, mul_comm]

theorem affineCoveredSiteSample_eq_values {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) (j : Fin m) :
    affineCoveredSiteSample U root difference D p hm x j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
        ((D : ℝ)⁻¹ • fun s => eval (integerSiteValue (affineSite root difference s) x)
          (restrictCoefficients (U j) (p j) (hm j))) := by
  unfold affineCoveredSiteSample
  rw [affine_site_substitution_eval]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def vectorIntervalSiteWeight {D : Type*} [Fintype D] (b r : ℝ)
    (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) : ℂ :=
  ∏ d, (intervalSiteWeight b r (k d) (x d) : ℂ)

theorem vectorIntervalSiteWeight_bound {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) :
    ‖vectorIntervalSiteWeight b r k x‖ ≤ 1 := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_bound (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  intro d y
  rw [Complex.norm_real, Real.norm_of_nonneg (intervalSiteWeight_range b hr _ _).1]
  exact (intervalSiteWeight_range b hr _ _).2

theorem vectorIntervalSiteWeight_lipschitz {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ≥0} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) :
    LipschitzWith (Fintype.card D * ((2 * intervalSiteCount b r + 1) / r))
      (vectorIntervalSiteWeight b r k) := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_lipschitz (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  · intro d
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (intervalSiteWeight_lipschitz b hr (k d))
  · intro d y
    have hw := intervalSiteWeight_range b (show (0 : ℝ) < r from hr) (k d) y
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

noncomputable def vectorResidueSiteWeight {D : Type*} [Fintype D] (b r : ℝ) (H : D → ℝ)
    {m : ℕ} (a : D → ZMod m) (k : D → Fin (intervalSiteCount b r)) (u : D → ℤ) : ℂ :=
  ∏ d, (residueIntervalSiteWeight b r (H d) (a d) (k d) (u d) : ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

noncomputable def groupedSiteCoefficient (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (k : S × D → Fin (intervalSiteCount B r)) : ℂ :=
  F (fun s d => intervalSiteCenter B r (k (s, d)))

noncomputable def groupedSiteFactor (B r : ℝ)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) : ℂ :=
  vectorIntervalSiteWeight B r (fun d => k (s, d)) x

noncomputable def groupedSiteApprox [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (x : S → D → ℝ) : ℂ :=
  ∑ k : S × D → Fin (intervalSiteCount B r),
    groupedSiteCoefficient B r F k * ∏ s, groupedSiteFactor B r k s (x s)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedCoveredDensity
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))

noncomputable def normalizedCoveredReference (d : ℕ) [NeZero d] :
    Measure ((W × (Fin n → ℤ)) × (R → ZMod d)) :=
  ((ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ)))).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure

variable (b : Basis (Fin n) ℝ Wᗮ)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePositiveCoefficientBases
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_positive_coefficient_basis (a : BoxedDegreeIndex bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
        (M.filtration.positiveCoefficientLayer a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : boxedDegreeMonomial a = 0
  · have hU : M.filtration.positiveCoefficientLayer a = ⊥ := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.positiveCoefficientLayer a = M.filtration.layer (fun i => (a i).val) := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis (fun i => (a i).val)
      (fun i => Nat.le_of_lt_succ (a i).isLt) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

noncomputable def positiveCoefficientBasis (p : ℝ) (a : BoxedDegreeIndex bound) :
    Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
      (M.filtration.positiveCoefficientLayer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem positiveCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : BoxedDegreeIndex bound) (j k) :
    RationalHeightLE (D.basis.repr (M.positiveCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_positive_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalFormalStageGeometry
namespace OAI

section

namespace Erdos3

def formalBracketMatrixHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H) ^ n

def formalCurrentMatrixHeight (n H : ℕ) : ℕ := (n + 1) * (H * H) ^ n

def formalGeometryHeight (n r H : ℕ) : ℕ :=
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M))

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_rational_formal_stage_geometry
    {L μ υ χ ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (f : Basis ι ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H r : ℕ} (hH : 1 ≤ H)
    (hrU : 2 * Fintype.card υ + Fintype.card μ ≤ r)
    (hrK : Fintype.card υ + Fintype.card χ + Fintype.card μ ≤ r)
    (hrV : Fintype.card υ + Fintype.card ι + Fintype.card μ ≤ r)
    (hQU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (hQK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (hQV : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (hK : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (hstructure : ∀ i z k, RationalHeightLE (b.repr ⁅b i, b z⁆ k) H)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H),
      G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
  classical
  let J := homogeneousIntersectionBasisHeight (Fintype.card μ) r H
  let M := max H J
  let B := if j = 2 then K else V
  let Ebr := homogeneousIntersection b w (j - 1) U.toSubmodule B
  let Ecur := homogeneousIntersection b w j U.toSubmodule U.toSubmodule
  have hMout : M ≤ formalGeometryHeight (Fintype.card μ) r H := Nat.le_max_left _ _
  have hHout : H ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_left H J).trans hMout
  have hJout : J ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_right H J).trans hMout
  obtain ⟨eBr, heBr⟩ : ∃ e : Basis (Fin (Module.finrank ℚ Ebr)) ℚ Ebr,
      ∀ i z, RationalHeightLE (b.repr (e z : L) i) J := by
    by_cases hj2 : j = 2
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule K fU fK hH hrK hQU hQK
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule K :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = K from if_pos hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule V fU f hH hrV hQU hQV
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule V :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = V from if_neg hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
  obtain ⟨eCur, heCur⟩ := exists_homogeneousIntersection_basis b w j U.toSubmodule U.toSubmodule fU fU (r := r)
    hH (by omega) hQU hQU
  have hbrmem (x : ℝ ⊗[ℚ] L) : x ∈ Ebr.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ B.baseChange ℝ ∧
      basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  have hcurmem (x : ℝ ⊗[ℚ] L) : x ∈ Ecur.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ realificationLieSubalgebra U ∧
      basisGradeProjection (b.baseChange ℝ) w j x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  let G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H) := {
    bracketSpace := Ebr
    currentSpace := Ecur
    bracketRank := Module.finrank ℚ Ebr
    currentRank := Module.finrank ℚ Ecur
    bracketBasis := eBr
    currentBasis := eCur
    bracket_grade := fun x hx => (hbrmem x).mp hx |>.2.2
    bracket_U := fun x hx => (hbrmem x).mp hx |>.1
    bracket_K := by
      intro h x hx
      simpa only [B, if_pos h] using ((hbrmem x).mp hx).2.1
    bracket_V := by
      intro h x hx
      simpa only [B, if_neg (show j ≠ 2 by omega)] using ((hbrmem x).mp hx).2.1
    bracket_complete := by
      intro x hx hgrade hKx hVx
      apply (hbrmem x).mpr
      refine ⟨hx, ?_, hgrade⟩
      by_cases h : j = 2
      · simpa only [B, if_pos h] using hKx h
      · simpa only [B, if_neg h] using hVx (by omega)
    current_grade := fun x hx => (hcurmem x).mp hx |>.2.2
    current_U := fun x hx => (hcurmem x).mp hx |>.1
    current_projection := by
      intro x hx
      apply (hcurmem _).mpr
      have hp := hU.baseChange b w U.toSubmodule j x hx
      exact ⟨hp, hp, basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j} x⟩
    bracket_matrix_height := by
      intro i z
      have h := bracketSystemMatrix_height b eBr f (fun k => (eK k : L))
        (fun i j k => (hstructure i j k).mono (Nat.le_max_left H J))
        (fun z i => (heBr i z).mono (Nat.le_max_right H J))
        (fun z i => (hK i z).mono (Nat.le_max_left H J))
        (fun i k => (hQV k i).mono (Nat.le_max_left H J)) i z
      exact h.mono ((Nat.le_max_right (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    current_matrix_height := by
      intro i z
      have h := subspaceQuotientMatrix_height b eCur f
        (fun i k => (hQV k i).mono (Nat.le_max_left H J))
        (fun z i => (heCur z i).mono (Nat.le_max_right H J)) i z
      exact h.mono ((Nat.le_max_left (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    bracket_basis_height := fun i z => (heBr i z).mono hJout
    current_basis_height := fun i z => (heCur z i).mono hJout }
  exact ⟨G, homogeneousIntersection_finrank_le b w (j - 1) U.toSubmodule B,
    homogeneousIntersection_finrank_le b w j U.toSubmodule U.toSubmodule⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepDropBasisBudget
namespace OAI

section

namespace Erdos3

open Module

theorem stepDropBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (stepDropBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (2 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (stepDropBracketHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p)) := by
    unfold stepDropBracketHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (2 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 8 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

theorem exists_stepDrop_basis_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (_hH : 1 ≤ H)
    (_hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (_hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (_hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (_heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (_hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hν : (Fintype.card ν : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + 2) ^ 5 + 2) ^ 9)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ κ ν _ _ _ _ _ _ _ b w U V K fU fK fV eK H hH hU hK hV heK hstructure
    p hp hμ hυ hχ hκ hν hHp
  let q := (p + 2) ^ 5
  let J := max H (stepDropBracketHeight (Fintype.card μ) H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hp2 : p ≤ p + 2 := by linarith
    apply hp2.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 5)
  have hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ q := by
    simp only [StepDropRow, Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
    have hprod : (Fintype.card κ : ℝ) * Fintype.card ν ≤ p * p :=
      mul_le_mul hκ hν (Nat.cast_nonneg _) hp
    have hpoly : p ^ 2 + 3 * p ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 10 * p ^ 4 + 40 * p ^ 3 + 79 * p ^ 2 + 77 * p + 32 := by positivity
      nlinarith
    dsimp [q]
    nlinarith
  have hJ : 1 ≤ J := hH.trans (Nat.le_max_left _ _)
  have hJq : (J : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHp.trans (Real.exp_le_exp.mpr hpq))
      (stepDropBracketHeight_le_exp (Fintype.card μ) H hp hμ hHp)
  obtain ⟨e, he⟩ := exists_stepDrop_basis_exp_height b w U V K fU fK fV eK hJ
    (fun i j => (hU i j).mono (Nat.le_max_left _ _))
    (fun i j => (hK i j).mono (Nat.le_max_left _ _))
    (fun i j => (hV i j).mono (Nat.le_max_left _ _))
    (fun i j z => (stepDrop_bracket_height b V K fV eK hV heK hstructure i j z).mono (Nat.le_max_right _ _))
    hq (hμ.trans hpq) hrows hJq
  have hcap : (q + 2) ^ 9 ≤ (p + C) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨e, fun i j => ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap),
    (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DependentCoordinateCorrections
namespace OAI

section

namespace Erdos3

theorem exists_coordinate_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (U V : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ) (w : ν → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (v a i) H) (hwH : ∀ a i, RationalHeightLE (w a i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan U →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan V →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (U ⊓ V) := by
  simpa only [realRationalCoordinateSpan_inf, realRationalCoordinateSpan_eq_image U v hv,
    realRationalCoordinateSpan_eq_image V w hw] using
    exists_common_intersection_corrections (fun i a => v a i) (fun i a => w a i)
      hH hl (fun i a => hvH a i) (fun i a => hwH a i) hp hι hcols hHp hlp T hT

end Erdos3

end

section

namespace Erdos3

theorem exists_dependent_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h₁₂ : (Fintype.card (Σ _ : ({1, 2} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (h₁₃ : (Fintype.card (Σ _ : ({1, 3} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ κ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ)
    (hT : ∀ i, Real.exp (separationBudget (p + sparseGeneratorBudget p)) ≤ T i) :
    let P := p + sparseGeneratorBudget p
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) →
        ‖e₁‖ ≤ Real.exp P / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp P / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp P + Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro P
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  have hpP : p ≤ P := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hp)
  have hP : 0 ≤ P := hp.trans hpP
  obtain ⟨M₁, hM₁, hM₁p, w₁, hw₁, hw₁H⟩ :=
    exists_sparse_generators_exp_height J {1, 2} v hv hH hvH hp h₁₂ hκ hHp
  obtain ⟨M₂, hM₂, hM₂p, w₂, hw₂, hw₂H⟩ :=
    exists_sparse_generators_exp_height J {1, 3} v hv hH hvH hp h₁₃ hκ hHp
  have hMP : ((max M₁ M₂ : ℕ) : ℝ) ≤ Real.exp P := by
    rw [Nat.cast_max]
    apply (max_le hM₁p hM₂p).trans
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_left hp
  exact exists_coordinate_intersection_corrections
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    w₁ w₂ hw₁ hw₂ (hM₁.trans (le_max_left _ _)) hl
    (fun a i => (hw₁H a i).mono (le_max_left _ _))
    (fun a i => (hw₂H a i).mono (le_max_right _ _))
    hP (hι.trans hpP) (hcols.trans hpP) hMP
    (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedDependentCoordinates
namespace OAI

section

namespace Erdos3

open Module

noncomputable def dependentCoordinateBudget (p : ℝ) : ℝ :=
  preimageBasisBudget (p + sparseGeneratorBudget (4 * p + 1))

theorem dependentCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ dependentCoordinateBudget p := by
  apply preimageBasisBudget_nonneg
  exact add_nonneg hp (sparseGeneratorBudget_nonneg (by positivity))

theorem exists_dependent_coordinate_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a k i, rationalLogHeight (v a k i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J),
      ∀ a i, rationalLogHeight ((b a : ι → ℚ) i) ≤ dependentCoordinateBudget p := by
  classical
  let q := 4 * p + 1
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p + 1 ≤ q := by dsimp only [q]; linarith
  have hrows (S : Finset (Fin 4)) : (Fintype.card (Σ _ : S, ι) : ℝ) ≤ q := by
    have hS : Fintype.card S ≤ 4 := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using S.card_le_univ
    have hc : Fintype.card (Σ _ : S, ι) ≤ 4 * Fintype.card ι := by
      simpa using Nat.mul_le_mul_right (Fintype.card ι) hS
    calc
      _ ≤ (4 : ℝ) * Fintype.card ι := by exact_mod_cast hc
      _ ≤ 4 * p := mul_le_mul_of_nonneg_left hι (by norm_num)
      _ ≤ q := by dsimp only [q]; linarith
  have hκq : (Fintype.card κ : ℝ) ≤ q := hκ.trans ((by linarith : p ≤ p + 1).trans hpq)
  have hHq : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨M, _, hM, u, hu, huH⟩ := exists_sparse_generators_exp_height J {1, 2} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 2}) hκq hHq
  obtain ⟨M', _, hM', u', hu', huH'⟩ := exists_sparse_generators_exp_height J {1, 3} v hv
    (one_le_ceil_exp p) (fun a k i => rationalHeightLE_ceil_exp (hvH a k i))
    hq (hrows {1, 3}) hκq hHq
  let t := p + sparseGeneratorBudget q
  have hpt : p ≤ t := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hq)
  have ht : 0 ≤ t := hp.trans hpt
  have huB (a : κ) (i : ι) : rationalLogHeight (u a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH a i) hM).trans (le_add_of_nonneg_left hp)
  have huB' (a : κ) (i : ι) : rationalLogHeight (u' a i) ≤ t :=
    (rationalLogHeight_le_of_height (huH' a i) hM').trans (le_add_of_nonneg_left hp)
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight (Pi.basisFun ℚ ι) (Pi.basisFun ℚ ι)
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    (LinearMap.id : (ι → ℚ) →ₗ[ℚ] (ι → ℚ)) u u' hu hu' ht
    (hι.trans hpt) (hκ.trans hpt) (hκ.trans hpt)
    (by simpa only [Pi.basisFun_repr] using huB)
    (by simpa only [Pi.basisFun_repr] using huB')
    (by simpa only [Pi.basisFun_repr, LinearMap.id_apply] using huB)
  change Basis (Fin (finrank ℚ (fourDependentProjection J))) ℚ (fourDependentProjection J) at b
  refine ⟨b, fun a i => ?_⟩
  exact hb a i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MultidegreeBasisConstruction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))

theorem ordinaryLayer_eq_span_multidegree_bases (n : ℕ) :
    F.ordinary.layer n = Submodule.span ℚ
      (Set.range (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
          Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)) := by
  rw [F.degree_eq]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    rw [← span_submodule_basis (F.layer a) (b a)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    have hle : F.layer a.val ≤ ⨆ (u : σ → ℕ) (_hu : n ≤ ∑ i, u i), F.layer u :=
      le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
    exact hle ((b a.val) j).property

theorem exists_bounded_ordinaryLayer_basis {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ L) {H : ℕ}
    (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H) (n : ℕ) :
    ∃ c : Basis (Fin (finrank ℚ (F.ordinary.layer n))) ℚ (F.ordinary.layer n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j) H := by
  apply exists_bounded_submodule_basis_from_spanning e (F.ordinary.layer n)
    (fun z : Σ a : {a : σ → ℕ // n ≤ ∑ i, a i},
      Fin (finrank ℚ (F.layer a.val)) => ((b z.1.val) z.2).val)
    (F.ordinaryLayer_eq_span_multidegree_bases b n).symm
  exact fun z j => hb z.1.val z.2 j

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

def layerKernelIndexBound (m B : ℕ) : ℕ := B^(m*2^(m+1))

theorem layerKernelIndexBound_le_exp (m : ℕ) {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) :
    (layerKernelIndexBound m B : ℝ) ≤ Real.exp ((m*2^(m+1) : ℕ)*p) := by
  unfold layerKernelIndexBound
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB _

noncomputable def fixedKernelInverseBound {α G O : Type*}
    [Fintype α] [DecidableEq α] [Fintype G] [DecidableEq G] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : G → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G degree)
    (hA : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) (κ : ℝ) : Prop :=
  ‖(scalarKernelFixedPivot hL x degree rows s hA).symm.toContinuousLinearMap‖ ≤
    kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card O) degree κ

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val + 1))]
variable (rows : ∀ j, O j → Finset α)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def allocatedKernelLog (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  P + (m*2^(m+1) : ℕ)*P + (Fintype.card α : ℝ)*(m+1) +
    ∑ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedKernelReplacementLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P e : ℝ) : ℝ :=
  ∑ j, coefficientFrontLog (Fintype.card (O j))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (allocatedKernelLog G α O P) (4*(P+8)) e

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CeilGridScaleRatio
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalGridScale : ℕ :=
  ⌈gamma * (basisAxisScale (basis j) i : ℝ)⌉₊

include hR hactive

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedPhysicalRootAllowance (c : LayerSamplerVariables G I n B → ℤ) : ℝ :=
  1 + ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k

variable {α : Type*} (x : G → IntegerScalarCubeBox α S.value)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSiteApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedNaturalConstantRadius (j : Fin m) (i : Fin (n j)) : ℝ :=
  2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)

noncomputable def allocatedNaturalSupportRadius (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4 +
    1 / 4 + allocatedNaturalConstantRadius (G := G) B j i

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedNaturalSupportRadius_nonneg (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : 0 ≤ allocatedNaturalSupportRadius (G := G) B α j i := by
  have h := blockJetScaleBound_nonneg (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) (by norm_num : (0 : ℝ) ≤ 4)
  unfold allocatedNaturalSupportRadius allocatedNaturalConstantRadius
  positivity

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "constantRadius" => allocatedNaturalConstantRadius (G := G) B j i

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "radius" => allocatedNaturalSupportRadius (G := G) B α j i
local notation "principalRadius" => blockJetScaleBound (Fintype.card α) (j.val + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 4

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def allocatedNaturalSiteRadius (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : ℝ :=
  rows.card * allocatedNaturalSupportRadius (G := G) B α j i

omit [Fintype G] [∀ j, Fintype (I j)] [DecidableEq α] in
theorem allocatedNaturalSiteRadius_nonneg (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : 0 ≤ allocatedNaturalSiteRadius (G := G) B j i rows :=
  mul_nonneg (Nat.cast_nonneg _) (allocatedNaturalSupportRadius_nonneg B α j i)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable {M : ℕ} [NeZero M] (rows : Finset (Finset α)) (P ε : ℝ)

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "supportRadius" => allocatedNaturalSiteRadius (G := G) B j i rows

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalChartRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedPhysicalChartRadius (C : Fin m → ℝ) (H : ℝ) (j : Fin m) : ℝ :=
  1 / (4 * (((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) *
    ((2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)) *
    ((C j + 1) * ((Fintype.card (I j) : ℝ) + 1))))

theorem allocatedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H : ℝ} (hH : 1 ≤ H) (j : Fin m) :
    0 < allocatedPhysicalChartRadius (G := G) B α C H j := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hC0 := hC j
  unfold allocatedPhysicalChartRadius
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedPhysicalChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H P : ℝ} (hH : 1 ≤ H) (hP : 0 ≤ P) (hHP : H ≤ Real.exp P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C H j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + Real.exp P := add_le_add ha h1
      _ = 2 * Real.exp P := by ring
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hq : H + Fintype.card α ≤ Real.exp (P + Fintype.card α + 1) := by
    have hq1 : (Fintype.card α : ℝ) + 1 ≤ Real.exp (Fintype.card α + 1) := by
      linarith [Real.add_one_le_exp ((Fintype.card α : ℝ) + 1)]
    calc
      _ ≤ Real.exp P + (Fintype.card α : ℝ) * Real.exp P :=
        add_le_add hHP (by simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (Fintype.card α)))
      _ = ((Fintype.card α : ℝ) + 1) * Real.exp P := by ring
      _ ≤ Real.exp (Fintype.card α + 1) * Real.exp P :=
        mul_le_mul_of_nonneg_right hq1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hN := hadd (hNP j)
  have hCj := hadd (hCP j)
  have hI := hadd (hIP j)
  have hC0 := hC j
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  simp only [allocatedPhysicalChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * (Real.exp (P + 1) *
        ((Real.exp 1) ^ Fintype.card α * (Real.exp (P + Fintype.card α + 1)) ^ (j.val + 1)) *
        (Real.exp (P + 1) * Real.exp (P + 1))) := by gcongr
    _ = _ := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberIntegerPoint_mem_integerBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : S.fiberIntegerPoint fixed u ∈ integerBox N := by
  rw [mem_integerBox]
  intro i
  by_cases hi : keep i
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simp only [finiteSplitPoint, dif_pos hi]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u ⟨i, hi⟩).isLt⟩
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

def fiberPointInBox (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : integerBox N :=
  ⟨S.fiberIntegerPoint fixed u, S.fiberIntegerPoint_mem_integerBox fixed hfixed u⟩

noncomputable def fiberSliceLaw
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ)) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))).finitePushforward
    (S.fiberPointInBox fixed hfixed)

theorem fiberSliceLaw_mean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

theorem fiberSliceLaw_score {s d : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (hq : 0 < q) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (Q : PolynomialPatch {x // keep x} s d) (f : (X → ℤ) → ℝ) (target : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean
      (fun x => (f x.val - target) *
        (S.fiberReinsertPatch Q).value (fun i => (x.val i : ℝ))) =
      relativePatchSliceScore S (fun x => f (finiteSplitPoint keep x fixed)) target Q := by
  rw [fiberSliceLaw_mean]
  unfold relativePatchSliceScore
  congr 1
  · ext u
    simp
  · funext u
    change (f (S.fiberIntegerPoint fixed u) - target) *
      (S.fiberReinsertPatch Q).value (fun i => (S.fiberIntegerPoint fixed u i : ℝ)) = _
    rw [fiberReinsertPatch_integerPoint_value S Q hq]
    rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.exists_fiber_law_with_slice
    {X : Type*} [Fintype X] [DecidableEq X] {keep : X → Prop} [DecidablePred keep]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hN : ∀ k : {x // keep x}, 0 < N k.val)
    (h : RelativePatchSliceConclusion s (fun k : {x // keep x} => N k.val)
      (fun x => f (finiteSplitPoint keep x fixed)) target rankBound cost) :
    ∃ (d : ℕ) (Qfull : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Qfull ≤ cost ∧
      (Qfull.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean
        (fun x => (f x.val - target) * Qfull.value (fun i => (x.val i : ℝ))) ∧
      ∃ (q : ℕ), 0 < q ∧
        ∃ (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
          (hlen : ∀ k, 0 < S.length k),
          (∀ k, Real.exp (-cost) * (N k.val : ℝ) ≤ (S.length k : ℝ)) ∧
          law = S.fiberSliceLaw hlen fixed hfixed := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  have hlen : ∀ k, 0 < S.length k := by
    intro k
    exact_mod_cast (mul_pos (Real.exp_pos (-cost))
      (Nat.cast_pos.mpr (hN k))).trans_le (hlength k)
  have hlog : Real.log (1 + (Q.kernel.lip : ℝ)) ≤ cost := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have hpos : 0 < 1 + (Q.kernel.lip : ℝ) := by positivity
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at he
    linarith
  refine ⟨d, S.fiberReinsertPatch Q, S.fiberSliceLaw hlen fixed hfixed,
    hd, hcost, hlip, ?_, q, hq, S, hlen, hlength, rfl⟩
  rwa [S.fiberSliceLaw_score hlen hq fixed hfixed Q f target]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerPrescribedScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerSamplerTailScaleFloor (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  32 * (probabilityProfileLipschitz : ℝ) *
    ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1) / (σ j * R j)

theorem layerSamplerTailWidth_of_scaleFloor
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {S0 : ℕ} (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0 := by
  intro j
  have hj := (div_le_iff₀ (mul_pos (hσ j) (hR j))).mp (hfloor j)
  change 8 * (probabilityProfileLipschitz : ℝ) ≤
    (σ j * R j / (4 * ((Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1))) * S0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  convert hj using 1 <;> ring

theorem layerSamplerTailScaleFloor_le_exp
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t) :
    ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ Real.exp (a + c + r + t) := by
  intro j
  calc
    _ = (8 * (probabilityProfileLipschitz : ℝ)) *
        (4 * ((Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1)) *
        (R j)⁻¹ * (σ j)⁻¹ := by
      unfold layerSamplerTailScaleFloor
      field_simp
      ring
    _ ≤ Real.exp a * Real.exp c * Real.exp r * Real.exp t := by
      have hRj := (hR j).le
      have hσj := (hσ j).le
      gcongr <;> first
        | exact hprofile
        | exact hcount j
        | exact hradius j
        | exact htolerance j
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_add]

variable [∀ j, IsEmpty (Fin (n j))]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

def emptyLayerSamplerScale (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    LayerSamplerScale (G := G) B U b R σ where
  value := S0
  positive := hS0
  width := hwidth
  gap := fun _ i => isEmptyElim i

@[simp] theorem emptyLayerSamplerScale_value (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    (emptyLayerSamplerScale B U b S0 hS0 hwidth).value = S0 := rfl

def emptyLayerSamplerScaleOfFloor
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScale B U b S0 hS0 (layerSamplerTailWidth_of_scaleFloor B hR hσ hfloor)

@[simp] theorem emptyLayerSamplerScaleOfFloor_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    (emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 hfloor).value = S0 := rfl

def emptyLayerSamplerScaleOfExp
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 (fun j =>
    (layerSamplerTailScaleFloor_le_exp B hR hσ hprofile hcount hradius htolerance j).trans hS)

@[simp] theorem emptyLayerSamplerScaleOfExp_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    (emptyLayerSamplerScaleOfExp B U b hR hσ hprofile hcount hradius htolerance
      S0 hS0 hS).value = S0 := rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSiteTermSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSiteJetSize (α : Type*) [Fintype α] (j : Fin m) : ℝ :=
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) + idealSiteEnvelopeRadius α m

theorem allocatedSiteJetSize_nonneg (α : Type*) [Fintype α] (j : Fin m) :
    0 ≤ allocatedSiteJetSize (G := G) B α j := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteJetSize
  positivity

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalSiteProjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalEuclideanSitePoint (w : X → ℝ) (j : Fin m) : euclideanSubspace (U j) :=
  (euclideanSubspaceArrayEquiv (U j)).symm
    (fun _ : Unit => eval w (restrictCoefficients (U j) (p j) (hm j)))

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

noncomputable def allocatedSlicedGridHeightCutoff (T : ℕ) : ℕ :=
  T ^ (layerTailDegree m + 1) + denom * 2 ^ degree * T ^ degree + 2 * denom

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem exists_denseSliceThreshold (c q : ℕ) {δ D v w : ℝ}
    (hδ : 0 < δ) (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hc : (c : ℝ) ≤ D) (hq : (q : ℝ) ≤ Real.exp v) (hδw : δ⁻¹ ≤ Real.exp w) :
    ∃ T : ℕ, (((c + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
      (T : ℝ) ≤ Real.exp (D + v + w + 1) := by
  let T : ℕ := ⌈(((c + 1) * q : ℕ) : ℝ) / δ⌉₊
  have hcp : ((c + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have hb : (((c + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (D + v + w) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hcp hq (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδw (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq (by rw [← Real.exp_add, ← Real.exp_add])
  exact ⟨T, Nat.le_ceil _, natCeil_le_exp_succ (by positivity) (by positivity) hb⟩

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q δ : ℝ} {q step : ℕ},
      0 ≤ F → 0 ≤ Q → 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
      (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
      ∃ T : ℕ, (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  let fixed := scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 +
    scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 + 2
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge fixed
  let C := max 2 C₀
  have hC : fixed ≤ (C : ℝ) := hC₀.trans (Nat.cast_le.mpr (le_max_right _ _))
  have hc0 := scalarCubePrimitiveEnvelope_nonneg Empty A 16 (128 * probabilityProfileLipschitz) 1
  have hs0 := scalarCubePrimitiveEnvelope_nonneg (Fin dim) A 1 0 1
  have hc : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  have hs : scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  refine ⟨C, le_max_left _ _, ?_⟩
  intro F Q δ q step hF hQ hδ hδF hq hqQ hstep
  obtain ⟨T, hT, hTb⟩ := exists_denseSliceThreshold dim q hδ (Nat.cast_nonneg dim)
    hQ hF le_rfl hqQ hδF
  refine ⟨T, hT, hTb, ?_⟩
  let logPg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + F + 4
  have hlog : 0 ≤ logPg := by dsimp only [logPg]; positivity
  have hCexp : (C : ℝ) ≤ Real.exp C := by linarith [Real.add_one_le_exp (C : ℝ)]
  have hCLog : (C : ℝ) ≤ logPg := by
    dsimp only [logPg]
    linarith [mul_nonneg (Nat.cast_nonneg (dim + 1) : (0 : ℝ) ≤ ((dim + 1 : ℕ) : ℝ)) hQ]
  refine ⟨Real.one_le_exp hlog, hc.trans (hCexp.trans (Real.exp_le_exp.mpr hCLog)), ?_, ?_⟩
  · have hpow : (q : ℝ) ^ (dim + 1) ≤ Real.exp (((dim + 1 : ℕ) : ℝ) * Q) := by
      calc
        _ ≤ (Real.exp Q) ^ (dim + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hqQ _
        _ = _ := (Real.exp_nat_mul _ _).symm
    have hscalar := scalarCubePrimitiveEnvelope_le_scaled (Fin dim) A 1 0 hq
    simp only [Fintype.card_fin] at hscalar
    apply hscalar.trans
    calc
      _ ≤ Real.exp C * Real.exp (((dim + 1 : ℕ) : ℝ) * Q) :=
        mul_le_mul (hs.trans hCexp) hpow (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
      _ = Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Nat.cast_mul]
    calc
      _ ≤ (Real.exp 4 * Real.exp F) * Real.exp Q :=
        mul_le_mul (hstep.trans (mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)))
          hqQ (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (4 + F + Q) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        push_cast
        nlinarith only [hQ, mul_nonneg (Nat.cast_nonneg dim : (0 : ℝ) ≤ dim) hQ,
          Nat.cast_nonneg (α := ℝ) C])

theorem exists_uniform_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q : ℝ}, 0 ≤ F → 0 ≤ Q →
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
      ∀ {δ : ℝ} {q step : ℕ}, 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
        (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro F Q hF hQ
  let T : ℕ := ⌈Real.exp (dim + Q + F)⌉₊
  refine ⟨T, natCeil_le_exp_succ (Real.exp_nonneg _) (by positivity) le_rfl, ?_⟩
  intro δ q step hδ hδF hq hqQ hstep
  obtain ⟨_, _, _, hprimitive⟩ := hparameters hF hQ hδ hδF hq hqQ hstep
  refine ⟨?_, hprimitive⟩
  have hdim : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp dim := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (dim : ℝ)
  have hbound : (((dim + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (dim + Q + F) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hdim hqQ (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδF (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq
      (by rw [← Real.exp_add, ← Real.exp_add])
  exact hbound.trans (Nat.le_ceil _)

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

def slicedGridGeometryLog {A : Type*} [Semiring A] (D v w t : A) : A :=
  (D + 1) * (D ^ 2 + 2 * D + v + 8 + (D + v + 8 + D + 1) + D * w) +
    (2 * D * t + D + 2 * (D + v + 8) + 5) + (D ^ 2 + 2 * D + 2 * v + 1)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) (q d T : ℕ)
local notation "degree" => j.val + 1
local notation "b" => Fintype.card (B (Sigma.mk j (Sum.inr i)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "cost" => (inactiveDenominator gamma : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor q degree b (4 * gamma)
local notation "torusI" => blockTorusFactor q degree b 1

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeDualCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeDualBasis (b : Basis ι ℤ Λ) : Basis ι ℝ E := by
  classical
  exact LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)

theorem euclideanDualLattice_eq_span (b : Basis ι ℤ Λ) :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range (latticeDualBasis Λ b)) := by
  classical
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E)
    realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, latticeDualBasis, Basis.ofZLatticeBasis_span] using h

noncomputable def latticeDualPoint (b : Basis ι ℤ Λ) (n : ι → ℤ) : E :=
  (latticeDualBasis Λ b).equivFun.symm (fun i => (n i : ℝ))

@[simp]
theorem latticeDualPoint_neg (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b (-n) = -latticeDualPoint Λ b n := by
  simp only [latticeDualPoint, Pi.neg_apply, Int.cast_neg]
  change (latticeDualBasis Λ b).equivFun.symm (-(fun i => (n i : ℝ))) = _
  exact map_neg _ _

theorem latticeDualPoint_mem (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b n ∈ euclideanDualLattice Λ := by
  rw [euclideanDualLattice_eq_span Λ b, (latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ]
  intro i
  refine ⟨n i, ?_⟩
  have h := congrFun ((latticeDualBasis Λ b).equivFun.apply_symm_apply (fun j => (n j : ℝ))) i
  exact h.symm

theorem latticeDualPoint_injective (b : Basis ι ℤ Λ) : Function.Injective (latticeDualPoint Λ b) := by
  intro n m h
  have he := congrArg (latticeDualBasis Λ b).equivFun h
  simp only [latticeDualPoint, LinearEquiv.apply_symm_apply] at he
  ext i
  exact Int.cast_injective (congrFun he i)

theorem latticeDualPoint_surjective (b : Basis ι ℤ Λ) (ξ : euclideanDualLattice Λ) :
    ∃ n : ι → ℤ, latticeDualPoint Λ b n = ξ := by
  classical
  have hmem := ((latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ (ξ : E)).mp
    ((euclideanDualLattice_eq_span Λ b).le ξ.property)
  choose n hn using hmem
  refine ⟨n, ?_⟩
  apply (latticeDualBasis Λ b).equivFun.injective
  ext i
  change (latticeDualBasis Λ b).equivFun
    ((latticeDualBasis Λ b).equivFun.symm (fun j => (n j : ℝ))) i = _
  rw [LinearEquiv.apply_symm_apply]
  exact hn i

noncomputable def latticeDualEquiv (b : Basis ι ℤ Λ) : (ι → ℤ) ≃ euclideanDualLattice Λ :=
  Equiv.ofBijective (fun n => ⟨latticeDualPoint Λ b n, latticeDualPoint_mem Λ b n⟩)
    ⟨fun _ _ h => latticeDualPoint_injective Λ b (congrArg Subtype.val h), fun ξ => by
      obtain ⟨n, hn⟩ := latticeDualPoint_surjective Λ b ξ
      exact ⟨n, Subtype.ext hn⟩⟩

@[simp]
theorem latticeDualEquiv_coe (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    ((latticeDualEquiv Λ b n : euclideanDualLattice Λ) : E) = latticeDualPoint Λ b n := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

def canonicalRankBlockEmbedding (h : D → ℕ) (d : D) (b : B d) :
    Fin (h d) ↪ SamplerTupleIndex G B h where
  toFun v := .inr ⟨d, b, v⟩
  inj' := by intro v w he; simpa only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    Prod.mk.injEq, true_and] using he

def canonicalRankBlock (h : D → ℕ) (d : D) (b : B d) :
    Finset (SamplerTupleIndex G B h) :=
  Finset.univ.map (canonicalRankBlockEmbedding h d b)

theorem principalCoefficientSlot_eq_block_sum (h : D → ℕ) (d : D) (b : B d) :
    (principalCoefficientSlot (G := G) h d b).val =
      ∑ k ∈ canonicalRankBlock h d b, Finsupp.single k 1 := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    canonicalRankBlock, Finset.sum_map, canonicalRankBlockEmbedding]
  rfl

theorem principalCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (h : D → ℕ) (d : D) (b : B d) (c : R) :
    MvPolynomial.monomial (principalCoefficientSlot (G := G) h d b).val c =
      MvPolynomial.C c * ∏ k ∈ canonicalRankBlock h d b, MvPolynomial.X k := by
  rw [principalCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index]
  rfl

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

def kernelRankBlockEmbedding (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Fin h ↪ SamplerTupleIndex G B degree where
  toFun v := .inl (e (a, v))
  inj' := by
    intro v w he
    exact congrArg Prod.snd (e.injective (Sum.inl.inj he))

@[simp] theorem kernelRankBlockEmbedding_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) (v : Fin h) :
    kernelRankBlockEmbedding (B := B) degree e a v = .inl (e (a, v)) := rfl

def kernelRankBlock (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Finset (SamplerTupleIndex G B degree) :=
  Finset.univ.map (kernelRankBlockEmbedding degree e a)

noncomputable def kernelRankCoefficientSlot (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    BoundedCoefficientExponent (SamplerTupleIndex G B degree) h :=
  ⟨productBlockExponent (kernelRankBlockEmbedding degree e a),
    (productBlockExponent_degree _).le⟩

theorem kernelRankCoefficientSlot_degree (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val.degree = h :=
  productBlockExponent_degree _

theorem kernelRankCoefficientSlot_eq_block_sum (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val =
      ∑ k ∈ kernelRankBlock degree e a, Finsupp.single k 1 := by
  simp only [kernelRankCoefficientSlot, productBlockExponent, kernelRankBlock,
    Finset.sum_map]

theorem kernelRankCoefficientSlot_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a b : A) (v : Fin h) :
    (kernelRankCoefficientSlot (B := B) degree e a).val (.inl (e (b, v))) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b <;>
    simp [kernelRankCoefficientSlot, productBlockExponent,
      Finsupp.single_apply, e.injective.eq_iff, hab]

theorem kernelRankCoefficientSlot_injective (degree : D → ℕ)
    (e : A × Fin h ↪ G) (hh : 0 < h) :
    Function.Injective (kernelRankCoefficientSlot (B := B) degree e) := by
  intro a b he
  have hv := congrArg (fun q : BoundedCoefficientExponent (SamplerTupleIndex G B degree) h =>
    q.val (.inl (e (b, ⟨0, hh⟩)))) he
  rw [kernelRankCoefficientSlot_apply, kernelRankCoefficientSlot_apply] at hv
  by_contra hab
  simp [hab] at hv

theorem kernelRankCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) (c : R) :
    MvPolynomial.monomial (kernelRankCoefficientSlot (B := B) degree e a).val c =
      c • ∏ k ∈ kernelRankBlock degree e a, MvPolynomial.X k := by
  rw [kernelRankCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index,
    MvPolynomial.smul_eq_C_mul]
  rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

abbrev SamplerLongVariables (inactive : D → Prop) (G : Type*) (B : D → Type*)
    (h : D → ℕ) :=
  SamplerTupleIndex G (fun d : {d // ¬ inactive d} => B d.val) (fun d => h d.val)

def samplerLongEmbedding (inactive : D → Prop) (h : D → ℕ) :
    SamplerLongVariables inactive G B h ↪ SamplerTupleIndex G B h :=
  Function.Embedding.sumMap (Function.Embedding.refl G)
    (Function.Embedding.sigmaMap (Function.Embedding.subtype (fun d => ¬ inactive d))
      (fun _ => Function.Embedding.refl _))

@[simp] theorem samplerLongEmbedding_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    samplerLongEmbedding (B := B) inactive h (.inl g) = .inl g := rfl

@[simp] theorem samplerLongEmbedding_dedicated (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (v : Fin (h d.val)) :
    samplerLongEmbedding (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr ⟨d.val, b, v⟩ := rfl

theorem samplerLongEmbedding_principalExponent (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) :
    ((principalCoefficientSlot (G := G) (B := fun a : {a // ¬ inactive a} => B a.val)
      (fun a => h a.val) d b).val).mapDomain (samplerLongEmbedding inactive h) =
        (principalCoefficientSlot h d.val b).val := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, samplerLongEmbedding_dedicated]

section TopPart

variable {I J R : Type*} [CommRing R]

theorem homogeneousComponent_killCompl (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (r : ℕ) :
    homogeneousComponent r (killCompl hf P) = killCompl hf (homogeneousComponent r P) := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_killCompl, Finsupp.degree_mapDomain]

theorem homogeneousComponent_polynomialTranslate_top (P : MvPolynomial I R)
    (v : I → R) (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (polynomialTranslate v P) = homogeneousComponent r P := by
  ext a
  simp only [coeff_homogeneousComponent]
  split_ifs with ha
  · exact top_coeff_polynomialTranslate P v a (ha.symm ▸ hP)
  · rfl

theorem homogeneousComponent_restricted_translate_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (killCompl hf (polynomialTranslate v P)) =
      killCompl hf (homogeneousComponent r P) := by
  rw [homogeneousComponent_killCompl, homogeneousComponent_polynomialTranslate_top P v r hP]

theorem homogeneousComponent_conditionPolynomial_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (conditionPolynomial f hf v P) =
      killCompl hf (homogeneousComponent r P) :=
  homogeneousComponent_restricted_translate_top f hf P _ r hP

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev LayerSamplerLongVariables (inactive : LayerSamplerAxis I n → Prop)
    (G : Type*) (B : LayerSamplerAxis I n → Type*) :=
  SamplerLongVariables inactive G B (layerSamplerDegree I n)

def allocatedLongEmbedding (inactive : LayerSamplerAxis I n → Prop) :
    LayerSamplerLongVariables inactive G B ↪ LayerSamplerVariables G I n B :=
  samplerLongEmbedding inactive (layerSamplerDegree I n)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedDegreeActiveAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {a : I j ⊕ Fin (n j) // ¬ inactive ⟨j, a⟩}

abbrev AllocatedDegreeRankOutput (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  E j ⊕ AllocatedDegreeActiveAxis inactive j

def allocatedDegreeLongAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (a : AllocatedDegreeActiveAxis inactive j) : {a // ¬ inactive a} :=
  ⟨⟨j, a.val⟩, a.property⟩

def allocatedDegreeRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => kernelRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1) kernel l
  | .inr a, l => canonicalRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1)
      (allocatedDegreeLongAxis inactive j a) (block a l)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

noncomputable def canonicalPrincipalSubblockSlot (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) :
    Fin J → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  fun j => principalCoefficientSlot h d (block j)

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_injective (h : D → ℕ) (d : D) (hd : 0 < h d)
    {J : ℕ} (block : Fin J ↪ B d) :
    Function.Injective (canonicalPrincipalSubblockSlot (G := G) h d block) :=
  (principalCoefficientSlot_injective h d hd).comp block.injective

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_degree (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) (j : Fin J) :
    (canonicalPrincipalSubblockSlot (G := G) h d block j).val.degree = h d :=
  canonicalPrincipalExponent_degree h d (block j)

noncomputable def canonicalSelectedTopResidual (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R) :
    MvPolynomial (SamplerTupleIndex G B h) R :=
  homogeneousComponent (h d) (modularUnselectedCoefficientPolynomial (h d)
    (canonicalPrincipalSubblockSlot h d block) fixed)

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in

theorem samplerLong_killCompl_principal_monomial (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (c : R) :
    killCompl (samplerLongEmbedding (G := G) inactive h).injective
      (monomial (principalCoefficientSlot h d.val b).val c) =
      c • ∏ k ∈ canonicalRankBlock (G := G)
        (B := fun a : {a // ¬ inactive a} => B a.val) (fun a => h a.val) d b, X k := by
  rw [← samplerLongEmbedding_principalExponent inactive h d b,
    killCompl_monomial_mapDomain, principalCoefficientSlot_monomial, smul_eq_C_mul]

noncomputable def canonicalSelectedLongTopResidual (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R) :
    MvPolynomial (SamplerLongVariables inactive G B h) R :=
  killCompl (samplerLongEmbedding inactive h).injective
    (canonicalSelectedTopResidual h d.val block fixed)

theorem canonicalBoundedCoefficient_selected_long_top (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (hd : 0 < h d.val) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R)
    (c : Fin J → R) (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent (h d.val)
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (modularBoundedCoefficientPolynomial (h d.val)
          (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed))) =
      canonicalSelectedLongTopResidual inactive h d block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun a : {a // ¬ inactive a} => B a.val)
          (fun a => h a.val) d (block j), X k := by
  have hdegree : (modularBoundedCoefficientPolynomial (h d.val)
      (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed)).totalDegree ≤
        h d.val := by
    apply totalDegree_finsetSum_le
    intro e _
    exact (totalDegree_monomial_le e.val _).trans e.property
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v (h d.val) hdegree,
    modularBoundedCoefficientPolynomial_selected_top (h d.val) _
      (canonicalPrincipalSubblockSlot_injective h d.val hd block)
      (canonicalPrincipalSubblockSlot_degree h d.val block), map_add, map_sum]
  change canonicalSelectedLongTopResidual inactive h d block fixed + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact samplerLong_killCompl_principal_monomial inactive h d (block j) (c j)

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

theorem allocatedBoundedCoefficient_selected_long_top
    (inactive : LayerSamplerAxis I n → Prop) (a : {a // ¬ inactive a})
    {J : ℕ} (block : Fin J ↪ B a.val)
    (fixed : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.val.1.val + 1) → R)
    (c : Fin J → R) (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent (a.val.1.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (a.val.1.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) a.val block)
            c fixed))) =
      canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n) a block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun b : {b // ¬ inactive b} => B b.val)
          (fun b => b.val.1.val + 1) a (block j), X k :=
  canonicalBoundedCoefficient_selected_long_top inactive (layerSamplerDegree I n) a
    (Nat.zero_lt_succ _) block fixed c v

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev SpatialDegreeOutput (X : Type*) (j : Fin m) := {_x : X // j.val = 0}

abbrev AllocatedTaggedRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ AllocatedDegreeRankOutput E inactive j

def allocatedSpatialRankBlock (inactive : LayerSamplerAxis I n → Prop)
    {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    Finset (LayerSamplerLongVariables inactive G B) :=
  {.inl (spatial l)}

def allocatedTaggedRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => allocatedSpatialRankBlock inactive spatial l
  | .inr o, l => allocatedDegreeRankBlock inactive j kernel block o l

theorem allocatedSpatialRankBlock_product {R : Type*} [CommSemiring R]
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    (∏ k ∈ allocatedSpatialRankBlock (B := B) inactive spatial l,
      MvPolynomial.X k : MvPolynomial (LayerSamplerLongVariables inactive G B) R) =
        MvPolynomial.X (.inl (spatial l)) := by
  rw [allocatedSpatialRankBlock, Finset.prod_singleton]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

abbrev AllocatedCongruenceIntegerAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {i : Fin (n j) // ¬ inactive ⟨j, Sum.inr i⟩}

abbrev AllocatedCongruenceRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)

def allocatedCongruenceIntegerEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceIntegerAxis inactive j ↪ AllocatedDegreeActiveAxis inactive j where
  toFun i := ⟨Sum.inr i.val, i.property⟩
  inj' := by
    intro i k he
    apply Subtype.ext
    exact Sum.inr.inj (congrArg Subtype.val he)

def allocatedCongruenceOutputEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j ↪ AllocatedTaggedRankOutput X E inactive j :=
  Function.Embedding.sumMap (Function.Embedding.refl _)
    (Function.Embedding.sumMap (Function.Embedding.refl _)
      (allocatedCongruenceIntegerEmbedding inactive j))

@[simp] theorem allocatedCongruenceOutputEmbedding_spatial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (x : SpatialDegreeOutput X j) :
    allocatedCongruenceOutputEmbedding (E := E) inactive j (.inl x) = .inl x := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_deck
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (e : E j) :
    allocatedCongruenceOutputEmbedding (X := X) inactive j (.inr (.inl e)) = .inr (.inl e) := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_integer
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (i : AllocatedCongruenceIntegerAxis inactive j) :
    allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j (.inr (.inr i)) =
      .inr (.inr ⟨Sum.inr i.val, i.property⟩) := rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativePatchRankTightening
namespace OAI

section

namespace Erdos3

theorem RelativePatchSliceConclusion.tighten_rank
    {X : Type*} [Fintype X] {s : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost) :
    RelativePatchSliceConclusion s N f target (min rankBound ⌊cost⌋₊) cost := by
  obtain ⟨q,hq,S,d,A,hlength,hd,hcomplexity,hscore⟩ := h
  have hdp : d ≤ ⌊cost⌋₊ := Nat.le_floor ((relativePatchComplexity_rank_le A).trans hcomplexity)
  exact ⟨q,hq,S,d,A,hlength,le_min hd hdp,hcomplexity,hscore⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

def RelativeReturnedFiberLaw {X : Type*} [Fintype X] [DecidableEq X]
    (keep : X → Prop) [DecidablePred keep] (N : X → ℕ) (cost : ℝ)
    (law : FiniteProbabilityWeights (integerBox N)) : Prop :=
  ∃ (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (q : ℕ), 0 < q ∧
    ∃ (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
      (hlen : ∀ i, 0 < S.length i),
      (∀ i, Real.exp (-cost) * (N i.val : ℝ) ≤ (S.length i : ℝ)) ∧
      law = S.fiberSliceLaw hlen fixed hfixed

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem exists_relative_finite_returned_fiber_normalization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {Ω X : Type*}
      [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
      (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω),
      0 < outer.mass productive →
      ∀ (N : X → ℕ) (keep : X → Prop) [DecidablePred keep],
      (∀ i, 0 < N i) → ∀ (p : ℝ), 0 ≤ p →
      ∀ (target : ℝ), target ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (rankBound : ℕ) (f : Ω → (X → ℤ) → ℝ),
      (∀ h x, x ∈ integerBox N → f h x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ h ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
        (∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) ∧
        RelativePatchSliceConclusion s (fun i : {i // keep i} => N i.val)
          (fun u => f h (finiteSplitPoint keep u fixed)) target rankBound p) →
      let q := p + (Fintype.card X : ℝ) + 2
      let D := min rankBound ⌊p⌋₊
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox N))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ d ≤ rankBound ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        (∀ h ∈ retained, RelativeReturnedFiberLaw keep N p (localLaw h)) ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => (f h t.val - target) * (B.shearTransformedSlots hw
            ((localForm h).loweringAt (fun i => (t.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hnormalize⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro Ω X _ _ _ _ outer productive hmass N keep _ hN p hp target ht
    rankBound f hf hreturn q D
  have hdata (h : Ω) (hh : h ∈ productive) :
      ∃ (d : ℕ) (Q : PolynomialPatch X s d)
        (law : FiniteProbabilityWeights (integerBox N)),
        d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ law.mean
          (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ))) ∧
        RelativeReturnedFiberLaw keep N p law := by
    obtain ⟨fixed, hfixed, hslice⟩ := hreturn h hh
    obtain ⟨d, Q, law, hd, _, hlip, hscore, r, hr, S, hlen, hlength, hlaw⟩ :=
      hslice.tighten_rank.exists_fiber_law_with_slice fixed hfixed (fun i => hN i.val)
    exact ⟨d, Q, law, hd, hlip, hscore, fixed, hfixed, r, hr, S, hlen, hlength, hlaw⟩
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault, _, _⟩ := hdata h₀ hh₀
  have hall (h : Ω) : ∃ (d : ℕ) (Q : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ law.mean
        (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ)))) ∧
      (h ∈ productive → RelativeReturnedFiberLaw keep N p law) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, Q, law, hd, hlip, hscore, hslice⟩ := hdata h hh
      exact ⟨d, Q, law, hd, hlip, fun _ => hscore, fun _ => hslice⟩
    · exact ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault,
        fun hmem => (hh hmem).elim, fun hmem => (hh hmem).elim⟩
  choose d patch localLaw hd hlip hpositive hslice using hall
  have hpq : p ≤ q := by dsimp only [q]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card X)]
  have hq : 0 ≤ q := hp.trans hpq
  have hD : (D : ℝ) ≤ q :=
    (Nat.cast_le.mpr (Nat.min_le_right rankBound ⌊p⌋₊)).trans ((Nat.floor_le hp).trans hpq)
  have hX : (Fintype.card X : ℝ) ≤ q := by dsimp only [q]; linarith
  let point := fun (_ : Ω) (x : integerBox N) => x.val
  let score := fun h (x : integerBox N) => f h x.val - target
  have hscore (h) (x : integerBox N) : |score h x| ≤ 1 := by
    dsimp only [score]
    obtain ⟨hf0, hf1⟩ := hf h x.val x.property
    exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hmass', hlocal⟩ :=
    hnormalize outer productive d patch D q hd hmass hq hD hX
      (fun h => (hlip h).trans (Real.exp_le_exp.mpr hpq)) localLaw point score hscore
      (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive h hh))
  exact ⟨localLaw, d', w, hw, Ψ, B, localForm, retained, hd',
    hd'.trans (Nat.min_le_left _ _), hpos, hws, hΨ, hB, hsub, hmass',
    fun h hh => hslice h (hsub hh), hlocal⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ}
  {G X : Type*}
  [Fintype G]
  [Fintype X]
  {I : Fin m → Type*}
  [∀ j, Fintype (I j)]
  {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}
  [∀ a, Fintype (B a)]
  {J : Fin m → Type*}
  [∀ j, Fintype (J j)]
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
  {R σ : Fin m → ℝ}
  {S : LayerSamplerScale (G := G) B U b R σ}
  {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}
  {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSamplerFamily

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeFinalEnvelope
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount p : ℝ) : ℝ :=
  2 + (p + 2) ^ preparationPower + (p + 2) ^ requiredPower +
    ((p + 2) ^ basePower + 2) ^ inputPower + (⌈discount⁻¹⌉₊ : ℝ) +
      (p + 2) ^ basePower + degree * p

end Erdos3.VectorPolynomial

end

end OAI

end


