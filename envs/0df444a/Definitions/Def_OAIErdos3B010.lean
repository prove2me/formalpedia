-- Prove2me | Definitions.Def_OAIErdos3B010
-- name    : OAIErdos3B010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:29:53.139949+00:00
-- url     : https://prove2.me/theorems/7397badc-05da-4238-b381-8b45ec8527eb
-- title:
--   OpenAI Erdős-3 split, definitions bundle 11 of 88
-- statement:
--   Definitions bundle 11 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B009`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 11 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.physicalCubeOptionEquiv`, `OAI.Erdos3.BooleanCubeKernel.physicalCubePivotIndex`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialInputScale`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialInverseBound`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialInverseBound_le_exp`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialOutputScale`, `OAI.Erdos3.BooleanCubeKernel.physicalSpatialOutputScale_pos`, `OAI.Erdos3.BooleanCubeKernel.trimmedSpatialRootScale`, `OAI.Erdos3.BooleanCubeKernel.trimmedSpatialSlopeScale`, `OAI.Erdos3.CellRefinement.replacementPotentialSum`, `OAI.Erdos3.CircleFourier.complex_fejerPolynomial_eq`, `OAI.Erdos3.CircleFourier.continuous_fejerPolynomial`, `OAI.Erdos3.CircleFourier.fejerCoefficient`, `OAI.Erdos3.CircleFourier.fejerCoefficient_le_one`, `OAI.Erdos3.CircleFourier.fejerCoefficient_nonneg`, `OAI.Erdos3.CircleFourier.fejerFrequencies`, `OAI.Erdos3.CircleFourier.fejerPairFrequency`, `OAI.Erdos3.CircleFourier.fejerPolynomial`, `OAI.Erdos3.CircleFourier.fejerPolynomial_eq`, `OAI.Erdos3.CircleFourier.fejerPolynomial_le_of_distance`, `OAI.Erdos3.CircleFourier.fejerPolynomial_nonneg`, `OAI.Erdos3.CircleFourier.integral_fejerPolynomial`, `OAI.Erdos3.DenseResidueSliceNetCode`, `OAI.Erdos3.DenseResidueSliceNetCode.Valid`, `OAI.Erdos3.DenseResidueSliceNetCode.card`, `OAI.Erdos3.DenseResidueSliceNetCode.fullParent`, `OAI.Erdos3.DenseResidueSliceNetCode.length`, `OAI.Erdos3.DenseResidueSliceNetCode.meshCode`, `OAI.Erdos3.DenseResidueSliceNetCode.realize`, `OAI.Erdos3.DenseResidueSliceNetCode.start`, `OAI.Erdos3.DenseResidueSliceNetCode.stride`, `OAI.Erdos3.FiniteProbabilityWeights.ofDensity`, `OAI.Erdos3.FixedDensity.FacePartition`, `OAI.Erdos3.FixedDensity.FacePartition.atomSetoid`, `OAI.Erdos3.FixedDensity.FacePartition.atomSetoid_rel`, `OAI.Erdos3.FixedDensity.FacePartition.complexity`, `OAI.Erdos3.FixedDensity.FacePartition.complexity_discrete`, `OAI.Erdos3.FixedDensity.FacePartition.complexity_generatedBy_le`, `OAI.Erdos3.FixedDensity.FacePartition.complexity_indiscrete`, `OAI.Erdos3.FixedDensity.FacePartition.complexity_join_le`, `OAI.Erdos3.FixedDensity.FacePartition.discrete`, `OAI.Erdos3.FixedDensity.FacePartition.ext_of_part_eq`, `OAI.Erdos3.FixedDensity.FacePartition.generatedBy`, `OAI.Erdos3.FixedDensity.FacePartition.generatedBy_antitone`, `OAI.Erdos3.FixedDensity.FacePartition.generatedBy_empty`, `OAI.Erdos3.FixedDensity.FacePartition.indiscrete`, `OAI.Erdos3.FixedDensity.FacePartition.instDecidableRelPullbackSetoid`, `OAI.Erdos3.FixedDensity.FacePartition.join`, `OAI.Erdos3.FixedDensity.FacePartition.joinFinset`, `OAI.Erdos3.FixedDensity.FacePartition.joinFinset_empty`, `OAI.Erdos3.FixedDensity.FacePartition.joinFinset_insert`, `OAI.Erdos3.FixedDensity.FacePartition.joinFinset_le_of_mem`, `OAI.Erdos3.FixedDensity.FacePartition.join_le_left`, `OAI.Erdos3.FixedDensity.FacePartition.join_le_right`, `OAI.Erdos3.FixedDensity.FacePartition.le_iff_part_subset`, `OAI.Erdos3.FixedDensity.FacePartition.le_joinFinset_iff`, `OAI.Erdos3.FixedDensity.FacePartition.le_join_iff`, `OAI.Erdos3.FixedDensity.FacePartition.mem_part_generatedBy_iff`, `OAI.Erdos3.FixedDensity.FacePartition.mem_part_joinFinset_iff`, `OAI.Erdos3.FixedDensity.FacePartition.mem_part_pullback_iff`, `OAI.Erdos3.FixedDensity.FacePartition.mem_part_pullback_iff_image_mem`, `OAI.Erdos3.FixedDensity.FacePartition.part_discrete`, `OAI.Erdos3.FixedDensity.FacePartition.part_indiscrete`, `OAI.Erdos3.FixedDensity.FacePartition.part_join`, `OAI.Erdos3.FixedDensity.FacePartition.part_subset_of_le`, `OAI.Erdos3.FixedDensity.FacePartition.pullback`, `OAI.Erdos3.FixedDensity.FacePartition.pullbackSetoid`, `OAI.Erdos3.FixedDensity.FacePartition.pullback_id`, `OAI.Erdos3.FixedDensity.FacePartition.pullback_mono`, `OAI.Erdos3.FixedDensity.FacePartition.representative`, `OAI.Erdos3.FixedDensity.FacePartition.representative_mem`, `OAI.Erdos3.FixedDensity.conditionalMean`, `OAI.Erdos3.FixedDensity.conditionalMean_const`, `OAI.Erdos3.FixedDensity.conditionalMean_eq_of_mem_part`, `OAI.Erdos3.FixedDensity.conditionalMean_eq_of_part_eq`, `OAI.Erdos3.FixedDensity.conditionalMean_idem`, `OAI.Erdos3.FixedDensity.conditionalMean_mul_conditionalMean_right`, `OAI.Erdos3.FixedDensity.conditionalMean_mul_right_of_constant_on_part`, `OAI.Erdos3.FixedDensity.conditionalMean_reverse_tower_of_le`, `OAI.Erdos3.FixedDensity.conditionalMean_smul`, `OAI.Erdos3.FixedDensity.conditionalMean_sq_le`, `OAI.Erdos3.FixedDensity.conditionalMean_sub`, `OAI.Erdos3.FixedDensity.conditionalMean_tower_of_le`, `OAI.Erdos3.FixedDensity.cyclicAPCount`, `OAI.Erdos3.FixedDensity.cyclicAPCount_const`, `OAI.Erdos3.FixedDensity.cyclicAPProduct`, `OAI.Erdos3.FixedDensity.cyclicAPProduct_const`, `OAI.Erdos3.FixedDensity.cyclicAPTerm`, `OAI.Erdos3.FixedDensity.finsetIndicator`, `OAI.Erdos3.FixedDensity.finsetIndicator_of_mem`, `OAI.Erdos3.FixedDensity.finsetIndicator_of_not_mem`, `OAI.Erdos3.FixedDensity.mean`, `OAI.Erdos3.FixedDensity.mean_add`, `OAI.Erdos3.FixedDensity.mean_conditionalMean`, `OAI.Erdos3.FixedDensity.mean_conditionalMean_mul_eq_sq_of_le`, `OAI.Erdos3.FixedDensity.mean_const`, `OAI.Erdos3.FixedDensity.mean_empty`, `OAI.Erdos3.FixedDensity.mean_le_of_le_const`, `OAI.Erdos3.FixedDensity.mean_mono`, `OAI.Erdos3.FixedDensity.mean_nonneg`, `OAI.Erdos3.FixedDensity.mean_smul`, `OAI.Erdos3.FixedDensity.mean_sub`, `OAI.Erdos3.FixedDensity.mean_zero`, `OAI.Erdos3.FixedDensity.mean₂`, `OAI.Erdos3.FixedDensity.partitionEnergy`, `OAI.Erdos3.FixedDensity.partitionEnergy_le_mean_sq`, `OAI.Erdos3.FixedDensity.partitionEnergy_mono`, `OAI.Erdos3.FixedDensity.partitionEnergy_nonneg`, `OAI.Erdos3.FixedDensity.partitionEnergy_pythagorean`, `OAI.Erdos3.FixedDensity.partitionEnergy_sub_eq_mean_sq`, `OAI.Erdos3.FixedDensity.sum_conditionalMean`, `OAI.Erdos3.FixedDensity.sum_conditionalMean_on_coarser_part`, `OAI.Erdos3.FixedDensity.sum_conditionalMean_on_part`, `OAI.Erdos3.LocalConvolution.convolution`, `OAI.Erdos3.LocalConvolution.correlation`, `OAI.Erdos3.LocalConvolution.differenceLp`, `OAI.Erdos3.LocalConvolution.differenceMoment`, `OAI.Erdos3.LocalConvolution.momentAmplificationFactor`, `OAI.Erdos3.LocalConvolution.momentAmplificationGain`, `OAI.Erdos3.LocalConvolution.momentVector`, `OAI.Erdos3.LocalConvolution.plusMomentVector`, `OAI.Erdos3.LocalConvolution.sumLp`, `OAI.Erdos3.LocalConvolution.sumMoment`, `OAI.Erdos3.Peeling.coefficientCost`, `OAI.Erdos3.Peeling.potentialCost`, `OAI.Erdos3.ResidueBoxSlice.fullSliceInverseParameters`, `OAI.Erdos3.ResidueBoxSlice.fullSliceInverseParameters_degree`, `OAI.Erdos3.ResidueBoxSlice.fullSliceLaw`, `OAI.Erdos3.ResidueBoxSlice.fullSliceLaw_mean`, `OAI.Erdos3.ResidueBoxSlice.fullSlicePointInIntegerBox`, `OAI.Erdos3.ResidueBoxSlice.fullSliceReinsertPatch`, `OAI.Erdos3.ResidueBoxSlice.fullSliceSupport`, `OAI.Erdos3.SlicedProductBlock.Admissible.casesOn`, `OAI.Erdos3.SlicedProductBlock.base`, `OAI.Erdos3.SlicedProductBlock.noConfusion`, `OAI.Erdos3.SlicedProductBlock.pairCap`, `OAI.Erdos3.SlicedProductBlock.pairCap_pos`, `OAI.Erdos3.SlicedProductBlock.pairScale`, `OAI.Erdos3.SlicedProductBlock.pairScale_pos`, `OAI.Erdos3.SlicedProductBlock.pairWidth`, `OAI.Erdos3.SlicedProductBlock.prefixProduct`, `OAI.Erdos3.SlicedProductBlock.slope`, `OAI.Erdos3.SlicedProductBlock.value`, `OAI.Erdos3.SlicedProductBlock.volumeScale`, `OAI.Erdos3.SlicedProductBlock.volumeScale_pos`, `OAI.Erdos3.UnselectedColumn`, `OAI.Erdos3.VectorPolynomial.modeAmplitudeAccuracy`, `OAI.Erdos3.VectorPolynomial.modeAmplitudeAccuracy_inv_le_exp`, `OAI.Erdos3.VectorPolynomial.modeAmplitudeAccuracy_pos`, `OAI.Erdos3.VectorPolynomial.modeAmplitudeError_bound`, `OAI.Erdos3.VectorPolynomial.modeRemovalRadius_le_error`, `OAI.Erdos3.abs_coordinate_le_coordinateL2Norm`, `OAI.Erdos3.abs_metricTentPartition_sub_le`, `OAI.Erdos3.abs_metricTentSum_sub_le`, `OAI.Erdos3.abs_metricTent_sub_le`, `OAI.Erdos3.abs_sub_le_of_circle_dist_on_interior`, `OAI.Erdos3.add_le_exp_add_one`, `OAI.Erdos3.additiveGraph`, `OAI.Erdos3.additiveGraphQuadruple`, `OAI.Erdos3.additiveGraphQuadruple_injective`, `OAI.Erdos3.additiveGraph_card`, `OAI.Erdos3.affineParameterBadPair`, `OAI.Erdos3.affine_interval_eq_progression`, `OAI.Erdos3.algebraicMajor_denominator_le_exp`, `OAI.Erdos3.algebraicMajor_mass_le_exp`, `OAI.Erdos3.allocatedProfile_budget`, `OAI.Erdos3.assemble_triple_fibers`, `OAI.Erdos3.assemble_tuple_fibers`, `OAI.Erdos3.basisAxisScale`, `OAI.Erdos3.basisAxisScale_mul_norm`, `OAI.Erdos3.basisAxisScale_pos`, `OAI.Erdos3.basis_coordinates_norm_le_of_covolume`, `OAI.Erdos3.basis_synthesis_norm_le`, `OAI.Erdos3.binarySorted`, `OAI.Erdos3.binarySorted_comp`, `OAI.Erdos3.binarySorted_tail`, `OAI.Erdos3.binarySorted_threshold`, `OAI.Erdos3.binaryZeroCount`, `OAI.Erdos3.binaryZeroCount_comp`, `OAI.Erdos3.binary_eq_one_of_ne_zero`, `OAI.Erdos3.binary_eq_zero_of_ne_one`, `OAI.Erdos3.blockSubsetEquiv`, `OAI.Erdos3.blockSubsetUnion`, `OAI.Erdos3.blockSubsetUnion_filter`, `OAI.Erdos3.blockSubsetUnion_filters`, `OAI.Erdos3.blockSubsetUnion_subset`, `OAI.Erdos3.booleanJetMassLog`, `OAI.Erdos3.booleanToleranceC2`, `OAI.Erdos3.booleanToleranceC2Log`, `OAI.Erdos3.boxCoverMeshCount`, `OAI.Erdos3.boxCoverMeshCount_add_one_le_exp`, `OAI.Erdos3.boxCoverMeshCount_error`, `OAI.Erdos3.boxCoverMeshCount_pos`, `OAI.Erdos3.box_overlap_cube_weight`, `OAI.Erdos3.canonicalCubeMinorThreshold`, `OAI.Erdos3.card_blockSubsets`, `OAI.Erdos3.card_integerProgressionSupport`, `OAI.Erdos3.chosenBiasBudget_le_exp`, `OAI.Erdos3.coe_toNNReal_le_exp`, `OAI.Erdos3.coefficientImagePMF`, `OAI.Erdos3.coefficientLogAllowance`, `OAI.Erdos3.coefficientPMF`, `OAI.Erdos3.coefficientProfileCenter`, `OAI.Erdos3.coefficientProfileWidth`, `OAI.Erdos3.coefficientProfileWidth_pos`, `OAI.Erdos3.coefficientProfile_budget`, `OAI.Erdos3.coefficientReplacementScale`, `OAI.Erdos3.coefficientWeight`, `OAI.Erdos3.coefficientWeightSum`, `OAI.Erdos3.coefficientWeight_summable`, `OAI.Erdos3.coefficient_gap_principal_width`, `OAI.Erdos3.columnInclusionMatrix`, `OAI.Erdos3.commonStrideBox`, `OAI.Erdos3.commonStrideBox_card`, `OAI.Erdos3.commonStrideBox_eq_image`, `OAI.Erdos3.commonStrideBox_nonempty`, `OAI.Erdos3.commonStrideIndex`, `OAI.Erdos3.commonStrideIndex_point`, `OAI.Erdos3.commonStridePoint`, `OAI.Erdos3.commonStridePoint_injective`, `OAI.Erdos3.commonStridePoint_mem`, `OAI.Erdos3.conditioningCoreSupports`, `OAI.Erdos3.conditioningShellSupports`, `OAI.Erdos3.convolutionPower`, `OAI.Erdos3.convolutionPower_nonneg`, `OAI.Erdos3.convolutionPower_succ`, `OAI.Erdos3.convolutionPower_zero`, `OAI.Erdos3.coordinateGridModule`, `OAI.Erdos3.coordinateGridModule_map_of_basis`, `OAI.Erdos3.coordinateGrid_bracket_divisible`, `OAI.Erdos3.coordinateGrid_functional_integral`, `OAI.Erdos3.coordinateL2Norm`, `OAI.Erdos3.coordinateL2Norm_le_card_bound`, `OAI.Erdos3.coordinateL2Norm_matrix_entry_bound`, `OAI.Erdos3.coordinateL2Norm_matrix_le`, `OAI.Erdos3.coordinateL2Norm_nonneg`, `OAI.Erdos3.coordinateLinearMap_L2_bound`, `OAI.Erdos3.coordinateLinearMap_apply_sum`, `OAI.Erdos3.covolume_basis_eq_orthonormal_det`, `OAI.Erdos3.covolume_basis_le_norm_bound`, `OAI.Erdos3.covolume_basis_scale`, `OAI.Erdos3.cubeMinorDegree`, `OAI.Erdos3.cubeMinorProbabilityConstant`, `OAI.Erdos3.cubeMinorProbabilityScale`, `OAI.Erdos3.cubeMinorThreshold`, `OAI.Erdos3.cubeMinorVariableCount`, `OAI.Erdos3.cyclicInterval_zeroExtension_average`, `OAI.Erdos3.cyclicWrapExceptional`, `OAI.Erdos3.cyclicWrapExceptional_card_le`, `OAI.Erdos3.cyclicWrapExceptional_density_le`, `OAI.Erdos3.degreeTailSupports`, `OAI.Erdos3.dense_product_approximation_density`, `OAI.Erdos3.dense_triple_fibers`, `OAI.Erdos3.dense_tuple_fibers`, `OAI.Erdos3.embedding_basis_coordinate_height`, `OAI.Erdos3.embedding_coordinate_height_budget`, `OAI.Erdos3.euclideanDerivativeLattice_covolume_le`, `OAI.Erdos3.euclidean_matrix_mulVec_norm_le`, `OAI.Erdos3.exists_bounded_common_stride_reindex`, `OAI.Erdos3.exists_bounded_ordered_exponents`, `OAI.Erdos3.exists_bounded_rational_grid_matrix`, `OAI.Erdos3.exists_bounded_rational_map_matrix`, `OAI.Erdos3.exists_bounded_rational_row_normalization`, `OAI.Erdos3.exists_common_integer_interval`, `OAI.Erdos3.exists_exp_integer_grid_scale`, `OAI.Erdos3.exists_filtered_finite_enumeration`, `OAI.Erdos3.exists_finite_classified_representatives`, `OAI.Erdos3.exists_finite_fiber_representatives`, `OAI.Erdos3.exists_finite_indexed_representative_enumeration`, `OAI.Erdos3.exists_grid_row_normalization`, `OAI.Erdos3.exists_integer_coefficient_scale_gap`, `OAI.Erdos3.exists_integer_scaled_grid_matrix`, `OAI.Erdos3.exists_lie_quotient_basis_exp_height`, `OAI.Erdos3.exists_linear_expansion_of_two_vanish`, `OAI.Erdos3.exists_nested_box_affine`, `OAI.Erdos3.exists_nested_progression_affine`, `OAI.Erdos3.exists_normalized_site_cutoff`, `OAI.Erdos3.exists_quotient_presentation_exp_height`, `OAI.Erdos3.exists_same_stride_progression_reindex`, `OAI.Erdos3.exists_unoccupied_coefficient_gap`, `OAI.Erdos3.expect_abs_le_of_exceptional_set`, `OAI.Erdos3.expect_finset_subtype`, `OAI.Erdos3.expect_zeroExtendFinset`, `OAI.Erdos3.extendIntegerSiteSection`, `OAI.Erdos3.extendIntegerSiteSection_cast`, `OAI.Erdos3.extendIntegerSiteSection_column_sum`, `OAI.Erdos3.extendIntegerSiteSection_column_sum_bound`, `OAI.Erdos3.finiteCommonStrideFamily`, `OAI.Erdos3.finiteCommonStrideFamily_card`, `OAI.Erdos3.finiteCommonStrideFamily_shape`, `OAI.Erdos3.finiteCorrelation_commonStrideBox`, `OAI.Erdos3.finiteFiberAverage`, `OAI.Erdos3.finiteKernelLiftLaw`, `OAI.Erdos3.finiteLayerBiasBudget`, `OAI.Erdos3.finiteLayerBiasBudget_le_exp`, `OAI.Erdos3.finiteLayerBiasBudget_one_le`, `OAI.Erdos3.finiteLayerInverseConstant`, `OAI.Erdos3.finiteLayerInverseExponent`, `OAI.Erdos3.finiteLayerInverseLog`, `OAI.Erdos3.finiteLayerInverseLog_nonneg`, `OAI.Erdos3.finiteSetLp`, `OAI.Erdos3.fixedPathSlicedGridMeshFloor`, `OAI.Erdos3.fixedPathSlicedGridMeshLog`, `OAI.Erdos3.frozenRealSection`, `OAI.Erdos3.frozenRealSection_unit_interval`, `OAI.Erdos3.frozenTupleCoordinate`, `OAI.Erdos3.good_circle_observations_control_representatives`, `OAI.Erdos3.graph_energy_of_few_quadruple_differences`, `OAI.Erdos3.inactiveDenominator`, `OAI.Erdos3.inactiveDenominator_bound`, `OAI.Erdos3.inactiveDenominator_pos`, `OAI.Erdos3.inactivePrincipalPMF`, `OAI.Erdos3.inactivePrincipalPMF_support`, `OAI.Erdos3.inactivePrincipal_scaled_upper`, `OAI.Erdos3.integerAffineMap`, `OAI.Erdos3.integerAffineMap_diagonal`, `OAI.Erdos3.integerAffinePolynomial`, `OAI.Erdos3.integerAffinePolynomial_eval`, `OAI.Erdos3.integerAffinePolynomial_support`, `OAI.Erdos3.integerBoxBadPairBudget`, `OAI.Erdos3.integerGridEnd`, `OAI.Erdos3.integerGridEnd_bounds`, `OAI.Erdos3.integerGridStart`, `OAI.Erdos3.integerGridStart_bounds`, `OAI.Erdos3.integerLinearForm_eq_sum`, `OAI.Erdos3.integerPeriod_range_le_of_columns`, `OAI.Erdos3.integerProgressionSupport_point`, `OAI.Erdos3.integerProgressionSupport_reindex`, `OAI.Erdos3.integerProgressionSupport_singleton`, `OAI.Erdos3.integerResidueTuple`, `OAI.Erdos3.integerSiteResidual_extend_columns`, `OAI.Erdos3.integer_grid_interval_correlation`, `OAI.Erdos3.integer_grid_interval_geometry`, `OAI.Erdos3.integer_row_normalization_entry`, `OAI.Erdos3.integer_row_normalization_grid`, `OAI.Erdos3.integer_row_normalization_height`, `OAI.Erdos3.interiorIntervalCutoff`, `OAI.Erdos3.interiorIntervalCutoff_lipschitz`, `OAI.Erdos3.interiorIntervalCutoff_range`, `OAI.Erdos3.interiorIntervalCutoff_support`, `OAI.Erdos3.jointBooleanWeightBudget`, `OAI.Erdos3.layerRemovalRankBudget`, `OAI.Erdos3.layerRemovalRankBudget_bounds`, `OAI.Erdos3.lengthAwareSpectrumCover`, `OAI.Erdos3.linearFunctional_coordinate_height`, `OAI.Erdos3.lipschitz_metricTentPartition`, `OAI.Erdos3.localizedMajorArcBudget`, `OAI.Erdos3.localizedMajorArcBudget_pos`, `OAI.Erdos3.localizedMajorArcErrorBudget`, `OAI.Erdos3.localizedMajorArcLengthBudget`, `OAI.Erdos3.lowDegreeCoordinateSets`, `OAI.Erdos3.majorArcBiasConstant`, `OAI.Erdos3.majorArcBiasExponent`, `OAI.Erdos3.majorArcCoverConstant`, `OAI.Erdos3.majorArcCoverExponent`, `OAI.Erdos3.majorArcErrorConstant`, `OAI.Erdos3.majorArcErrorExponent`, `OAI.Erdos3.majorArcLengthConstant`, `OAI.Erdos3.majorArcLengthExponent`, `OAI.Erdos3.majorArcLocalizationConstant`, `OAI.Erdos3.majorArcSpectrumConstant`, `OAI.Erdos3.majorArcSpectrumExponent`, `OAI.Erdos3.majorPhaseCoordinateDenominator_grid`, `OAI.Erdos3.majorPhaseCoordinateDenominator_le_exp`, `OAI.Erdos3.majorPhaseCoordinateDenominator_pos`, `OAI.Erdos3.massConvolution`, `OAI.Erdos3.massConvolution_comm`, `OAI.Erdos3.massConvolution_nonneg`, `OAI.Erdos3.matrix_mul_columnInclusion`, `OAI.Erdos3.mean_prod_error_le`, `OAI.Erdos3.mem_finiteCommonStrideFamily`, `OAI.Erdos3.mem_integerProgressionSupport_iff_parameter`, `OAI.Erdos3.mem_scalarCubeGridSet`, `OAI.Erdos3.metricPartition_constant_le_exp`, `OAI.Erdos3.metricTent`, `OAI.Erdos3.metricTentPartition`, `OAI.Erdos3.metricTentPartition_le_one`, `OAI.Erdos3.metricTentPartition_nonneg`, `OAI.Erdos3.metricTentPartition_zero_of_far`, `OAI.Erdos3.metricTentSum`, `OAI.Erdos3.metricTentSum_ge`, `OAI.Erdos3.metricTent_le`, `OAI.Erdos3.metricTent_nonneg`, `OAI.Erdos3.metricTent_zero_of_far`, `OAI.Erdos3.modeBiasLog`, `OAI.Erdos3.modeBiasLog_nonneg`, `OAI.Erdos3.modeProfileBound`, `OAI.Erdos3.modeProfileLog`, `OAI.Erdos3.modeProfileLog_nonneg`, `OAI.Erdos3.modeRemovalBeta`, `OAI.Erdos3.modeRemovalBeta_inv_le_exp`, `OAI.Erdos3.modeRemovalBeta_le_one`, `OAI.Erdos3.modeRemovalBeta_pos`, `OAI.Erdos3.modeRemovalBias`, `OAI.Erdos3.modeRemovalBias_inv_le_exp`, `OAI.Erdos3.modeRemovalBias_le`, `OAI.Erdos3.modeRemovalBias_pos`, `OAI.Erdos3.modeRemovalConstants_le_exp`, `OAI.Erdos3.modeRemovalError_bound`, `OAI.Erdos3.modeRemovalMesh`, `OAI.Erdos3.modeRemovalMeshConstant`, `OAI.Erdos3.modeRemovalMeshConstant_nonneg`, `OAI.Erdos3.modeRemovalMesh_inv_le_exp`, `OAI.Erdos3.modeRemovalMesh_le_one`, `OAI.Erdos3.modeRemovalMesh_of_width`, `OAI.Erdos3.modeRemovalMesh_pos`, `OAI.Erdos3.modeRemovalMesh_small`, `OAI.Erdos3.modeRemovalRadius`, `OAI.Erdos3.modeRemovalRadius_inv_le_exp`, `OAI.Erdos3.modeRemovalRadius_pos`, `OAI.Erdos3.modeRemovalRankThreshold`, `OAI.Erdos3.modeRemovalShrink`, `OAI.Erdos3.modeRemovalShrink_le_exp`, `OAI.Erdos3.modeRemovalShrink_move`, `OAI.Erdos3.modeRemovalShrink_one_le`, `OAI.Erdos3.modeRemovalSideThreshold`, `OAI.Erdos3.modeRemovalSideThreshold_bounds`, `OAI.Erdos3.modeRemovalSideThreshold_le_exp`, `OAI.Erdos3.modeRemovalTranslationConstant`, `OAI.Erdos3.modeRemovalTranslationConstant_nonneg`, `OAI.Erdos3.modeShrinkLog`, `OAI.Erdos3.modeShrinkLog_nonneg`, `OAI.Erdos3.modeSideLog`, `OAI.Erdos3.modeSideLog_nonneg`, `OAI.Erdos3.multiaffineBiasBudget_eq_inverse_power`, `OAI.Erdos3.multiaffineBiasBudget_le_exp`, `OAI.Erdos3.multiaffineBiasBudget_le_finite`, `OAI.Erdos3.multiaffineInverseConstant`, `OAI.Erdos3.multiaffineInverseExponent`, `OAI.Erdos3.multilinear_eq_first_order_of_two_vanish`, `OAI.Erdos3.norm_expect_zeroExtendFinset`, `OAI.Erdos3.norm_le_coordinateL2Norm`, `OAI.Erdos3.norm_prod_sub_prod_le_sum_error`, `OAI.Erdos3.norm_sum_subset_card_loss`, `OAI.Erdos3.normalizedAxisBasis`, `OAI.Erdos3.normalizedAxisBasis_apply`, `OAI.Erdos3.normalizedAxisBasis_coordinates`, `OAI.Erdos3.normalizedAxisBasis_coordinates_bound`, `OAI.Erdos3.normalizedAxisBasis_covolume`, `OAI.Erdos3.normalizedAxisBasis_covolume_lower`, `OAI.Erdos3.normalizedAxisBasis_covolume_ratio_bounds`, `OAI.Erdos3.normalizedAxisBasis_covolume_upper`, `OAI.Erdos3.normalizedAxisBasis_norm`, `OAI.Erdos3.normalizedAxisBasis_norm_bounds`, `OAI.Erdos3.normalizedAxisBasis_norm_product`, `OAI.Erdos3.normalizedAxisBasis_reciprocal_covolume`, `OAI.Erdos3.normalizedAxisBasis_synthesis_bound`, `OAI.Erdos3.normalizedJetColumn`, `OAI.Erdos3.normalizedJetMass`, `OAI.Erdos3.normalizedSiteCutoffBound`, `OAI.Erdos3.orderedGroupProduct`, `OAI.Erdos3.orderedGroupProduct_map`, `OAI.Erdos3.orderedGroupTailProduct`, `OAI.Erdos3.orderedGroupTailProduct_congr`, `OAI.Erdos3.orderedGroupTailProduct_step`, `OAI.Erdos3.orderedGroupTailProduct_terminal`, `OAI.Erdos3.orderedZpowProduct`, `OAI.Erdos3.orderedZpowProduct_map`, `OAI.Erdos3.orthonormal_basis_coordinate_abs_le`, `OAI.Erdos3.outside_cyclicWrapExceptional`, `OAI.Erdos3.overlap_weight_comparison`, `OAI.Erdos3.partitionedIdealRadius`, `OAI.Erdos3.partitionedIdealRadius_nonneg`, `OAI.Erdos3.physicalBoundaryBudget`, `OAI.Erdos3.physicalBoundaryNear`, `OAI.Erdos3.physicalBoxClassify`, `OAI.Erdos3.physicalMeshCrossing`, `OAI.Erdos3.pivotKernelCap`, `OAI.Erdos3.pivotKernelLip`, `OAI.Erdos3.polynomialGridCover`, `OAI.Erdos3.positiveCellParameter`, `OAI.Erdos3.powerSubgroup_index_le_of_ordered_generators`, `OAI.Erdos3.principalProfileSize`, `OAI.Erdos3.principalProfileSize_pos`, `OAI.Erdos3.product_denominator_le_budget`, `OAI.Erdos3.progression_endpoint_bounds`, `OAI.Erdos3.progression_slice_geometry`, `OAI.Erdos3.rationalGridMajorBox`, `OAI.Erdos3.rationalGridMajorSet`, `OAI.Erdos3.rationalInactiveForecast`, `OAI.Erdos3.rationalLieQuotientStructureHeight_le_exp`, `OAI.Erdos3.rationalOutputDensity`, `OAI.Erdos3.rationalOutputOrderTail`, `OAI.Erdos3.rationalQuotientSectionHeight_le_exp`, `OAI.Erdos3.realUniformMass`, `OAI.Erdos3.realUniformMass_apply_mem`, `OAI.Erdos3.realUniformMass_apply_not_mem`, `OAI.Erdos3.realUniformMass_ne_zero_iff`, `OAI.Erdos3.realUniformMass_nonneg`, `OAI.Erdos3.realZeroExtendFinset`, `OAI.Erdos3.residueBoxStrideValue`, `OAI.Erdos3.residueStepMatrix`, `OAI.Erdos3.restrictedDegreeSupports`, `OAI.Erdos3.row_normalization_abs_le`, `OAI.Erdos3.row_normalization_col_span`, `OAI.Erdos3.row_normalization_entry`, `OAI.Erdos3.row_normalization_submatrix`, `OAI.Erdos3.scalarCubeCutoffDerivativeNumerator`, `OAI.Erdos3.scalarCubeGridBoundaryConstant`, `OAI.Erdos3.scalarCubeGridHistogram`, `OAI.Erdos3.scalarCubeGridSet`, `OAI.Erdos3.scalarSpatialIndexAllowance`, `OAI.Erdos3.scalarSpatialInverseAllowance`, `OAI.Erdos3.scaled_basis_mem_coordinateGridModule`, `OAI.Erdos3.scaled_integer_minor_eq`, `OAI.Erdos3.scaled_integer_minor_natAbs_bound`, `OAI.Erdos3.scaled_integer_row_normalization_cast`, `OAI.Erdos3.selectedCoefficientEquiv`, `OAI.Erdos3.selectedCoefficientEquiv_apply`, `OAI.Erdos3.selectedCoefficientEquiv_lipschitz`, `OAI.Erdos3.selectedCoefficientEquiv_norm`, `OAI.Erdos3.selectedCoefficientMeasurableEquiv`, `OAI.Erdos3.selectedCoefficientProfile`, `OAI.Erdos3.selectedColumnEquiv`, `OAI.Erdos3.selectedDependentEquiv`, `OAI.Erdos3.selectedFreeFirstEquiv`, `OAI.Erdos3.selectedFullSpatialColumnEquiv`, `OAI.Erdos3.selectedIntegerCoefficientEquiv`, `OAI.Erdos3.selectedSpatialColumnEquiv`, `OAI.Erdos3.selectedSpatialFreeColumns`, `OAI.Erdos3.selectedSpatialPivot`, `OAI.Erdos3.selectedSplitCoefficients`, `OAI.Erdos3.shiftedAdditiveQuadruples`, `OAI.Erdos3.shiftedAdditiveQuadruples_card`, `OAI.Erdos3.shiftedAdditiveQuadruples_card_le_energy`, `OAI.Erdos3.shiftedSmoothCoefficientPMF`, `OAI.Erdos3.shiftedSmoothCoefficientPMF_apply`, `OAI.Erdos3.shiftedSmoothProductSamples_sum`, `OAI.Erdos3.shiftedSmoothSampleSum`, `OAI.Erdos3.shiftedSmoothSampleSum_error`, `OAI.Erdos3.shiftedSmoothSampleSum_pos`, `OAI.Erdos3.shiftedSmoothSamples_summable`, `OAI.Erdos3.shifted_power_self_mono`, `OAI.Erdos3.shortVectorLattice_covolume_le`, `OAI.Erdos3.shortVectorLattice_covolume_le_of_points`, `OAI.Erdos3.sigma_card_le_budget`, `OAI.Erdos3.smoothCoefficientPMF`, `OAI.Erdos3.smoothProductPMF`, `OAI.Erdos3.smoothProductSamples_sum`, `OAI.Erdos3.smoothProductSamples_sum_pos`, `OAI.Erdos3.smoothProductSamples_summable`, `OAI.Erdos3.smoothProfileSamples_summable`, `OAI.Erdos3.smoothSampleSum`, `OAI.Erdos3.smoothSampleSum_pos`, `OAI.Erdos3.smoothSplitProfile`, `OAI.Erdos3.smoothSplitProfile_join`, `OAI.Erdos3.smoothSplitProfile_range`, `OAI.Erdos3.smoothSplitProfile_zero_outside`, `OAI.Erdos3.smoothSplit_mass_pos`, `OAI.Erdos3.smoothSplit_weight_sum`, `OAI.Erdos3.sortedLayerCoordinateEquiv`, `OAI.Erdos3.sortedLayerCoordinateWeight`, `OAI.Erdos3.sortedLayerCoordinateWeight_le`, `OAI.Erdos3.sortedLayerCoordinateWeight_mono`, `OAI.Erdos3.sortedLayerCoordinateWeight_pos`, `OAI.Erdos3.spatialCoordinateArrayEquiv`, `OAI.Erdos3.splitFreeColumns`, `OAI.Erdos3.splitFreeProfile`, `OAI.Erdos3.splitInputProfile_smooth`, `OAI.Erdos3.submodule_basis_coordinate_height`, `OAI.Erdos3.subsetAlternatingTransform`, `OAI.Erdos3.sumElim_norm`, `OAI.Erdos3.sum_convolutionPower`, `OAI.Erdos3.sum_le_exp_card_add_sum`, `OAI.Erdos3.sum_massConvolution`, `OAI.Erdos3.sum_metricTentPartition`, `OAI.Erdos3.sum_realUniformMass`, `OAI.Erdos3.tailProfileSize`, `OAI.Erdos3.tailProfileSize_pos`, `OAI.Erdos3.uniformBlockSpectrumAccuracyConstant`, `OAI.Erdos3.uniformBlockSpectrumCardBudget`, `OAI.Erdos3.uniformBlockSpectrumCover`, `OAI.Erdos3.uniformCharacterDenominatorBound`, `OAI.Erdos3.uniformMass_translation_le_shell`, `OAI.Erdos3.uniformResidueSmallPeriodDensity`, `OAI.Erdos3.uniformScaledRetainedDenominatorBound`, `OAI.Erdos3.uniformScaledRetainedFrequencyBound`, `OAI.Erdos3.uniformSpectrumBlockCount`, `OAI.Erdos3.unitProfileCoefficientLog`, `OAI.Erdos3.unselectedColumnFintype`, `OAI.Erdos3.zeroExtendFinset`, `OAI.Erdos3.zeroExtendFinset_mul_left`, `OAI.Erdos3.zeroExtendFinset_mul_star`, `OAI.Erdos3.zeroExtendFinset_norm_le_one`, `OAI.Erdos3.zeroFixedPermutation`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_fiber_card_le`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_fin_sum_eq_geo`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_grouped`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_neg_sum_eq_conj`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_pair_sum_eq`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.fejer_pair_sum_eq_norm_sq`, `_private.Linear.CircleFejerKernel.0.OAI.Erdos3.CircleFourier.integral_character`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B006
import Definitions.Def_OAIErdos3B007
import Definitions.Def_OAIErdos3B008
import Definitions.Def_OAIErdos3B009

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientProfileCenter {J : Type*} (P : Finset J) (γ : ℝ) (j : J) : ℝ := by
  classical
  exact if j ∈ P then 3 * γ / 2 else 0

noncomputable def coefficientProfileWidth {J : Type*} (P : Finset J) (j₀ : J)
    (ρ γ ε : ℝ) (j : J) : ℝ := by
  classical
  exact if j = j₀ then ρ else if j ∈ P then γ / 2 else ε

theorem coefficientProfileWidth_pos {J : Type*} (P : Finset J) (j₀ : J)
    {ρ γ ε : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε) (j : J) :
    0 < coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> positivity

theorem coefficientProfile_budget {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {ρ γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε) :
    (∑ j, (|coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j)) ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  classical
  have hpoint (j : J) : |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j ≤
      (if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε := by
    by_cases hj : j = j₀
    · subst j
      simp [coefficientProfileCenter, coefficientProfileWidth, hj₀, hε]
    · by_cases hP : j ∈ P
      · have hpos : 0 ≤ 3 * γ / 2 := by positivity
        simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hP,
          ↓reduceIte, abs_of_nonneg hpos]
        linarith
      · simp [coefficientProfileCenter, coefficientProfileWidth, hj, hP]
  calc
    _ ≤ ∑ j, ((if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_mem]; ring

noncomputable def principalProfileSize (R : ℝ) (b : ℕ) : ℝ := R / (8 * ((b : ℝ) + 1))

noncomputable def tailProfileSize (R σ : ℝ) (m : ℕ) : ℝ := σ * R / (4 * ((m : ℝ) + 1))

theorem principalProfileSize_pos {R : ℝ} (hR : 0 < R) (b : ℕ) : 0 < principalProfileSize R b := by
  unfold principalProfileSize
  positivity

theorem tailProfileSize_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (m : ℕ) :
    0 < tailProfileSize R σ m := by
  unfold tailProfileSize
  positivity

theorem allocatedProfile_budget {R σ : ℝ} (hR : 0 ≤ R) (hσ1 : σ ≤ 1) (b m : ℕ) :
    R / 4 + 2 * principalProfileSize R b * b + tailProfileSize R σ m * m ≤ 3 * R / 4 := by
  have hb : (b : ℝ) / ((b : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hm : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hp : 2 * principalProfileSize R b * b ≤ R / 4 := by
    calc
      _ = (R / 4) * ((b : ℝ) / ((b : ℝ) + 1)) := by
        unfold principalProfileSize
        field_simp; ring
      _ ≤ (R / 4) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := mul_one _
  have ht : tailProfileSize R σ m * m ≤ R / 4 := by
    calc
      _ = σ * (R / 4) * ((m : ℝ) / ((m : ℝ) + 1)) := by
        unfold tailProfileSize
        field_simp
      _ ≤ 1 * (R / 4) * 1 := by gcongr
      _ = _ := by ring
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FiniteProductBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sigma_card_le_budget {α : Type*} [Fintype α] {κ : α → Type*}
    [∀ a, Fintype (κ a)] {p : ℝ} (hp : 0 ≤ p)
    (hα : (Fintype.card α : ℝ) ≤ p) (hκ : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p) :
    (Fintype.card (Σ a, κ a) : ℝ) ≤ p ^ 2 := by
  classical
  calc
    _ = ∑ a, (Fintype.card (κ a) : ℝ) := by rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _a : α, p := Finset.sum_le_sum (fun a _ => hκ a)
    _ = (Fintype.card α : ℝ) * p := by simp
    _ ≤ p * p := mul_le_mul_of_nonneg_right hα hp
    _ = p ^ 2 := by ring

theorem product_denominator_le_budget {α : Type*} [Fintype α] (m : α → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hm : ∀ a, (m a : ℝ) ≤ Real.exp p) :
    ((∏ a, m a : ℕ) : ℝ) ≤ Real.exp (p ^ 2) := by
  classical
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _a : α, Real.exp p := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun index _ => hm index)
    _ = Real.exp ((Fintype.card α : ℝ) * p) := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanWeightBudget (h : D → ℕ) (C : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : ℝ :=
  ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
    ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) +
    (Fintype.card (BlockParameter (B d) (Fin (h d)) α) : ℝ) * ((A : ℝ) / κ d *
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DenseProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation_density (e : ℕ)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  obtain ⟨hB, hBη, _⟩ := reciprocal_density_ceil hη hη1
  have hKB := denseProductBudget_ceil_le e hη hη1
  have hKN : ∀ i, denseProductBudget e ⌈1/η⌉₊ ≤ N i := by
    intro i
    exact_mod_cast hKB.trans (hN i)
  have hKp : (0 : ℝ) < denseProductBudget e ⌈1/η⌉₊ := by
    exact_mod_cast denseProductBudget_pos e ⌈1/η⌉₊ hB
  have hsmall' : ε ≤ 1/(denseProductBudget e ⌈1/η⌉₊ : ℝ) :=
    hsmall.trans (one_div_le_one_div_of_le hKp hKB)
  obtain ⟨q, hq, hqK, hnear⟩ := dense_product_approximation e ⌈1/η⌉₊ hB
    v hv N hKN hcard hbound hε hsmall' (hBη.trans hdensity)
  refine ⟨q, hq, (Nat.cast_le.mpr hqK).trans hKB, nearInteger_mono hnear ?_⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hε)
    (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (N i)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockSubsetCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

def blockSubsetUnion (f : σ → Finset ι) : Finset ι := Finset.univ.biUnion f

omit [DecidableEq σ] in
theorem blockSubsetUnion_subset (f : σ → Finset ι) (S : Finset ι)
    (h : ∀ i, f i ⊆ S) : blockSubsetUnion f ⊆ S := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact h i hi

theorem blockSubsetUnion_filter (π : ι → σ) (f : σ → Finset ι)
    (h : ∀ i, ∀ x ∈ f i, π x = i) (i : σ) :
    (blockSubsetUnion f).filter (fun x => π x = i) = f i := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    have hji : j = i := (h j x hj).symm.trans hxi
    exact hji ▸ hj
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩, h i x hx⟩

theorem blockSubsetUnion_filters (π : ι → σ) (S : Finset ι) :
    blockSubsetUnion (fun i => S.filter fun x => π x = i) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hi).1
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨π x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def blockSubsetEquiv (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} ≃
      (∀ i, {T : Finset ι // T ∈ (S.filter fun j => π j = i).powersetCard (a i)}) where
  toFun T i := ⟨T.val.filter (fun j => π j = i), Finset.mem_powersetCard.mpr ⟨by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨T.property.1 (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩,
    T.property.2 i⟩⟩
  invFun f := ⟨blockSubsetUnion (fun i => (f i).val), by
    have hf : ∀ i, (f i).val ⊆ S.filter (fun j => π j = i) :=
      fun i => (Finset.mem_powersetCard.mp (f i).property).1
    refine ⟨blockSubsetUnion_subset _ S (fun i j hj => (Finset.mem_filter.mp (hf i hj)).1), ?_⟩
    intro i
    rw [blockSubsetUnion_filter π _ (fun i j hj => (Finset.mem_filter.mp (hf i hj)).2)]
    exact (Finset.mem_powersetCard.mp (f i).property).2⟩
  left_inv T := Subtype.ext (blockSubsetUnion_filters π T.val)
  right_inv f := by
    funext i
    apply Subtype.ext
    exact blockSubsetUnion_filter π _
      (fun i j hj => (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (f i).property).1 hj)).2) i

theorem card_blockSubsets [Fintype ι] (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    Fintype.card {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} =
      ∏ i, ((S.filter fun j => π j = i).card).choose (a i) := by
  classical
  rw [Fintype.card_congr (blockSubsetEquiv π S a), Fintype.card_pi]
  simp only [Fintype.card_coe, Finset.card_powersetCard]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPairAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

structure SlicedProductBlock (ι : Type*) where
  coefficient : ℝ
  lower : ι → ℝ
  width : ι → ℝ
  lastLower : ℝ
  lastWidth : ℝ

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

structure Admissible (B : SlicedProductBlock ι) : Prop where
  coefficient_ne_zero : B.coefficient ≠ 0
  lower_nonneg : ∀ i, 0 ≤ B.lower i
  width_pos : ∀ i, 0 < B.width i
  lastWidth_pos : 0 < B.lastWidth

noncomputable def prefixProduct (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  ∏ i, (B.lower i + B.width i * x i)

noncomputable def value (B : SlicedProductBlock ι) (x : ι → ℝ) (u : ℝ) : ℝ :=
  B.coefficient * B.prefixProduct x * (B.lastLower + B.lastWidth * u)

noncomputable def slope (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastWidth * B.prefixProduct x

noncomputable def base (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastLower * B.prefixProduct x

noncomputable def volumeScale (B : SlicedProductBlock ι) : ℝ :=
  |B.coefficient| * B.lastWidth * ∏ i, B.width i

theorem volumeScale_pos {B : SlicedProductBlock ι} (hB : B.Admissible) : 0 < B.volumeScale :=
  mul_pos (mul_pos (abs_pos.mpr hB.coefficient_ne_zero) hB.lastWidth_pos)
    (Finset.prod_pos (fun i _ => hB.width_pos i))

end SlicedProductBlock

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairScale (A B : SlicedProductBlock ι) : ℝ := min A.volumeScale B.volumeScale

noncomputable def pairWidth (A B : SlicedProductBlock ι) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max |A.slope p.1| |B.slope p.2|

theorem pairScale_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairScale A B := lt_min (volumeScale_pos hA) (volumeScale_pos hB)

noncomputable def pairCap (A B : SlicedProductBlock ι) : ℝ :=
  (pairScale A B)⁻¹ * 4 ^ Fintype.card ι

theorem pairCap_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairCap A B := mul_pos (inv_pos.mpr (pairScale_pos hA hB)) (by positivity)

end Erdos3.SlicedProductBlock

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

abbrev UnselectedColumn {I J : Type*} (s : I ↪ J) := {j : J // j ∉ Set.range s}

noncomputable instance unselectedColumnFintype {I J : Type*} [Fintype J] (s : I ↪ J) :
    Fintype (UnselectedColumn s) := Fintype.ofFinite _

noncomputable def selectedColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) : I ⊕ UnselectedColumn s ≃ J := by
  classical
  exact (Equiv.sumCongr s.toEquivRange (Equiv.refl (UnselectedColumn s))).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range s))

noncomputable def selectedSpatialColumnEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    (Unit ⊕ I) ⊕ UnselectedColumn s ≃ Unit ⊕ J :=
  (Equiv.sumAssoc Unit I (UnselectedColumn s)).trans
    (Equiv.sumCongr (Equiv.refl Unit) (selectedColumnEquiv s))

def selectedSpatialPivot {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (Unit ⊕ I) R :=
  rootDifferenceMatrix (fun i => root (s i)) (D.submatrix id s)

def selectedSpatialFreeColumns {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (UnselectedColumn s) R :=
  Matrix.of (fun i j => Sum.elim (fun _ : Unit => root j.val) (fun i => D i j.val) i)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

noncomputable def splitFreeColumns (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) : (J ⊕ N → ℝ) →L[ℝ] (I → ℝ) :=
  B.comp (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (.inl j)) +
    C.comp (ContinuousLinearMap.pi fun n => ContinuousLinearMap.proj (.inr n))

noncomputable def splitFreeProfile (f : (J → ℝ) × (I → ℝ) → ℝ)
    (g : (N → ℝ) → ℝ) (p : (J ⊕ N → ℝ) × (I → ℝ)) : ℝ :=
  f ((fun j => p.1 (.inl j)), p.2) * g (fun n => p.1 (.inr n))

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothSplitProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

theorem smoothSplitProfile_join (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    smoothSplitProfile J I p = smoothProductProfile (J ⊕ I) (Sum.elim p.1 p.2) :=
  (smoothProductProfile_sum J I p.1 p.2).symm

theorem smoothSplitProfile_range (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    0 ≤ smoothSplitProfile J I p ∧ smoothSplitProfile J I p ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_range _ _

theorem sumElim_norm {J I : Type*} [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖Sum.elim p.1 p.2‖ = ‖p‖ :=
  (splitCoordinates_norm (Sum.elim p.1 p.2)).symm

theorem smoothSplitProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : smoothSplitProfile J I p = 0 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_zero_outside _ _ (by rwa [sumElim_norm])

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedFreeFirstEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    UnselectedColumn s ⊕ I ≃ J :=
  (Equiv.sumComm _ _).trans (selectedColumnEquiv s)

noncomputable def selectedCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (R : Type*) : (UnselectedColumn s → R) × (I → R) ≃ (J → R) :=
  (Equiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => R)).symm.trans
    (Equiv.arrowCongr (selectedFreeFirstEquiv s) (Equiv.refl R))

theorem selectedCoefficientEquiv_apply {I J R : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s → R) × (I → R)) (j : J) :
    selectedCoefficientEquiv s R p j =
      Sum.elim p.1 p.2 ((selectedFreeFirstEquiv s).symm j) := rfl

theorem selectedCoefficientEquiv_norm {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (p : (UnselectedColumn s → ℝ) × (I → ℝ)) :
    ‖selectedCoefficientEquiv s ℝ p‖ = ‖p‖ := by
  change ‖(Sum.elim p.1 p.2) ∘ (selectedFreeFirstEquiv s).symm‖ = _
  exact ((selectedFreeFirstEquiv s).symm.surjective.pi_norm_comp (Sum.elim p.1 p.2)).trans
    (sumElim_norm p)

theorem selectedCoefficientEquiv_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : LipschitzWith 1 (selectedCoefficientEquiv s ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have he : selectedCoefficientEquiv s ℝ p - selectedCoefficientEquiv s ℝ q =
      selectedCoefficientEquiv s ℝ (p - q) := by
    funext j
    simp only [Pi.sub_apply, selectedCoefficientEquiv_apply]
    cases (selectedFreeFirstEquiv s).symm j <;> rfl
  rw [he, selectedCoefficientEquiv_norm]

noncomputable def selectedCoefficientProfile {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) : (UnselectedColumn s → ℝ) × (I → ℝ) → ℝ :=
  f ∘ selectedCoefficientEquiv s ℝ

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def smoothSampleSum (S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile ((k : ℝ) / S)

theorem smoothProfileSamples_summable {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile ((k : ℝ) / S)) := by
  have h : Summable (sampledWeight smoothProbabilityProfile 0 S) :=
    (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
      (a := 0) hS smoothProbabilityProfile_zero_outside)).summable
  change Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - 0) / S)) at h
  simpa only [sub_zero] using h

theorem smoothSampleSum_pos {S : ℝ} (hS : 0 < S) : 0 < smoothSampleSum S := by
  have h := (smoothProfileSamples_summable hS).le_tsum 0
    (fun k _ => (smoothProbabilityProfile_range _).1)
  simp only [Int.cast_zero, zero_div] at h
  exact smoothProbabilityProfile_pos_zero.trans_le h

noncomputable def smoothCoefficientPMF (S : ℝ) (hS : 0 < S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile ((k : ℝ) / S))
    (fun _ => (smoothProbabilityProfile_range _).1)
    (smoothProfileSamples_summable hS) (smoothSampleSum_pos hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductSamples_summable {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Summable (fun z : I → ℤ => smoothProductProfile I (fun i => (z i : ℝ) / S i)) := by
  have h := rectangularWeight_summable (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change Summable (fun z : I → ℤ =>
    smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i)) at h
  simpa only [sub_zero] using h

theorem smoothProductSamples_sum {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i)) =
      ∏ i, smoothSampleSum (S i) := by
  classical
  have h := rectangularWeightSum_eq_tsum (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) (fun _ => 0) S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i) at h
  simp only [sub_zero] at h
  rw [← h]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, sub_zero, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices 0 (S i) 1)
    (fun i k => smoothProbabilityProfile ((k : ℝ) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := 0) (hS i)
    smoothProbabilityProfile_zero_outside
  simpa only [sampledWeightSum, sampledWeight, sub_zero, smoothSampleSum] using hi

theorem smoothProductSamples_sum_pos {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    0 < ∑' z : I → ℤ, smoothProductProfile I (fun i => (z i : ℝ) / S i) := by
  rw [smoothProductSamples_sum S hS]
  exact Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i))

noncomputable def smoothProductPMF {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) : PMF (I → ℤ) :=
  realWeightPMF (fun z => smoothProductProfile I (fun i => (z i : ℝ) / S i))
    (fun _ => (smoothProductProfile_range I _).1)
    (smoothProductSamples_summable S hS) (smoothProductSamples_sum_pos S hS)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def shiftedSmoothSampleSum (a S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S)

theorem shiftedSmoothSamples_summable (a : ℝ) {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S)) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
    (a := a) hS smoothProbabilityProfile_zero_outside)).summable

theorem shiftedSmoothSampleSum_error (a : ℝ) {S : ℝ} (hS : 1 ≤ S) :
    |shiftedSmoothSampleSum a S / S - 1| ≤ 4 * (probabilityProfileLipschitz : ℝ) / S := by
  have he := sampledWeightSum_error smoothProbabilityProfile smoothProbabilityProfile_lipschitz
    (a := a) zero_le_one hS smoothProbabilityProfile_zero_outside
  rw [sampledWeightSum_eq_tsum _ (zero_lt_one.trans_le hS) smoothProbabilityProfile_zero_outside] at he
  simpa only [shiftedSmoothSampleSum, smoothProbabilityProfile_integral,
    show (2 : ℝ) * 1 + 2 = 4 by norm_num] using he

theorem shiftedSmoothSampleSum_pos (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < shiftedSmoothSampleSum a S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ (zero_lt_one.trans_le hS1)).mpr (by linarith)
  have hlo := (abs_le.mp (he.trans hsmall)).1
  have hpos : 0 < shiftedSmoothSampleSum a S / S := by linarith
  rcases div_pos_iff.mp hpos with h | h
  · exact h.1
  · linarith [h.2]

noncomputable def shiftedSmoothCoefficientPMF (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (fun _ => (smoothProbabilityProfile_range _).1) (shiftedSmoothSamples_summable a hS) hZ

theorem shiftedSmoothCoefficientPMF_apply (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S hS hZ k).toReal =
      smoothProbabilityProfile (((k : ℝ) - a) / S) / shiftedSmoothSampleSum a S :=
  realWeightPMF_apply _ _ _ _ k

theorem shiftedSmoothProductSamples_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    (∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i)) =
      ∏ i, shiftedSmoothSampleSum (a i) (S i) := by
  classical
  have he := rectangularWeightSum_eq_tsum (smoothProductProfile I) a S hS
    (smoothProductProfile_zero_outside I)
  change rectangularWeightSum (smoothProductProfile I) a S 1 =
    ∑' z : I → ℤ, smoothProductProfile I (fun i => ((z i : ℝ) - a i) / S i) at he
  rw [← he]
  simp only [rectangularWeightSum, rectangularWeightIndices, rectangularWeight,
    rectangularLatticePoint, smoothProductProfile]
  rw [← Finset.prod_univ_sum (fun i => sampledWeightIndices (a i) (S i) 1)
    (fun i k => smoothProbabilityProfile (((k : ℝ) - a i) / S i))]
  apply Finset.prod_congr rfl
  intro i _
  have hi := sampledWeightSum_eq_tsum smoothProbabilityProfile (a := a i) (hS i)
    smoothProbabilityProfile_zero_outside
  exact hi

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

theorem splitInputProfile_smooth (J I : Type*) [Fintype J] [Fintype I] :
    splitInputProfile (smoothSplitProfile J I) = smoothProductProfile (J ⊕ I) := by
  funext x
  unfold splitInputProfile
  rw [smoothSplitProfile_join]
  congr 1
  funext k
  cases k <;> rfl

theorem smoothSplit_weight_sum {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    scaledInputWeightSum (smoothSplitProfile J I) S T =
      (∏ i, smoothSampleSum (S i)) * (∏ j, smoothSampleSum (T j)) := by
  have hST : ∀ k, 0 < Sum.elim T S k := by
    intro k
    cases k with
    | inl j => exact hT j
    | inr i => exact hS i
  unfold scaledInputWeightSum
  rw [← splitInputProfile_sample_sum, splitInputProfile_smooth,
    smoothProductSamples_sum _ hST]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_comm]

theorem smoothSplit_mass_pos {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    0 < scaledInputMass (smoothSplitProfile J I) S T := by
  rw [scaledInputMass, smoothSplit_weight_sum S T hS hT]
  exact div_pos
    (mul_pos (Finset.prod_pos (fun i _ => smoothSampleSum_pos (hS i)))
      (Finset.prod_pos (fun j _ => smoothSampleSum_pos (hT j))))
    (mul_pos (Finset.prod_pos (fun i _ => hS i)) (Finset.prod_pos (fun j _ => hT j)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

noncomputable def finiteSetLp (s : Finset ι) (f : ι → ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (𝔼 i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ))

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def convolution (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f x * g (t - x)) / L.card

noncomputable def correlation (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f (x + t) * g x) / L.card

noncomputable def sumMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s + t) ^ j

noncomputable def differenceMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s - t) ^ j

noncomputable def momentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s - v i)

noncomputable def plusMomentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s + v i)

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def momentAmplificationFactor (delta : ℝ) : ℕ := ⌈2 / delta⌉₊ + 1

noncomputable def momentAmplificationGain (delta : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / (momentAmplificationFactor delta : ℝ)) - 1

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def sumLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 + x.2)) p

noncomputable def differenceLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 - x.2)) p

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def frozenTupleCoordinate {Z P : Type*} (z : Z → ℝ) : Z ⊕ P → MvPolynomial P ℝ
  | .inl j => MvPolynomial.C (z j)
  | .inr i => MvPolynomial.X i

noncomputable def normalizedJetColumn {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanJetColumnPolynomial e (fun k r => frozenTupleCoordinate z (input k r)) s

noncomputable def normalizedJetMass (α : Type*) [Fintype α] (d : ℕ) : ℝ≥0 :=
  2^Fintype.card α * (Fintype.card α+1)^d

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotKernelAllowances
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def pivotKernelCap {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) : ℝ≥0 :=
  ⟨inverseJacobian A, (inverseJacobian_pos A).le⟩ * H * (2*R)^Fintype.card J

noncomputable def pivotKernelLip {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) : ℝ≥0 :=
  pivotKernelCap J A R K * ‖A.symm.toContinuousLinearMap‖₊

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI

namespace Erdos3

open scoped Matrix

noncomputable def coefficientWeight {J : Type*} (f : (J → ℝ) → ℝ)
    (S : J → ℝ) (z : J → ℤ) : ℝ := f (fun j => (z j : ℝ) / S j)

noncomputable def coefficientWeightSum {J : Type*} (f : (J → ℝ) → ℝ) (S : J → ℝ) : ℝ :=
  ∑' z : J → ℤ, coefficientWeight f S z

theorem coefficientWeight_summable {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Summable (coefficientWeight f S) := by
  convert rectangularWeight_summable f (fun _ => 0) S hS hsupport using 1
  funext z
  change f (fun j => (z j : ℝ) / S j) = f (rectangularLatticePoint (fun _ => 0) S z)
  congr 1
  funext j
  simp only [rectangularLatticePoint, sub_zero]

noncomputable def coefficientPMF {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) :
    PMF (J → ℤ) :=
  realWeightPMF (coefficientWeight f S) (fun _ => hf _)
    (coefficientWeight_summable f S hS hsupport) hZ

noncomputable def coefficientImagePMF {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) : PMF (I → ℤ) :=
  (coefficientPMF f hf S hS hsupport hZ).map (fun z => A *ᵥ z)

noncomputable def selectedIntegerCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) : (I → ℤ) × (UnselectedColumn s → ℤ) ≃ (J → ℤ) :=
  (Equiv.prodComm _ _).trans (selectedCoefficientEquiv s ℤ)

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def spatialCoordinateArrayEquiv (K X : Type*) : (K × X → ℤ) ≃ (X → K → ℤ) where
  toFun z x k := z (k, x)
  invFun z p := z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

noncomputable def uniformResidueSmallPeriodDensity {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℤ) (d period : ℕ) [NeZero d]
    (r : I → ZMod period) : ℝ :=
  (d : ℝ) ^ Fintype.card I *
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z))
        (fun i => ((r i).val : ZMod d))).toReal

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LayerRemovalBudgets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteLayerBiasBudget (m : ℕ) (ζ : ℝ) : ℝ :=
  1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ

theorem finiteLayerBiasBudget_one_le (m : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    1 ≤ finiteLayerBiasBudget m ζ := by
  unfold finiteLayerBiasBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (multiaffineBiasBudget_pos i.val hζ).le))

theorem multiaffineBiasBudget_le_finite {m : ℕ} (i : Fin m) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget i.val ζ ≤ finiteLayerBiasBudget m ζ := by
  apply le_trans (Finset.single_le_sum (fun j _ => (multiaffineBiasBudget_pos j.val hζ).le)
    (Finset.mem_univ i))
  exact le_add_of_nonneg_left zero_le_one

noncomputable def layerRemovalRankBudget (m d : ℕ) (C D B A S : ℝ) : ℝ :=
  1 + ∑ i : Fin m,
    (((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
      (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) +
      (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B))

theorem layerRemovalRankBudget_bounds {m : ℕ} (i : Fin m) (d : ℕ)
    {C D B A S : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hA : 0 ≤ A) (hS : 0 ≤ S) :
    ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤ layerRemovalRankBudget m d C D B A S := by
  let cost (j : Fin m) :=
    ((j.val + 1).factorial : ℝ) * (C * D ^ (j.val + 1)) +
      (B * S ^ (j.val + 1)) ^ (d ^ (j.val + 1)) +
      (d : ℝ) ^ (j.val + 1) * (A ^ (j.val + 1) * B)
  have hcost j : 0 ≤ cost j := by dsimp [cost]; positivity
  have hs : cost i ≤ ∑ j : Fin m, cost j :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have ht : cost i ≤ layerRemovalRankBudget m d C D B A S := by
    exact hs.trans (le_add_of_nonneg_left zero_le_one)
  have hrow : 0 ≤ ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) := by positivity
  have hden : 0 ≤ (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) := by positivity
  have hcoeff : 0 ≤ (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) := by positivity
  dsimp [cost] at ht
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModeRemovalThresholds
namespace OAI

section

namespace Erdos3

noncomputable def modeRemovalTranslationConstant (d : ℕ) : ℝ :=
  4 * (3 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

noncomputable def modeRemovalMeshConstant (d : ℕ) : ℝ :=
  (4 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

theorem modeRemovalTranslationConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalTranslationConstant d := by
  unfold modeRemovalTranslationConstant
  positivity

theorem modeRemovalMeshConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalMeshConstant d := by
  unfold modeRemovalMeshConstant
  positivity

noncomputable def modeRemovalBeta (ε : ℝ) : ℝ := min (1 / 2) (ε / 2)

theorem modeRemovalBeta_pos {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBeta ε := by
  exact lt_min (by norm_num) (by positivity)

theorem modeRemovalBeta_le_one (ε : ℝ) : modeRemovalBeta ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

noncomputable def modeRemovalRadius (d : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * (modeRemovalTranslationConstant d + 1))

theorem modeRemovalRadius_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalRadius d ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  positivity

theorem modeRemovalError_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d ε + modeRemovalBeta ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  have hr := (modeRemovalRadius_pos d hε).le
  have hd : modeRemovalTranslationConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalTranslationConstant d + 1) * modeRemovalRadius d ε = ε / 2 := by
    unfold modeRemovalRadius
    field_simp
  have hb : modeRemovalBeta ε ≤ ε / 2 := min_le_right _ _
  nlinarith

noncomputable def modeRemovalBias (m : ℕ) (ε : ℝ) : ℝ := modeRemovalBeta ε ^ (2 ^ m)

theorem modeRemovalBias_pos (m : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBias m ε :=
  pow_pos (modeRemovalBeta_pos hε) _

theorem modeRemovalBias_le {m : ℕ} (i : Fin m) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalBias m ε ≤ modeRemovalBeta ε ^ (2 ^ (i.val + 1)) := by
  apply pow_le_pow_of_le_one (modeRemovalBeta_pos hε).le (modeRemovalBeta_le_one ε)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.succ_le_of_lt i.isLt)

noncomputable def modeRemovalMesh (d : ℕ) : ℝ := 1 / (2 * (modeRemovalMeshConstant d + 1))

theorem modeRemovalMesh_pos (d : ℕ) : 0 < modeRemovalMesh d := by
  have hc := modeRemovalMeshConstant_nonneg d
  unfold modeRemovalMesh
  positivity

theorem modeRemovalMesh_le_one (d : ℕ) : modeRemovalMesh d ≤ 1 := by
  have hc := modeRemovalMeshConstant_nonneg d
  apply (div_le_iff₀ (by positivity : 0 < 2 * (modeRemovalMeshConstant d + 1))).mpr
  linarith

theorem modeRemovalMesh_small (d : ℕ) :
    modeRemovalMeshConstant d * modeRemovalMesh d ≤ 1 / 2 := by
  have hc := modeRemovalMeshConstant_nonneg d
  have hd : modeRemovalMeshConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalMeshConstant d + 1) * modeRemovalMesh d = 1 / 2 := by
    unfold modeRemovalMesh
    field_simp
  nlinarith [modeRemovalMesh_pos d]

theorem modeRemovalMesh_of_width (d : ℕ) {V : ℝ} (hV : 0 < V)
    (hwidth : 1 / modeRemovalMesh d ≤ V) : 1 ≤ V ∧ 1 / V ≤ modeRemovalMesh d := by
  have hm := (div_le_iff₀ (modeRemovalMesh_pos d)).mp hwidth
  have hmul := mul_le_mul_of_nonneg_left (modeRemovalMesh_le_one d) hV.le
  constructor
  · nlinarith
  · apply (div_le_iff₀ hV).mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def modeRemovalShrink (m d : ℕ) (D ρ ε : ℝ) : ℝ :=
  1 + (m : ℝ) * D / (modeRemovalRadius d ε * ρ)

theorem modeRemovalShrink_one_le (m d : ℕ) {D ρ ε : ℝ}
    (hD : 0 ≤ D) (hρ : 0 < ρ) (hε : 0 < ε) : 1 ≤ modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  unfold modeRemovalShrink
  exact le_add_of_nonneg_right (by positivity)

theorem modeRemovalShrink_move (m d : ℕ) {D ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    (m : ℝ) * D ≤ modeRemovalRadius d ε * ρ * modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  have hd : modeRemovalRadius d ε * ρ ≠ 0 := ne_of_gt (mul_pos hr hρ)
  unfold modeRemovalShrink
  rw [mul_add, mul_one, mul_div_cancel₀ _ hd]
  linarith [mul_pos hr hρ]

noncomputable def modeRemovalSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) +
    1 / (ρ * modeRemovalMesh d) + 1

noncomputable def modeRemovalRankThreshold (m n d : ℕ) (C D S ρ ε : ℝ) : ℝ :=
  layerRemovalRankBudget m n C D (finiteLayerBiasBudget m (modeRemovalBias m ε))
    (2 * modeRemovalShrink m d D ρ ε) S

theorem modeRemovalSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < modeRemovalSideThreshold m d D S ρ ε ∧
    S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      modeRemovalSideThreshold m d D S ρ ε ∧
    1 / modeRemovalMesh d ≤ ρ * modeRemovalSideThreshold m d D S ρ ε := by
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hδ := modeRemovalMesh_pos d
  have ha : 0 ≤ S * modeRemovalShrink m d D ρ ε *
      (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) := by positivity
  have hb : 0 < 1 / (ρ * modeRemovalMesh d) := by positivity
  have he : ρ * (1 / (ρ * modeRemovalMesh d)) = 1 / modeRemovalMesh d := by
    field_simp
  unfold modeRemovalSideThreshold
  refine ⟨by positivity, by linarith, ?_⟩
  nlinarith [mul_nonneg hρ.le ha]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeAmplitudeErrorBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def modeAmplitudeAccuracy (L ε : ℝ) : ℝ := ε / (2 * (L + 1))

theorem modeAmplitudeAccuracy_pos {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < modeAmplitudeAccuracy L ε := by
  unfold modeAmplitudeAccuracy
  positivity

theorem modeRemovalRadius_le_error (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalRadius d ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem modeAmplitudeError_bound (d : ℕ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      L * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      modeRemovalBeta (modeAmplitudeAccuracy L ε) ≤ ε := by
  have he := modeAmplitudeAccuracy_pos hL hε
  have hbase := modeRemovalError_bound d he
  have hr := modeRemovalRadius_le_error d he
  have hmul := mul_le_mul_of_nonneg_left hr hL
  have hidentity : (L + 1) * modeAmplitudeAccuracy L ε = ε / 2 := by
    unfold modeAmplitudeAccuracy
    field_simp
  nlinarith

theorem modeAmplitudeAccuracy_inv_le_exp {P L ε : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / modeAmplitudeAccuracy L ε ≤ Real.exp (2 * P + 2) := by
  have hden : 0 < L + 1 := by linarith
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg 1)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hinv : 1 / modeAmplitudeAccuracy L ε = 2 * (L + 1) * (1 / ε) := by
    unfold modeAmplitudeAccuracy
    field_simp
  rw [hinv]
  calc
    _ ≤ 4 * Real.exp P * Real.exp P := by
      have hfactor : 2 * (L + 1) ≤ 4 * Real.exp P := by linarith
      exact mul_le_mul hfactor hεP (by positivity) (by positivity)
    _ ≤ Real.exp 2 * Real.exp P * Real.exp P := by gcongr
    _ = Real.exp (2 * P + 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem add_le_exp_add_one {x y P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hx : x ≤ Real.exp P) (hy : y ≤ Real.exp Q) : x+y ≤ Real.exp (P+Q+1) := by
  have hx' := hx.trans (Real.exp_le_exp.mpr (show P ≤ P+Q by linarith))
  have hy' := hy.trans (Real.exp_le_exp.mpr (show Q ≤ P+Q by linarith))
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp (P+Q) := by linarith
    _ ≤ Real.exp 1*Real.exp (P+Q) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem sum_le_exp_card_add_sum {I : Type*} [Fintype I]
    (x P : I → ℝ) (hP : ∀ i, 0 ≤ P i) (hx : ∀ i, x i ≤ Real.exp (P i)) :
    (∑ i, x i) ≤ Real.exp ((Fintype.card I : ℝ)+∑ i, P i) := by
  have hi (i) : P i ≤ ∑ j, P j := Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)
  have hcard : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  calc
    _ ≤ ∑ _i : I, Real.exp (∑ j, P j) :=
      Finset.sum_le_sum (fun i _ => (hx i).trans (Real.exp_le_exp.mpr (hi i)))
    _ = (Fintype.card I : ℝ)*Real.exp (∑ j, P j) := by simp
    _ ≤ Real.exp (Fintype.card I)*Real.exp (∑ j, P j) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem coe_toNNReal_le_exp {x P : ℝ} (hx : x ≤ Real.exp P) :
    (Real.toNNReal x : ℝ) ≤ Real.exp P := by
  rw [Real.coe_toNNReal']
  exact max_le hx (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem algebraicMajor_mass_le_exp (d : ℕ) {p massF₀ massE massV Cbase : ℝ}
    (hp : 0 ≤ p) (_hF₀ : 0 ≤ massF₀) (_hE : 0 ≤ massE)
    (_hV : 0 ≤ massV) (hC : 0 ≤ Cbase)
    (hF₀p : massF₀ ≤ Real.exp p) (hEp : massE ≤ Real.exp p)
    (hVp : massV ≤ Real.exp p) (hCp : Cbase ≤ Real.exp p) :
    massF₀ + (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (((d : ℝ) + 3) * (p + 2)) := by
  have hsum : massE + massV ≤ Real.exp (2*p + 1) := by
    simpa only [two_mul] using add_le_exp_add_one hp hp hEp hVp
  have hbase := one_add_le_exp_succ hp hCp
  have hterm : (massE + massV) * (1 + Cbase)^d ≤
      Real.exp (2*p + 1 + (d : ℝ)*(p + 1)) := by
    calc
      _ ≤ Real.exp (2*p + 1) * (Real.exp (p + 1))^d := by
        exact mul_le_mul hsum
          (pow_le_pow_left₀ (by positivity) hbase d) (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have htotal := add_le_exp_add_one hp
    (by positivity : 0 ≤ 2*p + 1 + (d : ℝ)*(p + 1)) hF₀p hterm
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem algebraicMajor_denominator_le_exp (d qV qNat : ℕ) {p : ℝ}
    (hqV : (qV : ℝ) ≤ Real.exp p) (hqNat : (qNat : ℝ) ≤ Real.exp p) :
    (((qV*qNat)^(d+1) : ℕ) : ℝ) ≤
      Real.exp (2*((d : ℝ)+1)*p) := by
  have hprod : ((qV*qNat : ℕ) : ℝ) ≤ Real.exp (2*p) := by
    rw [Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hqV hqNat (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ = (((qV*qNat : ℕ) : ℝ))^(d+1) := by rw [Nat.cast_pow]
    _ ≤ (Real.exp (2*p))^(d+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def modeProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊

noncomputable def modeProfileLog (P : ℝ) : ℝ := 5 * P + (modeProfileBound : ℝ) + 4

theorem modeProfileLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeProfileLog P := by
  unfold modeProfileLog
  positivity

theorem modeRemovalConstants_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    modeRemovalTranslationConstant d ≤ Real.exp (modeProfileLog P) ∧
      modeRemovalMeshConstant d ≤ Real.exp (modeProfileLog P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (d : ℝ) ≤ Real.exp P := hd.trans (by linarith [Real.add_one_le_exp P])
  have hL : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (modeProfileBound : ℝ) := by
    have hc : (probabilityProfileLipschitz : ℝ) ≤ modeProfileBound := Nat.le_ceil _
    exact hc.trans (by linarith [Real.add_one_le_exp (modeProfileBound : ℝ)])
  constructor
  · unfold modeRemovalTranslationConstant
    calc
      _ ≤ Real.exp 4 * (Real.exp 3) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 + 3 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; nlinarith)
  · unfold modeRemovalMeshConstant
    calc
      _ ≤ (Real.exp 4) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; linarith)

theorem modeRemovalMesh_inv_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    1 / modeRemovalMesh d ≤ Real.exp (modeProfileLog P + 3) := by
  have hc0 := modeRemovalMeshConstant_nonneg d
  have hc : modeRemovalMeshConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).2
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  simp only [modeRemovalMesh, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (modeProfileLog P + 1) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem modeRemovalRadius_inv_le_exp (d : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalRadius d ε ≤ Real.exp (modeProfileLog P + P + 3) := by
  have hc0 := modeRemovalTranslationConstant_nonneg d
  have hc : modeRemovalTranslationConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).1
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have he : 1 / modeRemovalRadius d ε = 2 * (modeRemovalTranslationConstant d + 1) * (1 / ε) := by
    rw [modeRemovalRadius, one_div, inv_div]
    simp only [div_eq_mul_inv, one_mul]
  rw [he]
  calc
    _ ≤ (Real.exp 2 * Real.exp (modeProfileLog P + 1)) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def multiaffineInverseConstant (n : ℕ) : ℕ :=
  denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n

def multiaffineInverseExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

def finiteLayerInverseConstant (m : ℕ) : ℕ := m + 1 + ∑ i : Fin m, multiaffineInverseConstant i.val

def finiteLayerInverseExponent (m : ℕ) : ℕ := ∑ i : Fin m, multiaffineInverseExponent i.val

def finiteLayerInverseLog (m : ℕ) (Z : ℝ) : ℝ :=
  (finiteLayerInverseConstant m : ℝ) + (finiteLayerInverseExponent m : ℝ) * Z

theorem multiaffineBiasBudget_eq_inverse_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      (multiaffineInverseConstant n : ℝ) * (1 / ζ) ^ multiaffineInverseExponent n := by
  rw [multiaffineBiasBudget_eq_power n hζ]
  simp only [multiaffineInverseConstant, multiaffineInverseExponent,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul, inv_pow]

theorem multiaffineBiasBudget_le_exp (n : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ)
    (hZ : 1 / ζ ≤ Real.exp Z) :
    multiaffineBiasBudget n ζ ≤ Real.exp
      ((multiaffineInverseConstant n : ℝ) + (multiaffineInverseExponent n : ℝ) * Z) := by
  have hc : (multiaffineInverseConstant n : ℝ) ≤ Real.exp (multiaffineInverseConstant n : ℝ) := by
    linarith [Real.add_one_le_exp (multiaffineInverseConstant n : ℝ)]
  rw [multiaffineBiasBudget_eq_inverse_power n hζ]
  calc
    _ ≤ Real.exp (multiaffineInverseConstant n : ℝ) *
        (Real.exp Z) ^ multiaffineInverseExponent n := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem finiteLayerInverseLog_nonneg (m : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ finiteLayerInverseLog m Z := by unfold finiteLayerInverseLog; positivity

theorem finiteLayerBiasBudget_le_exp (m : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ) (hZ : 0 ≤ Z)
    (hInv : 1 / ζ ≤ Real.exp Z) : finiteLayerBiasBudget m ζ ≤ Real.exp (finiteLayerInverseLog m Z) := by
  have hsum := sum_le_exp_card_add_sum
    (fun i : Fin m => multiaffineBiasBudget i.val ζ)
    (fun i : Fin m => (multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z)
    (fun _ => by positivity) (fun i => multiaffineBiasBudget_le_exp i.val hζ hInv)
  have hs0 : 0 ≤ (Fintype.card (Fin m) : ℝ) +
      ∑ i : Fin m, ((multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z) := by
    positivity
  have h := one_add_le_exp_succ hs0 hsum
  change 1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ ≤ _
  convert h using 1
  congr 1
  simp only [finiteLayerInverseLog, finiteLayerInverseConstant, finiteLayerInverseExponent,
    Nat.cast_add, Nat.cast_one, Nat.cast_sum, Fintype.card_fin, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

theorem modeRemovalBeta_inv_le_exp {ε P : ℝ} (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBeta ε ≤ Real.exp (P + 2) := by
  have hEP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hmin : (modeRemovalBeta ε)⁻¹ ≤ 2 * Real.exp P := by
    apply inv_min_le_of_inv_le
    · norm_num
      linarith
    · rw [inv_div]
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hεInv (by norm_num : (0 : ℝ) ≤ 2)
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 2 * Real.exp P := by simpa only [one_div] using hmin
    _ ≤ Real.exp 2 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem modeRemovalBias_inv_le_exp (m : ℕ) {ε P : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBias m ε ≤ Real.exp (((2 ^ m : ℕ) : ℝ) * (P + 2)) := by
  have h := pow_le_pow_left₀ (div_nonneg zero_le_one (modeRemovalBeta_pos hε).le)
    (modeRemovalBeta_inv_le_exp hP hεInv) (2 ^ m)
  simpa only [modeRemovalBias, div_pow, one_pow, ← Real.exp_nat_mul] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def modeBiasLog (m : ℕ) (P : ℝ) : ℝ :=
  finiteLayerInverseLog m (((2 ^ m : ℕ) : ℝ) * (P + 2))

noncomputable def modeShrinkLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + modeProfileLog P + 3 * P + 4

noncomputable def modeSideLog (m : ℕ) (P : ℝ) : ℝ :=
  (P + modeShrinkLog m P + modeBiasLog m P + 1) + (P + modeProfileLog P + 3) + 2

theorem modeBiasLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeBiasLog m P :=
  finiteLayerInverseLog_nonneg m (by positivity)

theorem modeShrinkLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeShrinkLog m P := by
  have he := modeProfileLog_nonneg hP
  unfold modeShrinkLog
  positivity

theorem modeSideLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeSideLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  have he := modeProfileLog_nonneg hP
  unfold modeSideLog
  positivity

theorem chosenBiasBudget_le_exp (m : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    finiteLayerBiasBudget m (modeRemovalBias m ε) ≤ Real.exp (modeBiasLog m P) :=
  finiteLayerBiasBudget_le_exp m (modeRemovalBias_pos m hε) (by positivity)
    (modeRemovalBias_inv_le_exp m hε hP hεInv)

theorem modeRemovalShrink_le_exp (m d : ℕ) {P D ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalShrink m d D ρ ε ≤ Real.exp (modeShrinkLog m P) := by
  have hm : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hr := modeRemovalRadius_pos d hε
  have hrInv := modeRemovalRadius_inv_le_exp d hP hd hε hεInv
  have hE := modeProfileLog_nonneg hP
  have hprod : (m : ℝ) * D / (modeRemovalRadius d ε * ρ) ≤
      Real.exp ((m : ℝ) + modeProfileLog P + 3 * P + 3) := by
    calc
      _ = (m : ℝ) * D * (1 / modeRemovalRadius d ε) * (1 / ρ) := by
        simp only [div_eq_mul_inv, mul_inv, one_mul]
        ring
      _ ≤ Real.exp (m : ℝ) * Real.exp P * Real.exp (modeProfileLog P + P + 3) * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h := one_add_le_exp_succ (by positivity) hprod
  have he : ((m : ℝ) + modeProfileLog P + 3 * P + 3) + 1 = modeShrinkLog m P := by
    unfold modeShrinkLog
    ring
  simpa only [modeRemovalShrink, he] using h

theorem modeRemovalSideThreshold_le_exp (m d : ℕ) {P D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (_hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp (modeSideLog m P) := by
  have ht := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hb := chosenBiasBudget_le_exp m hP hε hεInv
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hBlog := modeBiasLog_nonneg m hP
  have hTlog := modeShrinkLog_nonneg m hP
  have hE := modeProfileLog_nonneg hP
  have hb1 : finiteLayerBiasBudget m (modeRemovalBias m ε) + 1 ≤ Real.exp (modeBiasLog m P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hBlog hb
  have ha : S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      Real.exp (P + modeShrinkLog m P + modeBiasLog m P + 1) := by
    calc
      _ ≤ Real.exp P * Real.exp (modeShrinkLog m P) * Real.exp (modeBiasLog m P + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hδ := modeRemovalMesh_pos d
  have hδInv := modeRemovalMesh_inv_le_exp d hP hd
  have hc : 1 / (ρ * modeRemovalMesh d) ≤ Real.exp (P + modeProfileLog P + 3) := by
    calc
      _ = (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp (modeProfileLog P + 3) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum := add_le_exp_add_one (by positivity) (by positivity) ha hc
  have hout := one_add_le_exp_succ (by positivity) hsum
  convert hout using 1
  · unfold modeRemovalSideThreshold
    ring
  · congr 1
    unfold modeSideLog
    ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MassConvolution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [DecidableEq G]

noncomputable def realUniformMass (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

theorem realUniformMass_nonneg (A : Finset G) (x : G) : 0 ≤ realUniformMass A x := by
  unfold realUniformMass
  split_ifs <;> positivity

theorem sum_realUniformMass [Fintype G] {A : Finset G} (hA : A.Nonempty) :
    ∑ x, realUniformMass A x = 1 := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  simp [realUniformMass, hcard]

theorem uniformMass_translation_le_shell [Fintype G] [AddCommGroup G]
    (A I O : Finset G) (t : G)
    (hinner : ∀ x ∈ I, x ∈ A ∧ x - t ∈ A)
    (houter : ∀ x, x ∈ A ∨ x - t ∈ A → x ∈ O) :
    ∑ x, |realUniformMass A (x - t) - realUniformMass A x| ≤
      ((O.card : ℝ) - I.card) / A.card := by
  have hpoint (x : G) :
      |realUniformMass A (x - t) - realUniformMass A x| ≤
        (if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
          (if x ∈ I then (A.card : ℝ)⁻¹ else 0) := by
    by_cases hi : x ∈ I
    · obtain ⟨ha, ht⟩ := hinner x hi
      have ho := houter x (Or.inl ha)
      simp [realUniformMass, hi, ho, ha, ht]
    · by_cases ha : x ∈ A <;> by_cases ht : x - t ∈ A
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inl ha)
        simp [realUniformMass, hi, ho, ha, ht]
      · have ho := houter x (Or.inr ht)
        simp [realUniformMass, hi, ho, ha, ht]
      · simp only [realUniformMass, ha, ht, hi, ite_false, sub_zero, abs_zero]
        split_ifs <;> positivity
  calc
    _ ≤ ∑ x, ((if x ∈ O then (A.card : ℝ)⁻¹ else 0) -
        (if x ∈ I then (A.card : ℝ)⁻¹ else 0)) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by simp [Finset.sum_sub_distrib, div_eq_mul_inv, sub_mul]

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    realUniformMass A x = (#A : ℝ)⁻¹ := by
  simp [realUniformMass, hx]

omit [AddCommGroup G] [Fintype G] in
@[simp]
theorem realUniformMass_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    realUniformMass A x = 0 := by
  simp [realUniformMass, hx]

omit [AddCommGroup G] [Fintype G] in
theorem realUniformMass_ne_zero_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    realUniformMass A x ≠ 0 ↔ x ∈ A := by
  unfold realUniformMass
  split_ifs with hx
  · simp [hx, hA.card_ne_zero]
  · simp [hx]

omit [DecidableEq G] in
theorem massConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ massConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (z - x))

omit [DecidableEq G] in

theorem massConvolution_comm (f g : G → ℝ) :
    massConvolution f g = massConvolution g f := by
  funext x
  rw [massConvolution, massConvolution]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ ?_
  simp [mul_comm]

omit [DecidableEq G] in

theorem sum_massConvolution (f g : G → ℝ) :
    ∑ x : G, massConvolution f g x = (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [massConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by simp

def convolutionPower (f : G → ℝ) : ℕ → G → ℝ
  | 0 => realUniformMass {0}
  | n + 1 => massConvolution (convolutionPower f n) f

@[simp] theorem convolutionPower_zero (f : G → ℝ) :
    convolutionPower f 0 = realUniformMass {0} := rfl

@[simp] theorem convolutionPower_succ (f : G → ℝ) (n : ℕ) :
    convolutionPower f (n + 1) =
      massConvolution (convolutionPower f n) f := rfl

theorem convolutionPower_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ convolutionPower f n x := by
  intro n
  induction n with
  | zero =>
      exact realUniformMass_nonneg {0}
  | succ n ihn =>
      exact massConvolution_nonneg ihn hf

theorem sum_convolutionPower {f : G → ℝ} (hf : ∑ x : G, f x = 1) :
    ∀ n, ∑ x : G, convolutionPower f n x = 1 := by
  intro n
  induction n with
  | zero =>
      exact sum_realUniformMass (singleton_nonempty 0)
  | succ n ihn =>
      rw [convolutionPower_succ, sum_massConvolution, ihn, hf, one_mul]

end

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCost
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def potentialCost (B : Finset G) (v : ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, C :: cs => (C.card : ℝ) / B.card * ((𝔼 x ∈ C, f x) * v) ^ (1 / 4 : ℝ) +
      potentialCost B v (remainder C f) cs

noncomputable def coefficientCost (B : Finset G) (cs : List (Finset G)) : ℝ :=
  (cs.map (fun C => (C.card : ℝ) / B.card)).sum

end Erdos3.Peeling

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PeelingReplacementPotential
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementPotentialSum (A Q : Finset G) (shape : Finset G → Finset G)
    (g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementPotential D Q (shape D) f g +
      replacementPotentialSum A Q shape g (Peeling.remainder D f) ds

variable [Fintype G]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_quotient_presentation_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hHpos : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ :=
    exists_bounded_quotient_presentation A hHpos hA
  have htp : (t : ℝ) ≤ p :=
    (show (t : ℝ) ≤ Fintype.card κ from by exact_mod_cast ht).trans hcols
  have hdp : (d : ℝ) ≤ p :=
    (show (d : ℝ) ≤ Fintype.card ι from by exact_mod_cast hd).trans hrows
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hSbudget : (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤
      Real.exp ((p + 2) ^ 45) := by
    have hb := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
      (by positivity : 0 ≤ (p + 2) ^ 7)
      (hdp.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
    exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hb
  refine ⟨d, hd, D, S, hker, hDS, ?_, ?_⟩
  · intro i j
    constructor
    · exact (show ((D i j).num.natAbs : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).1).trans hK
    · exact (show ((D i j).den : ℝ) ≤ rationalKernelHeight t H from
        by exact_mod_cast (hD i j).2).trans hK
  · intro i j
    constructor
    · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).1).trans hSbudget
    · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight d (rationalKernelHeight t H) from
        by exact_mod_cast (hS i j).2).trans hSbudget

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem rationalQuotientSectionHeight_le_exp (t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight d (rationalKernelHeight t H) : ℝ) ≤ Real.exp ((p + 2) ^ 45) := by
  have hK := rationalKernelHeight_le_budget t H hp ht hH
  have hS := rationalSolveHeight_le_budget d (rationalKernelHeight t H)
    (by positivity : 0 ≤ (p + 2) ^ 7)
    (hd.trans (le_power_budget hp (by decide : 1 ≤ 7))) hK
  exact exponential_budget_comp hp (by positivity) 7 5 le_rfl hS

theorem rationalLieQuotientStructureHeight_le_exp (n t d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight n
      (max H (max (rationalKernelHeight t H)
        (rationalSolveHeight d (rationalKernelHeight t H)))) : ℝ) ≤
      Real.exp ((p + 2) ^ 51) := by
  apply rationalLieStructureHeight_le_exp n _ hp hn 45
  simp only [Nat.cast_max, max_le_iff]
  refine ⟨hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide))), ?_,
    rationalQuotientSectionHeight_le_exp t d H hp ht hd hH⟩
  exact (rationalKernelHeight_le_budget t H hp ht hH).trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 7 ≤ 45)))

variable {ι η L : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [LieRing L] [LieAlgebra ℚ L]

theorem exists_lie_quotient_basis_exp_height (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (v : η → L) (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule)
    {H : ℕ} (hHpos : 1 ≤ H) (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hm : (Fintype.card η : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ b : Basis (Fin d) ℚ (L ⧸ I),
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 7)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) ∧
        ∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 51) ∧
          ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 51) := by
  classical
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_bounded_lie_quotient_with_structure e I v hspan hHpos hv hc
  have htp : (t : ℝ) ≤ p := (Nat.cast_le.mpr ht).trans hm
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hd).trans hn
  have hK := rationalKernelHeight_le_budget t H hp htp hH
  have hJ := rationalQuotientSectionHeight_le_exp t d H hp htp hdp hH
  have hC := rationalLieQuotientStructureHeight_le_exp (Fintype.card ι) t d H hp hn htp hdp hH
  refine ⟨d, hd, b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hD i j).1).trans hK, (Nat.cast_le.mpr (hD i j).2).trans hK⟩
  · intro i j
    exact ⟨(Nat.cast_le.mpr (hS i j).1).trans hJ, (Nat.cast_le.mpr (hS i j).2).trans hJ⟩
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hbracket i j k).1).trans hC,
      (Nat.cast_le.mpr (hbracket i j k).2).trans hC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BinaryTupleSorting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem binary_eq_zero_of_ne_one (b : Fin 2) (h : b ≠ 1) : b = 0 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 1 := fun heq => h (Fin.ext heq)
  change b.val = 0
  omega

theorem binary_eq_one_of_ne_zero (b : Fin 2) (h : b ≠ 0) : b = 1 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 0 := fun heq => h (Fin.ext heq)
  change b.val = 1
  omega

def binaryZeroCount {n : ℕ} (f : Fin n → Fin 2) : ℕ :=
  Fintype.card {i : Fin n // f i = 0}

def binarySorted {n : ℕ} (f : Fin n → Fin 2) : Fin n → Fin 2 := f ∘ Tuple.sort f

theorem binaryZeroCount_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binaryZeroCount (f ∘ e) = binaryZeroCount f := by
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem binarySorted_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binarySorted (f ∘ e) = binarySorted f :=
  Tuple.comp_perm_comp_sort_eq_comp_sort

theorem binarySorted_threshold {n : ℕ} (f : Fin n → Fin 2) (k : Fin n) :
    binarySorted f k = if k.val < binaryZeroCount f then 0 else 1 := by
  have hle (a : Fin 2) : a ≤ 0 ↔ a = 0 :=
    ⟨fun h => le_antisymm h (Fin.zero_le _), fun h => h ▸ le_rfl⟩
  have hiff : k.val < binaryZeroCount (binarySorted f) ↔ binarySorted f k = 0 := by
    have H := Tuple.lt_card_le_iff_apply_le_of_monotone
      (f := binarySorted f) (j := k) (a := (0 : Fin 2)) (Tuple.monotone_sort f)
    unfold binaryZeroCount
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun i : Fin n => binarySorted f i = 0)) =
        Finset.univ.filter (fun i : Fin n => binarySorted f i ≤ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hle]
    rw [hfilter]
    exact H.trans (hle _)
  have hcount : binaryZeroCount (binarySorted f) = binaryZeroCount f :=
    binaryZeroCount_comp f (Tuple.sort f)
  rw [hcount] at hiff
  split_ifs with hk
  · exact hiff.mp hk
  · exact binary_eq_one_of_ne_zero _ (fun h => hk (hiff.mpr h))

def zeroFixedPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun j => (e j).succ)
  invFun := Fin.cases 0 (fun j => (e.symm j).succ)
  left_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.symm_apply_apply]
  right_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.apply_symm_apply]

theorem binarySorted_tail {n : ℕ} (f : Fin (n + 1) → Fin 2) (h0 : f 0 = 0) :
    binarySorted f = f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ)) := by
  have hm : Monotone (f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j _
      change f 0 ≤ _
      rw [h0]
      exact Fin.zero_le _
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        have hi : ¬ i.succ ≤ (0 : Fin (n + 1)) := by
          intro h
          simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at h
          omega
        exact (hi hij).elim
      · intro hij
        exact (Tuple.monotone_sort (fun j : Fin n => f j.succ))
          (by simpa only [Fin.succ_le_succ_iff] using hij)
  exact Tuple.unique_monotone (Tuple.monotone_sort f) hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

noncomputable def boxCoverMeshCount (B : ℝ) (K : ℝ≥0) (ε : ℝ) : ℕ :=
  ⌈2 * B * K / ε⌉₊ + 1

theorem boxCoverMeshCount_pos (B : ℝ) (K : ℝ≥0) (ε : ℝ) : 0 < boxCoverMeshCount B K ε := by
  unfold boxCoverMeshCount
  omega

theorem boxCoverMeshCount_error {B ε : ℝ} (K : ℝ≥0) (hε : 0 < ε) :
    K * (2 * B / boxCoverMeshCount B K ε) ≤ ε := by
  have hN : (0 : ℝ) < boxCoverMeshCount B K ε := by exact_mod_cast boxCoverMeshCount_pos B K ε
  have hceil : 2 * B * K / ε ≤ (boxCoverMeshCount B K ε : ℝ) := by
    exact (Nat.le_ceil _).trans (by unfold boxCoverMeshCount; push_cast; linarith)
  have hm := (div_le_iff₀ hε).mp hceil
  rw [← mul_div_assoc, div_le_iff₀ hN]
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def metricTent (c : X) (r : ℝ) (x : X) : ℝ := max 0 (2 * r - dist x c)

theorem metricTent_nonneg (c : X) (r : ℝ) (x : X) : 0 ≤ metricTent c r x := le_max_left _ _

theorem metricTent_le (c : X) {r : ℝ} (hr : 0 ≤ r) (x : X) : metricTent c r x ≤ 2 * r :=
  max_le (by linarith) (by linarith [dist_nonneg (x := x) (y := c)])

theorem metricTent_zero_of_far (c x : X) {r : ℝ} (hx : 2 * r ≤ dist x c) : metricTent c r x = 0 := by
  exact max_eq_left (by linarith)

theorem abs_metricTent_sub_le (c : X) (r : ℝ) (x y : X) :
    |metricTent c r x - metricTent c r y| ≤ dist x y := by
  calc
    _ = |max (2 * r - dist x c) 0 - max (2 * r - dist y c) 0| := by
      simp only [metricTent, max_comm]
    _ ≤ |(2 * r - dist x c) - (2 * r - dist y c)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist x c - dist y c| := by
      rw [show (2 * r - dist x c) - (2 * r - dist y c) = -(dist x c - dist y c) by ring, abs_neg]
    _ ≤ dist x y := abs_dist_sub_le x y c

variable {ι : Type*} [Fintype ι]

noncomputable def metricTentSum (c : ι → X) (r : ℝ) (x : X) : ℝ := ∑ i, metricTent (c i) r x

theorem metricTentSum_ge (c : ι → X) {r : ℝ} (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) :
    r ≤ metricTentSum c r x := by
  obtain ⟨i, hi⟩ := hcover x
  calc
    r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
    _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)

theorem abs_metricTentSum_sub_le (c : ι → X) (r : ℝ) (x y : X) :
    |metricTentSum c r x - metricTentSum c r y| ≤ Fintype.card ι * dist x y := by
  unfold metricTentSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |metricTent (c i) r x - metricTent (c i) r y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, dist x y := Finset.sum_le_sum fun i _ => abs_metricTent_sub_le (c i) r x y
    _ = _ := by simp

noncomputable def metricTentPartition (c : ι → X) (r : ℝ) (i : ι) (x : X) : ℝ :=
  metricTent (c i) r x / metricTentSum c r x

theorem metricTentPartition_nonneg (c : ι → X) (r : ℝ) (i : ι) (x : X) :
    0 ≤ metricTentPartition c r i x :=
  div_nonneg (metricTent_nonneg _ _ _) (Finset.sum_nonneg fun j _ => metricTent_nonneg (c j) r x)

theorem sum_metricTentPartition (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) : ∑ i, metricTentPartition c r i x = 1 := by
  simp only [metricTentPartition, ← Finset.sum_div]
  exact div_self (hr.trans_le (metricTentSum_ge c hcover x)).ne'

theorem metricTentPartition_le_one (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x : X) : metricTentPartition c r i x ≤ 1 := by
  rw [← sum_metricTentPartition c hr hcover x]
  exact Finset.single_le_sum (fun j _ => metricTentPartition_nonneg c r j x) (Finset.mem_univ i)

theorem metricTentPartition_zero_of_far (c : ι → X) (r : ℝ) (i : ι) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : metricTentPartition c r i x = 0 := by
  simp only [metricTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem abs_metricTentPartition_sub_le (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x y : X) :
    |metricTentPartition c r i x - metricTentPartition c r i y| ≤
      ((2 * Fintype.card ι + 1) / r) * dist x y := by
  have h := abs_div_sub_div_bound hr (metricTentSum_ge c hcover x) (metricTentSum_ge c hcover y)
    dist_nonneg (by positivity : 0 ≤ 2 * r) (by positivity : 0 ≤ (Fintype.card ι : ℝ) * dist x y)
    (abs_metricTent_sub_le (c i) r x y)
    (by simpa only [abs_of_nonneg (metricTent_nonneg _ _ _)] using metricTent_le (c i) hr.le y)
    (abs_metricTentSum_sub_le c r x y)
  apply h.trans_eq
  field_simp
  ring

theorem lipschitz_metricTentPartition (c : ι → X) {r : ℝ≥0} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) :
    LipschitzWith ((2 * Fintype.card ι + 1) / r) (metricTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_ofNat] using abs_metricTentPartition_sub_le c (show (0 : ℝ) < r from hr) hcover i x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem boxCoverMeshCount_add_one_le_exp {B ε p : ℝ} (K : ℝ≥0)
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hεinv : 1 / ε ≤ Real.exp p) :
    ((boxCoverMeshCount B K ε + 1 : ℕ) : ℝ) ≤ Real.exp (3 * p + 4) := by
  have hprod : 2 * B * K / ε ≤ 2 * Real.exp (3 * p) := by
    calc
      _ = 2 * (B * K * (1 / ε)) := by ring
      _ ≤ 2 * (Real.exp p * Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * B * K / ε)).le
  have hone : 1 ≤ Real.exp (3 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp (3 * p) := by
      unfold boxCoverMeshCount
      push_cast
      linarith
    _ ≤ Real.exp 4 * Real.exp (3 * p) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

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

theorem shifted_power_self_mono {p : ℝ} (hp : 0 ≤ p) {C D : ℕ} (hC : 1 ≤ C) (hCD : C ≤ D) :
    (p + C) ^ C ≤ (p + D) ^ D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hC.trans hCD
  apply (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hCD)) C).trans
  exact pow_le_pow_right₀ (by linarith) hCD

theorem metricPartition_constant_le_exp (n : ℕ) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp p) (hr : 1 / (r : ℝ) ≤ Real.exp p) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + 2) := by
  have hnum : 2 * (n : ℝ) + 1 ≤ 3 * Real.exp p := by
    linarith [Real.one_le_exp_iff.mpr hp]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  change (2 * (n : ℝ) + 1) / r ≤ _
  calc
    _ = (2 * (n : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp p) * Real.exp p :=
      mul_le_mul hnum hr (by positivity) (by positivity)
    _ = 3 * Real.exp (2 * p) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSupNorm
namespace OAI

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def coordinateL2Norm (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

theorem coordinateL2Norm_nonneg (v : ι → ℝ) : 0 ≤ coordinateL2Norm v := Real.sqrt_nonneg _

theorem coordinateL2Norm_le_card_bound (v : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) : coordinateL2Norm v ≤ (Fintype.card ι + 1) * B := by
  unfold coordinateL2Norm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsum : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, B ^ 2 := Finset.sum_le_sum fun i _ =>
        sq_le_sq.mpr ((hv i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp
  apply hsum.trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι), sq_nonneg (Fintype.card ι : ℝ)]

theorem coordinateL2Norm_matrix_le (A : κ → ι → ℝ) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      Real.sqrt (∑ k, ∑ i, A k i ^ 2) * coordinateL2Norm v := by
  have h : (∑ k, (∑ i, A k i * v i) ^ 2) ≤
      (∑ k, ∑ i, A k i ^ 2) * ∑ i, v i ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A k) v)
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_mul
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) _)

theorem coordinateL2Norm_matrix_entry_bound (A : κ → ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A k i| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have hsum : (∑ k, ∑ i, A k i ^ 2) ≤
      (Fintype.card κ : ℝ) * Fintype.card ι * B ^ 2 := by
    calc
      (∑ k, ∑ i, A k i ^ 2) ≤ ∑ _k : κ, ∑ _i : ι, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq.mpr ((hA k i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hdim : (Fintype.card κ : ℝ) * Fintype.card ι ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) ^ 2 := by nlinarith [sq_nonneg ((Fintype.card κ : ℝ) - Fintype.card ι)]
  have hsq : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith
  have hroot : Real.sqrt (∑ k, ∑ i, A k i ^ 2) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hsum.trans ?_⟩
    rw [mul_pow]
    exact mul_le_mul hdim hsq (sq_nonneg _) (sq_nonneg _)
  exact (coordinateL2Norm_matrix_le A v).trans
    (mul_le_mul_of_nonneg_right hroot (coordinateL2Norm_nonneg v))

end Erdos3

end

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem coordinateLinearMap_apply_sum (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (v : ι → ℝ) (k : κ) :
    A v k = ∑ i, A (Pi.single i 1) k * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, LinearMap.sum_single_apply]
  calc
    A v k = A (∑ i, v i • Pi.single i (1 : ℝ)) k := congrArg (fun w => A w k) hv
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coordinateLinearMap_L2_bound (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A (Pi.single i 1) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (A v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : A v = fun k => ∑ i, A (Pi.single i 1) k * v i :=
    funext (coordinateLinearMap_apply_sum A v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => A (Pi.single i 1) k) B hB hA v

end Erdos3

end

section

namespace Erdos3

theorem abs_coordinate_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ coordinateL2Norm v := by
  have hsq : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsum : 0 ≤ ∑ j, (v j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (v j)
  have hroot := Real.sq_sqrt hsum
  have hnonneg := coordinateL2Norm_nonneg v
  unfold coordinateL2Norm at *
  nlinarith [sq_abs (v i), abs_nonneg (v i)]

theorem norm_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ≤ coordinateL2Norm v := by
  apply (pi_norm_le_iff_of_nonneg (coordinateL2Norm_nonneg v)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_coordinate_le_coordinateL2Norm v i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerIndexFromOrderedGenerators
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

def orderedGroupTailProduct (a : Fin d → G) (i : ℕ) : G :=
  (((List.finRange d).drop i).map a).prod

def orderedGroupProduct (a : Fin d → G) : G := orderedGroupTailProduct a 0

def orderedZpowProduct (a : Fin d → G) (z : Fin d → ℤ) : G :=
  orderedGroupProduct (fun j => a j ^ z j)

theorem orderedGroupTailProduct_terminal (a : Fin d → G) {i : ℕ} (hi : d ≤ i) :
    orderedGroupTailProduct a i = 1 := by
  simp only [orderedGroupTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem orderedGroupTailProduct_step (a : Fin d → G) (j : Fin d) :
    orderedGroupTailProduct a j.val = a j * orderedGroupTailProduct a (j.val + 1) := by
  unfold orderedGroupTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem orderedGroupTailProduct_congr (i : ℕ) {a b : Fin d → G}
    (h : ∀ j : Fin d, i ≤ j.val → a j = b j) :
    orderedGroupTailProduct a i = orderedGroupTailProduct b i := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  exact h j (mem_drop_finRange_iff.mp hj)

theorem orderedGroupProduct_map {H : Type*} [Group H] (f : G →* H) (a : Fin d → G) :
    f (orderedGroupProduct a) = orderedGroupProduct (fun j => f (a j)) := by
  simp only [orderedGroupProduct, orderedGroupTailProduct, List.drop_zero,
    map_list_prod, List.map_map, Function.comp_def]

theorem orderedZpowProduct_map {H : Type*} [Group H] (f : G →* H)
    (a : Fin d → G) (z : Fin d → ℤ) :
    f (orderedZpowProduct a z) = orderedZpowProduct (fun j => f (a j)) z := by
  simp only [orderedZpowProduct, orderedGroupProduct_map, map_zpow]

theorem exists_bounded_ordered_exponents (a : Fin d → G) (m : ℕ) (hm : 0 < m)
    (ha : ∀ j, a j ^ m = 1) (z : Fin d → ℤ) :
    ∃ r : Fin d → Fin m, orderedGroupProduct (fun j => a j ^ (r j).val) =
      orderedZpowProduct a z := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hnonneg (j : Fin d) : 0 ≤ z j % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hmz)
  let r : Fin d → Fin m := fun j => ⟨(z j % (m : ℤ)).toNat, by
    have hlt := Int.emod_lt_of_pos (z j) hmz
    omega⟩
  refine ⟨r, ?_⟩
  unfold orderedZpowProduct
  apply congrArg orderedGroupProduct
  funext j
  rw [zpow_eq_zpow_emod' (z j) (ha j)]
  change a j ^ (z j % (m : ℤ)).toNat = a j ^ (z j % (m : ℤ))
  rw [← zpow_natCast, Int.toNat_of_nonneg (hnonneg j)]

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

theorem powerSubgroup_index_le_of_ordered_generators (a : Fin d → G)
    (hgen : Function.Surjective (orderedZpowProduct a)) (m : ℕ) (hm : 0 < m) :
    (powerSubgroup G m).FiniteIndex ∧ (powerSubgroup G m).index ≤ m ^ d := by
  let Q := G ⧸ powerSubgroup G m
  let q : G →* Q := QuotientGroup.mk' _
  let f : (Fin d → Fin m) → Q := fun r => orderedGroupProduct (fun j => q (a j) ^ (r j).val)
  have hpow (j : Fin d) : q (a j) ^ m = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_mem_powerSubgroup (a j) m)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hgen g
    obtain ⟨r, hr⟩ := exists_bounded_ordered_exponents (fun j => q (a j)) m hm hpow z
    refine ⟨r, ?_⟩
    change orderedGroupProduct (fun j => q (a j) ^ (r j).val) = q (orderedZpowProduct a z)
    rw [orderedZpowProduct_map]
    exact hr
  let : Finite Q := Finite.of_surjective f hf
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  change Nat.card Q ≤ m ^ d
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using
    Nat.card_le_card_of_surjective f hf

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridFunctional
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

def coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) : Submodule ℤ L where
  carrier := {x | e.equivFun x ∈ scaledIntegerGrid B}
  zero_mem' := ⟨fun _ => 0, by ext i; simp⟩
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    refine ⟨fun i => z i + w i, ?_⟩
    rw [map_add, hz, hw]
    ext i
    simp [mul_add]
  smul_mem' := by
    rintro n x ⟨z, hz⟩
    refine ⟨fun i => n * z i, ?_⟩
    rw [map_zsmul, hz]
    ext i
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem scaled_basis_mem_coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) (i : ι) :
    (B : ℚ) • e i ∈ coordinateGridModule e B := by
  classical
  refine ⟨fun j => if i = j then 1 else 0, ?_⟩
  ext j
  simp only [map_smul, Pi.smul_apply, Basis.equivFun_self, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

theorem coordinateGrid_bracket_divisible (e : Basis ι ℚ L) (B D : ℕ)
    (hc : ∀ i j k, ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n)
    {a b : L} (ha : a ∈ coordinateGridModule e B) (hb : b ∈ coordinateGridModule e B) :
    ∃ z ∈ coordinateGridModule e B, ⁅a, b⁆ = (D : ℚ) • z := by
  classical
  choose c hc using hc
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  let w : ι → ℤ := fun k => ∑ ij : ι × ι, c ij.1 ij.2 k * u ij.1 * v ij.2
  let z : L := e.equivFun.symm ((B : ℚ) • fun k => (w k : ℚ))
  have hz : e.equivFun z = (B : ℚ) • fun k => (w k : ℚ) := e.equivFun.apply_symm_apply _
  refine ⟨z, ⟨w, hz⟩, ?_⟩
  apply e.equivFun.injective
  ext k
  rw [map_smul, hz]
  change e.repr ⁅a, b⁆ k = (D : ℚ) * ((B : ℚ) * (w k : ℚ))
  rw [lie_coordinate_formula]
  have hu' (i : ι) : e.repr a i = (B : ℚ) * (u i : ℚ) := congrFun hu i
  have hv' (i : ι) : e.repr b i = (B : ℚ) * (v i : ℚ) := congrFun hv i
  simp only [w, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hu', hv']
  calc
    _ = (B : ℚ) * (((B : ℚ) * lieStructureConstants e ij.1 ij.2 k) * u ij.1 * v ij.2) := by ring
    _ = (D : ℚ) * ((B : ℚ) * ((c ij.1 ij.2 k : ℚ) * u ij.1 * v ij.2)) := by
      rw [hc]
      ring

end Erdos3

end

section

namespace Erdos3

open Module

theorem coordinateGridModule_map_of_basis {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    (hφ : ∀ i, ∃ j, φ (b i) = c j) (B : ℕ) {x : L}
    (hx : x ∈ coordinateGridModule b B) : φ x ∈ coordinateGridModule c B := by
  classical
  obtain ⟨z, hz⟩ := hx
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨j, hj⟩ := hφ i
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, hi, hj]
  have hm := (coordinateGridModule c B).smul_mem (z i) (scaled_basis_mem_coordinateGridModule c B j)
  simpa only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm] using hm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem linearFunctional_coordinate_height {ι L : Type*} [Fintype ι]
    [AddCommGroup L] [Module ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    {H K : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (x : L) (hx : ∀ i, RationalHeightLE (b.repr x i) K) :
    RationalHeightLE (η x) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have heq : η x = ∑ i, b.repr x i * η (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hη i))

theorem coordinateGrid_functional_integral {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    (l B : ℕ) (hdiv : l ∣ B)
    (hη : ∀ i, ∃ n : ℤ, (l : ℚ) * η (b i) = n)
    {x : L} (hx : x ∈ coordinateGridModule b B) : ∃ n : ℤ, η x = n := by
  classical
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨z, hz⟩ := hx
  choose n hn using hη
  refine ⟨∑ i, (k : ℤ) * z i * n i, ?_⟩
  rw [← b.sum_repr x, map_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, smul_eq_mul, hi, hk, Nat.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (k : ℚ) * (z i : ℚ) * ((l : ℚ) * η (b i)) := by ring
    _ = _ := by rw [hn i]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CircleFejerKernel
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real
open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

def fejerPairFrequency {N : ℕ} (p : Fin N × Fin N) : ℤ :=
  (p.1.val : ℤ) - p.2.val

def fejerFrequencies (N : ℕ) : Finset ℤ := by
  classical
  exact (Finset.univ : Finset (Fin N × Fin N)).image fejerPairFrequency

def fejerCoefficient (N : ℕ) (h : ℤ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun p : Fin N × Fin N =>
    fejerPairFrequency p = h).card : ℝ) / N

def fejerPolynomial (N : ℕ) (x : Circle) : ℝ :=
  (∑ h ∈ fejerFrequencies N,
    (fejerCoefficient N h : ℂ) * character (h • x)).re

lemma fejer_grouped (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N =>
          fejerPairFrequency p = h), character (fejerPairFrequency p • x)) =
      ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) := by
  classical
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [Finset.filter_eq_self.2]
  intro p hp
  simp only [fejerFrequencies, Finset.mem_image]
  exact ⟨p, Finset.mem_univ _, rfl⟩

lemma fejer_pair_sum_eq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (∑ j : Fin N, character ((j.val : ℤ) • x)) *
        (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) := by
  calc
    _ = ∑ j : Fin N, ∑ k : Fin N,
        character (fejerPairFrequency (j, k) • x) := by
      exact Fintype.sum_prod_type (γ := ℂ)
        (fun p : Fin N × Fin N => character (fejerPairFrequency p • x))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← character_add]
      congr 2
      simp only [fejerPairFrequency, sub_eq_add_neg, add_smul]

lemma fejer_neg_sum_eq_conj (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
      star (∑ k : Fin N, character ((k.val : ℤ) • x)) := by
  change (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
    (starRingEnd ℂ) (∑ k : Fin N, character ((k.val : ℤ) • x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AddCircle.toCircle ((-(k.val : ℤ)) • x) =
    (starRingEnd ℂ) (AddCircle.toCircle ((k.val : ℤ) • x))
  rw [neg_smul, AddCircle.toCircle_neg]
  exact _root_.Circle.coe_inv_eq_conj _

lemma fejer_fin_sum_eq_geo (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((k.val : ℤ) • x)) =
      geometricCharacterSum N x := by
  rw [geometricCharacterSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natCast_zsmul]

lemma fejer_pair_sum_eq_norm_sq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (‖geometricCharacterSum N x‖ ^ 2 : ℝ) := by
  rw [fejer_pair_sum_eq, fejer_neg_sum_eq_conj, fejer_fin_sum_eq_geo]
  change geometricCharacterSum N x *
    (starRingEnd ℂ) (geometricCharacterSum N x) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _ |>.symm

lemma complex_fejerPolynomial_eq (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x) =
      ((‖geometricCharacterSum N x‖ ^ 2 / N : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_div]
  push_cast
  have hpair := fejer_pair_sum_eq_norm_sq N x
  rw [← Complex.ofReal_pow, ← hpair, ← fejer_grouped N x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h hh
  rw [fejerCoefficient, Complex.ofReal_div]
  push_cast
  rw [div_mul_eq_mul_div]
  congr 1
  calc
    (#{p : Fin N × Fin N | fejerPairFrequency p = h} : ℂ) *
        character (h • x) =
        ∑ p with fejerPairFrequency p = h, character (h • x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ p with fejerPairFrequency p = h,
        character (fejerPairFrequency p • x) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

lemma fejerPolynomial_eq (N : ℕ) (x : Circle) :
    fejerPolynomial N x = ‖geometricCharacterSum N x‖ ^ 2 / N := by
  have h := congrArg Complex.re (complex_fejerPolynomial_eq N x)
  simpa only [fejerPolynomial, Complex.ofReal_re] using h

lemma fejerPolynomial_nonneg (N : ℕ) (x : Circle) :
    0 ≤ fejerPolynomial N x := by
  rw [fejerPolynomial_eq]
  positivity

lemma fejerPolynomial_le_of_distance {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {x : Circle} (hx : η ≤ integerDistance x) :
    fejerPolynomial N x ≤ 1 / (4 * N * η ^ 2) := by
  rw [fejerPolynomial_eq]
  have hgeom :=
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hnorm := norm_nonneg (geometricCharacterSum N x)
  have hdist := integerDistance_nonneg x
  have hbound : 2 * η * ‖geometricCharacterSum N x‖ ≤ 1 := by nlinarith
  have hsquare : 4 * η ^ 2 * ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 := by
    have hs := mul_self_le_mul_self (mul_nonneg (by positivity) hnorm) hbound
    nlinarith
  have hn2 : ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 / (4 * η ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η ^ 2)]
    nlinarith
  calc
    ‖geometricCharacterSum N x‖ ^ 2 / (N : ℝ) ≤
        (1 / (4 * η ^ 2)) / N := by gcongr
    _ = 1 / (4 * N * η ^ 2) := by field_simp

lemma integral_character (h : ℤ) :
    ∫ x : Circle, character (h • x) ∂circleHaar = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp
  · simp only [hh, ↓reduceIte]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hh (by norm_num))

lemma integral_fejerPolynomial {N : ℕ} (hN : 0 < N) :
    ∫ x : Circle, fejerPolynomial N x ∂circleHaar = 1 := by
  simp_rw [fejerPolynomial]
  have hterm : ∀ h ∈ fejerFrequencies N,
      Integrable (fun x : Circle =>
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    intro h hh
    apply Integrable.const_mul
    apply Integrable.of_bound (fourier h).continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => (norm_character (h • x)).le
  have hint : Integrable (fun x : Circle =>
      ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    have hi := integrable_finsetSum' (fejerFrequencies N) hterm
    have heq : (∑ h ∈ fejerFrequencies N,
        fun x : Circle => (fejerCoefficient N h : ℂ) * character (h • x)) =
        fun x : Circle => ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) := by
      funext x
      exact Finset.sum_apply x (fejerFrequencies N) _
    rw [← heq]
    exact hi
  calc
    (∫ x : Circle, (∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)).re ∂circleHaar) =
        (∫ x : Circle, ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) ∂circleHaar).re :=
      integral_re hint
    _ = 1 := by
      rw [integral_finsetSum (fejerFrequencies N) hterm]
      simp_rw [integral_const_mul, integral_character]
      rw [Finset.sum_eq_single 0]
      · rw [if_pos rfl, mul_one]
        unfold fejerCoefficient fejerPairFrequency
        have hdiag : (Finset.univ.filter fun p : Fin N × Fin N =>
            (p.1.val : ℤ) - p.2.val = 0).card = N := by
          rw [show (Finset.univ.filter fun p : Fin N × Fin N =>
              (p.1.val : ℤ) - p.2.val = 0) =
              Finset.univ.image (fun j : Fin N => (j, j)) by
            ext p
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_image]
            constructor
            · intro hp
              have : p.1 = p.2 := by
                apply Fin.ext
                omega
              exact ⟨p.1, by ext <;> simp [this]⟩
            · rintro ⟨j, -, rfl⟩
              simp]
          calc
            (Finset.univ.image (fun j : Fin N => (j, j))).card =
                (Finset.univ : Finset (Fin N)).card :=
              Finset.card_image_of_injective _ fun i j h => by
                simpa using congrArg Prod.fst h
            _ = N := by simp
        rw [hdiag, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
        norm_num
      · intro h hh hne
        rw [if_neg hne, mul_zero]
      · intro hz
        exfalso
        apply hz
        unfold fejerFrequencies
        apply Finset.mem_image.2
        exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _,
          by simp [fejerPairFrequency]⟩

lemma fejer_fiber_card_le (N : ℕ) (h : ℤ) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      fejerPairFrequency p = h).card ≤ N := by
  let s := Finset.univ.filter fun p : Fin N × Fin N => fejerPairFrequency p = h
  calc
    s.card ≤ (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq hpq
        apply Prod.ext hpq
        apply Fin.ext
        have hpf := (Finset.mem_filter.mp hp).2
        have hqf := (Finset.mem_filter.mp hq).2
        unfold fejerPairFrequency at hpf hqf
        omega
    _ = N := by simp

lemma fejerCoefficient_nonneg (N : ℕ) (h : ℤ) :
    0 ≤ fejerCoefficient N h := by
  unfold fejerCoefficient
  positivity

lemma fejerCoefficient_le_one {N : ℕ} (hN : 0 < N) (h : ℤ) :
    fejerCoefficient N h ≤ 1 := by
  unfold fejerCoefficient
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast fejer_fiber_card_le N h

lemma continuous_fejerPolynomial (N : ℕ) : Continuous (fejerPolynomial N) := by
  rw [show fejerPolynomial N = fun x =>
      ‖geometricCharacterSum N x‖ ^ 2 / N by
    funext x
    exact fejerPolynomial_eq N x]
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  unfold geometricCharacterSum
  apply continuous_finsetSum
  intro n hn
  unfold character
  exact continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (continuous_nsmul n))

end
end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultilinearFirstOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {R I L E : Type*} [CommRing R] [Fintype I] [DecidableEq I]
  [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E]

theorem multilinear_eq_first_order_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x y : I → L) (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ D i) :
    f (x + y) = f x + f.linearDeriv x y := by
  classical
  rw [f.map_add_eq_map_add_linearDeriv_add]
  have hsum : (∑ s : Finset I with 2 ≤ s.card, f (s.piecewise y x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hs' : 1 < s.card := (Finset.mem_filter.mp hs).2
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs'
    refine hvanish _ ?_ i j hij ?_ ?_
    · intro k
      by_cases hk : k ∈ s
      · simpa only [s.piecewise_eq_of_mem _ _ hk] using hDC k (hy k)
      · simpa only [s.piecewise_eq_of_notMem _ _ hk] using hx k
    · simpa only [s.piecewise_eq_of_mem _ _ hi] using hy i
    · simpa only [s.piecewise_eq_of_mem _ _ hj] using hy j
  rw [hsum, add_zero]

theorem exists_linear_expansion_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x : I → L) (hx : ∀ i, x i ∈ C i) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      f (fun i => x i + (y i : L)) = f x + A y := by
  classical
  let inclusion : (∀ i, D i) →ₗ[R] (I → L) :=
    LinearMap.pi (fun i => (D i).subtype.comp (LinearMap.proj i))
  refine ⟨(f.linearDeriv x).comp inclusion, ?_⟩
  intro y
  exact multilinear_eq_first_order_of_two_vanish f C D hDC hvanish x
    (fun i => y i) hx (fun i => (y i).property)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def basisAxisScale (b : Basis I ℝ E) (i : I) : ℕ := ⌈‖b i‖⁻¹⌉₊

theorem basisAxisScale_pos (b : Basis I ℝ E) (i : I) : 0 < basisAxisScale b i := by
  apply Nat.ceil_pos.mpr
  exact inv_pos.mpr (norm_pos_iff.mpr (b.ne_zero i))

theorem basisAxisScale_mul_norm (b : Basis I ℝ E) (i : I) :
    1 ≤ (basisAxisScale b i : ℝ) * ‖b i‖ ∧
      (basisAxisScale b i : ℝ) * ‖b i‖ < ‖b i‖ + 1 := by
  have hpos : 0 < ‖b i‖ := norm_pos_iff.mpr (b.ne_zero i)
  have hlo := mul_le_mul_of_nonneg_right (Nat.le_ceil ‖b i‖⁻¹) hpos.le
  have hhi := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (inv_nonneg.mpr hpos.le)) hpos
  constructor
  · simpa only [basisAxisScale, inv_mul_cancel₀ hpos.ne'] using hlo
  · have he : (‖b i‖⁻¹ + 1) * ‖b i‖ = ‖b i‖ + 1 := by
      rw [add_mul, inv_mul_cancel₀ hpos.ne', one_mul, add_comm]
    simpa only [basisAxisScale, he] using hhi

noncomputable def normalizedAxisBasis (b : Basis I ℝ E) : Basis I ℝ E :=
  b.unitsSMul (fun i => Units.mk0 (basisAxisScale b i : ℝ)
    (Nat.cast_ne_zero.mpr (basisAxisScale_pos b i).ne'))

theorem normalizedAxisBasis_apply (b : Basis I ℝ E) (i : I) :
    normalizedAxisBasis b i = (basisAxisScale b i : ℝ) • b i := by
  simp only [normalizedAxisBasis, Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]

theorem normalizedAxisBasis_norm (b : Basis I ℝ E) (i : I) :
    ‖normalizedAxisBasis b i‖ = (basisAxisScale b i : ℝ) * ‖b i‖ := by
  rw [normalizedAxisBasis_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

theorem normalizedAxisBasis_norm_bounds (b : Basis I ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (i : I) :
    1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1 := by
  rw [normalizedAxisBasis_norm]
  refine ⟨(basisAxisScale_mul_norm b i).1, ?_⟩
  have h := (basisAxisScale_mul_norm b i).2
  have hi := hb i
  linarith

variable [Fintype I]

theorem normalizedAxisBasis_coordinates (b : Basis I ℝ E) (x : E) (i : I) :
    (normalizedAxisBasis b).equivFun x i = b.equivFun x i / (basisAxisScale b i : ℝ) := by
  simp only [normalizedAxisBasis, Basis.equivFun_apply, Basis.repr_unitsSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

theorem normalizedAxisBasis_norm_product (b : Basis I ℝ E) :
    (∏ i, ‖normalizedAxisBasis b i‖) = (∏ i, (basisAxisScale b i : ℝ)) * ∏ i, ‖b i‖ := by
  simp only [normalizedAxisBasis_norm, Finset.prod_mul_distrib]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NormalizedBasisBounds
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covolume_basis_eq_orthonormal_det [DecidableEq I]
    (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
  classical
  have hvolume : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_def]
    have hfd : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis, hvolume, mul_one]

theorem covolume_basis_scale (o : OrthonormalBasis I ℝ E) (b c : Basis I ℝ E)
    (t : I → ℝ) (ht : ∀ i, 0 ≤ t i) (hc : ∀ i, c i = t i • b i) :
    ZLattice.covolume (Submodule.span ℤ (Set.range c)) =
      (∏ i, t i) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  classical
  rw [covolume_basis_eq_orthonormal_det o c, covolume_basis_eq_orthonormal_det o b]
  rw [show (c : I → E) = (fun i => t i • b i) from funext hc,
    AlternatingMap.map_smul_univ, smul_eq_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => ht i))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthonormal_basis_coordinate_abs_le (o : OrthonormalBasis I ℝ E) (x : E) (i : I) :
    |o.toBasis.equivFun x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le (o.repr x) i
  change |o.repr x i| ≤ ‖x‖
  simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using h

theorem covolume_basis_le_norm_bound (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E)
    {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ≤
      (Fintype.card I).factorial * H ^ Fintype.card I := by
  classical
  rw [covolume_basis_eq_orthonormal_det o b, Basis.det_apply]
  apply matrix_det_abs_le_uniform_bound
  intro i j
  exact (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators Matrix

theorem basis_synthesis_norm_le {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis (Fin n) ℝ E) {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) (x : Fin n → ℝ) :
    ‖b.equivFun.symm x‖ ≤ (n : ℝ) * H * ‖x‖ := by
  rw [Basis.equivFun_symm_apply]
  calc
    _ ≤ ∑ i, ‖x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem basis_coordinates_norm_le_of_covolume {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (o : OrthonormalBasis (Fin n) ℝ E) (b : Basis (Fin n) ℝ E)
    {H κ : ℝ} (hH : 0 ≤ H) (hκ : 0 < κ) (hb : ∀ i, ‖b i‖ ≤ H)
    (hcovol : κ ≤ ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖b.equivFun x‖ ≤ ((n : ℝ) * n.factorial * H ^ (n - 1) / κ) * ‖x‖ := by
  classical
  let A := o.toBasis.toMatrix b
  have hdet : κ ≤ |A.det| := by
    simpa only [covolume_basis_eq_orthonormal_det o b, Basis.det_apply] using hcovol
  have hentry : ∀ i j, |A i j| ≤ H := fun i j =>
    (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)
  have hinv : ∀ i j, |A⁻¹ i j| ≤ (n.factorial : ℝ) * H ^ (n - 1) / κ := by
    intro i j
    simpa only [Fintype.card_fin] using matrix_inverse_entry_abs_le A hentry hκ hdet i j
  have hM : A *ᵥ (b.equivFun x) = o.toBasis.equivFun x :=
    basis_coordinate_matrix_mulVec b o.toBasis.equivFun.toLinearMap x
  have hback : A⁻¹ *ᵥ (o.toBasis.equivFun x) = b.equivFun x := by
    rw [← hM, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (abs_pos.mp (hκ.trans_le hdet))),
      Matrix.one_mulVec]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [← hback, Real.norm_eq_abs]
  change |∑ j, A⁻¹ i j * o.toBasis.equivFun x j| ≤ _
  calc
    _ ≤ ∑ j, |A⁻¹ i j * o.toBasis.equivFun x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((n.factorial : ℝ) * H ^ (n - 1) / κ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hinv i j) (orthonormal_basis_coordinate_abs_le o x j)
        (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalizedAxisBasis_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) =
      (∏ i, (basisAxisScale b i : ℝ)) * ZLattice.covolume (span ℤ (Set.range b)) :=
  covolume_basis_scale o b (normalizedAxisBasis b) (fun i => (basisAxisScale b i : ℝ))
    (fun _ => Nat.cast_nonneg _) (normalizedAxisBasis_apply b)

theorem normalizedAxisBasis_covolume_lower (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {D : ℝ} (hD : 0 < D)
    (hb : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) :
    1 / D ≤ ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hprod : 1 ≤ ∏ i, ‖normalizedAxisBasis b i‖ := by
    apply Finset.one_le_prod
    intro i _
    rw [normalizedAxisBasis_norm]
    exact (basisAxisScale_mul_norm b i).1
  have hupper : (∏ i, ‖normalizedAxisBasis b i‖) ≤
      D * ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
    rw [normalizedAxisBasis_norm_product, normalizedAxisBasis_covolume o b]
    calc
      _ ≤ (∏ i, (basisAxisScale b i : ℝ)) *
          (D * ZLattice.covolume (span ℤ (Set.range b))) :=
        mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      _ = _ := by ring
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using hprod.trans hupper

theorem normalizedAxisBasis_covolume_upper (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B : ℝ} (hb : ∀ i, ‖b i‖ ≤ B) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) ≤
      (n.factorial : ℝ) * (B + 1) ^ n := by
  simpa only [Fintype.card_fin] using covolume_basis_le_norm_bound o (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)

theorem normalizedAxisBasis_coordinates_bound (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖(normalizedAxisBasis b).equivFun x‖ ≤
      ((n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  have h := basis_coordinates_norm_le_of_covolume o (normalizedAxisBasis b)
    (by positivity : 0 ≤ B + 1) (one_div_pos.mpr hD)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)
    (normalizedAxisBasis_covolume_lower o b hD hprod) x
  simpa only [one_div, div_inv_eq_mul] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalizedAxisBasis_synthesis_bound (b : Basis (Fin n) ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (x : Fin n → ℝ) :
    ‖(normalizedAxisBasis b).equivFun.symm x‖ ≤ (n : ℝ) * (B + 1) * ‖x‖ :=
  basis_synthesis_norm_le (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2) x

theorem normalizedAxisBasis_reciprocal_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {q : ℝ}
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    q / (∏ i, (basisAxisScale b i : ℝ)) =
      1 / ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hc := (ZLattice.covolume_pos (span ℤ (Set.range b)) volume).ne'
  have hp : (∏ i, (basisAxisScale b i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i))).ne'
  have heq : q = 1 / ZLattice.covolume (span ℤ (Set.range b)) := (eq_div_iff hc).mpr hq
  rw [heq, normalizedAxisBasis_covolume o b]
  field_simp [hp, hc]

theorem normalizedAxisBasis_covolume_ratio_bounds (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D q : ℝ} (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b)))
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤ q / (∏ i, (basisAxisScale b i : ℝ)) ∧
      q / (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  rw [normalizedAxisBasis_reciprocal_covolume o b hq]
  have hpos := ZLattice.covolume_pos (span ℤ (Set.range (normalizedAxisBasis b))) volume
  refine ⟨div_le_div_of_nonneg_left zero_le_one hpos
    (normalizedAxisBasis_covolume_upper o b hb), ?_⟩
  apply (div_le_iff₀ hpos).mpr
  have h := (div_le_iff₀ hD).mp (normalizedAxisBasis_covolume_lower o b hD hprod)
  simpa only [mul_comm] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedExtendedSiteSection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def columnInclusionMatrix {I K : Type*} [DecidableEq I] (e : K → I) : Matrix I K ℝ :=
  fun i k => if e k = i then 1 else 0

theorem matrix_mul_columnInclusion {I K S : Type*} [Fintype I] [DecidableEq I]
    (E : Matrix S I ℝ) (e : K → I) : E * columnInclusionMatrix e = E.submatrix id e := by
  ext s k
  simp [Matrix.mul_apply, columnInclusionMatrix]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def extendIntegerSiteSection {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) : Matrix I S ℤ :=
  fun i s => ∑ k, if e k = i then T k s else 0

theorem extendIntegerSiteSection_cast {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) :
    Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) =
      columnInclusionMatrix e * Matrix.of (fun k s => (T k s : ℝ)) := by
  ext i s
  simp [extendIntegerSiteSection, columnInclusionMatrix, Matrix.mul_apply]

theorem integerSiteResidual_extend_columns {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S]
    (E₀ : Matrix S K ℤ) (E : Matrix S I ℤ) (e : K → I)
    (hcolumns : E.submatrix id e = E₀) (R : Matrix K I ℝ)
    (himage : Matrix.of (fun s k => (E₀ s k : ℝ)) * R = Matrix.of (fun s i => (E s i : ℝ)))
    (T : Matrix K S ℤ) (q : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (hT : ∀ (x : K → W),
      matrixModuleAction (fun s k => (E₀ s k : ℝ))
        (matrixModuleAction (fun k s => (T k s : ℝ))
          (matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)
    (x : I → W) :
    matrixModuleAction (fun s i => (E s i : ℝ))
      (matrixModuleAction (fun i s => (extendIntegerSiteSection e T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
      (q : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  let E₀' := Matrix.of (fun s k => (E₀ s k : ℝ))
  let E' := Matrix.of (fun s i => (E s i : ℝ))
  let T' := Matrix.of (fun k s => (T k s : ℝ))
  let U' := Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ))
  have hc : E'.submatrix id e = E₀' := by
    ext s k
    exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun (congrFun hcolumns s) k)
  have hET : E' * U' = E₀' * T' := by
    change E' * Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) = E₀' * T'
    rw [extendIntegerSiteSection_cast, ← Matrix.mul_assoc, matrix_mul_columnInclusion, hc]
  have hact (v : S → W) : matrixModuleAction E' (matrixModuleAction U' v) =
      matrixModuleAction E₀' (matrixModuleAction T' v) := by
    rw [matrixModuleAction_mul, hET, ← matrixModuleAction_mul]
  have hfactor : matrixModuleAction E₀' (matrixModuleAction R x) = matrixModuleAction E' x := by
    rw [matrixModuleAction_mul]
    exact congrArg (fun A => matrixModuleAction A x) himage
  change matrixModuleAction E' (matrixModuleAction U' (matrixModuleAction E' x)) =
    (q : ℝ) • matrixModuleAction E' x
  rw [hact, ← hfactor]
  exact hT (matrixModuleAction R x)

theorem integerPeriod_range_le_of_columns {O K I : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [Fintype I]
    (A₀ : Matrix O K ℤ) (A : Matrix O I ℤ) (e : K → I)
    (he : ∀ i k, A i (e k) = A₀ i k) : A₀.mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨k, rfl⟩
  exact ⟨e k, funext (fun i => he i k)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem extendIntegerSiteSection_column_sum {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ ∑ k, |(T k s : ℝ)| := by
  classical
  calc
    _ ≤ ∑ i : I, ∑ k : K, if e k = i then |(T k s : ℝ)| else 0 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [extendIntegerSiteSection, Int.cast_sum]
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    _ = ∑ k : K, ∑ i : I, if e k = i then |(T k s : ℝ)| else 0 := Finset.sum_comm
    _ = _ := by simp

theorem extendIntegerSiteSection_column_sum_bound {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) {B : ℝ} (hT : ∀ k s, |(T k s : ℝ)| ≤ B) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ Fintype.card K * B := by
  apply (extendIntegerSiteSection_column_sum e T s).trans
  calc
    _ ≤ ∑ _k : K, B := Finset.sum_le_sum (fun k _ => hT k s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

noncomputable def cubeMinorProbabilityConstant (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) : ℝ :=
  scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * multivariateSublevelConstant N d

noncomputable def cubeMinorProbabilityScale (O : Type*) [Fintype O] (N d : ℕ) (c₀ : ℝ) : ℝ :=
  (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O

noncomputable def cubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d) (cubeMinorProbabilityScale O N d c₀) η

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

def cubeMinorVariableCount (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) : ℕ :=
  Fintype.card O * (h * (Fintype.card α + 1))

def cubeMinorDegree (O : Type*) [Fintype O] (h : ℕ) : ℕ :=
  max 1 (Fintype.card O * (h - 1))

noncomputable def canonicalCubeMinorThreshold (J O α : Type*)
    [Fintype J] [Fintype O] [Fintype α] [DecidableEq α] (h : ℕ) (c₀ η : ℝ) : ℝ :=
  cubeMinorThreshold J O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ η

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientScaleGap
namespace OAI

section

namespace Erdos3

theorem exists_unoccupied_coefficient_gap {I : Type*} [Fintype I]
    (x : I → ℝ) (b : I → ℕ → ℝ) (hb : ∀ i, Monotone (b i)) :
    ∃ j : Fin (Fintype.card I + 1), ∀ i, ¬(b i j.val < x i ∧ x i < b i (j.val + 1)) := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a c hac
    apply Fin.ext
    rcases lt_trichotomy a.val c.val with hlt | heq | hgt
    · have hstep := hb (f a) (show a.val + 1 ≤ c.val by omega)
      have hc := (hf c).1
      rw [← hac] at hc
      linarith [(hf a).2]
    · exact heq
    · have hstep := hb (f c) (show c.val + 1 ≤ a.val by omega)
      have ha := (hf a).1
      rw [hac] at ha
      linarith [(hf c).2]
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

theorem exists_integer_coefficient_scale_gap {I : Type*} [Fintype I]
    (K : I → ℝ) (h : I → ℕ) (L₀ A : ℕ) (hL₀ : 0 < L₀) (hA : 1 ≤ A) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧ L ≤ L₀ * A ^ Fintype.card I ∧
      ∀ i, (L : ℝ) ^ h i < K i → ((A : ℝ) * L) ^ h i ≤ K i := by
  let b : I → ℕ → ℝ := fun i j => ((L₀ * A ^ j : ℕ) : ℝ) ^ h i
  have hb : ∀ i, Monotone (b i) := by
    intro i j k hjk
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega : 0 < A) hjk)
  obtain ⟨j, hj⟩ := exists_unoccupied_coefficient_gap K b hb
  refine ⟨L₀ * A ^ j.val, Nat.mul_pos hL₀ (pow_pos (by omega) _), ?_, ?_, ?_⟩
  · have hp : 1 ≤ A ^ j.val := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    nlinarith
  · exact Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ Fintype.card I))
  · intro i hi
    have hbound : b i (j.val + 1) ≤ K i := le_of_not_gt (fun hlt => hj i ⟨hi, hlt⟩)
    have he : ((L₀ * A ^ (j.val + 1) : ℕ) : ℝ) = (A : ℝ) * (L₀ * A ^ j.val : ℕ) := by
      push_cast
      rw [pow_succ]
      ring
    simpa only [b, he] using hbound

theorem coefficient_gap_principal_width {K L A γ : ℝ} {h : ℕ}
    (hL : 0 < L) (hA : 1 ≤ A) (hγ : 0 < γ) (hh : 1 ≤ h)
    (hgap : (A * L) ^ h ≤ K)
    (hwidth : 16 * (probabilityProfileLipschitz : ℝ) ≤ γ * A) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / L ^ h) := by
  have hpow : A ≤ A ^ h := by simpa only [pow_one] using pow_le_pow_right₀ hA hh
  have hratio : A ≤ K / L ^ h := (le_div_iff₀ (pow_pos hL h)).mpr (by
    calc
      A * L ^ h ≤ A ^ h * L ^ h := mul_le_mul_of_nonneg_right hpow (pow_pos hL h).le
      _ = (A * L) ^ h := (mul_pow A L h).symm
      _ ≤ K := hgap)
  have hm := mul_le_mul_of_nonneg_left hratio hγ.le
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTensorApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_prod_sub_prod_le_sum_error {I : Type*} (S : Finset I) (f g : I → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ B ^ S.card * ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hf hg
    have hrec := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _j ∈ S, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
        _ = _ := by simp
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Finset.sum_insert hi]
    calc
      _ = ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
          (f i - g i) * ∏ j ∈ S, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ S, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)) ((f i - g i) * ∏ j ∈ S, g j)
      _ ≤ B * (B ^ S.card * ∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card :=
        add_le_add (mul_le_mul (hf i (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
      _ = B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card := by
        rw [pow_succ]
        ring
      _ ≤ B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB (Nat.le_succ _)) (norm_nonneg _))
      _ = _ := by ring

theorem mean_prod_error_le {I X : Type*} [Fintype I] [Fintype X]
    (f g : I → X → ℂ) {B ε : ℝ} (hB : 1 ≤ B)
    (hf : ∀ i x, ‖f i x‖ ≤ B) (hg : ∀ i x, ‖g i x‖ ≤ B)
    (herr : ∀ i, (𝔼 x, ‖f i x - g i x‖) ≤ ε) :
    (𝔼 x, ‖(∏ i, f i x) - ∏ i, g i x‖) ≤ B ^ Fintype.card I * ((Fintype.card I : ℝ) * ε) := by
  calc
    _ ≤ 𝔼 x, B ^ Fintype.card I * ∑ i, ‖f i x - g i x‖ :=
      Finset.expect_le_expect (fun x _ => by
        simpa only [Finset.card_univ] using norm_prod_sub_prod_le_sum_error Finset.univ
          (fun i => f i x) (fun i => g i x) hB (fun i _ => hf i x) (fun i _ => hg i x))
    _ = B ^ Fintype.card I * ∑ i, 𝔼 x, ‖f i x - g i x‖ := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ B ^ Fintype.card I * ∑ _ : I, ε :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i))
        (pow_nonneg (zero_le_one.trans hB) _)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerGridStart (a L : ℕ) : ℕ := L * (a / L + 1)

def integerGridEnd (b L : ℕ) : ℕ := L * (b / L)

theorem integerGridStart_bounds (a : ℕ) {L : ℕ} (hL : 0 < L) :
    a ≤ integerGridStart a L ∧ integerGridStart a L ≤ a + L := by
  constructor
  · exact (Nat.lt_mul_div_succ a hL).le
  · dsimp [integerGridStart]
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self a L) L

theorem integerGridEnd_bounds (b : ℕ) {L : ℕ} (hL : 0 < L) :
    integerGridEnd b L ≤ b ∧ b < integerGridEnd b L + L := by
  exact ⟨by simpa only [integerGridEnd, Nat.mul_comm] using Nat.div_mul_le_self b L,
    Nat.lt_mul_div_self_add hL⟩

theorem integer_grid_interval_geometry (a len : ℕ) {L : ℕ} (hL : 0 < L)
    (hsmall : 4 * L ≤ len) :
    a ≤ integerGridStart a L ∧ integerGridEnd (a + len) L ≤ a + len ∧
      integerGridStart a L < integerGridEnd (a + len) L ∧
      integerGridEnd (a + len) L - integerGridStart a L ≤ len ∧
      len ≤ 2 * (integerGridEnd (a + len) L - integerGridStart a L) ∧
      len ≤ (integerGridEnd (a + len) L - integerGridStart a L) + 2 * L := by
  have hs := integerGridStart_bounds a hL
  have he := integerGridEnd_bounds (a + len) hL
  omega

theorem norm_sum_subset_card_loss {α : Type*} [DecidableEq α]
    {S T : Finset α} (hTS : T ⊆ S) (f : α → ℂ) (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) :
    ‖∑ x ∈ S, f x‖ ≤ ‖∑ x ∈ T, f x‖ + (S.card : ℝ) - (T.card : ℝ) := by
  have hsum := Finset.sum_sdiff (f := f) hTS
  have hb : ‖∑ x ∈ S \ T, f x‖ ≤ ((S \ T).card : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa using Finset.sum_le_sum (fun x hx => hf x (Finset.mem_sdiff.mp hx).1)
  have hc : ((S \ T).card : ℝ) + (T.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have hn := norm_add_le (∑ x ∈ S \ T, f x) (∑ x ∈ T, f x)
  rw [hsum] at hn
  linarith only [hb, hc, hn]

theorem integer_grid_interval_correlation (a len : ℕ) {L : ℕ} (hL : 0 < L)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hsmall : 4 * (L : ℝ) ≤ ρ * len)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n‖) :
    ρ / 2 ≤ ‖𝔼 n ∈ Finset.Ico (integerGridStart a L : ℤ)
      (integerGridEnd (a + len) L : ℤ), f n‖ := by
  have hsmallNat : 4 * L ≤ len := by
    have h := hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg len) hρone)
    exact_mod_cast h
  obtain ⟨hstart, hend, hpos, hlenle, _, hloss⟩ := integer_grid_interval_geometry a len hL hsmallNat
  let S := Finset.Ico (a : ℤ) (a + len)
  let T := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
  let d := integerGridEnd (a + len) L - integerGridStart a L
  have hTS : T ⊆ S := by
    intro n hn
    simp only [S, T, Finset.mem_Ico] at hn ⊢
    constructor <;> omega
  have hScard : S.card = len := by simp [S, Int.card_Ico]
  have hTcard : T.card = d := by
    simp only [T, Int.card_Ico]
    rw [← Int.natCast_sub hpos.le, Int.toNat_natCast]
  have hbound := norm_sum_subset_card_loss hTS f (fun n _ => hf n)
  rw [← Finset.card_mul_expect S f, ← Finset.card_mul_expect T f] at hbound
  simp only [norm_mul, Complex.norm_natCast, hScard, hTcard] at hbound
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.sub_pos_of_lt hpos
  have hdlen : (d : ℝ) ≤ len := by exact_mod_cast hlenle
  have hlossR : (len : ℝ) ≤ d + 2 * L := by exact_mod_cast hloss
  have hcor := mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg len : (0 : ℝ) ≤ len)
  change ρ / 2 ≤ ‖𝔼 n ∈ T, f n‖
  nlinarith only [hbound, hcor, hsmall, hd, hdlen, hlossR, hρ]

end Erdos3

end

section

namespace Erdos3

theorem exists_exp_integer_grid_scale {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ)) :
    ∃ L : ℕ, 0 < L ∧ 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N ∧
      ((N / L + 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 5) := by
  let x := Real.exp (-(2 * p)) * N / 8
  let L := ⌊x⌋₊
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have h16 : (16 : ℝ) ≤ Real.exp 8 :=
    (by norm_num : (16 : ℝ) ≤ 2 ^ 8).trans (two_pow_le_exp_of_le 8 le_rfl)
  have hscaled : Real.exp 8 ≤ Real.exp (-(2 * p)) * N := by
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (2 * p + 8) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)
  have hx2 : 2 ≤ x := by dsimp [x]; linarith only [h16, hscaled]
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le hx0
  have hlt : x < (L : ℝ) + 1 := Nat.lt_floor_add_one x
  have hL : 0 < L := by
    have : (0 : ℝ) < L := by linarith only [hx2, hlt]
    exact_mod_cast this
  have hhalf : x ≤ 2 * (L : ℝ) := by linarith only [hx2, hlt]
  have hupper : 4 * (L : ℝ) ≤ Real.exp (-(2 * p)) * N := by
    dsimp [x] at hfloor hx0
    linarith only [hfloor, hx0]
  have hlower : Real.exp (-(2 * p)) * N ≤ 16 * (L : ℝ) := by
    dsimp [x] at hhalf
    linarith only [hhalf]
  have hNL : (N : ℝ) ≤ 16 * Real.exp (2 * p) * L := by
    calc
      _ = Real.exp (2 * p) * (Real.exp (-(2 * p)) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (2 * p) * (16 * L) :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
      _ = _ := by ring
  have hdiv : ((N / L : ℕ) : ℝ) ≤ 16 * Real.exp (2 * p) :=
    Nat.cast_div_le.trans ((div_le_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr hNL)
  have h18 : (18 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (18 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  refine ⟨L, hL, hupper, ?_⟩
  calc
    _ = ((N / L : ℕ) : ℝ) + 2 := by norm_cast
    _ ≤ 18 * Real.exp (2 * p) := by
      have h1 := Real.one_le_exp (show 0 ≤ 2 * p by positivity)
      linarith only [hdiv, h1]
    _ ≤ Real.exp 5 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right h18 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_integer_interval {G : Type*} {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ))
    (H : Finset G) (hH : H.Nonempty) (start len : G → ℕ)
    (hend : ∀ t ∈ H, start t + len t ≤ N)
    (hshort : ∀ t ∈ H, 2 * ((len t : ℤ) - 1) < N)
    (hlength : ∀ t ∈ H, Real.exp (-p) * N ≤ (len t : ℝ))
    (f : G → ℤ → ℂ) (hf : ∀ t ∈ H, ∀ n, ‖f t n‖ ≤ 1)
    (hcorr : ∀ t ∈ H, Real.exp (-p) ≤
      ‖𝔼 n ∈ Finset.Ico (start t : ℤ) (start t + len t), f t n‖) :
    ∃ S : Finset G, S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(4 * p + 10)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∃ a d : ℕ, 0 < d ∧ a + d ≤ N ∧ 2 * ((d : ℤ) - 1) < N ∧
        Real.exp (-(p + 1)) * N ≤ (d : ℝ) ∧
        ∀ t ∈ S, Real.exp (-(p + 1)) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + d), f t n‖ := by
  classical
  obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
  have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hp])
  have hsmall (t : G) (ht : t ∈ H) : 4 * (L : ℝ) ≤ Real.exp (-p) * len t := by
    apply hscale.trans
    calc
      _ = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlength t ht) (Real.exp_nonneg _)
  have hsmallNat (t : G) (ht : t ∈ H) : 4 * L ≤ len t := by
    exact_mod_cast (hsmall t ht).trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
  let P := Fin (N / L + 2) × Fin (N / L + 2)
  let rel (t : G) (_ : Unit) (c : P) : Prop :=
    start t / L + 1 = c.1.val ∧ (start t + len t) / L = c.2.val
  have hchoice : ∀ t ∈ H, ∀ u, ∃ c, rel t u c := by
    intro t ht _
    have hs : start t ≤ N := by have hh := hend t ht; omega
    have hsd : start t / L ≤ N / L := Nat.div_le_div_right hs
    have hed : (start t + len t) / L ≤ N / L := Nat.div_le_div_right (hend t ht)
    exact ⟨(⟨start t / L + 1, by omega⟩, ⟨(start t + len t) / L, by omega⟩), rfl, rfl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (4 * p + 10) := by
    simp only [P, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
        mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, S, hSH, hS, hSdense, hfixed⟩ := exists_large_fixed_choices H hH rel hchoice hcount
  let a := L * (c ()).1.val
  let b := L * (c ()).2.val
  let d := b - a
  have hround (t : G) (ht : t ∈ S) :
      integerGridStart (start t) L = a ∧ integerGridEnd (start t + len t) L = b := by
    obtain ⟨hs, he⟩ := hfixed t ht ()
    constructor
    · dsimp only [integerGridStart, a]
      rw [hs]
    · dsimp only [integerGridEnd, b]
      rw [he]
  obtain ⟨t0, ht0⟩ := hS
  have ht0H := hSH ht0
  have hgeom := integer_grid_interval_geometry (start t0) (len t0) hL (hsmallNat t0 ht0H)
  rw [(hround t0 ht0).1, (hround t0 ht0).2] at hgeom
  obtain ⟨_, hb, hab, hdlen, hhalf, _⟩ := hgeom
  have had : a + d = b := Nat.add_sub_of_le hab.le
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hbN : b ≤ N := hb.trans (hend t0 ht0H)
  have hdshort : 2 * ((d : ℤ) - 1) < N := by
    have hs := hshort t0 ht0H
    change d ≤ len t0 at hdlen
    omega
  have hhalfR : (len t0 : ℝ) ≤ 2 * d := by exact_mod_cast hhalf
  have hvol : Real.exp (-p) / 2 * N ≤ (d : ℝ) := by
    have hv := hlength t0 ht0H
    nlinarith only [hv, hhalfR]
  have hthreshold : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
  refine ⟨S, hSH, ⟨t0, ht0⟩, ?_, a, d, hd, ?_, hdshort, ?_, ?_⟩
  · simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  · omega
  · exact (mul_le_mul_of_nonneg_right hthreshold (Nat.cast_nonneg _)).trans hvol
  · intro t ht
    have hc := integer_grid_interval_correlation (start t) (len t) hL
      (Real.exp_pos (-p)) hrho (hsmall t (hSH ht)) (f t) (hf t (hSH ht)) (hcorr t (hSH ht))
    rw [(hround t ht).1, (hround t ht).2] at hc
    have hupp : (a : ℤ) + d = b := by exact_mod_cast had
    simpa only [hupp] using hthreshold.trans hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalGridMajorSet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rationalGridMajorSet (M Q H : ℕ) : Finset (Fin M) :=
  (Finset.range (Q + 1)).biUnion fun d =>
    (Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)).biUnion fun a =>
      frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H

noncomputable def rationalGridMajorBox (J : Type*) [Fintype J] [DecidableEq J]
    (M Q H : ℕ) : Finset (J → Fin M) :=
  Fintype.piFinset (fun _ => rationalGridMajorSet M Q H)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

noncomputable def polynomialGridCover (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) (C : ℝ) (r : ℕ) (ζ : ℝ) : Finset (J → Fin M) :=
  rationalGridMajorBox J M ⌈C / ζ ^ r⌉₊ ⌈C / ζ ^ r⌉₊

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def lengthAwareSpectrumCover {K : Type*} [Fintype K]
    (C L : ℝ) (c : ℕ) (cover : ℝ → Finset K) (ζ : ℝ) : Finset K := by
  classical
  exact if C / ζ ^ c ≤ L then cover ζ else Finset.univ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

noncomputable def localizedMajorArcBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  multiaffineBiasBudget n (localizationThreshold U ζ (n + 1))

noncomputable def localizedMajorArcLengthBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizationLengthBudget U (localizationThreshold U ζ (n + 1))
    (localizedMajorArcBudget n U ζ + 1)

noncomputable def localizedMajorArcErrorBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizedMajorArcBudget n U ζ *
    (localizationLengthBudget U (localizationThreshold U ζ (n + 1)) 1) ^ (n + 1)

theorem localizedMajorArcBudget_pos (n : ℕ) {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) :
    0 < localizedMajorArcBudget n U ζ :=
  multiaffineBiasBudget_pos n (localizationThreshold_pos hU hζ (n + 1))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

def majorArcBiasExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

noncomputable def majorArcBiasConstant (n : ℕ) (U : ℝ) : ℝ :=
  ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
    (2 * U ^ 2) ^ ((n + 1) * majorArcBiasExponent n)

noncomputable def majorArcLocalizationConstant (n : ℕ) (U : ℝ) : ℝ :=
  256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2)

def majorArcLengthExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2

noncomputable def majorArcLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcLocalizationConstant n U * (majorArcBiasConstant n U + 1)

def majorArcErrorExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2 * (n + 1)

noncomputable def majorArcErrorConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcBiasConstant n U * majorArcLocalizationConstant n U ^ (n + 1)

end Erdos3

end

section

namespace Erdos3

def majorArcCoverExponent (n j : ℕ) : ℕ :=
  majorArcBiasExponent n * j + majorArcErrorExponent n

noncomputable def majorArcCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  1 + (majorArcBiasConstant n U * U ^ (n + 1)) ^ j + V * majorArcErrorConstant n U

def majorArcSpectrumExponent (n j : ℕ) : ℕ := 4 * majorArcCoverExponent n j * j

noncomputable def majorArcSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * majorArcCoverConstant n j U V ^ 4) ^ j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def uniformSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) + 1

noncomputable def uniformBlockSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (majorArcLengthConstant n U) L (majorArcLengthExponent n)
    (polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J))) ζ

noncomputable def uniformBlockSpectrumCardBudget (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  majorArcSpectrumConstant n j U V / ζ ^ majorArcSpectrumExponent n j +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

noncomputable def uniformBlockSpectrumAccuracyConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j +
    W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformCharacterDenominatorBound (n j t : ℕ) (U V W ζ : ℝ) : ℝ :=
  1 + (3 * majorArcCoverConstant n j U V) ^ j / ζ ^ (majorArcCoverExponent n j * j) +
    W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t)

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformScaledRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d⌉₊ : ℝ)

noncomputable def uniformScaledRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((uniformScaledRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem card_integerProgressionSupport (c : ℤ) (m H : ℕ) (hm : 0 < m) :
    (integerProgressionSupport c (m : ℤ) H).card = H := by
  unfold integerProgressionSupport
  rw [card_translateSupport, Finset.card_image_of_injective]
  · simp
  · intro x y h
    apply mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)
    exact h

theorem integerProgressionSupport_point (c : ℤ) (m H : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < H) :
    c + (m : ℤ) * j ∈ integerProgressionSupport c (m : ℤ) H := by
  apply (mem_integerProgressionSupport_iff c m H hm _).mpr
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hj' : (j : ℤ) < H := by exact_mod_cast hj
  refine ⟨?_, ?_, ?_⟩
  · have := mul_nonneg hm'.le (Int.natCast_nonneg j)
    omega
  · push_cast
    nlinarith
  · simp

theorem progression_endpoint_bounds {L m H : ℕ} {c δ : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) (hδ : 0 < δ)
    (hc : 0 ≤ c) (hlast : c + (m : ℝ) * ((H : ℝ) - 1) < L)
    (hdense : δ * L ≤ H) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |c| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hmlast : (m : ℝ) * ((H : ℝ) - 1) < L := by linarith
  have hmL : (m : ℝ) < L := by nlinarith
  have hwidth : (m : ℝ) * H < 2 * L := by nlinarith
  have hlower : δ * L ≤ (m : ℝ) * H := hdense.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) H])
  have hprod : ((m : ℝ) * δ) * L < 2 * L := by
    have he := mul_le_mul_of_nonneg_left hdense (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [he, hwidth]
  have hstride : (m : ℝ) < 2 / δ :=
    (lt_div_iff₀ hδ).mpr ((mul_lt_mul_iff_left₀ hL0).mp hprod)
  have hcL : c ≤ L := by nlinarith
  have hLwidth : (L : ℝ) ≤ ((m : ℝ) * H) / δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hlower])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hlower
  · simpa only [Nat.cast_mul] using hwidth
  · exact_mod_cast hstride.le.trans (Nat.le_ceil (2 / δ))
  · rw [abs_of_nonneg hc]
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_comm] using hcL.trans hLwidth

theorem progression_slice_geometry {L m H : ℕ} (c : ℤ)
    (hL : 0 < L) (hm : 0 < m) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (m : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (m : ℤ) H).card : ℝ)) :
    δ * L ≤ (m * H : ℕ) ∧ ((m * H : ℕ) : ℝ) < 2 * L ∧
      m ≤ ⌈2 / δ⌉₊ ∧ |(c : ℝ)| ≤ δ⁻¹ * (m * H : ℕ) := by
  have hbase := hsubset (integerProgressionSupport_point c m H hm 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hc0 : 0 ≤ c := by simpa only [Nat.cast_zero, mul_zero, add_zero] using (Finset.mem_Ico.mp hbase).1
  have hh : (c : ℝ) + (m : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] at hh
  rw [card_integerProgressionSupport c m H hm] at hdense
  exact progression_endpoint_bounds hL hm hH hδ (by exact_mod_cast hc0) hh hdense

end Erdos3

end

section

namespace Erdos3

theorem integerProgressionSupport_reindex (r m a H : ℕ) :
    integerProgressionSupport ((r : ℤ) + m * a) m H =
      (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have he : Finset.Ico (a : ℤ) (a + H) =
      (Finset.Ico (0 : ℤ) H).image (fun x => (a : ℤ) + x) := by
    simpa only [add_zero] using (Finset.image_add_left_Ico (0 : ℤ) H (a : ℤ)).symm
  rw [he, Finset.image_image]
  unfold integerProgressionSupport translateSupport
  rw [Finset.image_image]
  congr 1
  funext x
  change (r : ℤ) + m * a + m * x = r + m * (a + x)
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem integerProgressionSupport_singleton (c m : ℤ) :
    integerProgressionSupport c m 1 = {c} := by
  have hz : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  simp [integerProgressionSupport, translateSupport, hz, integerStrideHom]

theorem exists_same_stride_progression_reindex {N m H : ℕ} (c : ℤ)
    (hm : 0 < m) (hH : 0 < H)
    (hsub : integerProgressionSupport c m H ⊆ Finset.Ico (0 : ℤ) N) :
    ∃ r a : ℕ, r < m ∧ a + H ≤ N ∧
      integerProgressionSupport c m H =
        (Finset.Ico (a : ℤ) (a + H)).image (fun x => (r : ℤ) + m * x) := by
  have hbase := hsub (integerProgressionSupport_point c m H hm 0 hH)
  simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
  have hc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hbase.1
  let a := c.toNat / m
  let r := c.toNat % m
  have ha : a ≤ c.toNat := Nat.div_le_self _ _
  have hlast := hsub (integerProgressionSupport_point c m H hm (H - 1) (by omega))
  have hlastN : c.toNat + m * (H - 1) < N := by
    have ht := (Finset.mem_Ico.mp hlast).2
    rw [← hc] at ht
    exact_mod_cast ht
  have hmul : H - 1 ≤ m * (H - 1) := by nlinarith
  have hrepr : c = (r : ℤ) + m * a := by
    rw [← hc]
    exact_mod_cast (Nat.mod_add_div c.toNat m).symm
  refine ⟨r, a, Nat.mod_lt _ hm, by omega, ?_⟩
  rw [hrepr]
  exact integerProgressionSupport_reindex r m a H

theorem exists_bounded_common_stride_reindex {I : Type*} (N H : I → ℕ) (c : I → ℤ)
    {m : ℕ} (hm : 0 < m) (hH : ∀ i, 0 < H i) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsub : ∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i))
    (hdense : ∀ i, δ * N i ≤ (H i : ℝ)) :
    ∃ d : ℕ, ∃ r a : I → ℕ, 0 < d ∧ d ≤ ⌈2 / δ⌉₊ ∧
      ∀ i, r i < ⌈2 / δ⌉₊ ∧ a i + H i ≤ N i ∧
        integerProgressionSupport (c i) m (H i) =
          (Finset.Ico (a i : ℤ) (a i + H i)).image (fun x => (r i : ℤ) + d * x) := by
  classical
  by_cases hlong : ∃ i, 2 ≤ H i
  · obtain ⟨i, hi⟩ := hlong
    have hbase := hsub i (integerProgressionSupport_point (c i) m (H i) hm 0 (hH i))
    have hNi : 0 < N i := by
      simp only [Nat.cast_zero, mul_zero, add_zero, Finset.mem_Ico] at hbase
      omega
    have hgeom := progression_slice_geometry (c i) hNi hm hi hδ (hsub i)
      (by simpa only [card_integerProgressionSupport (c i) m (H i) hm] using hdense i)
    choose r a hr ha he using fun i => exists_same_stride_progression_reindex (c i) hm (hH i) (hsub i)
    exact ⟨m, r, a, hm, hgeom.2.2.1, fun i => ⟨(hr i).trans_le hgeom.2.2.1, ha i, he i⟩⟩
  · have hsingle (i : I) : H i = 1 := by have := hH i; have := not_exists.mp hlong i; omega
    have he (i : I) : integerProgressionSupport (c i) m (H i) =
        integerProgressionSupport (c i) 1 (H i) := by simp only [hsingle i, integerProgressionSupport_singleton]
    have hsub1 (i : I) : integerProgressionSupport (c i) 1 (H i) ⊆ Finset.Ico (0 : ℤ) (N i) :=
      he i ▸ hsub i
    choose r a hr ha he' using fun i => exists_same_stride_progression_reindex (m := 1)
      (c i) zero_lt_one (hH i) (hsub1 i)
    have hM : 1 ≤ ⌈2 / δ⌉₊ := by
      have h1 : (1 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
      exact_mod_cast h1.trans (Nat.le_ceil _)
    exact ⟨1, r, a, zero_lt_one, hM, fun i => ⟨(hr i).trans_le hM, ha i, (he i).trans (he' i)⟩⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

def integerAffineMap (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) : ℤ :=
  b i + ∑ j, A i j * x j

noncomputable def integerAffinePolynomial (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    MvPolynomial τ ℚ :=
  MvPolynomial.C (b i : ℚ) + ∑ j, MvPolynomial.C (A i j : ℚ) * MvPolynomial.X j

theorem integerAffinePolynomial_support (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    integerAffinePolynomial A b i ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (b i : ℚ)
  · apply Submodule.sum_mem
    intro j _
    have hx : (MvPolynomial.X j : MvPolynomial τ ℚ) ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
      simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
        weightedSupportLE_monomial (fun _ : τ => 1) (Finsupp.single j 1) (1 : ℚ)
    simpa only [zero_add] using weightedSupportLE_mul (weightedSupportLE_C _ 0 (A i j : ℚ)) hx

theorem integerAffinePolynomial_eval (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) :
    MvPolynomial.aeval (fun j => (x j : ℚ)) (integerAffinePolynomial A b i) =
      (integerAffineMap A b x i : ℚ) := by
  simp [integerAffinePolynomial, integerAffineMap]

theorem integerLinearForm_eq_sum [DecidableEq τ] (f : (τ → ℤ) →+ ℤ) (x : τ → ℤ) :
    f x = ∑ j, f (Pi.single j 1) * x j := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  change x j * f (Pi.single j 1) = f (Pi.single j 1) * x j
  exact mul_comm _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i => integerProgressionSupport (c i) m (H i))

theorem commonStrideBox_card {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) :
    (commonStrideBox c m H).card = ∏ i, H i := by
  simp only [commonStrideBox, Fintype.card_piFinset, card_integerProgressionSupport _ _ _ hm]

theorem commonStrideBox_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) (hH : ∀ i, 0 < H i) :
    (commonStrideBox c m H).Nonempty := by
  apply Fintype.piFinset_nonempty.mpr
  intro i
  apply Finset.card_pos.mp
  simpa only [card_integerProgressionSupport _ _ _ hm] using hH i

theorem affine_interval_eq_progression (r m a b : ℕ) :
    (Finset.Ico (a : ℤ) (b : ℤ)).image (fun x => (r : ℤ) + m * x) =
      integerProgressionSupport ((r : ℤ) + m * a) m (b - a) := by
  by_cases hab : a ≤ b
  · have he : (a : ℤ) + (b - a : ℕ) = b := by omega
    rw [integerProgressionSupport_reindex, he]
  · have hi : Finset.Ico (a : ℤ) (b : ℤ) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp [Nat.sub_eq_zero_of_le (by omega : b ≤ a), hi, integerProgressionSupport, translateSupport]

theorem commonStrideBox_eq_image {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) :
    commonStrideBox c m H = (integerBox H).image (fun x i => c i + (m : ℤ) * x i) := by
  simp only [commonStrideBox, integerProgressionSupport, translateSupport, Finset.image_image]
  exact Fintype.piFinset_image (fun i x => c i + (m : ℤ) * x) (fun i => Finset.Ico (0 : ℤ) (H i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def commonStridePoint {I : Type*} (c : I → ℤ) (m : ℕ) (x : I → ℤ) : I → ℤ :=
  fun i => c i + (m : ℤ) * x i

def commonStrideIndex {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ) : I → ℤ :=
  fun i => (y i - c i) / (m : ℤ)

theorem commonStrideIndex_point {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) (x : I → ℤ) :
    commonStrideIndex c m (commonStridePoint c m x) = x := by
  funext i
  simp only [commonStrideIndex, commonStridePoint, add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)

theorem commonStridePoint_injective {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) :
    Function.Injective (commonStridePoint c m) :=
  Function.LeftInverse.injective (commonStrideIndex_point c hm)

theorem commonStridePoint_mem {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) {x : I → ℤ} (hx : x ∈ integerBox H) :
    commonStridePoint c m x ∈ commonStrideBox c m H := by
  rw [commonStrideBox_eq_image]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem integerAffineMap_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (a s x : I → ℤ) :
    integerAffineMap (fun i j => if i = j then s i else 0) a x = fun i => a i + s i * x i := by
  funext i
  simp [integerAffineMap, ite_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonStrideCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteCorrelation_commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → ℤ) {d : ℕ} (hd : 0 < d) (K : I → ℕ) (f g : (I → ℤ) → ℂ) :
    finiteCorrelation (commonStrideBox b d K) f g =
      finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
        (fun x => g (commonStridePoint b d x)) := by
  rw [commonStrideBox_eq_image]
  unfold finiteCorrelation
  exact Finset.expect_image (commonStridePoint_injective b hd).injOn

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

def lowDegreeCoordinateSets (b : ℕ) : Finset (Finset I) :=
  (Finset.range (b + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

def restrictedDegreeSupports (J : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => S.card ≤ b)

def degreeTailSupports (J : Finset ι) (r b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => r < S.card ∧ S.card ≤ b)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubsetAlternatingInversion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

noncomputable def subsetAlternatingTransform (F : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * F (S \ U)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConditioningShellError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditioningCoreSupports (I : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => B.card ≤ b - I.card)

def conditioningShellSupports (I A : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => b - I.card < B.card ∧ A.card + B.card ≤ b)

variable {X Y : ι → Type*}
  [∀ i, Fintype (X i)]
  [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)}
  {ν : ∀ i, FiniteProbabilityWeights (Y i)}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}
  [Fintype ι]
  [DecidableEq ι]
  {X Y : ι → Type*}
  [∀ i, Fintype (X i)]
  [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)}
  {ν : ∀ i, FiniteProbabilityWeights (Y i)}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanDerivativeCovolume
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem shortVectorLattice_covolume_le
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  let d := finrank ℝ (shortVectorSpan Λ R)
  have hpack := shortVectorLattice_covolume_packing Λ R P hP
  have hvol := euclidean_closedBall_volume_le (E := shortVectorSpan Λ R)
    (R + (d : ℝ) * R / 2) (by positivity)
  have he : 2 * (R + (d : ℝ) * R / 2) = ((d : ℝ) + 2) * R := by ring
  rw [he] at hvol
  have hcov : 0 ≤ ZLattice.covolume (shortVectorLattice Λ R) :=
    (ZLattice.covolume_pos (shortVectorLattice Λ R) volume).le
  apply (le_div_iff₀ hN).mpr
  calc
    ZLattice.covolume (shortVectorLattice Λ R) * N =
        N * ZLattice.covolume (shortVectorLattice Λ R) := mul_comm _ _
    _ ≤ (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) :=
      mul_le_mul_of_nonneg_right hcard hcov
    _ ≤ _ := hpack.trans hvol

theorem shortVectorLattice_covolume_le_of_points
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset E) (hP : ∀ p ∈ P, p ∈ Λ ∧ ‖p‖ ≤ R) (hcard : N ≤ (P.card : ℝ)) :
    ZLattice.covolume (shortVectorLattice Λ R) ≤
      (((finrank ℝ (shortVectorSpan Λ R) : ℝ) + 2) * R) ^
        finrank ℝ (shortVectorSpan Λ R) / N := by
  classical
  let f : P → shortVectorLattice Λ R := fun p =>
    ⟨⟨p.val, mem_shortVectorSpan Λ R (hP p.val p.property).1 (hP p.val p.property).2⟩,
      (hP p.val p.property).1⟩
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun z : shortVectorLattice Λ R => z.val.val) hpq)
  let Q : Finset (shortVectorLattice Λ R) := Finset.univ.image f
  have hQcard : Q.card = P.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hQ : ∀ q ∈ Q, ‖(q : shortVectorSpan Λ R)‖ ≤ R := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hP p.val p.property).2
  exact shortVectorLattice_covolume_le Λ R N hR hN Q hQ (hQcard ▸ hcard)

end Erdos3

end

section

namespace Erdos3

open Module

theorem euclideanDerivativeLattice_covolume_le
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R N : ℝ) (hR : 0 ≤ R) (hN : 0 < N)
    (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R)
    (hcard : N ≤ (P.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((finrank ℝ (shortVectorSpan Λ ρ) : ℝ) + 2) * ρ) ^
        finrank ℝ (shortVectorSpan Λ ρ) / N := by
  obtain ⟨Q, hQcard, hQ⟩ := exists_bounded_euclideanDerivativeLattice_family
    T hT scale hscale Y A l hl R P hP
  apply shortVectorLattice_covolume_le_of_points _ _ N
    (mul_nonneg (Nat.cast_nonneg _) hR) hN Q hQ
  simpa only [hQcard] using hcard

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteClassifiedRepresentatives
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_indexed_representative_enumeration
    {Γ α : Type*} [Fintype Γ] (valid : Γ → α → Prop) (rel : Γ → α → α → Prop)
    {B : ℝ}
    (hbranch : ∀ i, ∃ n : ℕ, (n : ℝ) ≤ B ∧ ∃ candidate : Fin n → α,
      (∀ j, valid i (candidate j)) ∧
      ∀ x, valid i x → ∃ j, rel i (candidate j) x) :
    ∃ n : ℕ, (n : ℝ) ≤ Fintype.card Γ * B ∧
      ∃ candidate : Fin n → Γ × α,
        (∀ j, valid (candidate j).1 (candidate j).2) ∧
        ∀ i x, valid i x → ∃ j,
          (candidate j).1 = i ∧ rel i (candidate j).2 x := by
  classical
  choose n hn candidate hvalid hcover using hbranch
  let J := Σ i : Γ, Fin (n i)
  let e := Fintype.equivFin J
  let combined : Fin (Fintype.card J) → Γ × α :=
    fun j => ((e.symm j).1, candidate (e.symm j).1 (e.symm j).2)
  refine ⟨Fintype.card J, ?_, combined, ?_, ?_⟩
  · change ((Fintype.card (Σ i : Γ, Fin (n i)) : ℕ) : ℝ) ≤ _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_sum]
    calc
      (∑ i, (n i : ℝ)) ≤ ∑ _i : Γ, B := Finset.sum_le_sum (fun i _ => hn i)
      _ = Fintype.card Γ * B := by simp
  · intro j
    exact hvalid (e.symm j).1 (e.symm j).2
  · intro i x hx
    obtain ⟨j, hj⟩ := hcover i x hx
    have hpair : combined (e ⟨i, j⟩) = (i, candidate i j) :=
      congrArg (fun k : J => (k.1, candidate k.1 k.2)) (e.symm_apply_apply ⟨i, j⟩)
    refine ⟨e ⟨i, j⟩, congrArg Prod.fst hpair, ?_⟩
    rw [hpair]
    exact hj

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_classified_representatives {Λ α : Type*} {n : ℕ}
    (labels : Fin n → Λ) (valid : Λ → α → Prop) (rel : Λ → α → α → Prop)
    (hlabels : ∀ l x, valid l x → ∃ i, labels i = l) {B : ℝ}
    (hbranch : ∀ i, ∃ c : ℕ, (c : ℝ) ≤ B ∧ ∃ candidate : Fin c → α,
      (∀ j, valid (labels i) (candidate j)) ∧
      ∀ x, valid (labels i) x → ∃ j, rel (labels i) (candidate j) x) :
    ∃ c : ℕ, (c : ℝ) ≤ (n : ℝ) * B ∧ ∃ candidate : Fin c → Λ × α,
      (∀ j, valid (candidate j).1 (candidate j).2) ∧
      ∀ l x, valid l x → ∃ j, (candidate j).1 = l ∧ rel l (candidate j).2 x := by
  obtain ⟨c, hc, family, hvalid, hcover⟩ :=
    exists_finite_indexed_representative_enumeration
      (fun i => valid (labels i)) (fun i => rel (labels i)) hbranch
  let candidate := fun j : Fin c => (labels (family j).1, (family j).2)
  refine ⟨c, by simpa only [Fintype.card_fin] using hc, candidate, hvalid, ?_⟩
  intro l x hx
  obtain ⟨i, hi⟩ := hlabels l x hx
  obtain ⟨j, hj, hr⟩ := hcover i x (hi ▸ hx)
  refine ⟨j, ?_, ?_⟩
  · change labels (family j).1 = l
    rw [hj, hi]
  · exact hi ▸ hr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCommonStrideFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) : Finset (Finset (I → ℤ)) :=
  (Finset.univ : Finset (Fin M × (I → Fin M))).biUnion (fun q =>
    (Fintype.piFinset C).image (fun S => Fintype.piFinset (fun i =>
      (S i).image (fun x => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * x))))

theorem finiteCommonStrideFamily_card {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) :
    (finiteCommonStrideFamily M C).card ≤ M ^ (Fintype.card I + 1) * ∏ i, (C i).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q : Fin M × (I → Fin M), (Fintype.piFinset C).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [Fintype.card_piFinset, pow_succ, mul_assoc, mul_comm]

theorem mem_finiteCommonStrideFamily {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ)) {m : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (r : I → ℕ) (hr : ∀ i, r i < M) (S : I → Finset ℤ) (hS : ∀ i, S i ∈ C i) :
    Fintype.piFinset (fun i => (S i).image (fun x => (r i : ℤ) + m * x)) ∈
      finiteCommonStrideFamily M C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(⟨m - 1, by omega⟩, fun i => ⟨r i, hr i⟩), Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨S, Fintype.mem_piFinset.mpr hS, by simp only [Nat.sub_add_cancel hm]⟩

theorem finiteCommonStrideFamily_shape {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (C : I → Finset (Finset ℤ))
    (hshape : ∀ i S, S ∈ C i → ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ))
    {A : Finset (I → ℤ)} (hA : A ∈ finiteCommonStrideFamily M C) :
    ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ m ≤ M ∧ A = commonStrideBox c m H := by
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hA
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
  choose a b hab using fun i => hshape i (S i) (Fintype.mem_piFinset.mp hS i)
  refine ⟨(fun i => ((q.2 i).val : ℤ) + (q.1.val + 1 : ℕ) * a i), q.1.val + 1,
    (fun i => b i - a i), by omega, by omega, ?_⟩
  congr 1
  funext i
  rw [hab i, affine_interval_eq_progression]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEnumerationFilter
namespace OAI

section

namespace Erdos3

theorem exists_filtered_finite_enumeration {α : Type*} {n : ℕ}
    (c : Fin n → α) (P : α → Prop) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      (∀ j, ∃ i, c i = d j) ∧
      ∀ x, P x → (∃ i, c i = x) → ∃ j, d j = x := by
  classical
  let I := {i : Fin n // P (c i)}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, (fun j => c (e.symm j).val), ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => P (c i))
  · intro j
    exact (e.symm j).property
  · intro j
    exact ⟨(e.symm j).val, rfl⟩
  · rintro x hx ⟨i, hi⟩
    have hpi : P (c i) := hi ▸ hx
    refine ⟨e ⟨i, hpi⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberRepresentatives
namespace OAI

section

namespace Erdos3

theorem exists_finite_fiber_representatives {α β : Type*} {n : ℕ}
    (f : α → β) (P : α → Prop) (c : Fin n → β)
    (hc : ∀ a, P a → ∃ i, c i = f a) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      ∀ a, P a → ∃ j, f (d j) = f a := by
  classical
  let I := {i : Fin n // ∃ a, P a ∧ f a = c i}
  let choose : I → α := fun i => Classical.choose i.property
  have hchoose (i : I) : P (choose i) ∧ f (choose i) = c i.val :=
    Classical.choose_spec i.property
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, fun j => choose (e.symm j), ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => ∃ a, P a ∧ f a = c i)
  · intro j
    exact (hchoose _).1
  · intro a ha
    obtain ⟨i, hi⟩ := hc a ha
    let i' : I := ⟨i, a, ha, hi.symm⟩
    refine ⟨e i', ?_⟩
    change f (choose (e.symm (e i'))) = f a
    rw [Equiv.symm_apply_apply]
    exact (hchoose i').2.trans hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGraphEnergy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def shiftedAdditiveQuadruples (A : Finset G) (d : G) : Finset ((G × G) × (G × G)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2 + d)

theorem shiftedAdditiveQuadruples_card (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card =
      ∑ r : G, ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card *
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : (G × G) × (G × G) => x.1.1 + x.1.2)
    (t := Finset.univ) (by intro x _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  have heq : (shiftedAdditiveQuadruples A d).filter
      (fun x => x.1.1 + x.1.2 = r) =
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)) ×ˢ
          ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)) := by
    ext x
    simp only [shiftedAdditiveQuadruples, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, hsum⟩, hr⟩
      exact ⟨⟨h₁, hr⟩, h₂, (eq_sub_iff_add_eq).mpr (hsum.symm.trans hr)⟩
    · rintro ⟨⟨h₁, hr⟩, h₂, hd⟩
      exact ⟨⟨⟨h₁, h₂⟩, hr.trans ((eq_sub_iff_add_eq).mp hd).symm⟩, hr⟩
  rw [heq, Finset.card_product]

theorem shiftedAdditiveQuadruples_card_le_energy (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card ≤ Finset.addEnergy A A := by
  rw [shiftedAdditiveQuadruples_card, Finset.addEnergy_eq_sum_sq]
  let f : G → ℕ := fun r => ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card
  change (∑ r : G, f r * f (r - d)) ≤ ∑ r : G, f r ^ 2
  have hshift : (∑ r : G, f (r - d) ^ 2) = ∑ r : G, f r ^ 2 :=
    Fintype.sum_equiv (Equiv.subRight d) _ _ (fun _ => rfl)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun r => f (r - d))
  rw [hshift] at hcs
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by simpa only [pow_two] using hcs)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]
  [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K]

def additiveGraph (H : Finset G) (b : G → K) : Finset (G × K) :=
  H.image (fun h => (h, b h))

omit [AddCommGroup G] [AddCommGroup K] [Fintype G] [Fintype K] in
theorem additiveGraph_card (H : Finset G) (b : G → K) :
    (additiveGraph H b).card = H.card :=
  Finset.card_image_of_injective H (fun _ _ h => congrArg Prod.fst h)

def additiveGraphQuadruple (b : G → K) (t : G × G × G) :
    ((G × K) × (G × K)) × ((G × K) × (G × K)) :=
  (((t.2.1 - t.1, b (t.2.1 - t.1)), (t.2.2, b t.2.2)),
    ((t.2.1, b t.2.1), (t.2.2 - t.1, b (t.2.2 - t.1))))

omit [AddCommGroup K] [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K] in
theorem additiveGraphQuadruple_injective (b : G → K) :
    Function.Injective (additiveGraphQuadruple b) := by
  intro t u h
  have hh : t.2.1 = u.2.1 := congrArg (fun x => x.2.1.1) h
  have hk : t.2.2 = u.2.2 := congrArg (fun x => x.1.2.1) h
  have hs : t.2.1 - t.1 = u.2.1 - u.1 := congrArg (fun x => x.1.1.1) h
  rw [hh, sub_eq_add_neg, sub_eq_add_neg] at hs
  exact Prod.ext (neg_injective (add_left_cancel hs)) (Prod.ext hh hk)

theorem graph_energy_of_few_quadruple_differences
    (H : Finset G) (S : Finset (G × G × G)) (b : G → K) (D : Finset K)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hD : ∀ t ∈ S, b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1) ∈ D) :
    S.card ≤ D.card * Finset.addEnergy (additiveGraph H b) (additiveGraph H b) := by
  let δ : G × G × G → K := fun t =>
    b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1)
  have hcard (d : K) : (S.filter (fun t => δ t = d)).card ≤
      (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card := by
    apply Finset.card_le_card_of_injOn (additiveGraphQuadruple b) _
      (fun _ _ _ _ h => additiveGraphQuadruple_injective b h)
    intro t ht
    obtain ⟨htS, hδ⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₀, h₁, h₂, h₃⟩ := hH t htS
    have hmem (x : G) (hx : x ∈ H) : (x, b x) ∈ additiveGraph H b :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hmem _ h₁, hmem _ h₂⟩,
        Finset.mem_product.mpr ⟨hmem _ h₀, hmem _ h₃⟩⟩, ?_⟩
    apply Prod.ext
    · change (t.2.1 - t.1) + t.2.2 = (t.2.1 + (t.2.2 - t.1)) + 0
      abel
    · change b (t.2.1 - t.1) + b t.2.2 = (b t.2.1 + b (t.2.2 - t.1)) + d
      rw [← hδ]
      dsimp only [δ]
      abel
  calc
    S.card = ∑ d ∈ D, (S.filter (fun t => δ t = d)).card :=
      Finset.card_eq_sum_card_fiberwise hD
    _ ≤ ∑ d ∈ D, (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card :=
      Finset.sum_le_sum (fun d _ => hcard d)
    _ ≤ ∑ _d ∈ D, Finset.addEnergy (additiveGraph H b) (additiveGraph H b) :=
      Finset.sum_le_sum (fun d _ => shiftedAdditiveQuadruples_card_le_energy _ (0, d))
    _ = _ := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTripleAssembly
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_triple_fibers {G : Type*} (A : Finset G) (P : A → Finset (G × G)) :
    ∃ Q : Finset (G × G × G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  classical
  let e : (Σ _ : A, G × G) ↪ G × G × G := {
    toFun := fun t => (t.1.val, t.2)
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrArg Prod.fst h)
      have huv : u = v := congrArg Prod.snd h
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have ha := (Finset.mem_sigma.mp hau).2
      exact ⟨a, congrArg Prod.fst heq, (congrArg Prod.snd heq) ▸ ha⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, t.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      exact Prod.ext ha rfl

theorem dense_triple_fibers {G : Type*} [Fintype G]
    (A : Finset G) (P : A → Finset (G × G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ 2 ≤ (P a).card) :
    ∃ Q : Finset (G × G × G),
      α * β * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_triple_fibers A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ 2) := by ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (sq_nonneg _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTupleFibers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_tuple_fibers {G : Type*} (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) :
    ∃ Q : Finset (Fin (d + 1) → G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  classical
  let e : (Σ _ : A, Fin d → G) ↪ (Fin (d + 1) → G) := {
    toFun := fun t => Fin.cons t.1.val t.2
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrFun h 0)
      have huv : u = v := by funext i; exact congrFun h i.succ
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have hu := (Finset.mem_sigma.mp hau).2
      have hut : u = Fin.tail t := by funext i; exact congrFun heq i.succ
      exact ⟨a, congrFun heq 0, hut ▸ hu⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, Fin.tail t⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact ha

theorem dense_tuple_fibers {G : Type*} [Fintype G] (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ d ≤ (P a).card) :
    ∃ Q : Finset (Fin (d + 1) → G),
      α * β * (Fintype.card G : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_tuple_fibers d A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ d) := by rw [pow_succ]; ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (pow_nonneg (Nat.cast_nonneg _) _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_on_interior {x y η δ : ℝ}
    (hx : η ≤ x ∧ x ≤ 1 - η) (hy : η ≤ y ∧ y ≤ 1 - η)
    (hδ : δ < 2 * η) (hdist : dist (x : CircleFourier.Circle) (y : CircleFourier.Circle) ≤ δ) :
    |x - y| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxy : |x - y| ≤ 1 - 2 * η := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - y) : ℝ)| ≤ |x - y - (round (x - y) : ℝ)| + |x - y| := by
    calc
      _ = |((round (x - y) : ℝ) - (x - y)) + (x - y)| := by ring_nf
      _ ≤ |(round (x - y) : ℝ) - (x - y)| + |x - y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - y) : ℝ) (x - y)]
  have hzlt : |(round (x - y) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - y) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - y) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - y) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def frozenRealSection {Z Ξ : Type*} (F : Z → Ξ → ℝ) (a : Option Ξ) (z : Z) : ℝ :=
  a.elim 0 (F z)

theorem frozenRealSection_unit_interval {Z Ξ : Type*} (F : Z → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (a : Option Ξ) (z : Z) :
    0 ≤ frozenRealSection F a z ∧ frozenRealSection F a z ≤ 1 := by
  cases a with
  | none => simp [frozenRealSection]
  | some a => exact hF z a

noncomputable def positiveCellParameter {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A) : Option Ξ := by
  classical
  exact if h : ∃ x, x ∉ E ∧ 0 < w a x then some (xi h.choose) else none

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_abs_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (f : X → ℝ) {M ε : ℝ} (hε : 0 ≤ ε)
    (hcap : ∀ x, |f x| ≤ M) (hgood : ∀ x, x ∉ E → |f x| ≤ ε) :
    (𝔼 x, |f x|) ≤ ε + M * (E.card : ℝ) / Fintype.card X := by
  classical
  have hbound (x : X) : |f x| ≤ ε + if x ∈ E then M else 0 := by
    by_cases hx : x ∈ E
    · simp only [hx, ↓reduceIte]
      exact (hcap x).trans (le_add_of_nonneg_left hε)
    · simpa only [hx, ↓reduceIte, add_zero] using hgood x hx
  calc
    _ ≤ (𝔼 x : X, (ε + if x ∈ E then M else 0)) := Finset.expect_le_expect (fun x _ => hbound x)
    _ = ε + M * (E.card : ℝ) / Fintype.card X := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
      congr 1
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicWrapExceptional {N : ℕ} [NeZero N] (h : ZMod N) (ρ : ℝ) : Finset (ZMod N) :=
  cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ) ∪
    cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)

theorem cyclicWrapExceptional_card_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) ≤ 6 * N * ρ + 3 := by
  have hδ : 0 ≤ (N : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have h0 := cyclicCutNeighborhood_card_le N 0 hδ
  have hN := cyclicCutNeighborhood_card_le N N hδ
  have hw := cyclicCutNeighborhood_card_le N ((N - h.val : ℕ) : ℤ) hδ
  have hu := Finset.card_union_le (cyclicCutNeighborhood N 0 (N * ρ))
    (cyclicCutNeighborhood N N (N * ρ))
  have hv := Finset.card_union_le
    (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ))
    (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ))
  have hu' : ((cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ)).card + (cyclicCutNeighborhood N N (N * ρ)).card := by
    exact_mod_cast hu
  have hv' : ((cyclicWrapExceptional h ρ).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card +
        (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)).card := by
    exact_mod_cast hv
  linarith

theorem cyclicWrapExceptional_density_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ ≤ (6 * (N : ℝ) * ρ + 3) / N :=
      div_le_div_of_nonneg_right (cyclicWrapExceptional_card_le h hρ) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem outside_cyclicWrapExceptional {N : ℕ} [NeZero N] (h x : ZMod N) {ρ : ℝ}
    (hx : x ∉ cyclicWrapExceptional h ρ) :
    ρ < (x.val : ℝ) / N ∧ (x.val : ℝ) / N < 1 - ρ ∧
      (N : ℝ) * ρ < |(x.val : ℝ) - ((N - h.val : ℕ) : ℝ)| := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hxN : (x.val : ℝ) < N := Nat.cast_lt.mpr x.val_lt
  simp only [cyclicWrapExceptional, Finset.mem_union, not_or, mem_cyclicCutNeighborhood] at hx
  have h0 : (N : ℝ) * ρ < (x.val : ℝ) := by
    simpa only [Int.cast_zero, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using lt_of_not_ge hx.1.1
  have h1 : (N : ℝ) * ρ < (N : ℝ) - x.val := by
    simpa only [Int.cast_natCast, abs_of_neg (sub_neg.mpr hxN), neg_sub] using lt_of_not_ge hx.1.2
  refine ⟨(lt_div_iff₀ hN).mpr (by nlinarith), (div_lt_iff₀ hN).mpr (by nlinarith), ?_⟩
  simpa only [Int.cast_natCast] using lt_of_not_ge hx.2

end Erdos3

end

section

namespace Erdos3

theorem good_circle_observations_control_representatives {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ := by
  have hx' := outside_cyclicWrapExceptional h x hx
  have hy' := outside_cyclicWrapExceptional h y hy
  apply abs_sub_le_of_circle_dist_on_interior ⟨hx'.1.le, hx'.2.1.le⟩ ⟨hy'.1.le, hy'.2.1.le⟩
    (by linarith)
  simpa only [ZMod.toAddCircle_apply] using hdist

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def interiorIntervalCutoff (eta : ℝ≥0) (x : ℝ) : ℝ :=
  linearCutoff (1 / 2 - 2 * eta) eta |x - 1 / 2|

theorem interiorIntervalCutoff_range (eta : ℝ≥0) (x : ℝ) :
    0 ≤ interiorIntervalCutoff eta x ∧ interiorIntervalCutoff eta x ≤ 1 :=
  linearCutoff_range _ _ _

theorem interiorIntervalCutoff_support (eta : ℝ≥0) {x : ℝ}
    (hx : interiorIntervalCutoff eta x ≠ 0) : (eta : ℝ) < x ∧ x < 1 - eta := by
  have h : |x - 1 / 2| < 1 / 2 - eta := by
    by_contra h
    apply hx
    exact linearCutoff_eq_zero _ _ (by linarith [le_of_not_gt h])
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

theorem interiorIntervalCutoff_lipschitz (eta : ℝ≥0) (heta : 0 < eta) :
    LipschitzWith eta⁻¹ (interiorIntervalCutoff eta) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz _ eta heta).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans_eq (by rw [sub_sub_sub_cancel_right]; rfl)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NestedProgressionReindex
namespace OAI

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff_parameter (c m x : ℤ) (H : ℕ) :
    x ∈ integerProgressionSupport c m H ↔
      ∃ j : ℤ, 0 ≤ j ∧ j < H ∧ x = c + m * j := by
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    have hb := Finset.mem_Ico.mp hj
    change m * j = x - c at he
    exact ⟨j, hb.1, hb.2, by omega⟩
  · rintro ⟨j, hj0, hjH, rfl⟩
    exact ⟨j, Finset.mem_Ico.mpr ⟨hj0, hjH⟩, by simp [integerStrideHom]⟩

theorem exists_nested_progression_affine (c b : ℤ) {m d H L : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hL : 0 < L)
    (hsub : integerProgressionSupport b d L ⊆ integerProgressionSupport c m H) :
    ∃ a s : ℤ, ∀ x : ℤ, 0 ≤ x → x < L →
      0 ≤ a + s * x ∧ a + s * x < H ∧ b + (d : ℤ) * x = c + m * (a + s * x) := by
  have hb := hsub (integerProgressionSupport_point b d L hd 0 hL)
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  obtain ⟨a, ha0, haH, hba⟩ := (mem_integerProgressionSupport_iff_parameter c m b H).mp hb
  by_cases hsingle : L = 1
  · refine ⟨a, 0, fun x hx0 hxL => ?_⟩
    have hx : x = 0 := by rw [hsingle] at hxL; omega
    simpa only [hx, mul_zero, add_zero] using And.intro ha0 (And.intro haH hba)
  · have hb1 := hsub (integerProgressionSupport_point b d L hd 1 (by omega))
    simp only [Nat.cast_one, mul_one] at hb1
    obtain ⟨a₁, _, _, hba₁⟩ := (mem_integerProgressionSupport_iff_parameter c m (b + d) H).mp hb1
    let s := a₁ - a
    have hs : (d : ℤ) = m * s := by dsimp [s]; nlinarith [hba, hba₁]
    refine ⟨a, s, fun x hx0 hxL => ?_⟩
    have hinner : b + (d : ℤ) * x ∈ integerProgressionSupport b d L :=
      (mem_integerProgressionSupport_iff_parameter b d _ L).mpr ⟨x, hx0, hxL, rfl⟩
    obtain ⟨j, hj0, hjH, hj⟩ := (mem_integerProgressionSupport_iff_parameter c m _ H).mp (hsub hinner)
    have hpoint : b + (d : ℤ) * x = c + m * (a + s * x) := by rw [hba, hs]; ring
    have hj' : j = a + s * x :=
      mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) (add_left_cancel (hj.symm.trans hpoint))
    exact ⟨hj' ▸ hj0, hj' ▸ hjH, hpoint⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedMinorCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_entry {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    (H * (H.submatrix p id)⁻¹) i j =
      (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det := by
  have h := row_minor_update_det H p (H * (H.submatrix p id)⁻¹)
    (Matrix.nonsing_inv_mul_cancel_right (H.submatrix p id) H (isUnit_iff_ne_zero.mpr hp)) i j
  exact (eq_div_iff hp).mpr h.symm

theorem row_normalization_submatrix {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    (H * (H.submatrix p id)⁻¹).submatrix p id = 1 := by
  rw [Matrix.submatrix_mul H (H.submatrix p id)⁻¹ p id id Function.bijective_id,
    Matrix.submatrix_id_id]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp)

theorem row_normalization_col_span {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    Submodule.span K (Set.range (H * (H.submatrix p id)⁻¹).col) =
      Submodule.span K (Set.range H.col) := by
  let B := H.submatrix p id
  have hsurj : Function.Surjective B⁻¹.mulVecLin := by
    intro x
    refine ⟨B *ᵥ x, ?_⟩
    change B⁻¹ *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hp),
      Matrix.one_mulVec]
  rw [← Matrix.range_mulVecLin, ← Matrix.range_mulVecLin, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMinorBounds
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_abs_le {ι : Type*} {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (p : Fin k → ι)
    (hp : (M.submatrix p id).det ≠ 0) (C D : ℝ) (hD : 0 < D)
    (hminor : ∀ q : Fin k → ι, |(M.submatrix q id).det| ≤ C)
    (hlower : 1 / D ≤ |(M.submatrix p id).det|) (i : ι) (j : Fin k) :
    |(M * (M.submatrix p id)⁻¹) i j| ≤ C * D := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hminor p)
  calc
    _ = |(M.submatrix (Function.update p j i) id).det| /
        |(M.submatrix p id).det| := by rw [row_normalization_entry M p hp i j, abs_div]
    _ ≤ C / |(M.submatrix p id).det| :=
      div_le_div_of_nonneg_right (hminor _) (abs_nonneg _)
    _ ≤ C / (1 / D) := div_le_div_of_nonneg_left hC (one_div_pos.mpr hD) hlower
    _ = C * D := by rw [one_div, div_inv_eq_mul]

theorem euclidean_matrix_mulVec_norm_le {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hM : ∀ i j, |M i j| ≤ H) (x : Fin k → ℝ) :
    ‖(EuclideanSpace.equiv ι ℝ).symm (M *ᵥ x)‖ ≤
      (Fintype.card ι : ℝ) * k * H * ‖x‖ := by
  have hi (i : ι) : |(M *ᵥ x) i| ≤ (k : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hM i j)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  calc
    _ ≤ ∑ i, |(M *ᵥ x) i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : ι, (k : ℝ) * H * ‖x‖ := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OverlapCubeWeights
namespace OAI

section

namespace Erdos3

theorem overlap_weight_comparison (j : ℕ) {q r C D c δ : ℝ}
    (hq : 0 < q) (hr : 0 ≤ r) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hD : 0 < D) (hDq : D ≤ q ^ (j + 3))
    (hC : c * r ^ (j + 2) ≤ C) (hδr : δ * q ≤ r) :
    c * δ ^ (j + 1) * (r / q ^ 2) ≤ C / D := by
  have hδq : δ ≤ r / q := (le_div_iff₀ hq).mpr hδr
  have hC0 : 0 ≤ C := (mul_nonneg hc (pow_nonneg hr _)).trans hC
  calc
    _ ≤ c * (r / q) ^ (j + 1) * (r / q ^ 2) := by gcongr
    _ = (c * r ^ (j + 2)) / q ^ (j + 3) := by
      simp only [div_pow, pow_succ]
      field_simp
    _ ≤ C / q ^ (j + 3) := div_le_div_of_nonneg_right hC (by positivity)
    _ ≤ C / D := div_le_div_of_nonneg_left hC0 hD hDq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem box_overlap_cube_weight (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)]
    (j : ℕ) {h : ι → ℤ} (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : δ * (translatedIntegerBox a T).card ≤
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) :
    let Q := translatedIntegerBox a T
    let R := derivativeSupport Q h
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι * δ ^ (j + 1) *
        ((R.card : ℝ) / (Q.card : ℝ) ^ 2) ≤
      (Nat.card (SupportedCube (j + 1) (R : Set (ι → ℤ))) : ℝ) /
        Nat.card (SupportedCube (j + 2) (Q : Set (ι → ℤ))) := by
  let Q := translatedIntegerBox a T
  let lengths := fun i => ((T i : ℤ) - |h i|).toNat
  let origin := fun i => a i + max 0 (-h i)
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(box_overlap_length_pos a T hh i).ne'⟩
  have hR : derivativeSupport Q h = translatedIntegerBox origin lengths :=
    derivativeSupport_translatedIntegerBox a T h
  have hC := (translatedIntegerBox_cubeCount_bounds lengths origin (j + 1)).1
  rw [← hR] at hC
  have hC' : ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) ^ Fintype.card ι *
      ((derivativeSupport Q h).card : ℝ) ^ (j + 2) ≤
      Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set (ι → ℤ))) := by
    convert hC using 1
    push_cast
    ring
  apply overlap_weight_comparison j
    (by exact_mod_cast (translatedIntegerBox_nonempty T a).card_pos)
    (Nat.cast_nonneg _) (by positivity) hδ
    (by exact_mod_cast card_supportedCube_pos (j + 2) (translatedIntegerBox_nonempty T a))
    _ hC' hsize
  exact_mod_cast card_supportedCube_le (j + 2) Q

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBoundaryLabels
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxClassify (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : I → ℤ) : Option (∀ i, (P i).Label) :=
  if hx : x ∈ translatedIntegerBox lo N then some (physicalBoxCell lo N P ⟨x, hx⟩) else none

def physicalBoundaryNear (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (x : I → ℤ) : Prop :=
  ∃ i c, |x i - intervalCellLower (lo i) (P i) c| ≤ (r i : ℤ) ∨
    |x i - intervalCellUpper (lo i) (P i) c| ≤ (r i : ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.InactivePrincipalLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def inactivePrincipalPMF (K q : ℕ) : PMF ℤ :=
  PMF.pure (inactivePrincipalCoefficient K q)

theorem inactivePrincipalPMF_support {K q : ℕ} {k : ℤ}
    (hk : k ∈ (inactivePrincipalPMF K q).support) : k = inactivePrincipalCoefficient K q := by
  simpa only [inactivePrincipalPMF, PMF.support_pure, Set.mem_singleton_iff] using hk

theorem inactivePrincipal_scaled_upper {h K q : ℕ} (hh : 0 < h) (hK : 0 < K) (hq : 0 < q) :
    |(inactivePrincipalCoefficient K q : ℝ)| * (inactiveSideLength h K q : ℝ) ^ h / K ≤ 1 / (q : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hlarge : 2 * q ≤ K
  · rw [inactivePrincipal_large hlarge, Int.cast_one, abs_one, one_mul]
    have hb : q * inactiveSideLength h K q ^ h ≤ K := by
      calc
        _ ≤ q * (K / q) := Nat.mul_le_mul_left q (inactiveSideLength_power hh hlarge)
        _ ≤ K := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K q
    have hbr : (q : ℝ) * (inactiveSideLength h K q : ℝ) ^ h ≤ K := by exact_mod_cast hb
    apply (div_le_div_iff₀ hKr hqr).mpr
    nlinarith
  · rw [inactivePrincipal_small (lt_of_not_ge hlarge), Int.cast_zero, abs_zero, zero_mul, zero_div]
    positivity

noncomputable def inactiveDenominator (γ : ℝ) : ℕ := max 1 ⌈γ⁻¹⌉₊

theorem inactiveDenominator_pos (γ : ℝ) : 0 < inactiveDenominator γ :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

theorem inactiveDenominator_bound {γ : ℝ} (hγ : 0 < γ) : 1 / (inactiveDenominator γ : ℝ) ≤ γ := by
  have hq : (0 : ℝ) < inactiveDenominator γ := by exact_mod_cast inactiveDenominator_pos γ
  have hceil : γ⁻¹ ≤ (inactiveDenominator γ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈γ⁻¹⌉₊))
  have hb := mul_le_mul_of_nonneg_left hceil hγ.le
  rw [mul_inv_cancel₀ hγ.ne'] at hb
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hb)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityNormalization
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedCoefficientMeasurableEquiv {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : (UnselectedColumn s → ℝ) × (I → ℝ) ≃ᵐ (J → ℝ) where
  toEquiv := selectedCoefficientEquiv s ℝ
  measurable_toFun := (selectedCoefficientEquiv_lipschitz s).continuous.measurable
  measurable_invFun := by
    change Measurable (fun x : J → ℝ => ((fun j : UnselectedColumn s => x j.val), fun i => x (s i)))
    fun_prop

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def zeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℂ) (x : X) : ℂ := by
  classical
  exact if x ∈ S then f x else 0

theorem expect_finset_subtype {X : Type*} (S : Finset X) (f : X → ℂ) :
    (𝔼 x : S, f x.val) = 𝔼 x ∈ S, f x := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort]

theorem expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    (𝔼 x ∈ A, zeroExtendFinset S f x) =
      ((S.card : ℂ) / (A.card : ℂ)) * (𝔼 x ∈ S, f x) := by
  classical
  rw [Finset.expect_eq_sum_div_card]
  simp only [zeroExtendFinset, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSA]
  rw [← Finset.card_mul_expect S f]
  ring

theorem norm_expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    ‖𝔼 x ∈ A, zeroExtendFinset S f x‖ =
      ((S.card : ℝ) / (A.card : ℝ)) * ‖𝔼 x ∈ S, f x‖ := by
  rw [expect_zeroExtendFinset A S hSA f, norm_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]

theorem zeroExtendFinset_mul_left {X : Type*} (S : Finset X) (f g : X → ℂ) (x : X) :
    f x * zeroExtendFinset S g x = zeroExtendFinset S (fun x => f x * g x) x := by
  classical
  by_cases hx : x ∈ S <;> simp [zeroExtendFinset, hx]

theorem zeroExtendFinset_mul_star {X : Type*} [DecidableEq X] (S T : Finset X) (f g : X → ℂ) (x : X) :
    zeroExtendFinset S f x * star (zeroExtendFinset T g x) =
      zeroExtendFinset (S ∩ T) (fun x => f x * star (g x)) x := by
  classical
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [zeroExtendFinset, hs, ht]

theorem zeroExtendFinset_norm_le_one {X : Type*} (S : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) (x : X) : ‖zeroExtendFinset S f x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S
  · simpa [zeroExtendFinset, hx] using hf x hx
  · simp [zeroExtendFinset, hx]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def realZeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℝ) (x : X) : ℝ :=
  if x ∈ S then f x else 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

noncomputable def fullSliceInverseParameters (S : ResidueBoxSlice N q) (i : X) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • (MvPolynomial.X i - MvPolynomial.C (S.start i : ℝ))

omit [Fintype X] [DecidableEq X] in
theorem fullSliceInverseParameters_degree (S : ResidueBoxSlice N q) (i : X) :
    S.fullSliceInverseParameters i ∈ weightedSupportLE (fun _ => 1) 1 :=
  (weightedSupportLE _ _).smul_mem _ ((weightedSupportLE _ _).sub_mem
    (weightedSupportLE_X _ _) (weightedSupportLE_C _ _ _))

noncomputable def fullSliceReinsertPatch (S : ResidueBoxSlice N q)
    (Q : PolynomialPatch X s d) : PolynomialPatch X s d :=
  Q.reparam S.fullSliceInverseParameters S.fullSliceInverseParameters_degree

def fullSlicePointInIntegerBox (S : ResidueBoxSlice N q) (u : ∀ i, Fin (S.length i)) : integerBox N :=
  ⟨fun i => ((S.point u i).val : ℤ), (mem_integerBox _ _).mpr
    (fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u i).isLt⟩)⟩

noncomputable def fullSliceLaw (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i) :
    FiniteProbabilityWeights (integerBox N) := by
  letI : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ i, Fin (S.length i))).finitePushforward S.fullSlicePointInIntegerBox

theorem fullSliceLaw_mean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

end ResidueBoxSlice

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
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

open scoped BigOperators Classical

def affineParameterBadPair {J : Type*} [Fintype J]
    (D Q r : ℕ) (a x y : J → ℤ) : Prop :=
  Q < (BohrLattice.Primitive.content
    (fun j => (a j + (D : ℤ) * y j) - (a j + (D : ℤ) * x j))).natAbs ∨
    ∀ j, |y j - x j| ≤ (r : ℤ)

noncomputable def integerBoxBadPairBudget (d B R r : ℕ) (L : ℝ) : ℝ :=
  2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + (R : ℝ) / L ^ d) +
    ((2 * (r : ℝ) + 1) / L) ^ d

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

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

noncomputable def physicalBoundaryBudget {I : Type*} [Fintype I]
    (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (width : I → ℝ) : ℝ :=
  ∑ i, 2 * (Fintype.card (P i).Label : ℝ) * (2 * (r i : ℝ) + 1) / width i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalMeshCrossing {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) (x : X) : Prop :=
  ∃ y, mesh y = mesh x ∧ physicalBoxClassify lo N P (location x) ≠ physicalBoxClassify lo N P (location y)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rationalOutputDensity {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : ℝ :=
  Fintype.card (J → ZMod N) * finiteImageMass p (fun x j => (Y x j : ZMod N)) b

noncomputable def rationalInactiveForecast {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (b : J → ZMod N) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b)

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

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

def integerResidueTuple (N : ℕ) : (J → ℤ) →+ (J → ZMod N) where
  toFun x j := (x j : ZMod N)
  map_zero' := by ext j; simp
  map_add' := by intro x y; ext j; simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]
variable (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N)
variable (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ b, Continuous (φ b))
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)

local notation "Domain" => (V → ℝ) × (J → ℝ)
local notation "rout" => rationalOutputDensity p Y N

include hg hφ hsupport

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω O : Type*} [Fintype Ω] [Fintype O] [DecidableEq O]

noncomputable def rationalOutputOrderTail
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    (T : ℕ) (b : O → ZMod N) : ℂ :=
  (rationalOutputDensity p Y N b : ℂ) -
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar (O → ZMod N) ℂ => orderOf χ ≤ T),
      finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridHistogram (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : (Option I → ℝ) → ℝ :=
  rectangularWeightHistogram (scalarCubeIndicator I) a S 1

noncomputable def scalarCubeGridBoundaryConstant (I : Type*) [Fintype I] : ℝ :=
  Fintype.card (Bool × Finset I) * (4 : ℝ)^Fintype.card I * 2 * (Fintype.card I + 1)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridSet (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Finset (Option I → ℤ) :=
  (rectangularWeightIndices a S 1).filter (fun k =>
    rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I)

theorem mem_scalarCubeGridSet {I : Type*} [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (k : Option I → ℤ) :
    k ∈ scalarCubeGridSet I a S ↔ rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I := by
  rw [scalarCubeGridSet, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hk
    refine ⟨?_, hk⟩
    by_contra hn
    have h := rectangularWeight_zero_off_indices (scalarCubeIndicator I) a S hS
      (scalarCubeIndicator_zero_outside I) k hn
    change scalarCubeIndicator I (rectangularLatticePoint a S k) = 0 at h
    simp only [scalarCubeIndicator, hk, ite_true] at h
    exact one_ne_zero h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedPathSlicedGridMeshLog (D C V cost E : ℝ) : ℝ :=
  Real.log (D + C + 8) + V + cost + E + 2

noncomputable def fixedPathSlicedGridMeshFloor (D C V cost E : ℝ) : ℕ :=
  ⌈Real.exp (fixedPathSlicedGridMeshLog D C V cost E)⌉₊

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedExpectationWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofDensity {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) : FiniteProbabilityWeights X where
  weight x := (Fintype.card X : ℝ)⁻¹ * w x
  nonneg x := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hw x)
  total := by
    rw [← Finset.mul_sum]
    simpa only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm] using htotal

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCutoffLengthBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubeCutoffDerivativeNumerator (I : Type*) [Fintype I]
    (A : ℝ≥0) : ℝ :=
  (2 * 2 ^ Fintype.card I : ℕ) * ((A : ℝ) * ((Fintype.card I : ℝ) + 1))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

noncomputable def finiteFiberAverage (f : G → ℝ) (x : G) : ℝ :=
  (Fintype.card C.ker : ℝ)⁻¹ * ∑ k : C.ker, f (x + k.val)

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

noncomputable def finiteKernelLiftLaw (ρ : Measure X) (s : X → G) : Measure G :=
  (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure).map (fun p => s p.1 + p.2.val)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [CompactSpace G] [HasOuterApproxClosed G]
variable [MeasurableAdd₂ G]
variable [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RawSourceTolerance
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def booleanToleranceC2 {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (Csum Wsum : ℝ) : ℝ :=
  polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree+2) (booleanJetMassBudget (Fintype.card α) degree Csum+
      booleanJetMassBudget (Fintype.card α) degree Wsum)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget
namespace OAI

section

namespace Erdos3

def booleanJetMassLog (q h : ℕ) (P : ℝ) : ℝ := q+P+(h : ℝ)*q

noncomputable def booleanToleranceC2Log {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (P : ℝ) : ℝ :=
  3*Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))*(degree+2 : ℕ)+
    (2*booleanJetMassLog (Fintype.card α) degree P+1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDensitySplit
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

noncomputable def selectedSplitCoefficients {I J N : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) : J ⊕ N → ℝ :=
  Sum.elim (selectedCoefficientEquiv s ℝ ((fun j => p.1 (.inl j)), p.2))
    (fun n => p.1 (.inr n))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientLogAllowance (j d : ℕ) (b : ℝ) : ℝ :=
  2*(j : ℝ)^2 + (2*j+4)*b + (j+2*d)*(b+4) + 4

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientReplacementScale {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (b t ε L : ℝ) (h : ℕ) : ℝ :=
  Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
    (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
      (1+ε⁻¹) * L^(h*(Fintype.card I+1))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
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

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SubmoduleCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem submodule_basis_coordinate_height {ν κ L : Type*} [Fintype ν] [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (U : Submodule ℚ L)
    (b : Basis κ ℚ U) (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (e.repr (b j).val i) H)
    (x : U) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr x.val i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ν + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ν) := by
  classical
  let B := LinearMap.toMatrix b e U.subtype
  have hBmul (w : κ → ℚ) : B *ᵥ w = e.equivFun (b.equivFun.symm w).val := by
    have h := LinearMap.toMatrix_mulVec_repr b e U.subtype (b.equivFun.symm w)
    simp only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] at h
    exact h
  have hBi : Function.Injective B.mulVec := by
    intro u v huv
    rw [hBmul, hBmul] at huv
    exact b.equivFun.symm.injective (Subtype.ext (e.equivFun.injective huv))
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp hBi) hH
    (by
      intro i j
      dsimp only [B]
      rw [LinearMap.toMatrix_apply]
      exact hB i j)
  have hretract : P *ᵥ e.repr x.val = b.repr x := by
    have hrepr : B *ᵥ b.repr x = e.repr x.val :=
      LinearMap.toMatrix_mulVec_repr b e U.subtype x
    rw [← hrepr, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr x.val i)
    (fun i => (hP j i).mul (hx i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NestedBoxReindex
namespace OAI

section

namespace Erdos3

theorem exists_nested_box_affine {I : Type*} [Fintype I] [DecidableEq I]
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H L : I → ℕ) (hL : ∀ i, 0 < L i)
    (hsub : commonStrideBox b d L ⊆ commonStrideBox c m H) :
    ∃ (A : I → I → ℤ) (a : I → ℤ), ∀ x ∈ integerBox L,
      integerAffineMap A a x ∈ integerBox H ∧
      commonStridePoint b d x = commonStridePoint c m (integerAffineMap A a x) := by
  have haxis (i : I) : (integerProgressionSupport (b i) d (L i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hd] using hL i)
  have hcoord (i : I) := piFinset_axis_subset _ _ haxis hsub i
  choose a s ha using fun i => exists_nested_progression_affine (c i) (b i) hm hd (hL i) (hcoord i)
  refine ⟨(fun i j => if i = j then s i else 0), a, fun x hx => ?_⟩
  rw [integerAffineMap_diagonal]
  have hb (i : I) := ha i (x i) ((mem_integerBox L x).mp hx i).1 ((mem_integerBox L x).mp hx i).2
  refine ⟨(mem_integerBox H _).mpr (fun i => ⟨(hb i).1, (hb i).2.1⟩), ?_⟩
  funext i
  exact (hb i).2.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem embedding_basis_coordinate_height {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (e.repr (φ (b j)) i) H)
    (x : M) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr (φ x) i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ι) := by
  classical
  let B := LinearMap.toMatrix b e φ
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ hφ)) hH
    (by simpa only [B, LinearMap.toMatrix_apply] using hB)
  have hretract : P *ᵥ e.repr (φ x) = b.repr x := by
    rw [← LinearMap.toMatrix_mulVec_repr b e φ x, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr (φ x) i)
    (fun i => (hP j i).mul (hx i))

theorem embedding_coordinate_height_budget (n d H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalSolveHeight d H * K) ^ n : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hproduct : ((rationalSolveHeight d H * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp p :=
        mul_le_mul (rationalSolveHeight_le_budget d H hp hd hH) hK (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((p + 2) ^ 5 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
        calc
          _ ≤ 2 * (p + 2) ^ 5 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = (p + 2) ^ 6 := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hproduct (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

def residueBoxStrideValue {I : Type*} {a b r v : I → ℤ}
    (f : (I → ℤ) → ℂ) (u : I → ℤ) (M : ℕ) (x : IntegerResidueBox a b r v) : ℂ :=
  f (commonStrideIndex u M (fun i => (x i).val))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def residueStepMatrix {I : Type*} [DecidableEq I] (J : I → ℕ) : I → I → ℤ :=
  fun i j => if i = j then (J i : ℤ) else 0

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*}
  [Fintype σ]
  [DecidableEq σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]
  {s d : ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*}
  [Fintype σ]
  [DecidableEq σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]
  {s d : ℕ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSpatialProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarSpatialIndexAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (B : ℝ)^(Fintype.card I + 1)

noncomputable def scalarSpatialInverseAllowance (I : Type*) [Fintype I] (B : ℕ) : ℝ :=
  (Fintype.card I + 1 : ℝ) * ((Fintype.card I + 1).factorial : ℝ) * B

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSelectedSpatialLaw
namespace OAI

section

namespace Erdos3

noncomputable def selectedFullSpatialColumnEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (N : Type*) :
    (Unit ⊕ I) ⊕ (UnselectedColumn s ⊕ N) ≃ (Unit ⊕ J) ⊕ N :=
  (Equiv.sumAssoc (Unit ⊕ I) (UnselectedColumn s) N).symm.trans
    (Equiv.sumCongr (selectedSpatialColumnEquiv s) (Equiv.refl N))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PartitionedIdealSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def partitionedIdealRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  1 / 4 + 2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree

theorem partitionedIdealRadius_nonneg (α : Type*) [Fintype α] (degree : ℕ) :
    0 ≤ partitionedIdealRadius α degree := by
  unfold partitionedIdealRadius
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

def physicalCubeOptionEquiv (K : Type*) : (Unit ⊕ K) ≃ Option K where
  toFun := Sum.elim (fun _ => none) some
  invFun := Option.elim' (.inl ()) Sum.inr
  left_inv x := by cases x with | inl x => cases x; rfl | inr x => rfl
  right_inv x := by cases x <;> rfl

def physicalCubePivotIndex {α K : Type*} (s : α ↪ K) : (Unit ⊕ α) ↪ Option K where
  toFun := Sum.elim (fun _ => none) (fun i => some (s i))
  inj' := by
    intro i j h
    cases i with
    | inl i => cases j with
      | inl j => cases i; cases j; rfl
      | inr j => cases h
    | inr i => cases j with
      | inl j => cases h
      | inr j => exact congrArg Sum.inr (s.injective (Option.some.inj h))

noncomputable def physicalSpatialInputScale (K : Type*) (A R : ℝ) : Option K → ℝ :=
  Option.elim' A (fun _ => R)

noncomputable def physicalSpatialOutputScale (α : Type*) (A R L : ℝ) : (Unit ⊕ α) → ℝ :=
  Sum.elim (fun _ => A) (fun _ => L * R)

theorem physicalSpatialOutputScale_pos (α : Type*) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) :
    ∀ i, 0 < physicalSpatialOutputScale α A R L i := by
  intro i
  cases i
  · exact hA
  · exact mul_pos hL hR

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def physicalSpatialInverseBound (α : Type*) [Fintype α] (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalSpatialInverseBound_le_exp (α : Type*) [Fintype α] {κ b : ℝ}
    (hκ : 0 < κ) (hi : κ⁻¹ ≤ Real.exp b) :
    physicalSpatialInverseBound α κ ≤
      Real.exp ((Fintype.card (Unit ⊕ α) : ℝ) ^ 2 + Fintype.card (Unit ⊕ α) + b) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj : (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
  change (j : ℝ) * j.factorial / κ ≤ _
  calc
    _ ≤ Real.exp (j : ℝ) * Real.exp ((j : ℝ) ^ 2) * Real.exp b := by
      rw [div_eq_mul_inv]
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def trimmedSpatialRootScale {X : Type*} (τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / 8 / modulus x

noncomputable def trimmedSpatialSlopeScale {X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / (8 * (1 + B)) / modulus x

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

def finsetIndicator {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0

@[simp]
theorem finsetIndicator_of_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp]
theorem finsetIndicator_of_not_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

@[simp]
theorem mean_empty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]

@[simp]
theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  exact Fintype.expect_const c

@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  exact Finset.expect_add_distrib Finset.univ f g

theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  exact Finset.expect_sub_distrib Finset.univ f g

theorem mean_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  rw [mean, mean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

theorem mean_le_of_le_const {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    mean f ≤ c := by
  simpa using mean_mono (f := f) (g := fun _ => c) hf

noncomputable def mean₂ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) : ℝ :=
  mean (fun x => mean (f x))

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

@[simp]
theorem cyclicAPProduct_const (k N : ℕ) (c : ℝ) (a d : ZMod N) :
    cyclicAPProduct k N (fun _ => c) a d = c ^ k := by
  simp [cyclicAPProduct]

@[simp]
theorem cyclicAPCount_const (k N : ℕ) [NeZero N] (c : ℝ) :
    cyclicAPCount k N (fun _ => c) = c ^ k := by
  simp [cyclicAPCount, mean₂]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f

theorem conditionalMean_eq_of_part_eq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hxy : P.part x = P.part y) :
    conditionalMean P f x = conditionalMean P f y := by
  rw [conditionalMean, conditionalMean, hxy]

theorem conditionalMean_eq_of_mem_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    conditionalMean P f y = conditionalMean P f x := by
  apply conditionalMean_eq_of_part_eq
  apply P.part_eq_of_mem
  · simp
  · exact hy

theorem conditionalMean_sub {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y - g y) x =
      conditionalMean P f x - conditionalMean P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g

theorem conditionalMean_smul {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => c * f y) x =
      c * conditionalMean P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm

@[simp]
theorem conditionalMean_const {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (x : Ω) :
    conditionalMean P (fun _ => c) x = c := by
  rw [conditionalMean]
  exact Finset.expect_const (by simp) c

@[simp]
theorem conditionalMean_idem {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean P f) x =
      conditionalMean P f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean P f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean P f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part P f hy
    _ = conditionalMean P f x :=
      Finset.expect_const (by simp) _

theorem sum_conditionalMean_on_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [conditionalMean, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f

theorem sum_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, conditionalMean P f x = ∑ x, f x := by
  classical
  have hparts :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, conditionalMean P f x =
        ∑ x ∈ P.parts.biUnion id, conditionalMean P f x := by
      exact Finset.sum_congr hparts.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, conditionalMean P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sum_conditionalMean_on_part P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr hparts fun _ _ => rfl

theorem mean_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (conditionalMean P f) = mean f := by
  change (𝔼 x, conditionalMean P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, sum_conditionalMean P f]

theorem conditionalMean_sq_le {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P f x ^ 2 ≤
      conditionalMean P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [conditionalMean,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h

noncomputable def partitionEnergy {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => conditionalMean P f x ^ 2

theorem partitionEnergy_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ partitionEnergy P f := by
  exact mean_nonneg fun x => sq_nonneg _

theorem partitionEnergy_le_mean_sq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    partitionEnergy P f ≤ mean fun x => f x ^ 2 := by
  calc
    partitionEnergy P f ≤
        mean (conditionalMean P fun x => f x ^ 2) :=
      mean_mono fun x => conditionalMean_sq_le P f x
    _ = mean (fun x => f x ^ 2) :=
      mean_conditionalMean P fun x => f x ^ 2

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

abbrev FacePartition (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :=
  Finpartition (Finset.univ : Finset Ω)

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ext_of_part_eq {P Q : FacePartition Ω}
    (h : ∀ x, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    have hxs : Q.part x = s :=
      (h x).symm.trans (P.part_eq_of_mem hs hx)
    rw [← hxs]
    exact Q.part_mem.2 (Finset.mem_univ x)
  · intro hs
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hs
    have hxs : P.part x = s :=
      (h x).trans (Q.part_eq_of_mem hs hx)
    rw [← hxs]
    exact P.part_mem.2 (Finset.mem_univ x)

theorem part_subset_of_le {P Q : FacePartition Ω}
    (h : P ≤ Q) (x : Ω) :
    P.part x ⊆ Q.part x := by
  obtain ⟨s, hs, hsub⟩ :=
    h (P.part_mem.2 (Finset.mem_univ x))
  have hxs : x ∈ s :=
    hsub (P.mem_part (Finset.mem_univ x))
  rw [Q.part_eq_of_mem hs hxs]
  exact hsub

theorem le_iff_part_subset {P Q : FacePartition Ω} :
    P ≤ Q ↔ ∀ x, P.part x ⊆ Q.part x := by
  constructor
  · exact fun h x => part_subset_of_le h x
  · intro h s hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), ?_⟩
    rw [← P.part_eq_of_mem hs hx]
    exact h x

def indiscrete : FacePartition Ω :=
  ⊤

def discrete : FacePartition Ω :=
  ⊥

@[simp]
theorem part_indiscrete (x : Ω) :
    (indiscrete : FacePartition Ω).part x = Finset.univ := by
  change (⊤ : FacePartition Ω).part x = Finset.univ
  have hmem :
      (⊤ : FacePartition Ω).part x ∈
        (⊤ : FacePartition Ω).parts :=
    (⊤ : FacePartition Ω).part_mem.2 (Finset.mem_univ x)
  exact Finset.mem_singleton.mp
    (Finpartition.parts_top_subset
      (Finset.univ : Finset Ω) hmem)

@[simp]
theorem part_discrete (x : Ω) :
    (discrete : FacePartition Ω).part x = {x} := by
  apply Finpartition.part_eq_of_mem
  · rw [discrete, Finpartition.mem_bot_iff]
    exact ⟨x, Finset.mem_univ x, rfl⟩
  · exact Finset.mem_singleton_self x

def complexity (P : FacePartition Ω) : ℕ :=
  P.parts.card

noncomputable def representative
    (P : FacePartition Ω) (a : P.parts) : Ω :=
  Classical.choose (P.nonempty_of_mem_parts a.2)

theorem representative_mem
    (P : FacePartition Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)

@[simp]
theorem complexity_discrete :
    complexity (discrete : FacePartition Ω) = Fintype.card Ω := by
  simp [complexity, discrete]

@[simp]
theorem complexity_indiscrete [Nonempty Ω] :
    complexity (indiscrete : FacePartition Ω) = 1 := by
  let x : Ω := Classical.choice inferInstance
  have huniv :
      (Finset.univ : Finset Ω) ∈
        (⊤ : FacePartition Ω).parts := by
    have hx :=
      (⊤ : FacePartition Ω).part_mem.2
        (Finset.mem_univ x)
    change
      (indiscrete : FacePartition Ω).part x ∈
        (indiscrete : FacePartition Ω).parts at hx
    rw [part_indiscrete] at hx
    exact hx
  have hparts :
      (⊤ : FacePartition Ω).parts =
        {(Finset.univ : Finset Ω)} := by
    apply Finset.Subset.antisymm
    · exact Finpartition.parts_top_subset _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      simpa [hs] using huniv
  simp [complexity, indiscrete, hparts]

def join (P Q : FacePartition Ω) : FacePartition Ω :=
  P ⊓ Q

theorem join_le_left (P Q : FacePartition Ω) :
    join P Q ≤ P :=
  inf_le_left

theorem join_le_right (P Q : FacePartition Ω) :
    join P Q ≤ Q :=
  inf_le_right

theorem le_join_iff {P Q R : FacePartition Ω} :
    R ≤ join P Q ↔ R ≤ P ∧ R ≤ Q :=
  le_inf_iff

@[simp]
theorem part_join (P Q : FacePartition Ω) (x : Ω) :
    (join P Q).part x = P.part x ∩ Q.part x := by
  apply Finpartition.part_eq_of_mem
  · rw [join, Finpartition.parts_inf]
    apply Finset.mem_erase.mpr
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(P.part x, Q.part x), ?_, rfl⟩
      simp
  · simp

theorem complexity_join_le (P Q : FacePartition Ω) :
    complexity (join P Q) ≤ complexity P * complexity Q := by
  change (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card
  calc
    (P ⊓ Q).parts.card =
        (((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).erase ⊥).card :=
      congrArg Finset.card (Finpartition.parts_inf P Q)
    _ ≤
        ((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (P.parts ×ˢ Q.parts).card :=
      Finset.card_image_le
    _ = P.parts.card * Q.parts.card :=
      Finset.card_product P.parts Q.parts

def joinFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω) :
    FacePartition Ω :=
  s.inf P

@[simp]
theorem joinFinset_empty {ι : Type*} [DecidableEq ι]
    (P : ι → FacePartition Ω) :
    joinFinset ∅ P = indiscrete :=
  rfl

@[simp]
theorem joinFinset_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (P : ι → FacePartition Ω) :
    joinFinset (insert a s) P =
      join (P a) (joinFinset s P) := by
  simp [joinFinset, join]

theorem joinFinset_le_of_mem {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : ι → FacePartition Ω)
    {i : ι} (hi : i ∈ s) :
    joinFinset s P ≤ P i :=
  Finset.inf_le hi

theorem le_joinFinset_iff {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {P : ι → FacePartition Ω}
    {Q : FacePartition Ω} :
    Q ≤ joinFinset s P ↔ ∀ i ∈ s, Q ≤ P i :=
  Finset.le_inf_iff

theorem mem_part_joinFinset_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω)
    (x y : Ω) :
    y ∈ (joinFinset s P).part x ↔
      ∀ i ∈ s, y ∈ (P i).part x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [joinFinset_empty]
      simp
  | @insert a s ha ih =>
      simp only [joinFinset_insert, part_join,
        Finset.mem_inter, Finset.mem_insert, forall_eq_or_imp,
        ih]

def generatedBy (F : Finset (Finset Ω)) : FacePartition Ω :=
  Finpartition.atomise Finset.univ F

@[simp]
theorem mem_part_generatedBy_iff (F : Finset (Finset Ω))
    (x y : Ω) :
    y ∈ (generatedBy F).part x ↔
      ∀ s ∈ F, (x ∈ s ↔ y ∈ s) := by
  classical
  let P : FacePartition Ω := generatedBy F
  have hp : P.part x ∈ P.parts :=
    P.part_mem.2 (Finset.mem_univ x)
  have hpAtom :
      P.part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts := by
    change
      (Finpartition.atomise
        (Finset.univ : Finset Ω) F).part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts at hp
    exact hp
  obtain ⟨_, Q, hQ, hpart⟩ :=
    Finpartition.mem_atomise.mp hpAtom
  have hmem := Finset.ext_iff.mp hpart
  have hx : x ∈ P.part x :=
    P.mem_part (Finset.mem_univ x)
  have hxAtom := (hmem x).2 hx
  simp only [Finset.mem_filter] at hxAtom
  constructor
  · intro hy s hs
    have hyAtom := (hmem y).2 hy
    simp only [Finset.mem_filter] at hyAtom
    exact (hxAtom.2 s hs).symm.trans (hyAtom.2 s hs)
  · intro hsignature
    apply (hmem y).1
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    intro s hs
    exact (hxAtom.2 s hs).trans (hsignature s hs)

theorem generatedBy_antitone {F G : Finset (Finset Ω)}
    (hFG : F ⊆ G) :
    generatedBy G ≤ generatedBy F := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_generatedBy_iff] at hy ⊢
  intro s hs
  exact hy s (hFG hs)

theorem complexity_generatedBy_le (F : Finset (Finset Ω)) :
    complexity (generatedBy F) ≤ 2 ^ F.card := by
  exact Finpartition.card_atomise_le

@[simp]
theorem generatedBy_empty :
    generatedBy (∅ : Finset (Finset Ω)) =
      indiscrete := by
  apply ext_of_part_eq
  intro x
  ext y
  simp [mem_part_generatedBy_iff, part_indiscrete]

abbrev atomSetoid (P : FacePartition Ω) : Setoid Ω :=
  Setoid.ker P.part

@[simp]
theorem atomSetoid_rel (P : FacePartition Ω) (x y : Ω) :
    atomSetoid P x y ↔ P.part x = P.part y :=
  Iff.rfl

def pullbackSetoid {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : Setoid Ω where
  r x y := Q.part (f x) = Q.part (f y)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

instance instDecidableRelPullbackSetoid {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) :
    DecidableRel (pullbackSetoid f Q) := by
  intro x y
  change Decidable (Q.part (f x) = Q.part (f y))
  infer_instance

def pullback {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : FacePartition Ω :=
  Finpartition.ofSetoid (pullbackSetoid f Q)

@[simp]
theorem mem_part_pullback_iff {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      Q.part (f x) = Q.part (f y) := by
  change
    y ∈
        (Finpartition.ofSetoid
          (pullbackSetoid f Q)).part x ↔
      Q.part (f x) = Q.part (f y)
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

theorem mem_part_pullback_iff_image_mem {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      f y ∈ Q.part (f x) := by
  rw [mem_part_pullback_iff]
  constructor
  · intro h
    exact
      (Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).2 h.symm
  · intro h
    exact
      ((Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).1 h).symm

theorem pullback_mono {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) {P Q : FacePartition Λ}
    (h : P ≤ Q) :
    pullback f P ≤ pullback f Q := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_pullback_iff_image_mem] at hy ⊢
  exact part_subset_of_le h (f x) hy

@[simp]
theorem pullback_id (P : FacePartition Ω) :
    pullback id P = P := by
  apply ext_of_part_eq
  intro x
  ext y
  simp only [mem_part_pullback_iff_image_mem, id_eq]

end FacePartition

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem sum_conditionalMean_on_coarser_part
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  let fineParts : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have hUnion : fineParts.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 hxt
    · intro hxs
      obtain ⟨t, ht, hxt⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, htu⟩ := hPQ ht
      have hus : u = s :=
        Q.eq_of_mem_parts hu hs (htu hxt) hxs
      have hts : t ⊆ s := by
        simpa [hus] using htu
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩, hxt⟩
  have hdisjoint :
      (↑fineParts : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ fineParts.biUnion id,
          conditionalMean P f x := by
      exact Finset.sum_congr hUnion.symm fun _ _ => rfl
    _ =
        ∑ t ∈ fineParts,
          ∑ x ∈ t, conditionalMean P f x :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ fineParts, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_conditionalMean_on_part P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ fineParts.biUnion id, f x :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr hUnion fun _ _ => rfl

@[simp]
theorem conditionalMean_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean Q (conditionalMean P f) x =
      conditionalMean Q f x := by
  change
    Finset.expect (Q.part x) (conditionalMean P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    sum_conditionalMean_on_coarser_part P Q hPQ f
      (Q.part_mem.2 (Finset.mem_univ x))]

@[simp]
theorem conditionalMean_reverse_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean Q f) x =
      conditionalMean Q f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean Q f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part Q f
        (FacePartition.part_subset_of_le hPQ x hy)
    _ = conditionalMean Q f x :=
      Finset.expect_const (by simp) _

theorem conditionalMean_mul_right_of_constant_on_part
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    conditionalMean P (fun y => u y * v y) x =
      conditionalMean P u x * v x := by
  calc
    conditionalMean P (fun y => u y * v y) x =
        conditionalMean P (fun y => v x * u y) x := by
      rw [conditionalMean, conditionalMean]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * conditionalMean P u x :=
      conditionalMean_smul P (v x) u x
    _ = conditionalMean P u x * v x := by
      ring

theorem conditionalMean_mul_conditionalMean_right
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => u y * conditionalMean P v y) x =
      conditionalMean P u x * conditionalMean P v x := by
  apply conditionalMean_mul_right_of_constant_on_part
  intro y hy
  exact conditionalMean_eq_of_mem_part P v hy

theorem mean_conditionalMean_mul_eq_sq_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      conditionalMean P f x * conditionalMean Q f x) =
      mean (fun x => conditionalMean Q f x ^ 2) := by
  calc
    mean (fun x =>
        conditionalMean P f x * conditionalMean Q f x) =
        mean (conditionalMean Q (fun x =>
          conditionalMean P f x * conditionalMean Q f x)) :=
      (mean_conditionalMean Q _).symm
    _ =
        mean (fun x =>
          conditionalMean Q (conditionalMean P f) x *
            conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_conditionalMean_right
        Q (conditionalMean P f) f x
    _ =
        mean (fun x =>
          conditionalMean Q f x * conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      rw [conditionalMean_tower_of_le P Q hPQ]
    _ = mean (fun x => conditionalMean Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]

theorem partitionEnergy_pythagorean
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f =
      partitionEnergy Q f +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) := by
  have hcross :=
    mean_conditionalMean_mul_eq_sq_of_le P Q hPQ f
  have hdiff :
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) =
        mean (fun x => conditionalMean P f x ^ 2) -
          2 * mean (fun x =>
            conditionalMean P f x * conditionalMean Q f x) +
          mean (fun x => conditionalMean Q f x ^ 2) := by
    calc
      mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) =
          mean (fun x =>
            conditionalMean P f x ^ 2 -
              2 * (conditionalMean P f x *
                conditionalMean Q f x) +
              conditionalMean Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => conditionalMean P f x ^ 2) -
            2 * mean (fun x =>
              conditionalMean P f x * conditionalMean Q f x) +
            mean (fun x => conditionalMean Q f x ^ 2) := by
        rw [mean_add, mean_sub, mean_smul]
  change
    mean (fun x => conditionalMean P f x ^ 2) =
      mean (fun x => conditionalMean Q f x ^ 2) +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2)
  rw [hdiff, hcross]
  ring

theorem partitionEnergy_sub_eq_mean_sq
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f - partitionEnergy Q f =
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  ring

theorem partitionEnergy_mono
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy Q f ≤ partitionEnergy P f := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  exact le_add_of_nonneg_right
    (mean_nonneg fun x => sq_nonneg _)

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerMinorNormalization
namespace OAI

section

namespace Erdos3

theorem integer_row_normalization_entry {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    (H * (H.submatrix p id)⁻¹) i j =
      ((Z.submatrix (Function.update p j i) id).det : ℚ) / ((Z.submatrix p id).det : ℚ) := by
  let H := Z.map (Int.castRingHom ℚ)
  have hdet (q : Fin k → ι) : (H.submatrix q id).det = ((Z.submatrix q id).det : ℚ) := by
    change ((Z.submatrix q id).map (Int.castRingHom ℚ)).det = _
    exact ((Int.castRingHom ℚ).map_det _).symm
  have hp' : (H.submatrix p id).det ≠ 0 := by rw [hdet]; exact_mod_cast hp
  change (H * (H.submatrix p id)⁻¹) i j = _
  calc
    _ = (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det :=
      row_normalization_entry H p hp' i j
    _ = _ := by rw [hdet, hdet]

theorem integer_row_normalization_height {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (N : ℕ) (hN : ∀ q : Fin k → ι, (Z.submatrix q id).det.natAbs ≤ N)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    RationalHeightLE ((H * (H.submatrix p id)⁻¹) i j) N := by
  dsimp only
  rw [integer_row_normalization_entry Z p hp i j]
  exact rationalHeightLE_fraction _ _ hp (hN _) (hN _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationDenominator
namespace OAI

section

namespace Erdos3

theorem exists_integer_scaled_grid_matrix {ι κ : Type*}
    (H : Matrix ι κ ℝ) (l : ℕ) (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l) :
    ∃ Z : Matrix ι κ ℤ, Z.map (Int.castRingHom ℝ) = (l : ℝ) • H := by
  choose z hz using hgrid
  refine ⟨fun i j => z j i, ?_⟩
  ext i j
  exact congrFun (hz j) i

theorem scaled_integer_minor_eq {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H) (p : Fin k → ι) :
    ((Z.submatrix p id).det : ℝ) = t ^ k * (H.submatrix p id).det := by
  calc
    _ = ((Z.submatrix p id).map (Int.castRingHom ℝ)).det :=
      (Int.castRingHom ℝ).map_det _
    _ = (t • H.submatrix p id).det := by
      congr 1
      ext i j
      exact congrArg (fun M : Matrix ι (Fin k) ℝ => M (p i) j) hZ
    _ = _ := by rw [Matrix.det_smul, Fintype.card_fin]

theorem scaled_integer_minor_natAbs_bound {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t C : ℝ) (ht : 0 < t)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (hminor : ∀ p : Fin k → ι, |(H.submatrix p id).det| ≤ C) :
    ∀ p : Fin k → ι, (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * t ^ k) := by
  intro p
  have h : |((Z.submatrix p id).det : ℝ)| ≤ C * t ^ k := by
    rw [scaled_integer_minor_eq Z H t hZ, abs_mul, abs_of_pos (pow_pos ht _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hminor p) (pow_pos ht k).le
  have hc := h.trans (Nat.le_ceil (C * t ^ k))
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_bounded_rational_grid_matrix {ι κ : Type*}
    (A : Matrix ι κ ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, A.col j ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ i j, |A i j| ≤ C) :
    ∃ Q : Matrix ι κ ℚ, Q.map (Rat.castHom ℝ) = A ∧
      ∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C))) := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix A l hgrid
  let Q : Matrix ι κ ℚ := fun i j => (Z i j : ℚ) / l
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  refine ⟨Q, ?_, ?_⟩
  · ext i j
    change (((Z i j : ℚ) / l : ℚ) : ℝ) = A i j
    push_cast
    apply (div_eq_iff hlr.ne').mpr
    have h := congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
    change (Z i j : ℝ) = (l : ℝ) * A i j at h
    simpa only [mul_comm] using h
  · intro i j
    have hz : (Z i j).natAbs ≤ Nat.ceil ((l : ℝ) * C) := by
      have he : (Z i j : ℝ) = (l : ℝ) * A i j :=
        congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
      have hb : |(Z i j : ℝ)| ≤ (l : ℝ) * C := by
        rw [he, abs_mul, abs_of_pos hlr]
        exact mul_le_mul_of_nonneg_left (hbound i j) hlr.le
      have hc := hb.trans (Nat.le_ceil ((l : ℝ) * C))
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
    change RationalHeightLE ((Z i j : ℚ) / l) _
    have h := rationalHeightLE_fraction (Z i j) (l : ℤ)
      (by exact_mod_cast hl.ne') (hz.trans (le_max_right _ _))
      (by simpa only [Int.natAbs_natCast] using le_max_left l (Nat.ceil ((l : ℝ) * C)))
    simpa only [Int.cast_natCast] using h

theorem exists_bounded_rational_map_matrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, f (Pi.single j 1) ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ∃ Q : Matrix ι κ ℚ,
      (∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C)))) ∧
      ∀ x, f x = Q.map (Rat.castHom ℝ) *ᵥ x := by
  have hcol (j : κ) : (LinearMap.toMatrix' f).col j = f (Pi.single j 1) := by
    funext i
    exact LinearMap.toMatrix'_apply f i j
  obtain ⟨Q, hQ, hheight⟩ := exists_bounded_rational_grid_matrix (LinearMap.toMatrix' f) l hl
    (fun j => by rw [hcol]; exact hgrid j) C (by
      intro i j
      rw [LinearMap.toMatrix'_apply]
      have h := (norm_le_pi_norm (f (Pi.single j 1)) i).trans (hbound (Pi.single j 1))
      simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using h)
  refine ⟨Q, hheight, fun x => ?_⟩
  rw [hQ]
  exact (LinearMap.toMatrix'_mulVec f x).symm

end Erdos3

end

section

namespace Erdos3

theorem scaled_integer_row_normalization_cast {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ) (ht : t ≠ 0)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (hZp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    (W * (W.submatrix p id)⁻¹).map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
  dsimp only
  ext i j
  have he := integer_row_normalization_entry Z p hZp i j
  change (((Z.map (Int.castRingHom ℚ) *
    ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j : ℚ) : ℝ) = _
  rw [he]
  simp only [Rat.cast_div, Rat.cast_intCast]
  rw [scaled_integer_minor_eq Z H t hZ, scaled_integer_minor_eq Z H t hZ]
  rw [row_normalization_entry H p hp i j]
  field_simp

theorem exists_bounded_rational_row_normalization {ι : Type*} {k : ℕ}
    (H : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → ι, |(H.submatrix q id).det| ≤ C) :
    ∃ Q : Matrix ι (Fin k) ℚ,
      Q.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ ∧
      (∀ i j, RationalHeightLE (Q i j) (Nat.ceil (C * (l : ℝ) ^ k))) ∧
      Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix H l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z H (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  let W := Z.map (Int.castRingHom ℚ)
  let Q := W * (W.submatrix p id)⁻¹
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨Q, ?_, ?_, row_normalization_submatrix W p hWp⟩
  · exact scaled_integer_row_normalization_cast Z H (l : ℝ) hlr.ne' hZ p hp hZp
  · intro i j
    exact integer_row_normalization_height Z p hZp _
      (scaled_integer_minor_natAbs_bound Z H (l : ℝ) C hlr hZ hminor) i j

end Erdos3

end

section

namespace Erdos3

theorem integer_row_normalization_grid {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    ∀ j, (W * (W.submatrix p id)⁻¹).col j ∈
      denominatorGrid (Z.submatrix p id).det.natAbs := by
  let d := (Z.submatrix p id).det
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hp
  have habs : (d.natAbs : ℚ) = (d.sign : ℚ) * (d : ℚ) := by
    calc
      _ = ((d.natAbs : ℤ) : ℚ) := (Int.cast_natCast _).symm
      _ = ((d.sign * d : ℤ) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs d).symm
      _ = _ := Int.cast_mul _ _
  dsimp only
  intro j
  refine ⟨fun i => d.sign * (Z.submatrix (Function.update p j i) id).det, fun i => ?_⟩
  change (d.natAbs : ℚ) *
    ((Z.map (Int.castRingHom ℚ) * ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j) = _
  rw [integer_row_normalization_entry Z p hp i j]
  change (d.natAbs : ℚ) * (_ / (d : ℚ)) = _
  rw [habs, Int.cast_mul]
  field_simp

theorem exists_grid_row_normalization {ι : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : |(B.submatrix p id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix p id)⁻¹ ∧
        Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix B l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z B (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  have hbound : (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * (l : ℝ) ^ k) := by
    have h : |((Z.submatrix p id).det : ℝ)| ≤ C * (l : ℝ) ^ k := by
      rw [scaled_integer_minor_eq Z B (l : ℝ) hZ, abs_mul,
        abs_of_pos (pow_pos hlr _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hminor (pow_pos hlr k).le
    have hc := h.trans (Nat.le_ceil (C * (l : ℝ) ^ k))
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  let W := Z.map (Int.castRingHom ℚ)
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨_, Int.natAbs_pos.mpr hZp, hbound, W * (W.submatrix p id)⁻¹,
    integer_row_normalization_grid Z p hZp, ?_, row_normalization_submatrix W p hWp⟩
  exact scaled_integer_row_normalization_cast Z B (l : ℝ) hlr.ne' hZ p hp hZp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalCyclicAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cyclicInterval_zeroExtension_average {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ℤ → ℂ) :
    (𝔼 n : ZMod N, finiteIndicator (cyclicInterval (a : ZMod N) len) n * f (n.val : ℤ)) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n) := by
  let I := cyclicInterval (a : ZMod N) len
  have hrep : (𝔼 n ∈ I, f (n.val : ℤ)) =
      𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n := by
    simpa only [finiteCorrelation, one_mul, star_star] using
      cyclicInterval_representative_correlation a len hbound hshort
        (fun _ : ZMod N => (1 : ℂ)) (fun n => star (f n))
  have hstar (n : ZMod N) : star (finiteIndicator I n) = finiteIndicator I n := by
    by_cases hn : n ∈ I <;> simp [finiteIndicator, hn]
  have h := finiteCorrelation_mul_indicator I (fun _ : ZMod N => (1 : ℂ))
    (fun n => star (f (n.val : ℤ)))
  simp only [finiteCorrelation, one_mul, star_mul, star_star, hstar, hrep] at h
  have hcard : I.card = len := cyclicInterval_card _ (by omega)
  simpa only [hcard, ZMod.card, Complex.ofReal_div, Complex.ofReal_natCast, mul_comm] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseCoordinateDenominator
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {η σ : Type*} [Fintype η]

theorem majorPhaseCoordinateDenominator_pos (q : η → ℕ)
    (hq : ∀ i, 0 < q i) : 0 < ∏ i, q i :=
  Finset.prod_pos (fun i _ => hq i)

theorem majorPhaseCoordinateDenominator_le_exp (q : η → ℕ) (B : ℝ)
    (hq : ∀ i, (q i : ℝ) ≤ Real.exp B) :
    ((∏ i, q i : ℕ) : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) := by
  classical
  rw [Nat.cast_prod]
  calc
    (∏ i, (q i : ℝ)) ≤ ∏ _i : η, Real.exp B :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg (q i)) (fun i _ => hq i)
    _ = Real.exp ((Fintype.card η : ℝ) * B) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

theorem majorPhaseCoordinateDenominator_grid (q : η → ℕ)
    (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i)) (i : η) :
    (fun α => (R i).coeff α) ∈ denominatorGrid (∏ j, q j) := by
  classical
  exact denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    (hR i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]

noncomputable def unitProfileCoefficientLog (A T : ℝ≥0) : ℝ :=
  (∑ d, (Fintype.card (B d) : ℝ)) + A + T + 7

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def normalizedSiteCutoffBound : ℝ≥0 :=
  Classical.choose exists_smooth_scalar_cutoff

theorem exists_normalized_site_cutoff {D : Type*} [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ χ : (D → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → χ v = 1) ∧
      (∀ v, χ v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r)) χ := by
  obtain ⟨χ, hsmooth, hχ, hone, hzero, hLip⟩ :=
    (Classical.choose_spec exists_smooth_scalar_cutoff).2
  have hr2 : 0 < 2 * (r : ℝ) := by positivity
  refine ⟨coordinateBoxCutoff χ (2 * (r : ℝ)),
    contDiff_coordinateBoxCutoff χ hsmooth _,
    hasCompactSupport_coordinateBoxCutoff χ hzero hr2,
    coordinateBoxCutoff_range χ hχ _, ?_, ?_, ?_⟩
  · intro v hv
    apply coordinateBoxCutoff_eq_one χ hone hr2
    intro d
    have he : 2 * (r : ℝ) / 2 = r := by ring
    rw [he]
    exact hv d
  · intro v hv d
    by_contra! hd
    apply hv
    apply coordinateBoxCutoff_eq_zero χ hzero hr2
    refine ⟨d, ?_⟩
    have hr0 : (0 : ℝ) ≤ r := r.coe_nonneg
    linarith
  · simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      lipschitz_coordinateBoxCutoff χ normalizedSiteCutoffBound (2 * r) (by positivity) hχ hLip

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SortedLayerCoordinateEnumeration
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {m : ℕ} (E : Fin m → Type) [∀ j, Fintype (E j)]

noncomputable def sortedLayerCoordinateEquiv :
    Fin (Fintype.card (Σ j, E j)) ≃ (Σ j, E j) :=
  (Tuple.sort (fun i : Fin (Fintype.card (Σ j, E j)) =>
    ((Fintype.equivFin (Σ j, E j)).symm i).1.val + 1)).trans
    (Fintype.equivFin (Σ j, E j)).symm

noncomputable def sortedLayerCoordinateWeight (i : Fin (Fintype.card (Σ j, E j))) : ℕ :=
  (sortedLayerCoordinateEquiv E i).1.val + 1

theorem sortedLayerCoordinateWeight_pos (i : Fin (Fintype.card (Σ j, E j))) :
    1 ≤ sortedLayerCoordinateWeight E i := Nat.succ_le_succ (Nat.zero_le _)

theorem sortedLayerCoordinateWeight_le (i : Fin (Fintype.card (Σ j, E j))) :
    sortedLayerCoordinateWeight E i ≤ m :=
  Nat.succ_le_of_lt (sortedLayerCoordinateEquiv E i).1.isLt

theorem sortedLayerCoordinateWeight_mono : Monotone (sortedLayerCoordinateWeight E) :=
  Tuple.monotone_sort (fun i : Fin (Fintype.card (Σ j, E j)) =>
    ((Fintype.equivFin (Σ j, E j)).symm i).1.val + 1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3

abbrev DenseResidueSliceNetCode (X : Type*) (Q K : ℕ) :=
  Fin (Q + 1) × (X → Fin (Q + 1)) × (X → Fin (K + 1)) × (X → Fin (K + 1))

namespace DenseResidueSliceNetCode

variable {X : Type*} {Q K : ℕ}

def stride (c : DenseResidueSliceNetCode X Q K) : ℕ := c.1.val

def start (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  (c.2.1 i).val + c.stride * (M * (c.2.2.1 i).val)

def length (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  M * (c.2.2.2 i).val - M * (c.2.2.1 i).val

def Valid (N : X → ℕ) (H : ℝ) (M : ℕ) (c : DenseResidueSliceNetCode X Q K) : Prop :=
  0 < c.stride ∧
    (∀ i j, j < c.length M i → c.start M i + c.stride * j < N i) ∧
    ∀ i, H / 2 ≤ (c.length M i : ℝ)

def fullParent (N : X → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside i j hj := by simpa using hj

noncomputable def realize (N : X → ℕ) (H : ℝ) (M : ℕ)
    (c : DenseResidueSliceNetCode X Q K) : Σ q, ResidueBoxSlice N q := by
  classical
  exact if h : c.Valid N H M then
    ⟨c.stride, ⟨c.start M, c.length M, h.2.1⟩⟩ else ⟨1, fullParent N⟩

theorem card [Fintype X] [DecidableEq X] (Q K : ℕ) :
    Fintype.card (DenseResidueSliceNetCode X Q K) =
      (Q + 1) * ((Q + 1) * (K + 1) ^ 2) ^ Fintype.card X := by
  simp only [DenseResidueSliceNetCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [mul_pow, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
  ring

def meshCode {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M) :
    DenseResidueSliceNetCode X Q K :=
  ⟨⟨q, Nat.lt_succ_of_le hqQ⟩,
    (fun i => ⟨S.start i % q, (Nat.mod_lt _ hq).trans_le (Nat.le_succ_of_le hqQ)⟩),
    (fun i => ⟨S.start i / q / M + 1, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).1)⟩),
    (fun i => ⟨(S.start i / q + S.length i) / M, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).2)⟩)⟩

end DenseResidueSliceNetCode
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSliceSupport (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

theorem fullSlicePointInIntegerBox_injective (S : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective S.fullSlicePointInIntegerBox := by
  intro u v he
  funext i
  apply Fin.ext
  have hi := congrArg (fun x : integerBox N => x.val i) he
  change ((S.start i + q * (u i).val : ℕ) : ℤ) =
    ((S.start i + q * (v i).val : ℕ) : ℤ) at hi
  have hi' : S.start i + q * (u i).val = S.start i + q * (v i).val := by
    exact_mod_cast hi
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel hi')

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDependentMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] (s : I ↪ J)
variable (X : J → Type*) [∀ j, MeasurableSpace (X j)]

noncomputable def selectedDependentEquiv :
    ((∀ j : UnselectedColumn s, X j.val) × (∀ i, X (s i))) ≃ᵐ (∀ j, X j) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun j : UnselectedColumn s ⊕ I => X (selectedFreeFirstEquiv s j))).symm.trans
      (MeasurableEquiv.piCongrLeft X (selectedFreeFirstEquiv s))

end Erdos3

end

end OAI

end


