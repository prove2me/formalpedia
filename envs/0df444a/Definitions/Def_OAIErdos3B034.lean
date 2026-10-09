-- Prove2me | Definitions.Def_OAIErdos3B034
-- name    : OAIErdos3B034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:10:10.078718+00:00
-- url     : https://prove2.me/theorems/77fd5c6f-881d-4e15-ad6b-826aabd477b6
-- title:
--   OpenAI Erdős-3 split, definitions bundle 35 of 132
-- statement:
--   Definitions bundle 35 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B033`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 35 available.
--
--   Modules: `OAI.Erdos3.BoolLieFamily`, `OAI.Erdos3.BoolLieFamily.instContinuousSMul`, `OAI.Erdos3.BoolLieFamily.instIsTopologicalAddGroup`, `OAI.Erdos3.BoolLieFamily.instLieAlgebra`, `OAI.Erdos3.BoolLieFamily.instLieRing`, `OAI.Erdos3.BoolLieFamily.instT2Space`, `OAI.Erdos3.BoolLieFamily.instTopologicalSpace`, `OAI.Erdos3.CircleFourier.CircleAverageTuple`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_const`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_eigenfunction`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_eq_integral`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_equivariant`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_invariant`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_lipschitz`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_norm_le`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_sub`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_sub_norm_le`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_sum`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.average_unit_interval`, `OAI.Erdos3.CircleFourier.circleAverageTupleBorelSpace`, `OAI.Erdos3.CircleFourier.circleAverageTupleCompactSpace`, `OAI.Erdos3.CircleFourier.circleAverageTupleMeasurableSpace`, `OAI.Erdos3.CircleFourier.circleAverageTupleMeasure`, `OAI.Erdos3.CircleFourier.circleAverageTupleMeasure_probability`, `OAI.Erdos3.CircleFourier.circleAverageTupleSecondCountableTopology`, `OAI.Erdos3.CircleFourier.circleAverageTupleTopologicalSpace`, `OAI.Erdos3.CircleFourier.continuous_iteratedCircleAction`, `OAI.Erdos3.CircleFourier.continuous_iteratedCircleAction_parameter`, `OAI.Erdos3.CircleFourier.integrable_iteratedCircleAction`, `OAI.Erdos3.CircleFourier.integral_circleCharacter`, `OAI.Erdos3.CircleFourier.iteratedCircleAction`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_eigenfunction`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_eq_integral`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_family_tested_weighted_error`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_invariant`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_lipschitz`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_norm_le`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_sub_norm_le`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_sum`, `OAI.Erdos3.CircleFourier.iteratedCircleAverage_unit_interval`, `OAI.Erdos3.CircleFourier.lipschitz_finite_complex_sum`, `OAI.Erdos3.CyclicNiltestShiftBound`, `OAI.Erdos3.CyclicNiltestUpperComparison`, `OAI.Erdos3.CyclicNiltestUpperComparison.test_positive`, `OAI.Erdos3.FiniteProbabilityWeights.finite_projection_tested_error`, `OAI.Erdos3.FiniteProbabilityWeights.norm_tested_difference_le`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraph`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLayer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLayer_induction`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLayer_le_degree`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraph_lie`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraph_mem_degree`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraph_mem_graphLayer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraph_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_le_of_generators`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_le_product`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_terminal`, `OAI.Erdos3.NativeNilsequenceExpansion.mul`, `OAI.Erdos3.NativeNilsequenceExpansion.ofFamily`, `OAI.Erdos3.NativeNilsequenceExpansion.ofProduct`, `OAI.Erdos3.NativeNilsequenceExpansion.weightedSum`, `OAI.Erdos3.NativeVectorEquivalence.mono`, `OAI.Erdos3.NativeVectorEquivalence.symm`, `OAI.Erdos3.NativeVectorEquivalence.trans`, `OAI.Erdos3.NilpotentLieBCHGroup.central_span_character`, `OAI.Erdos3.NilpotentLieFiltration.SymbolFactorizationIn.dilate_ratio`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_grade_fixed`, `OAI.Erdos3.NilpotentLieFiltration.descended_square_mode_frequency_restriction`, `OAI.Erdos3.NilpotentLieFiltration.exists_lipschitz_realSquare_descent`, `OAI.Erdos3.NilpotentLieFiltration.frequency_zero_on_refiltered_top`, `OAI.Erdos3.NilpotentLieFiltration.mem_pivotAnnihilatorIdeal`, `OAI.Erdos3.NilpotentLieFiltration.pivotAnnihilatorIdeal`, `OAI.Erdos3.NilpotentLieFiltration.pivotProductMarkedMap`, `OAI.Erdos3.NilpotentLieFiltration.pivotProductMarkedMap_quotient`, `OAI.Erdos3.NilpotentLieFiltration.pivotProductQuotientMap`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientFrequency`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientFrequency_mk`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientMarkedMap`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientMarkedMap_mk`, `OAI.Erdos3.NilpotentLieFiltration.realSquareFstHom`, `OAI.Erdos3.NilpotentLieFiltration.realSquareLattice_le_fst`, `OAI.Erdos3.NilpotentLieFiltration.realSquareLattice_le_snd`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_mk`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_norm_le`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_recovers_product`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_relative_character`, `OAI.Erdos3.NilpotentLieFiltration.realSquareObservable_top_invariant`, `OAI.Erdos3.NilpotentLieFiltration.realSquareSndHom`, `OAI.Erdos3.NilpotentLieFiltration.realSquare_descent_relative_character`, `OAI.Erdos3.NilpotentLieFiltration.real_frequency_zero_on_refiltered_top`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareEquiv_symm_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareGroupEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareGroupEquiv_fst`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareGroupEquiv_snd`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareOrbit`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareOrbit_eval`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareOrbit_fst`, `OAI.Erdos3.NilpotentLieFiltration.realifiedSquareOrbit_snd`, `OAI.Erdos3.NilpotentLieFiltration.squareLayerConstraint`, `OAI.Erdos3.NilpotentLieFiltration.squareLayer_eq_ker_constraint`, `OAI.Erdos3.NilpotentLieFiltration.squareObservable_recovers_product`, `OAI.Erdos3.NilpotentLieFiltration.square_mode_relative_frequency`, `OAI.Erdos3.PatchKernel.weight`, `OAI.Erdos3.PatchKernel.weightAlong`, `OAI.Erdos3.PatchKernel.weightAlong_lip`, `OAI.Erdos3.PatchKernel.weightAlong_value`, `OAI.Erdos3.PatchKernel.weight_lip`, `OAI.Erdos3.PatchKernel.weight_value`, `OAI.Erdos3.PolynomialTranslationLie.apply_projectedBaseCoordinates`, `OAI.Erdos3.PolynomialTranslationLie.baseLinear`, `OAI.Erdos3.PolynomialTranslationLie.baseRange`, `OAI.Erdos3.PolynomialTranslationLie.baseRangeBase`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_eval_potential`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_eval_potential_on_real_base_image`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_rational_eval_potential`, `OAI.Erdos3.PolynomialTranslationLie.bchRealTranslationHom_rational_residue`, `OAI.Erdos3.PolynomialTranslationLie.bufferedTranslationPhase_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.bufferedTranslationTermLip`, `OAI.Erdos3.PolynomialTranslationLie.bufferedTranslationTerm_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.eval_real_map_at_rational`, `OAI.Erdos3.PolynomialTranslationLie.exists_majorRationalLift_detection_budget`, `OAI.Erdos3.PolynomialTranslationLie.exists_weightedTranslationBuffered_budget`, `OAI.Erdos3.PolynomialTranslationLie.exists_weightedTranslationBuffered_scalar_budget`, `OAI.Erdos3.PolynomialTranslationLie.exists_weightedTwistedTranslation_budget`, `OAI.Erdos3.PolynomialTranslationLie.mem_baseRange`, `OAI.Erdos3.PolynomialTranslationLie.projectedBaseCoordinates`, `OAI.Erdos3.PolynomialTranslationLie.projectedPotentialRelation`, `OAI.Erdos3.PolynomialTranslationLie.projectedRestriction`, `OAI.Erdos3.PolynomialTranslationLie.projectedRestriction_base`, `OAI.Erdos3.PolynomialTranslationLie.projectedRestriction_polynomial`, `OAI.Erdos3.PolynomialTranslationLie.projectedSubalgebra`, `OAI.Erdos3.PolynomialTranslationLie.projected_pure_constant_zero`, `OAI.Erdos3.PolynomialTranslationLie.realResidueLattice_translation_residue_map`, `OAI.Erdos3.PolynomialTranslationLie.realification_pair_eq_of_rational`, `OAI.Erdos3.PolynomialTranslationLie.translationDisplacementNN`, `OAI.Erdos3.PolynomialTranslationLie.twistedBufferedTranslationPhase_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.twistedBufferedTranslationTermLip`, `OAI.Erdos3.PolynomialTranslationLie.twistedBufferedTranslationTerm_lipschitz`, `OAI.Erdos3.PolynomialTranslationLie.twistedBufferedTranslation_log_bound`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationBase_real_image_graded`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueNilmanifold`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueNilmanifold_complexity_add_log`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResiduePhaseQuotientMap`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResiduePhaseQuotientMap_mk`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueQuotientMap`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationResidueQuotientMap_mk`, `OAI.Erdos3.PositiveCyclicNiltest.mono`, `OAI.Erdos3.PositiveCyclicNiltest.rec`, `OAI.Erdos3.PositiveCyclicNiltest.unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SquarefreeBasisIndex`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SquarefreeGridStable`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.blockLayerMap_chosen_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonGraph_chosen_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonLayerBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonLayerBasis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_comparison_layer_basis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_squarefree_stable_grid`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeBasisIndex_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeBasis_permute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeBasis_structure_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeCoefficientBasis_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeFinBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeFinBasis_degree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeFinBasis_multidegree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeFinBasis_structure_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeGrid_permute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeGrid_permute_iff`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeLattice_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeLattice_permute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeModel`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeModelMultidegree`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeModel_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealPermute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealPermute_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealPermute_mul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealPermute_one`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealPermute_top`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpaceAction`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_commutes_top`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_mul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_one`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeSpacePermute_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.UnitIntervalValued`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.UnitIntervalValued.norm_le_one`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.averageCircles`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.averageCircles_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.averageCircles_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.chartKernel`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.complement`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.intervalClip`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.positiveLocalization`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_top_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.realObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.realObservable_tsupport`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.unit_interval_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.unit_interval_evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withUnitBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withUnitBound_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.cyclicOrbitPoint`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_idealInvariant_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_idealInvariant_niltest_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_optionProductMetric_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.idealQuotientOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.idealQuotientOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.invariant_of_kernel_circles`, `OAI.Erdos3.RationalFilteredNilmanifold.optionFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.optionMaps`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProduct`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductMap`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductMap_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProduct_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.piNiltest_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.pi_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.productInclusionHom`, `OAI.Erdos3.RationalFilteredNilmanifold.productInclusionHom_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productInclusion_matrix_height`, `OAI.Erdos3.RationalFilteredNilmanifold.productLayerBasis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.productMetricBound`, `OAI.Erdos3.RationalFilteredNilmanifold.productMetricBound_le`, `OAI.Erdos3.RationalFilteredNilmanifold.productMetricBound_le_exp`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable_norm_le_one`, `OAI.Erdos3.RationalFilteredNilmanifold.productObservable_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjectionHom`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjectionHom_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_joint_injective`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_joint_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_lipschitz_bound`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_matrix_height`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjection_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_symm_coordinate_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_symm_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_symm_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_symm_update_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStepProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStepProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStepProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStepProjection_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStepRealOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_observable_top_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_top_subgroup_eq_bot`, `OAI.Erdos3.RationalFilteredNilmanifold.realBCHPiEquiv_symm_single`, `OAI.Erdos3.RationalFilteredNilmanifold.sectionNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.sectionNiltest_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.sectionNiltest_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.unitBoundedPiNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.unitBoundedPiNiltest_eval`, `OAI.Erdos3.RationalHeightLE.inv`, `OAI.Erdos3.allocatedCandidateNativeMajorBudget`, `OAI.Erdos3.allocatedCandidateNativeMajorBudget_bounds`, `OAI.Erdos3.allocatedCandidateNativeMajorBudget_mono`, `OAI.Erdos3.allocatedCandidateNativeMajorBudget_nonneg`, `OAI.Erdos3.bufferedTranslationPhase`, `OAI.Erdos3.bufferedTranslationPhase_central`, `OAI.Erdos3.bufferedTranslationPhase_eq_chart`, `OAI.Erdos3.bufferedTranslationPhase_eq_phaseFunction`, `OAI.Erdos3.bufferedTranslationPhase_integerSubgroup`, `OAI.Erdos3.bufferedTranslationPhase_integer_lattice`, `OAI.Erdos3.bufferedTranslationPhase_majorSymbol`, `OAI.Erdos3.bufferedTranslationPhase_norm_le_one`, `OAI.Erdos3.bufferedTranslationQuotientPhase`, `OAI.Erdos3.bufferedTranslationQuotientPhase_mk`, `OAI.Erdos3.bufferedTranslationQuotientPhase_norm_le_one`, `OAI.Erdos3.bufferedTranslationTerm`, `OAI.Erdos3.bufferedTranslationTerm_increment_bound`, `OAI.Erdos3.bufferedTranslationTerm_integer_lattice`, `OAI.Erdos3.bufferedTranslationTerm_nonzero_iff`, `OAI.Erdos3.bufferedTranslationTerm_unique`, `OAI.Erdos3.chartCoordinateKernel`, `OAI.Erdos3.chartCoordinateKernel_lipschitz`, `OAI.Erdos3.chartCoordinateKernel_of_mem`, `OAI.Erdos3.chartCoordinateKernel_of_not_mem`, `OAI.Erdos3.chartCoordinateKernel_range`, `OAI.Erdos3.chartCoordinateKernel_support`, `OAI.Erdos3.chartKernelScaling_lipschitz`, `OAI.Erdos3.coe_productExpBound`, `OAI.Erdos3.complex_prod_unit_interval`, `OAI.Erdos3.coordinateFunctionalMatrix`, `OAI.Erdos3.coordinateImage_eq_span`, `OAI.Erdos3.cyclicProductCutoffBudget`, `OAI.Erdos3.cyclicProductDetectionBudget`, `OAI.Erdos3.cyclicProductInputBudget`, `OAI.Erdos3.cyclicProductVolumeBudget`, `OAI.Erdos3.dividedFrequency`, `OAI.Erdos3.dividedFrequency_height`, `OAI.Erdos3.euclidean_coefficient_norm_le_exp`, `OAI.Erdos3.euclidean_error_le_of_coordinate_errors`, `OAI.Erdos3.euclidean_norm_le_card_add_one_mul`, `OAI.Erdos3.exists_allocated_candidate_promoted_native_major_budget`, `OAI.Erdos3.exists_bounded_frequency_direction`, `OAI.Erdos3.exists_bounded_normalized_square_orbit`, `OAI.Erdos3.exists_bounded_realified_square_orbit`, `OAI.Erdos3.exists_frozen_correlation_budget`, `OAI.Erdos3.exists_global_error_budget`, `OAI.Erdos3.exists_majorTranslationPartnerBudget_bound`, `OAI.Erdos3.exists_normalized_complex_family`, `OAI.Erdos3.exists_productNiltestBudget_bound`, `OAI.Erdos3.exists_restricted_frequency_basis`, `OAI.Erdos3.exists_translationMajorCorrelationBudget`, `OAI.Erdos3.finiteFrequencyKernel`, `OAI.Erdos3.finiteFrequencyKernel_eq_map_coannihilator`, `OAI.Erdos3.finiteFrequencyKernel_eq_of_span_eq`, `OAI.Erdos3.finiteFrequencyKernel_le`, `OAI.Erdos3.finite_projection_tested_error`, `OAI.Erdos3.fixedListBudgetPolynomial`, `OAI.Erdos3.fixedListComparisonBudget`, `OAI.Erdos3.fixedListRequiredBudget`, `OAI.Erdos3.fixedListWorkingBudget`, `OAI.Erdos3.frequencyKernelProjection`, `OAI.Erdos3.frequencyKernelProjection_apply`, `OAI.Erdos3.frequencyKernelProjection_range`, `OAI.Erdos3.frequencyKernel_spanning`, `OAI.Erdos3.frequencyKernel_spanning_height`, `OAI.Erdos3.frozen_correlation_precision_error`, `OAI.Erdos3.frozen_witness_budget_mono`, `OAI.Erdos3.le_raisedNiltestBudget`, `OAI.Erdos3.lipschitzWith_complex_vector`, `OAI.Erdos3.lipschitzWith_normalize`, `OAI.Erdos3.lipschitz_mul_unit_interval`, `OAI.Erdos3.map_mem_submodule_of_basis`, `OAI.Erdos3.mem_finiteFrequencyKernel`, `OAI.Erdos3.mem_realified_frequency_kernel_iff`, `OAI.Erdos3.mem_restrictedFrequencySpan_coannihilator`, `OAI.Erdos3.norm_complex_half_le_one`, `OAI.Erdos3.norm_normalize_sub_le`, `OAI.Erdos3.norm_weighted_mean_sub_le`, `OAI.Erdos3.normalize_complex_unit_smul`, `OAI.Erdos3.optionDimension`, `OAI.Erdos3.optionLieAlgebra`, `OAI.Erdos3.optionLieRing`, `OAI.Erdos3.optionLieSpace`, `OAI.Erdos3.productExpBound`, `OAI.Erdos3.productNiltestBudget`, `OAI.Erdos3.productNiltestBudget_geometry`, `OAI.Erdos3.productNiltestBudget_observable`, `OAI.Erdos3.productObservableLipBudget`, `OAI.Erdos3.productObservableLipBudget_nonneg`, `OAI.Erdos3.raisedNiltestBudget`, `OAI.Erdos3.rationalLogHeight_nat_inv_mul`, `OAI.Erdos3.real_frequency_eq_of_character_multiples`, `OAI.Erdos3.realificationLieHom_id_apply`, `OAI.Erdos3.realification_piRight_symm_single`, `OAI.Erdos3.realifyCoordinateMap`, `OAI.Erdos3.realifyCoordinateMap_comp`, `OAI.Erdos3.realifyCoordinateMap_eq_matrix`, `OAI.Erdos3.realifyCoordinateMap_grid`, `OAI.Erdos3.realifyCoordinateMap_image_eq_span`, `OAI.Erdos3.realifyCoordinateMap_mem_span`, `OAI.Erdos3.realifyCoordinateMap_norm_bound`, `OAI.Erdos3.realifyCoordinateMap_tmul`, `OAI.Erdos3.realifyFunctional_comp`, `OAI.Erdos3.realifyFunctional_eq_rid`, `OAI.Erdos3.restrictedFrequencySpan`, `OAI.Erdos3.restrictedFrequencySpan_finRange`, `OAI.Erdos3.scalar_error_le_of_vector_error`, `OAI.Erdos3.scaledChartKernel`, `OAI.Erdos3.sum_double_half_products`, `OAI.Erdos3.translationMajorPairBudget`, `OAI.Erdos3.translationMajorPairBudget_controls`, `OAI.Erdos3.translation_cutoff_increment_bound`, `OAI.Erdos3.twistedBufferedTranslationPhase`, `OAI.Erdos3.twistedBufferedTranslationPhase_central`, `OAI.Erdos3.twistedBufferedTranslationPhase_eq_chart`, `OAI.Erdos3.twistedBufferedTranslationPhase_integer_lattice`, `OAI.Erdos3.twistedBufferedTranslationPhase_majorSymbol`, `OAI.Erdos3.twistedBufferedTranslationPhase_norm_le_one`, `OAI.Erdos3.twistedBufferedTranslationPhase_residueCover`, `OAI.Erdos3.twistedBufferedTranslationQuotientPhase`, `OAI.Erdos3.twistedBufferedTranslationQuotientPhase_mk`, `OAI.Erdos3.twistedBufferedTranslationQuotientPhase_norm_le_one`, `OAI.Erdos3.twistedBufferedTranslationTerm`, `OAI.Erdos3.twistedBufferedTranslationTerm_central`, `OAI.Erdos3.twistedBufferedTranslationTerm_integer_lattice`, `OAI.Erdos3.twistedBufferedTranslationTerm_norm_le_one`, `OAI.Erdos3.twistedBufferedTranslationTerm_unique`, `OAI.Erdos3.vector_approximation_precision`, `OAI.Erdos3.vector_approximation_precompose`, `OAI.Erdos3.vertical_frequency_eq_of_real_line`, `OAI.Erdos3.vertical_frequency_eq_one_of_real_line`, `OAI.Erdos3.vertical_frequency_integral_on_lattice`, `OAI.Erdos3.vertical_frequency_on_real_direction`, `_private.Dynamics.RealProjectedPotentialGroupIdentity.0.OAI.Erdos3.PolynomialTranslationLie.continuous_pair_potential_difference`, `_private.Dynamics.RealProjectedPotentialGroupIdentity.0.OAI.Erdos3.PolynomialTranslationLie.continuous_pair_pullback`, `_private.Estimates.WeightedTwistedTranslationLipschitz.0.OAI.Erdos3.complex_mul_sub_mul_le_unit`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B032
import Definitions.Def_OAIErdos3B033

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

def UnitIntervalValued (T : D.Niltest w) : Prop :=
  ∀ z, (T.observable z).im = 0 ∧ 0 ≤ (T.observable z).re ∧ (T.observable z).re ≤ 1

end RationalFilteredNilmanifold.Niltest

def CyclicNiltestUpperComparison.{u} (degree N : ℕ) [NeZero N]
    (P epsilon : ℝ) (f g : ZMod N → ℝ) : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE P →
    (𝔼 x : ZMod N, (f x - g x) * (T.evalCyclic N (fun _ => x)).re) ≤ epsilon

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

noncomputable def idealQuotientOrbit {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit I hI g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQF]; exact q.adapted)

theorem idealQuotientOrbit_eval {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.idealQuotientOrbit I hI Q hQF g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval I hI g x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

theorem exists_idealInvariant_niltest
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr (lieQuotientMap I (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      (∀ x, S.eval x = T.eval x) ∧
      (T.UnitIntervalValued → S.UnitIntervalValued) := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap I) (lieQuotientMap_surjective I) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff I.toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := D.idealQuotientOrbit I hI Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl) }
  refine ⟨S, rfl, rfl, rfl, hf, ?_, ?_⟩
  · intro x
    exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
      (D.idealQuotientOrbit_eval I hI Q hQF T.orbit x)).trans (hf _)
  · intro hT z
    induction z using Quotient.inductionOn with
    | h z =>
      obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) z.coord
      let g : D.RealGroup := ⟨x⟩
      have hg : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g = z :=
        NilpotentLieBCHGroup.ext hx
      have hfg := hf g
      rw [hg] at hfg
      change (f (QuotientGroup.mk z)).im = 0 ∧ 0 ≤ (f (QuotientGroup.mk z)).re ∧
        (f (QuotientGroup.mk z)).re ≤ 1
      rw [hfg]
      exact hT (QuotientGroup.mk g)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def intervalClip (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => ((max 0 (min 1 (T.observable z).re) : ℝ) : ℂ)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact (max_le (norm_nonneg _) ((min_le_right _ _).trans (Complex.re_le_norm _))).trans (T.norm_le z)
  lipschitz := by
    let := D.metricSpace
    have hr : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (T.observable x).re (T.observable y).re ≤ dist (T.observable x) (T.observable y) := by
          simpa only [Real.dist_eq, dist_eq_norm, Complex.sub_re, Real.norm_eq_abs] using
            Complex.abs_re_le_norm (T.observable x - T.observable y)
        _ ≤ T.lipBound * dist x y := T.lipschitz.dist_le_mul x y
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp ((hr.const_min 1).const_max 0)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

noncomputable def cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w
    (fun i => ((x i).val : ℤ)) g)

noncomputable def sectionNiltest
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) : D.Niltest w where
  orbit := g
  observable := fun z => (frozenRealSection F a z : ℂ)
  normBound := 1
  lipBound := M
  norm_le z := by
    have h := frozenRealSection_unit_interval F hF a z
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_one] using h.2
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    cases a with
    | none =>
      change dist (0 : ℂ) 0 ≤ (M : ℝ) * dist x y
      rw [dist_self]
      positivity
    | some a =>
      change dist (F x a : ℂ) (F y a : ℂ) ≤ (M : ℝ) * dist x y
      simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (hLip a).dist_le_mul x y

theorem sectionNiltest_unit_interval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a)) (a : Option Ξ) :
    (D.sectionNiltest g F hF M hLip a).UnitIntervalValued := by
  intro z
  exact ⟨rfl, frozenRealSection_unit_interval F hF a z⟩

theorem sectionNiltest_complexityLE
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hbudget : Real.log (3 + (M : ℝ)) ≤ p) :
    (D.sectionNiltest g F hF M hLip a).ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + (1 : ℝ) + (M : ℝ)) ≤ p
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
  exact hbudget

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CyclicNiltestShiftBound.{u} (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE p →
    (𝔼 x : ZMod N, a x * J (x + h) * (T.evalCyclic N (fun _ => x)).re) ≤ error

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem UnitIntervalValued.norm_le_one {T : D.Niltest w} (hT : T.UnitIntervalValued) (x : D.Space) :
    ‖T.observable x‖ ≤ 1 := by
  have heq : ((T.observable x).re : ℂ) = T.observable x := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hT x).1.symm
  rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT x).2.1]
  exact (hT x).2.2

noncomputable def withUnitBound (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) : D.Niltest w :=
  { T with normBound := 1, norm_le := hcap }

theorem withUnitBound_complexity (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.withUnitBound hcap).ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [Real.exp_add]
  have h := T.observable_budget hT
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg p)
  nlinarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

noncomputable def positiveLocalization : D.Niltest w where
  orbit := T.orbit
  observable z := (((T.observable z).re * psi z : ℝ) : ℂ)
  normBound := 1
  lipBound := T.lipBound + K
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT z).2.1 (hpsi z).1)]
    exact (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2
  lipschitz := by
    let := D.metricSpace
    have ht : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz
    have hproduct := bounded_weight_cutoff_lipschitz (fun z => (T.observable z).re) psi
      (B := 1)
      (fun z => by rw [abs_of_nonneg (hT z).2.1]; exact (hT z).2.2)
      (fun z => by rw [abs_of_nonneg (hpsi z).1]; exact (hpsi z).2) ht hLip
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hproduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_idealInvariant_niltest_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]
      (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
      (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
      (hQF : Q.filtration = D.filtration.quotientLie I hI)
      (_hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p) →
      (∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + 2) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        (∀ x, S.eval x = T.eval x) ∧ (T.UnitIntervalValued → S.UnitIntervalValued) := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp t
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((X + 1 + Polynomial.C a) ^ a + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ s d n D I _ _ _ _ hI Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hObs, hSe, hPos⟩ := D.exists_idealInvariant_niltest I hI Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + 2) ^ C := by
    simpa [r, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩,
    hObs, hSe, hPos⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped NNReal

namespace Erdos3

noncomputable def productExpBound (p : ℝ) : ℝ≥0 := ⟨Real.exp p, Real.exp_nonneg p⟩

@[simp] theorem coe_productExpBound (p : ℝ) : (productExpBound p : ℝ) = Real.exp p := rfl

def productObservableLipBudget (p : ℝ) : ℝ := p + (p ^ 2 + p + 3) ^ 2

def productNiltestBudget (p : ℝ) : ℝ :=
  (p + 2) ^ 2 + p + productObservableLipBudget p + p ^ 2 + 4

theorem productObservableLipBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ productObservableLipBudget p := by
  unfold productObservableLipBudget
  positivity

theorem productNiltestBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 2 ≤ productNiltestBudget p := by
  have hr := productObservableLipBudget_nonneg hp
  unfold productNiltestBudget
  nlinarith [sq_nonneg p]

theorem productNiltestBudget_observable {p : ℝ} (hp : 0 ≤ p) (m : ℕ) (hm : (m : ℝ) ≤ p) :
    2 + Real.exp p ^ m + (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤
      Real.exp (productNiltestBudget p) := by
  let A := p + productObservableLipBudget p + p ^ 2
  have hR := productObservableLipBudget_nonneg hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : Real.exp p ^ m ≤ Real.exp (p ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hB' : Real.exp p ^ m ≤ Real.exp A := hB.trans (Real.exp_le_exp.mpr (by dsimp [A]; linarith))
  have hK : (m : ℝ) * Real.exp (productObservableLipBudget p) * Real.exp p ^ m ≤ Real.exp A := by
    calc
      _ ≤ Real.exp p * Real.exp (productObservableLipBudget p) * Real.exp (p ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp A := by linarith [Real.one_le_exp_iff.mpr hA]
    _ ≤ Real.exp 4 * Real.exp A := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = Real.exp (4 + A) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold productNiltestBudget; dsimp [A]; nlinarith [sq_nonneg (p + 2)])

theorem exists_productNiltestBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → productNiltestBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget] using hbound p hp

end Erdos3

end

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (j : Fin (s + 1))
    (k : Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) (l : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr ((productLayerBasis D j k).val) l) ≤ p := by
  classical
  rcases k with ⟨a, k⟩
  rcases l with ⟨b, l⟩
  simp only [productLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (D i).layerBasis j)) ⟨a, k⟩ b).val) l) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hD a).2.2.2 j k l
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

theorem pi_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (pi D).GeometryComplexityLE ((p + 2) ^ 2) := by
  classical
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hgrid : ((∏ i, (D i).grid : ℕ) : ℝ) ≤ Real.exp (p ^ 2) :=
    product_denominator_le_budget (fun i => (D i).grid) hp hι (fun i => (hD i).2.1)
  have hsmall : p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hsq : p ^ 2 ≤ (p + 2) ^ 2 := by nlinarith
  refine ⟨hdim.trans hsq, hgrid.trans (Real.exp_le_exp.mpr hsq), ?_, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (productFinBasis D) i j k) ≤ _
    rw [productFinBasis, lieStructureConstants_reindex]
    have hh := lie_pi_structure_height (fun i => (D i).basis) (one_le_ceil_exp p)
      (fun a i j k => rationalHeightLE_ceil_exp ((hD a).2.2.1 i j k))
    exact (rationalLogHeight_le_of_height (hh _ _ _) (ceil_exp_le_exp_add_one hp)).trans hsmall
  · change ∀ (j : Fin (s + 1))
      (k : Fin (finrank ℚ ((NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer (j.val + 1))))
      (l : Fin (Fintype.card (Σ i, Fin (d i)))),
        rationalLogHeight ((productFinBasis D).repr ((productLayerFinBasis D j k).val) l) ≤ (p + 2) ^ 2
    intro j k l
    rw [productFinBasis, Basis.repr_reindex_apply, productLayerFinBasis, Basis.reindex_apply]
    apply le_trans _ (show p ≤ (p + 2) ^ 2 by linarith)
    exact productLayerBasis_logHeight D hp hD j _ _

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_lattice (i : ι) :
    (pi D).lattice ≤ (D i).lattice.comap (NilpotentLieBCHGroup.mapOfSteps (liePiEval i)) := by
  intro g hg
  exact (mem_piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice) g).mp hg i

noncomputable def productProjectionHom (i : ι) : (pi D).RealGroup →* (D i).RealGroup :=
  NilpotentLieBCHGroup.realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
    (hM := (D i).filtration.lowerCentralSeries_eq_bot) (liePiEval i)

noncomputable def productProjection (i : ι) : (pi D).Space → (D i).Space :=
  cosetMap (pi D).realLattice (D i).realLattice (productProjectionHom D i)
    (NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _ (productProjection_lattice D i))

@[simp] theorem productProjection_mk (i : ι) (g : (pi D).RealGroup) :
    productProjection D i (QuotientGroup.mk g) = QuotientGroup.mk (productProjectionHom D i g) := rfl

theorem productProjection_matrix_height (i : ι)
    (j : Fin (Fintype.card (Σ i, Fin (d i)))) (k : Fin (d i)) :
    RationalHeightLE ((D i).basis.repr (liePiEval (R := ℚ) i ((pi D).basis j)) k) 1 := by
  classical
  change RationalHeightLE ((D i).basis.repr (productFinBasis D j i) k) 1
  rw [productFinBasis, Basis.reindex_apply]
  generalize he : (Fintype.equivFin (Σ i, Fin (d i))).symm j = z
  rcases z with ⟨a, l⟩
  rw [Pi.basis_apply]
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Basis.repr_self]
    by_cases hlk : l = k <;> simp [hlk, RationalHeightLE]
  · rw [Pi.single_eq_of_ne (Ne.symm hai), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productProjection_lipschitz (i : ι) :
    letI := (pi D).metricSpace
    letI := (D i).metricSpace
    LipschitzWith (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1)
      (productProjection D i) := by
  let := realificationQuotientMetricSpace (pi D).basis (pi D).lattice
    (pi D).grid (pi D).grid_pos (pi D).outer_grid
  let := realificationQuotientMetricSpace (D i).basis (D i).lattice
    (D i).grid (D i).grid_pos (D i).outer_grid
  have hh := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (pi D).basis (D i).basis (liePiEval i) (pi D).lattice (D i).lattice
    (productProjection_lattice D i) (pi D).grid (D i).grid (pi D).grid_pos (D i).grid_pos
    (pi D).outer_grid (D i).outer_grid 1 (fun k j => productProjection_matrix_height D i j k)
  exact hh.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

omit [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productProjection_lipschitz_bound {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (i : ι) :
    (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤
      Real.exp ((p ^ 2 + p + 3) ^ 2) := by
  have hdim := sigma_card_le_budget hp hι
    (κ := fun i => Fin (d i)) (fun i => by simpa only [Fintype.card_fin] using (hD i).1)
  have hi := (hD i).1
  have hq : 0 ≤ p ^ 2 + p + 1 := by positivity
  have hh := coordinateLipschitzBound_le_exp (d i) (Fintype.card (Σ i, Fin (d i))) 1 hq
    (by nlinarith [sq_nonneg p]) (by linarith)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hq)
  convert hh using 2
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

def optionLieSpace {ι : Type v} (L₀ : Type u) (L : ι → Type u) : Option ι → Type u
  | none => L₀
  | some i => L i

instance optionLieRing {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] (i : Option ι) : LieRing (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

instance optionLieAlgebra {ι : Type v} {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    (i : Option ι) : LieAlgebra ℚ (optionLieSpace L₀ L i) := by
  cases i <;> dsimp [optionLieSpace] <;> infer_instance

def optionDimension {ι : Type v} (d₀ : ℕ) (d : ι → ℕ) : Option ι → ℕ
  | none => d₀
  | some i => d i

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionFactors : ∀ i : Option ι,
    RationalFilteredNilmanifold (optionLieSpace L₀ L i) s (optionDimension d₀ d i)
  | none => D₀
  | some i => D i

noncomputable def optionProduct := pi (optionFactors D₀ D)

theorem optionProduct_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD₀ : D₀.GeometryComplexityLE p) (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (optionProduct D₀ D).GeometryComplexityLE ((p + 3) ^ 2) := by
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have h := pi_geometry (optionFactors D₀ D) (p := p + 1) (by linarith)
    (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
    (fun i => by cases i with
      | none => exact hD₀.mono D₀ hpp
      | some i => exact (hD i).mono (D i) hpp)
  simpa only [optionProduct, show p + 1 + 2 = p + 3 by ring] using h

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

def optionMaps (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    ∀ i : Option ι, H →ₗ⁅ℚ⁆ optionLieSpace L₀ L i
  | none => φ₀
  | some i => φ i

def optionProductMap (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    H →ₗ⁅ℚ⁆ (∀ i : Option ι, optionLieSpace L₀ L i) :=
  liePiMap (optionMaps φ₀ φ)

theorem optionProductMap_logHeight {κ : Type*} (b : Basis κ ℚ H)
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ}
    (h₀ : ∀ i j, rationalLogHeight (D₀.basis.repr (φ₀ (b j)) i) ≤ p)
    (hφ : ∀ a i j, rationalLogHeight ((D a).basis.repr (φ a (b j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ (b j)) i) ≤ p := by
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k j
  | some a => exact hφ a k j

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

noncomputable def productObservable (T : ∀ i, (D i).Niltest w) (z : (pi D).Space) : ℂ :=
  ∏ i, (T i).observable (productProjection D i z)

theorem productObservable_bounds (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    letI := (pi D).metricSpace
    (∀ z, ‖productObservable D T z‖ ≤ Real.exp p ^ Fintype.card ι) ∧
    LipschitzWith ((Fintype.card ι : ℝ≥0) *
      productExpBound (productObservableLipBudget p) *
        productExpBound p ^ Fintype.card ι) (productObservable D T) := by
  let := (pi D).metricSpace
  have hB : (1 : ℝ≥0) ≤ productExpBound p := Real.one_le_exp_iff.mpr hp
  have hnorm (i : ι) (z : (pi D).Space) :
      ‖(T i).observable (productProjection D i z)‖ ≤ Real.exp p := by
    have hb := (T i).observable_budget (hT i)
    exact ((T i).norm_le _).trans (by linarith [(T i).lipBound.coe_nonneg])
  have hlip (i : ι) : LipschitzWith
      (productExpBound (productObservableLipBudget p))
        (fun z => (T i).observable (productProjection D i z)) := by
    let := (D i).metricSpace
    apply ((T i).lipschitz.comp (productProjection_lipschitz D i)).weaken
    change (T i).lipBound *
      (coordinateLipschitzBound (d i) (Fintype.card (Σ i, Fin (d i))) 1 : ℝ) ≤ _
    have hb := (T i).observable_budget (hT i)
    have hk : ((T i).lipBound : ℝ) ≤ Real.exp p := by linarith [(T i).normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2) :=
        mul_le_mul hk (productProjection_lipschitz_bound D hp hι (fun i => (hT i).1) i)
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  exact bounded_lipschitz_fintype_prod (fun i z => (T i).observable (productProjection D i z))
    hB hlip hnorm

noncomputable def piNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) : (pi D).Niltest w where
  orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)
  observable := productObservable D T
  normBound := productExpBound p ^ Fintype.card ι
  lipBound := (Fintype.card ι : ℝ≥0) *
    productExpBound (productObservableLipBudget p) *
      productExpBound p ^ Fintype.card ι
  norm_le z := by simpa only [NNReal.coe_pow, coe_productExpBound] using (productObservable_bounds D T hp hι hT).1 z
  lipschitz := (productObservable_bounds D T hp hι hT).2

theorem piNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) (x : σ → ℤ) :
    (piNiltest D T hp hι hT).eval x = ∏ i, (T i).eval x := by
  change (∏ i, (T i).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (fun i => (T i).orbit)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g => (T i).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (fun i => (T i).orbit) x i)

theorem piNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    (piNiltest D T hp hι hT).ComplexityLE (productNiltestBudget p) := by
  constructor
  · exact GeometryComplexityLE.mono (pi D) (pi_geometry D hp hι (fun i => (hT i).1))
      (productNiltestBudget_geometry hp)
  · change Real.log (2 + (Real.exp p) ^ Fintype.card ι +
      (Fintype.card ι : ℝ) * Real.exp (productObservableLipBudget p) * (Real.exp p) ^ Fintype.card ι) ≤ _
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    exact productNiltestBudget_observable hp _ hι

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_smul (i : ι) (g : (pi D).RealGroup) (x : (pi D).Space) :
    productProjection D i (g • x) = productProjectionHom D i g • productProjection D i x :=
  cosetMap_smul _ _ _ _ g x

theorem productProjectionHom_mem_layer (i : ι) (k : ℕ) (g : (pi D).RealGroup)
    (hg : g ∈ (pi D).filtration.realification.subgroup k) :
    productProjectionHom D i g ∈ (D i).filtration.realification.subgroup k := by
  apply baseChange_mem_of_mapsTo ((pi D).filtration.layer k) ((D i).filtration.layer k)
    (liePiEval i).toLinearMap _ hg
  intro x hx
  exact (NilpotentLieFiltration.mem_pi_layer (fun i => (D i).filtration) k x).mp hx i

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_layer D i s z hz) _

theorem piNiltest_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_vertical D T eta hvert z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_norm_le_one (T : ∀ i, (D i).Niltest w)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : (pi D).Space) :
    ‖productObservable D T x‖ ≤ 1 := by
  unfold productObservable
  calc
    _ = ∏ i, ‖(T i).observable (productProjection D i x)‖ := norm_prod _ _
    _ ≤ ∏ _i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => ((T i).norm_le _).trans (by exact_mod_cast hcap i))
    _ = 1 := by simp

noncomputable def unitBoundedPiNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) : (pi D).Niltest w :=
  { piNiltest D T hp hι hT with
    normBound := 1
    norm_le := productObservable_norm_le_one D T hcap }

theorem unitBoundedPiNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : σ → ℤ) :
    (unitBoundedPiNiltest D T hp hι hT hcap).eval x = ∏ i, (T i).eval x :=
  piNiltest_eval D T hp hι hT x

theorem unitBoundedPiNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) :
    (unitBoundedPiNiltest D T hp hι hT hcap).ComplexityLE (productNiltestBudget p) := by
  have h := piNiltest_complexity D T hp hι hT
  refine ⟨h.1, le_trans ?_ h.2⟩
  apply Real.log_le_log (by positivity)
  change 2 + 1 + ((piNiltest D T hp hι hT).lipBound : ℝ) ≤
    2 + Real.exp p ^ Fintype.card ι + ((piNiltest D T hp hι hT).lipBound : ℝ)
  have hb : 1 ≤ Real.exp p ^ Fintype.card ι := one_le_pow₀ (Real.one_le_exp_iff.mpr hp)
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem complex_prod_unit_interval {I : Type*} [Fintype I] (a : I → ℂ)
    (ha : ∀ i, (a i).im = 0 ∧ 0 ≤ (a i).re ∧ (a i).re ≤ 1) :
    (∏ i, a i).im = 0 ∧ 0 ≤ (∏ i, a i).re ∧ (∏ i, a i).re ≤ 1 := by
  have he (i : I) : a i = ((a i).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (ha i).1
  have hprod : (∏ i, a i) = ((∏ i, (a i).re : ℝ) : ℂ) := by
    calc
      _ = ∏ i, ((a i).re : ℂ) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := by rw [Complex.ofReal_prod]
  rw [hprod]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact ⟨Finset.prod_nonneg (fun i _ => (ha i).2.1),
    Finset.prod_le_one (fun i _ => (ha i).2.1) (fun i _ => (ha i).2.2)⟩

namespace RationalFilteredNilmanifold

theorem piNiltest_unit_interval {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hunit : ∀ i, (T i).UnitIntervalValued) :
    (piNiltest D T hp hι hT).UnitIntervalValued := by
  intro z
  exact complex_prod_unit_interval (fun i => (T i).observable (productProjection D i z))
    (fun i => hunit i _)

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem unit_interval_eval (T : D.Niltest w) (hT : T.UnitIntervalValued) (x : σ → ℤ) :
    (T.eval x).im = 0 ∧ 0 ≤ (T.eval x).re ∧ (T.eval x).re ≤ 1 := hT _

theorem unit_interval_evalCyclic (T : D.Niltest w) (hT : T.UnitIntervalValued)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.evalCyclic N x).im = 0 ∧ 0 ≤ (T.evalCyclic N x).re ∧ (T.evalCyclic N x).re ≤ 1 := hT _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNativeMajorBudget
namespace OAI

section

namespace Erdos3

def allocatedCandidateNativeMajorBudget (pNative v : ℝ) : ℝ :=
  productNiltestBudget pNative + pNative + v + 2

theorem allocatedCandidateNativeMajorBudget_bounds {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      productNiltestBudget pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      v ≤ allocatedCandidateNativeMajorBudget pNative v := by
  have hproduct : 0 ≤ productNiltestBudget pNative :=
    (sq_nonneg (pNative + 2)).trans (productNiltestBudget_geometry hpNative)
  unfold allocatedCandidateNativeMajorBudget
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedCandidateNativeMajorBudget_nonneg {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).1

theorem allocatedCandidateNativeMajorBudget_mono {pNative qNative v w : ℝ}
    (hpNative : 0 ≤ pNative) (hNative : pNative ≤ qNative) (hvw : v ≤ w) :
    allocatedCandidateNativeMajorBudget pNative v ≤
      allocatedCandidateNativeMajorBudget qNative w := by
  unfold allocatedCandidateNativeMajorBudget productNiltestBudget productObservableLipBudget
  gcongr

theorem exists_allocated_candidate_promoted_native_major_budget (Cnative : ℕ) :
    ∃ Cmajor : ℕ, 2 ≤ Cmajor ∧ ∀ t v pNative : ℝ,
      0 ≤ t → 0 ≤ v → v ≤ t → 0 ≤ pNative →
      pNative ≤ (t + Cnative) ^ Cnative →
      allocatedCandidateNativeMajorBudget (pNative + v + 2) v ≤
        (t + Cmajor) ^ Cmajor := by
  let X : Polynomial ℕ := Polynomial.X
  let N := (X + Polynomial.C Cnative) ^ Cnative + X + 2
  let P := (N + 2) ^ 2 + N + (N + (N ^ 2 + N + 3) ^ 2) + N ^ 2 + 4 + N + X + 2
  obtain ⟨Cmajor, hCmajor, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨Cmajor, hCmajor, ?_⟩
  intro t v pNative ht hv hvt hpNative hNative
  have hpromoted : pNative + v + 2 ≤ (t + Cnative) ^ Cnative + t + 2 := by
    linarith
  apply (allocatedCandidateNativeMajorBudget_mono (by linarith) hpromoted hvt).trans
  simpa [P, N, X, Polynomial.eval₂_pow, allocatedCandidateNativeMajorBudget,
    productNiltestBudget, productObservableLipBudget] using hbudget t ht

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicProductBudget
namespace OAI

section

namespace Erdos3

def cyclicProductInputBudget (p : ℝ) : ℝ := productNiltestBudget p + 3 * p + 17

def cyclicProductVolumeBudget (p : ℝ) : ℝ := p ^ 2 + 3 * p + 16

def cyclicProductCutoffBudget (s c : ℕ) (p : ℝ) : ℝ :=
  ((s + 3) ^ (s + 3) : ℕ) + (s + 3 : ℕ) * cyclicProductVolumeBudget p +
    (2 ^ (s + 2) : ℕ) * (cyclicProductInputBudget p + c) ^ c

def cyclicProductDetectionBudget (s c : ℕ) (p : ℝ) : ℝ :=
  (2 ^ (s + 2) + 1 : ℕ) * (cyclicProductCutoffBudget s c p + 1) + 4

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def BoolLieFamily (L₁ L₂ : Type u) : Bool → Type u
  | false => L₂
  | true => L₁

namespace BoolLieFamily

variable {L₁ L₂ : Type u} [LieRing L₁] [LieAlgebra ℚ L₁]
    [LieRing L₂] [LieAlgebra ℚ L₂]

instance instLieRing (b : Bool) : LieRing (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieRing L₂)
  · exact (inferInstance : LieRing L₁)

instance instLieAlgebra (b : Bool) : LieAlgebra ℚ (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieAlgebra ℚ L₂)
  · exact (inferInstance : LieAlgebra ℚ L₁)

variable [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)]

instance instTopologicalSpace (b : Bool) :
    TopologicalSpace (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₁))

instance instIsTopologicalAddGroup (b : Bool) :
    IsTopologicalAddGroup (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))

instance instContinuousSMul (b : Bool) :
    ContinuousSMul ℝ (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))

instance instT2Space (b : Bool) : T2Space (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₁))

end BoolLieFamily
end Erdos3

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s N : ℕ} [NeZero N] {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : I → ℂ)
    {p : ℝ} {f : ZMod N → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).evalCyclic N (fun _ => x)) :
    NativeNilsequenceExpansion s N p f := by
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
      (fun i => c i * (T i).evalCyclic N (fun _ => x))).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
    {p q : ℝ} {f : I → ZMod N → ℂ} (E : ∀ i, NativeNilsequenceExpansion s N p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeNilsequenceExpansion s N (p + q) (fun x => ∑ i, c i * f i x) := by
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

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

variable {J K : Type*} [Fintype J] [Fintype K] {s N : ℕ} [NeZero N] {p q : ℝ}
  {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}

theorem mono (E : NativeVectorEquivalence s N p chi chi') (hpq : p ≤ q) :
    NativeVectorEquivalence s N q chi chi' where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

theorem symm (E : NativeVectorEquivalence s N p chi chi') :
    NativeVectorEquivalence s N p chi' chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeNilsequenceExpansion s N p
        (fun x => star (chi j x * star (chi' k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {s d e N : ℕ} [NeZero N] {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest (fun _ : Unit => 1)) (U : E.Niltest (fun _ : Unit => 1))
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p)
      (fun x => T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x)) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact U
    · exact T
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact hU
    · exact hT
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  have hB : 1 ≤ Real.exp (productNiltestBudget p) :=
    Real.one_le_exp_iff.mpr ((sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0))
  refine ofFamily (I := Unit) (fun _ => RationalFilteredNilmanifold.pi models)
    (fun _ => S) (fun _ => 1) (by simpa using hB)
    (fun _ => RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (by simpa using hB) ?_
  intro x
  simpa only [one_mul, Fintype.sum_unique] using (heval x).symm

noncomputable def mul {s N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℂ}
    (E : NativeNilsequenceExpansion s N p f) (F : NativeNilsequenceExpansion s N p g)
    (hp : 2 ≤ p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → ZMod N → ℂ := fun ij x =>
    (E.test ij.1).evalCyclic N (fun _ => x) * (F.test ij.2).evalCyclic N (fun _ => x)
  let R : ∀ ij, NativeNilsequenceExpansion s N (productNiltestBudget p) (v ij) :=
    fun ij => ofProduct (E.model ij.1) (F.model ij.2) (E.test ij.1) (F.test ij.2)
      hp (E.complexity ij.1) (F.complexity ij.2)
  have hexp : Real.exp p * Real.exp p = Real.exp (2 * p) := by
    rw [← Real.exp_add, two_mul]
  have hcard : (Fintype.card (Fin E.count × Fin F.count) : ℝ) ≤ Real.exp (2 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul E.count_bound F.count_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq hexp
  have hc : (∑ ij, ‖c ij‖) ≤ Real.exp (2 * p) := by
    calc
      _ = (∑ i, ‖E.coefficient i‖) * (∑ j, ‖F.coefficient j‖) := by
        simp only [c, norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.cost F.cost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_nonneg _)
      _ = _ := hexp
  have heq : (fun x => ∑ ij, c ij * v ij x) = (fun x => f x * g x) := by
    funext x
    rw [E.eval x, F.eval x]
    simp only [c, v, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact heq ▸ weightedSum R c (by linarith) hcard hc

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped BigOperators

theorem trans {J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s N : ℕ} [NeZero N] {p : ℝ}
    {chi : J → ZMod N → ℂ} {eta : K → ZMod N → ℂ} {psi : M → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi eta) (F : NativeVectorEquivalence s N p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeVectorEquivalence s N (productNiltestBudget p + 2 * p + p) chi psi := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hpq : p ≤ productNiltestBudget p + 2 * p + p := by linarith
  refine {
    left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
    right_dimension := F.right_dimension.trans (Real.exp_le_exp.mpr hpq)
    expansion := ?_
  }
  intro j l
  let A : ∀ k, NativeNilsequenceExpansion s N p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeNilsequenceExpansion s N p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeNilsequenceExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
  have heq : (fun x => ∑ k, (1 : ℂ) *
      ((chi j x * star (eta k x)) * (eta k x * star (psi l x)))) =
      (fun x => chi j x * star (psi l x)) := by
    funext x
    calc
      _ = ∑ k, ((chi j x * star (psi l x)) * star (eta k x)) * eta k x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (complex_unit_vector_resolution (fun k => eta k x) (hunit x) _).symm
  exact ⟨heq ▸ S⟩

end Erdos3.NativeVectorEquivalence

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (x : ℝ ⊗[ℚ] L) : realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raiseStepProjection : (D.raiseStep hst).Space → D.Space :=
  cosetMap (D.raiseStep hst).realLattice D.realLattice
    (NilpotentLieBCHGroup.realificationMap
      (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (NilpotentLieBCHGroup.realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L)
      (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst))

theorem raiseStepProjection_mk (x : (D.raiseStep hst).RealGroup) :
    D.raiseStepProjection hst (QuotientGroup.mk x) =
      QuotientGroup.mk (NilpotentLieBCHGroup.realificationMap
        (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) := rfl

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem raiseStepProjection_lipschitz :
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) (D.raiseStepProjection hst) := by
  let := realificationQuotientMetricSpace (D.raiseStep hst).basis (D.raiseStep hst).lattice
    (D.raiseStep hst).grid (D.raiseStep hst).grid_pos (D.raiseStep hst).outer_grid
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  have hentry (k i : Fin d) :
      RationalHeightLE (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) ((D.raiseStep hst).basis i)) k) 1 := by
    change RationalHeightLE (D.basis.repr (D.basis i) k) 1
    rw [Basis.repr_self]
    by_cases h : i = k <;> simp [h, RationalHeightLE]
  have h := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (D.raiseStep hst).basis D.basis (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst)
    (D.raiseStep hst).grid D.grid (D.raiseStep hst).grid_pos D.grid_pos
    (D.raiseStep hst).outer_grid D.outer_grid 1 hentry
  exact h.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

end Metric

noncomputable def raiseStepRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.raiseStep hst).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem raiseStepProjection_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.raiseStepProjection hst (QuotientGroup.mk
      ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.raiseStepProjection_mk]
  apply congrArg (QuotientGroup.mk : D.RealGroup → D.Space)
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log) =
      VectorPolynomial.eval (fun i => (x i : ℚ)) g.log
  exact realificationLieHom_id_apply _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

def raisedNiltestBudget (p : ℝ) : ℝ := p + (p + 2) ^ 2 + 3

theorem le_raisedNiltestBudget (p : ℝ) : p ≤ raisedNiltestBudget p := by
  unfold raisedNiltestBudget
  nlinarith [sq_nonneg (p + 2)]

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def raiseStep (T : D.Niltest w) (hst : s ≤ t) : (D.raiseStep hst).Niltest w where
  orbit := D.raiseStepRealOrbit hst T.orbit
  observable := fun z => T.observable (D.raiseStepProjection hst z)
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le z := T.norm_le _
  lipschitz := by
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    exact T.lipschitz.comp (D.raiseStepProjection_lipschitz hst)

theorem raiseStep_eval (T : D.Niltest w) (hst : s ≤ t) (x : σ → ℤ) :
    (T.raiseStep hst).eval x = T.eval x := by
  change T.observable (D.raiseStepProjection hst (QuotientGroup.mk
    ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
      (D.raiseStepRealOrbit hst T.orbit)))) = T.eval x
  rw [D.raiseStepProjection_orbit]
  rfl

theorem raiseStep_evalCyclic (T : D.Niltest w) (hst : s ≤ t)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.raiseStep hst).evalCyclic N x = T.evalCyclic N x :=
  T.raiseStep_eval hst _

theorem raiseStep_unit_interval (T : D.Niltest w) (hst : s ≤ t) (hT : T.UnitIntervalValued) :
    (T.raiseStep hst).UnitIntervalValued := fun z => hT (D.raiseStepProjection hst z)

theorem raiseStep_complexity (T : D.Niltest w) (hst : s ≤ t) {p : ℝ}
    (hp : 0 ≤ p) (hT : T.ComplexityLE p) :
    (T.raiseStep hst).ComplexityLE (raisedNiltestBudget p) := by
  refine ⟨GeometryComplexityLE.mono (D.raiseStep hst)
    (D.raiseStep_geometry hst hT.1) (le_raisedNiltestBudget p), ?_⟩
  have hraw := T.observable_budget hT
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith [T.lipBound.coe_nonneg]
  have hl : (T.lipBound : ℝ) ≤ Real.exp p := by linarith [T.normBound.coe_nonneg]
  have hK := coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hT.1.1
    (by simpa using Real.one_le_exp_iff.mpr hp)
  have hn' : (T.normBound : ℝ) ≤ Real.exp (p + (p + 2) ^ 2) :=
    hn.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p + 2)]))
  have hl' : (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
      Real.exp (p + (p + 2) ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hl hK (by positivity) (Real.exp_nonneg _)
  have hone : 1 ≤ Real.exp (p + (p + 2) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : 2 + (T.normBound : ℝ) +
      (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
        Real.exp (raisedNiltestBudget p) := by
    calc
      _ ≤ 4 * Real.exp (p + (p + 2) ^ 2) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + (p + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold raisedNiltestBudget; ring
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ)) ≤ raisedNiltestBudget p
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_top_vertical (T : D.Niltest w) (hst : s < t)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    (T.raiseStep hst.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hst.le).observable x := by
  have hz' : z = 1 := by
    apply NilpotentLieBCHGroup.ext
    change z.coord = 0
    change z.coord ∈ D.filtration.realification.layer t at hz
    simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
      Submodule.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t n : ℕ}

theorem raiseStep_top_subgroup_eq_bot (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) :
    (D.raiseStep hst.le).filtration.realification.subgroup t = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 1
  apply NilpotentLieBCHGroup.ext
  change z.coord = 0
  change z.coord ∈ D.filtration.realification.layer t at hz
  simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
    Submodule.mem_bot] using hz

theorem raiseStep_observable_top_vertical (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) (f : (D.raiseStep hst.le).Space → ℂ)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    f (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) * f x := by
  have hz' : z = 1 := by
    simpa only [raiseStep_top_subgroup_eq_bot D hst, Subgroup.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

universe u

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

inductive PositiveCyclicNiltest.{u} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℝ) : Prop where
  | of_test {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (hdegree : s ≤ degree)
      (T : D.Niltest (fun _ : Unit => 1)) (hpositive : T.UnitIntervalValued)
      (hcomplexity : T.ComplexityLE p)
      (heval : ∀ x, f x = (T.evalCyclic N (fun _ => x)).re) :
      PositiveCyclicNiltest degree N p f

namespace PositiveCyclicNiltest

universe u

theorem unit_interval {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (x : ZMod N) :
    0 ≤ f x ∧ f x ≤ 1 := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  rw [heval]
  exact (T.unit_interval_evalCyclic hT N (fun _ => x)).2

theorem mono {degree degree' N : ℕ} [NeZero N] {p p' : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (hdegree : degree ≤ degree')
    (hp : p ≤ p') : PositiveCyclicNiltest.{u} degree' N p' f := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  exact .of_test D (hs.trans hdegree) T hT (hTc.mono hp) heval

end PositiveCyclicNiltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def complement (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => 1 - T.observable z
  normBound := 1 + T.normBound
  lipBound := T.lipBound
  norm_le z := by
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (T.norm_le z) 1)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : (1 - T.observable x) - (1 - T.observable y) =
        -(T.observable x - T.observable y) := by ring
    rw [dist_eq_norm, he, norm_neg]
    simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul x y

end RationalFilteredNilmanifold.Niltest

theorem CyclicNiltestUpperComparison.test_positive {degree N : ℕ} [NeZero N]
    {P R error : ℝ} {f g a : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (ha : PositiveCyclicNiltest.{u} degree N R a) (hRP : R ≤ P) :
    (𝔼 x, (f x - g x) * a x) ≤ error := by
  rcases ha with ⟨D, hs, T, hT, hTc, heval⟩
  simpa only [heval] using hcompare D hs T hT (hTc.mono hRP)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedListPowerBudget
namespace OAI

section

namespace Erdos3

def fixedListWorkingBudget (p b : ℝ) : ℝ := 10 * (p + b + 2)

def fixedListComparisonBudget (B c : ℕ) (p : ℝ) : ℝ :=
  (fixedListWorkingBudget p ((p + 2) ^ B) + 2) ^ c

def fixedListRequiredBudget (B c : ℕ) (p : ℝ) : ℝ :=
  fixedListComparisonBudget B c p +
    productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p))

noncomputable def fixedListBudgetPolynomial (B c : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let q := Polynomial.C 10 * (X + (X + 2) ^ B + 2)
  let R := (q + 2) ^ c
  let S := R + (R + 2) ^ 2 + 3
  R + ((S + 2) ^ 2 + S + (S + (S ^ 2 + S + 3) ^ 2) + S ^ 2 + 4)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FrozenCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem frozen_correlation_precision_error (P D : ℝ) (hD : 0 ≤ D)
    {N : ℕ} (hN : 0 < N) (hlarge : Real.exp (D + 2 * P + 40) ≤ N) :
    Real.exp D * Real.exp (-(D + 2 * P + 40)) +
      12 * Real.exp (-(D + 2 * P + 40)) + 6 / N ≤ Real.exp (-(2 * P)) / 2 := by
  let ε := Real.exp (-(2 * P) - 40)
  have he : 0 < ε := Real.exp_pos _
  have hprod : Real.exp D * Real.exp (-(D + 2 * P + 40)) = ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrho : Real.exp (-(D + 2 * P + 40)) ≤ ε := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : 1 / (N : ℝ) ≤ Real.exp (-(D + 2 * P + 40)) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have h := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(D + 2 * P + 40))).le
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h
  have h6 : 6 / (N : ℝ) ≤ 6 * Real.exp (-(D + 2 * P + 40)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 6)
  have h38 : (38 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hexp : Real.exp (-(2 * P)) = Real.exp 40 * ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hprod, hexp]
  nlinarith [mul_le_mul_of_nonneg_right h38 he.le]

theorem frozen_witness_budget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget (raisedNiltestBudget p) ≤ productNiltestBudget (raisedNiltestBudget q) := by
  unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
  gcongr

theorem exists_frozen_correlation_budget (c b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let L := (P + c) ^ c + 2 * P + 40
      let Q := P + (L + b) ^ b + 2
      L ≤ (P + C) ^ C ∧
        productNiltestBudget (raisedNiltestBudget (P + Q + 2)) ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C c) ^ c + 2 * X + 40
  let Q := X + (L + Polynomial.C b) ^ b + 2
  let R := X + Q + 2
  let A := R + (R + 2) ^ 2 + 3
  let U := (A + 2) ^ 2 + A + (A + (A ^ 2 + A + 3) ^ 2) + A ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (L + U)
  refine ⟨C, hC, ?_⟩
  intro P hP L' Q'
  have hL : 0 ≤ L' := by dsimp only [L']; positivity
  have hU : 0 ≤ productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) := by
    dsimp only [productNiltestBudget, productObservableLipBudget, raisedNiltestBudget, Q', L']
    positivity
  have htotal : L' + productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) ≤ (P + C) ^ C := by
    simpa [X, L, Q, R, A, U, L', Q', Polynomial.eval₂_pow,
      productNiltestBudget, productObservableLipBudget, raisedNiltestBudget] using hbudget P hP
  exact ⟨by linarith only [htotal, hU], by linarith only [htotal, hL]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.GlobalErrorSplittingBudget
namespace OAI

section

namespace Erdos3

theorem exists_global_error_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b : ℝ, 0 ≤ b →
      let B := (b + a) ^ a
      let F := (B + c) ^ c
      let Q := 3 * b + B + F + 3
      B ≤ (b + C) ^ C ∧ productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := by
  obtain ⟨e, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let B₀ := (X + Polynomial.C a) ^ a
  let F₀ := (B₀ + Polynomial.C c) ^ c
  let Q₀ := 3 * X + B₀ + F₀ + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (3 * Q₀ + 4 + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro b hb B F Q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpoly : B + (3 * Q + 4 + e) ^ e ≤ (b + C) ^ C := by
    simpa [X, B₀, F₀, Q₀, B, F, Q, Polynomial.eval₂_pow] using hbudget b hb
  have hnon : 0 ≤ (3 * Q + 4 + e) ^ e := by positivity
  exact ⟨by linarith, (hproduct _ (by positivity)).trans (by linarith)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MajorTranslationPartnerBudget
namespace OAI

section

namespace Erdos3

theorem exists_majorTranslationPartnerBudget_bound (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget ((p + a) ^ a + raisedNiltestBudget p + 2) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + (X + (X + 2) ^ 2 + 3) + 2
  let P := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow, productNiltestBudget,
    productObservableLipBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProductInclusion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productProjection_joint_injective :
    Function.Injective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro x y h
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    apply QuotientGroup.eq.mpr
    change x⁻¹ * y ∈ (piBCHSubgroup (fun i => (D i).filtration) (fun i => (D i).lattice)).map realificationHom
    rw [realBCHPiEquiv_mem_lattice]
    intro i
    have hi := congrFun h i
    have hmem := QuotientGroup.eq.mp hi
    change productProjectionHom D i (x⁻¹ * y) ∈ (D i).realLattice
    simpa only [map_mul, map_inv] using hmem

theorem productProjection_joint_surjective :
    Function.Surjective (fun x : (pi D).Space => fun i => productProjection D i x) := by
  intro y
  let F := fun i => (D i).filtration
  let g := (realBCHPiEquiv F).symm (fun i => (y i).out)
  refine ⟨QuotientGroup.mk g, ?_⟩
  funext i
  change QuotientGroup.mk (realBCHPiEquiv F g i) = y i
  rw [show realBCHPiEquiv F g = (fun i => (y i).out) from (realBCHPiEquiv F).apply_symm_apply _]
  exact Quotient.out_eq (y i)

noncomputable def productSpaceEquiv : (pi D).Space ≃ (∀ i, (D i).Space) :=
  Equiv.ofBijective (fun x i => productProjection D i x)
    ⟨productProjection_joint_injective D, productProjection_joint_surjective D⟩

@[simp] theorem productSpaceEquiv_apply (x : (pi D).Space) (i : ι) :
    productSpaceEquiv D x i = productProjection D i x := rfl

@[simp] theorem productSpaceEquiv_mk (g : (pi D).RealGroup) (i : ι) :
    productSpaceEquiv D (QuotientGroup.mk g) i = QuotientGroup.mk (productProjectionHom D i g) := rfl

theorem productSpaceEquiv_symm_mk (g : ∀ i, (D i).RealGroup) :
    (productSpaceEquiv D).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) := by
  apply (productSpaceEquiv D).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change QuotientGroup.mk (g i) = QuotientGroup.mk
    (realBCHPiEquiv (fun i => (D i).filtration)
      ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) i)
  rw [MulEquiv.apply_symm_apply]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realification_piRight_symm_single (i : ι) (x : ℝ ⊗[ℚ] L i) :
    (TensorProduct.piRight ℚ ℝ ℝ L).symm (Pi.single i x) =
      realificationLieHom (liePiSingle i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [TensorProduct.piRight_symm_single]
    rfl
  | add x y hx hy => simp only [Pi.single_add, map_add, hx, hy]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productInclusionHom (i : ι) : (D i).RealGroup →* (pi D).RealGroup :=
  realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
    (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiSingle i)

theorem realBCHPiEquiv_symm_single (i : ι) (g : (D i).RealGroup) :
    (realBCHPiEquiv (fun i => (D i).filtration)).symm (Pi.mulSingle i g) = productInclusionHom D i g := by
  apply NilpotentLieBCHGroup.ext
  change (TensorProduct.piRight ℚ ℝ ℝ L).symm
    (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) =
    realificationLieHom (liePiSingle i) g.coord
  have h : (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) = Pi.single i g.coord := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    · simp only [Pi.mulSingle_eq_of_ne hji, Pi.single_eq_of_ne hji, coord_one]
  rw [h, realification_piRight_symm_single]

theorem productInclusion_matrix_height (i : ι) (j : Fin (d i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    RationalHeightLE ((pi D).basis.repr (liePiSingle i ((D i).basis j)) k) 1 := by
  change RationalHeightLE ((pi D).basis.repr (Pi.single i ((D i).basis j)) k) 1
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨a, l⟩
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Module.Basis.repr_self]
    by_cases hjl : j = l <;> simp [hjl, RationalHeightLE]
  · rw [Pi.single_eq_of_ne hai, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

theorem productSpaceEquiv_symm_update_mk (g : ∀ i, (D i).RealGroup) (i : ι) (a : (D i).RealGroup) :
    (productSpaceEquiv D).symm (Function.update (fun j => QuotientGroup.mk (g j)) i (QuotientGroup.mk a)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun j => (D j).filtration)).symm (Function.update g i a)) := by
  have h : Function.update (fun j => (QuotientGroup.mk (g j) : (D j).Space)) i (QuotientGroup.mk a) =
      (fun j => QuotientGroup.mk (Function.update g i a j)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  rw [h, productSpaceEquiv_symm_mk]

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productMetricBound (d : ι → ℕ) : ℝ≥0 :=
  ∑ i, coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productInclusionHom_lipschitz (i : ι) :
    letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1)
      (productInclusionHom D i) := by
  unfold productInclusionHom
  simpa only [Fintype.card_fin, Nat.cast_one] using
    (lipschitz_realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
      (D i).basis (pi D).basis (liePiSingle i) 1 (fun k j => productInclusion_matrix_height D i j k))

theorem productSpaceEquiv_symm_coordinate_lipschitz (i : ι) (y : ∀ j, (D j).Space) :
    letI := (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a => (productSpaceEquiv D).symm (Function.update y i a)) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L i) := ((D i).basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ j, L j)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := (pi D).metricSpace
  let g : ∀ j, (D j).RealGroup := fun j => (y j).out
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update g i 1)
  have hbase : (fun j => (QuotientGroup.mk (g j) : (D j).Space)) = y :=
    funext (fun j => Quotient.out_eq (y j))
  have heval (a : (D i).RealGroup) :
      (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a)) =
        QuotientGroup.mk (productInclusionHom D i a * u) := by
    rw [← hbase, productSpaceEquiv_symm_update_mk]
    have hup : Function.update g i a = Pi.mulSingle i a * Function.update g i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have hm : LipschitzWith 1 (QuotientGroup.mk : (pi D).RealGroup → (pi D).Space) :=
    quotientMetricSpace_lipschitz_mk ((pi D).basis.baseChange ℝ) (pi D).realLattice
      (pi D).realLattice_closed_discrete.1
  have hf := hm.comp ((isometry_mul_right u).lipschitz.comp (productInclusionHom_lipschitz D i))
  have hf' : LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a : (D i).RealGroup => (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a))) := by
    simpa only [Function.comp_def, one_mul, heval] using hf
  exact rightCosetMetricSpace_lipschitz_lift (D i).realLattice (D i).realLattice_closed_discrete.1 _ hf'

theorem productSpaceEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  exact lipschitzWith_of_coordinatewise _ _ (fun i y => productSpaceEquiv_symm_coordinate_lipschitz D i y)

theorem productSpaceEquiv_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D) := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (productMetricBound d).coe_nonneg dist_nonneg)).mpr
  intro i
  have hc : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 ≤ productMetricBound d := by
    have heq : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 =
        coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 := by
      unfold coordinateLipschitzBound
      congr 1
      ring
    rw [heq]
    unfold productMetricBound
    exact Finset.single_le_sum
      (f := fun j : ι => coordinateLipschitzBound (Fintype.card (Σ k, Fin (d k))) (d j) 1)
      (s := Finset.univ) (fun _ _ => zero_le) (Finset.mem_univ i)
  exact ((productProjection_lipschitz D i).dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (show (coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 : ℝ) ≤
      productMetricBound d from hc) dist_nonneg)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

theorem productMetricBound_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ 2 * p * (p ^ 2 + p + 1) := by
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using hd i)
  have hC (i : ι) : (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 : ℝ) ≤
      2 * (p ^ 2 + p + 1) := by
    change ((Fintype.card (Σ j, Fin (d j)) : ℝ) + (d i : ℝ) + 1) * (1 + 1) ≤ _
    nlinarith [hd i]
  unfold productMetricBound
  rw [NNReal.coe_sum]
  calc
    _ ≤ ∑ _ : ι, 2 * (p ^ 2 + p + 1) := Finset.sum_le_sum (fun i _ => hC i)
    _ = (Fintype.card ι : ℝ) * (2 * (p ^ 2 + p + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ p * (2 * (p ^ 2 + p + 1)) := mul_le_mul_of_nonneg_right hι (by positivity)
    _ = _ := by ring

theorem productMetricBound_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4) := by
  have hpoly : 2 * p * (p ^ 2 + p + 1) ≤ (p + 4) ^ 4 := by
    nlinarith [sq_nonneg (p ^ 2), mul_nonneg hp (sq_nonneg p)]
  apply (productMetricBound_le d hp hι hd).trans
  exact hpoly.trans (by linarith [Real.add_one_le_exp ((p + 4) ^ 4)])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι σ : Type*} [Fintype ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {w : σ → ℕ} (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
  (N : ℕ) [NeZero N]

variable [DecidableEq ι]

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeOptionProductBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal

theorem exists_optionProductMetric_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (d : Option ι → ℕ) {p : ℝ},
      0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p → (∀ i, (d i : ℝ) ≤ p) →
      (((1 + productMetricBound (fun i => d (some i))) * productMetricBound d : ℝ≥0) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X * (X ^ 2 + X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((1 + T) * T)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ d p hp hι hd
  have hι' : (Fintype.card ι : ℝ) ≤ p := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hfull := productMetricBound_le d hp hι hd
  have hrest := productMetricBound_le (fun i => d (some i)) hp hι' (fun i => hd (some i))
  have hpoly : (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) ≤
      (p + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) := by
      push_cast
      gcongr
    _ ≤ (p + C) ^ C := hpoly
    _ ≤ Real.exp ((p + C) ^ C) := by linarith [Real.add_one_le_exp ((p + C) ^ C)]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

noncomputable def chartCoordinateKernel (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) : (ι → ℝ) → ℝ := chartCutoff phi.symm F

omit [Fintype ι] in
theorem chartCoordinateKernel_of_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∈ phi.source) :
    chartCoordinateKernel phi F v = F (phi v) := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [if_pos hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_of_not_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∉ phi.source) :
    chartCoordinateKernel phi F v = 0 := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [if_neg hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_range (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (v : ι → ℝ) :
    0 ≤ chartCoordinateKernel phi F v ∧ chartCoordinateKernel phi F v ≤ 1 :=
  chartCutoff_range phi.symm F hF v

theorem chartCoordinateKernel_support (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : phi.source = {v | ∀ i, |v i| < r})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * r / 4)) :
    Function.support (chartCoordinateKernel phi F) ⊆ Metric.closedBall 0 (3 * r / 4) := by
  intro v hv
  change chartCoordinateKernel phi F v ≠ 0 at hv
  have hvs : v ∈ phi.source := by
    by_contra h
    exact hv (chartCoordinateKernel_of_not_mem phi F h)
  have hFv : F (phi v) ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hvs] at hv
  obtain ⟨u, hu, heq⟩ := hinner (subset_closure hFv)
  have hus := closedBox_subset_chart_source phi hr hsource hu
  have huv : u = v := by
    calc
      u = phi.symm (phi u) := (phi.left_inv hus).symm
      _ = phi.symm (phi v) := congrArg phi.symm heq
      _ = v := phi.left_inv hvs
  exact huv ▸ hu

theorem chartCoordinateKernel_lipschitz (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (A K r : ℝ≥0) (hr : 0 < r)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
    (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
    (hForward : LipschitzOnWith K phi phi.source) :
    LipschitzWith (A * K + 1 / (r / 4)) (chartCoordinateKernel phi F) := by
  apply lipschitz_chartCutoff phi.symm F A K (r / 4) (by positivity) hF hLip hForward
  intro v hv hFv y hy
  change v ∈ phi.source at hv
  change y ∉ phi.source at hy
  have hvk : chartCoordinateKernel phi F v ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hv]
  have hball := chartCoordinateKernel_support phi F hr hsource hinner hvk
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  obtain ⟨i, hyi⟩ : ∃ i, (r : ℝ) ≤ |y i| := by
    simpa only [hsource, mem_ofPred_eq, not_forall, not_lt] using hy
  have hvi : |v i| ≤ 3 * (r : ℝ) / 4 := by
    calc
      |v i| = ‖v i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v‖ := norm_le_pi_norm v i
      _ ≤ _ := hball
  have hd : |y i - v i| ≤ dist v y := by
    simpa only [Real.dist_eq, abs_sub_comm] using dist_le_pi_dist v y i
  have ht : |y i| ≤ |y i - v i| + |v i| := by
    simpa only [sub_add_cancel] using abs_add_le (y i - v i) (v i)
  change (r : ℝ) / 4 ≤ dist v y
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem chartKernelScaling_lipschitz (d B : ℕ) :
    LipschitzWith (B : ℝ≥0) (fun x : Fin d → ℝ => (B : ℝ) • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B), NNReal.coe_natCast]
  exact le_rfl

variable {X : Type*} [MetricSpace X] {d : ℕ}
  (phi : OpenPartialHomeomorph (Fin d → ℝ) X) (F : X → ℝ)
  (A K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : LipschitzOnWith K phi phi.source) (B : ℕ) (hB : 4 ≤ B)

noncomputable def scaledChartKernel : PatchKernel d where
  value x := chartCoordinateKernel phi F ((B : ℝ) • x)
  nonneg x := (chartCoordinateKernel_range phi F hF _).1
  le_one x := (chartCoordinateKernel_range phi F hF _).2
  support x hx i := by
    have hb := chartCoordinateKernel_support phi F hr hsource hinner hx
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    have hi : (B : ℝ) * |x i| ≤ 3 * (r : ℝ) / 4 := by
      calc
        (B : ℝ) * |x i| = ‖((B : ℝ) • x) i‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B)]
        _ ≤ ‖(B : ℝ) • x‖ := norm_le_pi_norm ((B : ℝ) • x) i
        _ ≤ _ := hb
    have hBr : (4 : ℝ) ≤ B := by exact_mod_cast hB
    have hsmall := mul_le_mul_of_nonneg_right hBr (abs_nonneg (x i))
    have hr1' : (r : ℝ) ≤ 1 := hr1
    linarith
  lip := (A * K + 1 / (r / 4)) * B
  lipschitz := by
    simpa only [Function.comp_def] using
      (chartCoordinateKernel_lipschitz phi F A K r hr hF hLip hsource hinner hForward).comp
        (chartKernelScaling_lipschitz d B)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} (T : D.Niltest w)

theorem realObservable_lipschitz :
    letI := D.metricSpace
    LipschitzWith T.lipBound (fun x => (T.observable x).re) := by
  let := D.metricSpace
  simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
    (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz

theorem realObservable_tsupport :
    tsupport (fun x => (T.observable x).re) ⊆ tsupport T.observable := by
  apply closure_mono
  intro x hx
  change T.observable x ≠ 0
  intro hzero
  apply hx
  change (T.observable x).re = 0
  rw [hzero, Complex.zero_re]

variable (hT : T.UnitIntervalValued) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space)
  (K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport T.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : letI := D.metricSpace; LipschitzOnWith K phi phi.source) (hgrid : 4 ≤ D.grid)

noncomputable def chartKernel : PatchKernel d := by
  let := D.metricSpace
  exact scaledChartKernel phi (fun x => (T.observable x).re) T.lipBound K r hr hr1
    (fun x => (hT x).2) T.realObservable_lipschitz hsource
    (T.realObservable_tsupport.trans hinner) hForward D.grid hgrid

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IteratedCircleAverageIntegral
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

theorem integral_circleCharacter (n : ℤ) :
    (∫ t : Circle, character (n • t) ∂circleHaar) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hn (by norm_num))

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def average (A : IsometricCircleAction X) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent 0 f

theorem average_eq_integral (A : IsometricCircleAction X) (f : X → ℂ) (x : X) :
    A.average f x = ∫ t : Circle, f (A.act t x) ∂circleHaar := by
  simp [average, circleFourierComponent]
  rfl

theorem average_lipschitz (A : IsometricCircleAction X) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (A.average f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent 0 hf A.isometry_act

theorem average_norm_le (A : IsometricCircleAction X) {f : X → ℂ} {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.average f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le 0 f hf x

theorem average_const (A : IsometricCircleAction X) (c : ℂ) (x : X) :
    A.average (fun _ => c) x = c := by
  simp [average_eq_integral]

theorem average_invariant (A : IsometricCircleAction X) (f : X → ℂ) (t : Circle) (x : X) :
    A.average f (A.act t x) = A.average f x := by
  let := A.toAddAction
  change circleFourierComponent 0 f (t +ᵥ x) = circleFourierComponent 0 f x
  simpa only [neg_zero, zero_smul, character_zero, one_mul] using
    circleFourierComponent_vadd 0 f t x

theorem average_unit_interval (A : IsometricCircleAction X) {f : X → ℂ}
    (hf : Continuous f) (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) (x : X) :
    (A.average f x).im = 0 ∧ 0 ≤ (A.average f x).re ∧ (A.average f x).re ≤ 1 := by
  have hcont : Continuous (fun t : Circle => f (A.act t x)) :=
    hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const))
  have hi := circle_integrable_of_continuous hcont
  have him : (∫ t : Circle, f (A.act t x) ∂circleHaar).im =
      ∫ t : Circle, (f (A.act t x)).im ∂circleHaar := (integral_im hi).symm
  have hre : (∫ t : Circle, f (A.act t x) ∂circleHaar).re =
      ∫ t : Circle, (f (A.act t x)).re ∂circleHaar := (integral_re hi).symm
  rw [average_eq_integral, him, hre]
  refine ⟨?_, integral_nonneg (fun t => (hb (A.act t x)).2.1), ?_⟩
  · simp_rw [(hb _).1]
    simp
  · have hle := integral_mono (circle_integrable_of_continuous (Complex.continuous_re.comp hcont))
      (integrable_const (1 : ℝ)) (fun t => (hb (A.act t x)).2.2)
    simpa using hle

theorem average_sub (A : IsometricCircleAction X) {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.average (fun y => f y - g y) x = A.average f x - A.average g x := by
  simp only [average_eq_integral]
  apply integral_sub
  · exact circle_integrable_of_continuous
      (hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))
  · exact circle_integrable_of_continuous
      (hg.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_sub_norm_le (A : IsometricCircleAction X) {f g : X → ℂ} {B : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, ‖f x - g x‖ ≤ B) (x : X) :
    ‖A.average f x - A.average g x‖ ≤ B := by
  rw [← A.average_sub hf hg]
  exact A.average_norm_le hfg x

theorem average_sum {ι : Type*} (A : IsometricCircleAction X) (s : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.average (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.average (f i) x := by
  simp only [average_eq_integral]
  apply integral_finsetSum
  intro i hi
  exact circle_integrable_of_continuous
    ((hf i hi).comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_equivariant (A : IsometricCircleAction X) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hcomm : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.average f (g x) = z * A.average f x := by
  simp only [average_eq_integral]
  simp_rw [hcomm, hf]
  exact integral_const_mul z _

theorem average_eigenfunction (A : IsometricCircleAction X) {f : X → ℂ} (n : ℤ)
    (hf : ∀ t x, f (A.act t x) = character (n • t) * f x) (x : X) :
    A.average f x = if n = 0 then f x else 0 := by
  rw [average_eq_integral]
  simp_rw [hf]
  rw [integral_mul_const, integral_circleCharacter]
  split_ifs <;> simp

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleAverage (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).average (iteratedCircleAverage A is f)

theorem iteratedCircleAverage_lipschitz (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleAverage A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_lipschitz ih

theorem iteratedCircleAverage_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_norm_le ih

theorem iteratedCircleAverage_unit_interval (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    ∀ x, (iteratedCircleAverage A is f x).im = 0 ∧
      0 ≤ (iteratedCircleAverage A is f x).re ∧ (iteratedCircleAverage A is f x).re ≤ 1 := by
  induction is with
  | nil => exact hb
  | cons i is ih =>
    exact (A i).average_unit_interval (iteratedCircleAverage_lipschitz A is hf).continuous ih

theorem iteratedCircleAverage_sub_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f g : X → ℂ} {Lf Lg : ℝ≥0} {B : ℝ} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfg : ∀ x, ‖f x - g x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x - iteratedCircleAverage A is g x‖ ≤ B := by
  induction is with
  | nil => exact hfg
  | cons i is ih =>
    exact (A i).average_sub_norm_le (iteratedCircleAverage_lipschitz A is hf).continuous
      (iteratedCircleAverage_lipschitz A is hg).continuous ih

theorem iteratedCircleAverage_sum {ι : Type*} (A : α → IsometricCircleAction X) (is : List α)
    (s : Finset ι) (f : ι → X → ℂ) (L : ι → ℝ≥0) (hf : ∀ i ∈ s, LipschitzWith (L i) (f i)) :
    ∀ x, iteratedCircleAverage A is (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedCircleAverage A is (f i) x := by
  induction is with
  | nil => intro x; rfl
  | cons i is ih =>
    have heq : iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y) =
        fun y => ∑ j ∈ s, iteratedCircleAverage A is (f j) y := funext ih
    intro x
    change (A i).average (iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y)) x = _
    rw [heq]
    exact (A i).average_sum s _ (fun j hj => (iteratedCircleAverage_lipschitz A is (hf j hj)).continuous) x

theorem iteratedCircleAverage_invariant (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedCircleAverage A is f ((A j).act t x) = iteratedCircleAverage A is f x := by
  induction is generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact (A i).average_invariant _ t x
    · have htcomm : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
        fun a ha b hb => hcomm a (by simp [ha]) b (by simp [hb])
      have ht : ∀ y, iteratedCircleAverage A is f ((A j).act t y) =
          (1 : ℂ) * iteratedCircleAverage A is f y := by
        intro y
        simpa using ih htcomm hj y
      simpa only [iteratedCircleAverage, one_mul] using (A i).average_equivariant ((A j).act t) 1
        (fun u y => hcomm i (by simp) j (by simp [hj]) u t y) ht x

theorem iteratedCircleAverage_eigenfunction (A : α → IsometricCircleAction X) (is : List α)
    (n : α → ℤ) (f : X → ℂ)
    (hf : ∀ i ∈ is, ∀ t x, f ((A i).act t x) = character (n i • t) * f x) :
    iteratedCircleAverage A is f = if ∀ i ∈ is, n i = 0 then f else fun _ => 0 := by
  classical
  induction is with
  | nil => simp [iteratedCircleAverage]
  | cons i is ih =>
    have ht := ih (fun j hj => hf j (by simp [hj]))
    rw [iteratedCircleAverage, ht]
    by_cases htail : ∀ j ∈ is, n j = 0
    · have htail' : (∀ j ∈ is, n j = 0) = True := eq_true htail
      simp only [List.forall_mem_cons, htail', ite_true, and_true]
      funext x
      rw [(A i).average_eigenfunction (n i) (hf i (by simp))]
      split_ifs <;> rfl
    · have htail' : (∀ j ∈ is, n j = 0) = False := eq_false htail
      simp only [List.forall_mem_cons, htail', ite_false, and_false]
      funext x
      exact (A i).average_const 0 x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {α : Type*}

def CircleAverageTuple : List α → Type
  | [] => Unit
  | _ :: is => Circle × CircleAverageTuple is

instance circleAverageTupleMeasurableSpace : (is : List α) → MeasurableSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (MeasurableSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleMeasurableSpace is
      inferInstanceAs (MeasurableSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleTopologicalSpace : (is : List α) → TopologicalSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (TopologicalSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleTopologicalSpace is
      inferInstanceAs (TopologicalSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleSecondCountableTopology :
    (is : List α) → SecondCountableTopology (CircleAverageTuple is)
  | [] => inferInstanceAs (SecondCountableTopology Unit)
  | _ :: is =>
      let _ := circleAverageTupleSecondCountableTopology is
      inferInstanceAs (SecondCountableTopology (Circle × CircleAverageTuple is))

instance circleAverageTupleBorelSpace : (is : List α) → BorelSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (BorelSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleBorelSpace is
      inferInstanceAs (BorelSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleCompactSpace : (is : List α) → CompactSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (CompactSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleCompactSpace is
      inferInstanceAs (CompactSpace (Circle × CircleAverageTuple is))

noncomputable def circleAverageTupleMeasure : (is : List α) → Measure (CircleAverageTuple is)
  | [] => Measure.dirac ()
  | _ :: is => circleHaar.prod (circleAverageTupleMeasure is)

instance circleAverageTupleMeasure_probability :
    (is : List α) → IsProbabilityMeasure (circleAverageTupleMeasure is)
  | [] => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | _ :: is =>
      let _ := circleAverageTupleMeasure_probability is
      inferInstanceAs (IsProbabilityMeasure (circleHaar.prod (circleAverageTupleMeasure is)))

variable {X : Type*} [PseudoMetricSpace X]

def iteratedCircleAction (A : α → IsometricCircleAction X) :
    (is : List α) → CircleAverageTuple is → X → X
  | [], _, x => x
  | i :: is, t, x => iteratedCircleAction A is t.2 ((A i).act t.1 x)

theorem continuous_iteratedCircleAction (A : α → IsometricCircleAction X) (is : List α) :
    Continuous (fun p : CircleAverageTuple is × X =>
      iteratedCircleAction A is p.1 p.2) := by
  induction is with
  | nil => exact continuous_snd
  | cons i is ih =>
      change Continuous (fun p : (Circle × CircleAverageTuple is) × X =>
        iteratedCircleAction A is p.1.2 ((A i).act p.1.1 p.2))
      exact ih.comp (continuous_fst.snd.prodMk
        ((A i).continuous_act.comp (continuous_fst.fst.prodMk continuous_snd)))

theorem continuous_iteratedCircleAction_parameter (A : α → IsometricCircleAction X)
    (is : List α) (x : X) : Continuous (fun t => iteratedCircleAction A is t x) :=
  (continuous_iteratedCircleAction A is).comp (continuous_id.prodMk continuous_const)

theorem integrable_iteratedCircleAction (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t => f (iteratedCircleAction A is t x))
      (circleAverageTupleMeasure is) :=
  (hf.comp (continuous_iteratedCircleAction_parameter A is x)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem iteratedCircleAverage_eq_integral (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    iteratedCircleAverage A is f x =
      ∫ t, f (iteratedCircleAction A is t x) ∂circleAverageTupleMeasure is := by
  induction is generalizing x with
  | nil =>
      change f x = ∫ _ : CircleAverageTuple ([] : List α), f x
        ∂circleAverageTupleMeasure ([] : List α)
      simp
  | cons i is ih =>
      change (A i).average (iteratedCircleAverage A is f) x =
        ∫ t : Circle × CircleAverageTuple is,
          f (iteratedCircleAction A is t.2 ((A i).act t.1 x))
          ∂circleHaar.prod (circleAverageTupleMeasure is)
      rw [(A i).average_eq_integral]
      have hint : Integrable
          (fun t : Circle × CircleAverageTuple is =>
            f (iteratedCircleAction A is t.2 ((A i).act t.1 x)))
          (circleHaar.prod (circleAverageTupleMeasure is)) :=
        integrable_iteratedCircleAction A (i :: is) hf x
      rw [integral_prod _ hint]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => ih ((A i).act t x)))

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_mean_sub_le {G : Type*} [Fintype G] [Nonempty G]
    (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (hfg : ∀ n, ‖f n - g n‖ ≤ rho) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * g n)‖ ≤ B * rho := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const Finset.univ_nonempty _)
  intro n _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw n) (hfg n) (norm_nonneg _) hB

theorem finite_projection_tested_error {G J : Type*} [Fintype G] [Nonempty G] [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hw : ∀ n, ‖w n‖ ≤ B)
    (hfull : ∀ n, ‖f n - ∑ j, v j n‖ ≤ rho)
    (hprojected : ∀ n, ‖(∑ j, if keep j then v j n else 0) - projected n‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖𝔼 n, w n * v j n‖ ≤ tau) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * projected n)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := norm_weighted_mean_sub_le w f (fun n => ∑ j, v j n) hB hw hfull
  have hlast := norm_weighted_mean_sub_le w
    (fun n => ∑ j, if keep j then v j n else 0) projected hB hw hprojected
  have hid : (𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0) =
      ∑ j, if keep j then 0 else (𝔼 n, w n * v j n) := by
    calc
      _ = 𝔼 n, w n * ((∑ j, v j n) - ∑ j, if keep j then v j n else 0) := by
        simp only [mul_sub, Finset.expect_sub_distrib]
      _ = 𝔼 n, ∑ j, if keep j then 0 else w n * v j n := by
        apply Finset.expect_congr rfl
        intro n _
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, 𝔼 n, if keep j then 0 else w n * v j n := Finset.expect_sum_comm _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * f n) (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * projected n)
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * ∑ j, if keep j then v j n else 0)
    (𝔼 n, w n * projected n)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem lipschitz_finite_complex_sum {X J : Type*} [PseudoMetricSpace X] [Fintype J]
    (v : J → X → ℂ) (L : J → ℝ≥0) (hv : ∀ j, LipschitzWith (L j) (v j)) :
    LipschitzWith (∑ j, L j) (fun x => ∑ j, v j x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖v j x - v j y‖ := norm_sum_le _ _
    _ ≤ ∑ j, (L j : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [dist_eq_norm] using (hv j).dist_le_mul x y
    _ = _ := by simp only [NNReal.coe_sum, Finset.sum_mul]

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace FiniteProbabilityWeights

variable {G : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

theorem norm_tested_difference_le (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ x, ‖w x‖ ≤ B) (hfg : ∀ x, ‖f x - g x‖ ≤ rho) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤ B * rho := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * rho) ?_).trans_eq (p.mean_const _)
  intro x _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw x) (hfg x) (norm_nonneg _) hB

theorem finite_projection_tested_error {J : Type*} [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hw : ∀ x, ‖w x‖ ≤ B)
    (hfull : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (hprojected : ∀ x, ‖(∑ j, if keep j then v j x else 0) - projected x‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * v j x)‖ ≤ tau) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * projected x)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := p.norm_tested_difference_le w f (fun x => ∑ j, v j x) hB hw hfull
  have hlast := p.norm_tested_difference_le w
    (fun x => ∑ j, if keep j then v j x else 0) projected hB hw hprojected
  have hid : p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0) =
      ∑ j, if keep j then 0 else p.complexMean (fun x => w x * v j x) := by
    rw [← p.complexMean_sub]
    calc
      _ = ∑ x, ∑ j, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only
        rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, ∑ x, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj, complexMean]
  have hmiddle : ‖p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * projected x))
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0))
    (p.complexMean (fun x => w x * projected x))
  linarith

end FiniteProbabilityWeights

namespace CircleFourier

end CircleFourier
end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem iteratedCircleAverage_family_tested_weighted_error
    {X Y α G J : Type*} [PseudoMetricSpace Y] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G)
    (A : α → IsometricCircleAction Y) (is : List α) (f : X → Y → ℂ)
    (v : J → X → Y → ℂ) (n : J → α → ℤ)
    (physical : G → X) (path : G → Y) (weight : G → ℂ)
    (Lf : X → ℝ≥0) (Lv : J → X → ℝ≥0)
    (hf : ∀ x, LipschitzWith (Lf x) (f x))
    (hv : ∀ j x, LipschitzWith (Lv j x) (v j x))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ g, ‖weight g‖ ≤ B)
    (happrox : ∀ x y, ‖f x y - ∑ j, v j x y‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x y,
      v j x ((A i).act t y) = character (n j i • t) * v j x y)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖p.complexMean (fun g => weight g * v j (physical g) (path g))‖ ≤ tau) :
    ‖p.complexMean (fun g => weight g * f (physical g) (path g)) -
      p.complexMean (fun g =>
        weight g * iteratedCircleAverage A is (f (physical g)) (path g))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) (y : Y) :
      iteratedCircleAverage A is (fun z => ∑ j, v j x z) y =
        ∑ j, if keep j then v j x y else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ
      (fun j => v j x) (fun j => Lv j x) (fun j _ => hv j x)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j x)
      (fun i hi t y => heigen j i hi t x y)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply p.finite_projection_tested_error weight
    (fun g => f (physical g) (path g))
    (fun g => iteratedCircleAverage A is (f (physical g)) (path g))
    (fun j g => v j (physical g) (path g)) keep hB htau hweight
    (fun g => happrox (physical g) (path g)) _ hdiscard
  intro g
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is (hf (physical g))
    (lipschitz_finite_complex_sum (fun j => v j (physical g))
      (fun j => Lv j (physical g)) (fun j => hv j (physical g)))
    (happrox (physical g)) (path g)

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareLayerConstraint (j : ℕ) : F.squareLieSubalgebra →ₗ[ℚ]
    ((L ⧸ F.layer j) × (L ⧸ F.layer (j + 1))) :=
  ((F.layer j).mkQ.comp F.squareSnd.toLinearMap).prod
    ((F.layer (j + 1)).mkQ.comp (F.squareFst.toLinearMap - F.squareSnd.toLinearMap))

theorem squareLayer_eq_ker_constraint (j : ℕ) :
    F.squareFiltration.layer j = LinearMap.ker (F.squareLayerConstraint j) := by
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference]
  change (x.val.2 ∈ F.layer j ∧ x.val.1 - x.val.2 ∈ F.layer (j + 1)) ↔
    ((F.layer j).mkQ x.val.2, (F.layer (j + 1)).mkQ (x.val.1 - x.val.2)) = 0
  simp only [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem realifiedSquareEquiv_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.realification.layer j ↔
      F.realifiedSquareEquiv x ∈ F.realification.squareFiltration.layer j := by
  change x ∈ (F.squareFiltration.layer j).baseChange ℝ ↔ _
  rw [F.squareLayer_eq_ker_constraint, realification_ker, LinearMap.mem_ker,
    F.realification.mem_squareFiltration_layer,
    F.realification.mem_squareLayer_iff_second_and_difference]
  change (F.squareLayerConstraint j).baseChange ℝ x = 0 ↔
    F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer j ∧
      F.realification.squareFst (F.realifiedSquareEquiv x) -
        F.realification.squareSnd (F.realifiedSquareEquiv x) ∈ F.realification.layer (j + 1)
  rw [F.realifiedSquareEquiv_snd, F.realifiedSquareEquiv_fst]
  simp only [squareLayerConstraint, realification_prod_eq_zero_iff,
    LinearMap.baseChange_comp, LinearMap.comp_apply, realification_mkQ_eq_zero_iff,
    LinearMap.baseChange_sub, LinearMap.sub_apply]
  rfl

theorem realifiedSquareEquiv_symm_mem_layer (j : ℕ) (x : F.realification.squareLieSubalgebra) :
    F.realifiedSquareEquiv.symm x ∈ F.squareFiltration.realification.layer j ↔
      x ∈ F.realification.squareFiltration.layer j := by
  rw [F.realifiedSquareEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareGroupEquiv :
    F.squareFiltration.realification.Group ≃* F.realification.squareFiltration.Group where
  toFun g := ⟨F.realifiedSquareEquiv g.coord⟩
  invFun g := ⟨F.realifiedSquareEquiv.symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext (F.realifiedSquareEquiv.apply_symm_apply g.coord)
  map_mul' g h := NilpotentLieBCHGroup.ext
    (map_lieBCH_of_nilpotent_steps F.realifiedSquareLieEquiv.toLieHom
      F.squareFiltration.realification.lowerCentralSeries_eq_bot
      F.realification.squareFiltration.lowerCentralSeries_eq_bot g.coord h.coord)

noncomputable def realSquareFstHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareFst

noncomputable def realSquareSndHom : F.squareFiltration.realification.Group →* F.realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) F.squareSnd

theorem realifiedSquareGroupEquiv_fst (g : F.squareFiltration.realification.Group) :
    F.realification.squareFstHom (F.realifiedSquareGroupEquiv g) = F.realSquareFstHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_fst g.coord

theorem realifiedSquareGroupEquiv_snd (g : F.squareFiltration.realification.Group) :
    F.realification.squareSndHom (F.realifiedSquareGroupEquiv g) = F.realSquareSndHom g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realifiedSquareEquiv_snd g.coord

noncomputable def realifiedSquareOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) :
    F.squareFiltration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)
    (F.realification.squareFiltration.adapted_map F.squareFiltration.realification
      F.realifiedSquareEquiv.symm.toLinearMap
      (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w q.adapted)

theorem realifiedSquareOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realifiedSquareGroupEquiv
      (F.squareFiltration.realification.polynomialOrbitEval w x (F.realifiedSquareOrbit q)) =
        F.realification.squareFiltration.polynomialOrbitEval w x q := by
  apply NilpotentLieBCHGroup.ext
  change F.realifiedSquareEquiv (eval (fun i => (x i : ℚ))
    (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact F.realifiedSquareEquiv.apply_symm_apply _

theorem realifiedSquareOrbit_fst {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareFstHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_fst, F.realifiedSquareOrbit_eval]

theorem realifiedSquareOrbit_snd {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareSndHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_snd, F.realifiedSquareOrbit_eval]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareLattice_le_fst :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareFstHom := by
  apply realificationMap_subgroup F.squareFst
  exact F.squareLattice_le_fst Γ

theorem realSquareLattice_le_snd :
    (F.squareLattice Γ).map realificationHom ≤
      (Γ.map realificationHom).comap F.realSquareSndHom := by
  apply realificationMap_subgroup F.squareSnd
  exact F.squareLattice_le_snd Γ

noncomputable def realSquareObservable (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) : ℂ :=
  u (ε • cosetMap _ _ F.realSquareFstHom (F.realSquareLattice_le_fst Γ) x) *
    star (u (cosetMap _ _ F.realSquareSndHom (F.realSquareLattice_le_snd Γ) x))

theorem realSquareObservable_mk (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (g : F.squareFiltration.realification.Group) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk g) =
      F.realification.squareObservable (Γ.map realificationHom) ε u
        (QuotientGroup.mk (F.realifiedSquareGroupEquiv g)) := by
  rw [F.realification.squareObservable_mk, F.realifiedSquareGroupEquiv_fst,
    F.realifiedSquareGroupEquiv_snd]
  rfl

theorem realSquareObservable_norm_le (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x, ‖u x‖ ≤ B)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    ‖F.realSquareObservable Γ ε u x‖ ≤ B ^ 2 := by
  rw [realSquareObservable, norm_mul, norm_star, pow_two]
  exact mul_le_mul (hu _) (hu _) (norm_nonneg _) hB

theorem realSquareObservable_top_invariant (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group) (hk : k ∈ F.squareFiltration.realification.subgroup s)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) = F.realSquareObservable Γ ε u x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change F.realSquareObservable Γ ε u (QuotientGroup.mk (k * g)) = _
    rw [F.realSquareObservable_mk, F.realSquareObservable_mk, map_mul]
    exact F.realification.squareObservable_top_invariant _ ε u χ hu
      (F.realifiedSquareGroupEquiv k) ((F.realifiedSquareEquiv_mem_layer s k.coord).mp hk)
      (QuotientGroup.mk (F.realifiedSquareGroupEquiv g))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_lipschitz_realSquare_descent
    (b : Basis ι ℚ F.squareLieSubalgebra)
    (c : Basis κ ℚ (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hin : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid l)
    (hout : bchSubgroupCoordinates c ((F.squareLattice Γ).map
      (F.squareFiltration.quotientStepHom (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)) ⊆
        denominatorGrid m)
    (he : ∀ i j, RationalHeightLE
      (c.repr (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants c i j k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) l hl hin
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let I := F.squareFiltration.layerIdeal (s + 1)
    let Δ := (F.squareLattice Γ).map (F.squareFiltration.quotientStepHom I (t := s) le_rfl)
    letI := realificationQuotientMetricSpace c Δ m hm hout
    ∃ v : F.squareFiltration.quotientTop.realification.Group ⧸ Δ.map realificationHom → ℂ,
      (∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom I (t := s) le_rfl g)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s (Fintype.card ι) (Fintype.card κ) H A (B ^ 2)) v ∧
      ∀ x, ‖v x‖ ≤ (B : ℝ) ^ 2 := by
  dsimp only
  refine exists_lipschitz_realification_reconstruction b c
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))) (lieQuotientMap_surjective _)
    (F.squareLattice Γ) _ le_rfl l m H hl hm hH hin hout he hc
    (F.realSquareObservable Γ ε u) ?_ A (B ^ 2) hLip ?_
  · intro k hk x
    exact F.realSquareObservable_top_invariant Γ ε u χ hu k
      ((F.squareFiltration.mem_realQuotientStepHom_ker _ le_rfl k).mp hk)
      (QuotientGroup.mk x)
  · simpa only [NNReal.coe_pow] using F.realSquareObservable_norm_le Γ ε u B.coe_nonneg hb

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.realification.squareFiltration.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realification.squareFstHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realification.squareSndHom
              (D.filtration.realification.squareFiltration.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hfst, hsnd⟩ :=
    hnorm D p hp hD w hw (fun i => (h i : ℚ)) f
  let q := NilpotentLieFiltration.polynomialOrbitOfLog r hr
  refine ⟨ε, γ, hγ, hε, q, ?_⟩
  intro x
  constructor
  · rw [mul_assoc]
    apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hfst
    rw [eval_map, eval_normalizedShiftLog] at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 = _ at hh
    change (eval (fun i => (x i : ℚ)) r).val.1 =
      lieBCH s (-ε.coord) (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ)) f.log) (-γ.coord))
    simpa only [Int.cast_add] using hh
  · apply NilpotentLieBCHGroup.ext
    have hh := congrArg (eval (fun i => (x i : ℚ))) hsnd
    rw [eval_map] at hh
    exact hh

end Erdos3

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem squareObservable_recovers_product (ε γ a b : F.Group) (hγ : γ ∈ Γ)
    (u : F.Group ⧸ Γ → ℂ) (q : F.squareFiltration.Group)
    (hfst : F.squareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.squareSndHom q = b) :
    F.squareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.squareObservable_mk, hfst, hsnd]
  have heq : (QuotientGroup.mk (ε * (ε⁻¹ * a * γ⁻¹)) : F.Group ⧸ Γ) = QuotientGroup.mk a := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, inv_inv, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_assoc, inv_mul_cancel, mul_one] using hγ
  rw [heq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_bounded_realified_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.squareFiltration.realification.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realSquareFstHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realSquareSndHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square_orbit s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, D.filtration.realifiedSquareOrbit q, ?_⟩
  intro x
  rw [D.filtration.realifiedSquareOrbit_fst, D.filtration.realifiedSquareOrbit_snd]
  exact hq x

end Erdos3

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_recovers_product (ε γ a b : F.realification.Group)
    (hγ : γ ∈ Γ.map realificationHom)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (q : F.squareFiltration.realification.Group)
    (hfst : F.realSquareFstHom q = ε⁻¹ * a * γ⁻¹) (hsnd : F.realSquareSndHom q = b) :
    F.realSquareObservable Γ ε u (QuotientGroup.mk q) =
      u (QuotientGroup.mk a) * star (u (QuotientGroup.mk b)) := by
  rw [F.realSquareObservable_mk]
  exact F.realification.squareObservable_recovers_product (Γ.map realificationHom)
    ε γ a b hγ u (F.realifiedSquareGroupEquiv q)
    ((F.realifiedSquareGroupEquiv_fst q).trans hfst)
    ((F.realifiedSquareGroupEquiv_snd q).trans hsnd)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L X ι : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [MulAction (NilpotentLieBCHGroup L s hnil) X]

theorem central_span_character (u : ι → L) (hu : ∀ i (w : L), ⁅u i, w⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (f : X → ℂ)
    (hf : ∀ i (r : ℝ) x, f (realBCHLine (hnil := hnil) (u i) r • x) =
      CircleFourier.character ((r * η (u i) : ℝ) : CircleFourier.Circle) * f x)
    {v : L} (hv : v ∈ Submodule.span ℝ (Set.range u)) (x : X) :
    f ((⟨v⟩ : NilpotentLieBCHGroup L s hnil) • x) =
      CircleFourier.character ((η v : ℝ) : CircleFourier.Circle) * f x := by
  have h : (∀ w : L, ⁅v, w⁆ = 0) ∧ ∀ (r : ℝ) x,
      f (realBCHLine (hnil := hnil) v r • x) =
        CircleFourier.character ((r * η v : ℝ) : CircleFourier.Circle) * f x := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact ⟨hu i, hf i⟩
    | zero =>
      refine ⟨fun w => zero_lie w, ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (0 : L) r = 1 := by
        apply ext
        exact smul_zero r
      simp [he]
    | @add v w hv hw ihv ihw =>
      refine ⟨fun z => by rw [add_lie, ihv.1, ihw.1, add_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (v + w) r =
          realBCHLine v r * realBCHLine w r := by
        apply ext
        change r • (v + w) = lieBCH s (r • v) (r • w)
        rw [lieBCH_eq_add_of_lie_eq_zero hnil (by rw [smul_lie, ihv.1, smul_zero]), smul_add]
      rw [he, mul_smul, ihv.2, ihw.2, map_add, mul_add,
        AddCircle.coe_add, CircleFourier.character_add, mul_assoc]
    | @smul a v hv ih =>
      refine ⟨fun w => by rw [smul_lie, ih.1, smul_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (a • v) r = realBCHLine v (r * a) := by
        apply ext
        exact (mul_smul r a v).symm
      rw [he, ih.2, map_smul, smul_eq_mul, mul_assoc]
  simpa only [realBCHLine_one, one_mul] using h.2 1 x

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup s)
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) =
      character (χ (F.realSquareFstHom k)) * F.realSquareObservable Γ ε u x := by
  have hcomm (y : F.realification.Group ⧸ Γ.map realificationHom) :
      ε • (F.realSquareFstHom k • y) = F.realSquareFstHom k • (ε • y) := by
    rw [← mul_smul, ← mul_smul, (F.realification.top_commutes _ hk ε).eq]
  simp only [realSquareObservable, cosetMap_smul, hs, one_smul]
  rw [hcomm, hu _ hk]
  exact mul_assoc _ _ _

variable (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

theorem realSquare_descent_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (v : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1))
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :
    v (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • x) =
      character (χ (F.realSquareFstHom k)) * v x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := F.squareFiltration.realQuotientStepHom_surjective
    (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g
  change v (QuotientGroup.mk
    (F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl k *
      F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl y)) = _
  rw [← map_mul, hv, hv]
  exact F.realSquareObservable_relative_character Γ ε u χ hu k hk hs (QuotientGroup.mk y)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (Γ : Subgroup F.realification.Group)

theorem vertical_frequency_integral_on_lattice (η : L →ₗ[ℚ] ℚ)
    (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (z : F.realification.Group)
    (hz : z ∈ F.realification.subgroup s) (hΓ : z ∈ Γ) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨x, hx⟩ := hne
  have hc : ∀ a : F.realification.Group, Commute z a := by
    intro a
    exact commute_of_lie_eq_zero z a (F.realification.top_layer_central hz a.coord)
  have he : character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) = 1 := by
    apply mul_right_cancel₀ hx
    calc
      _ = f (z • x) := (hf z hz x).symm
      _ = f x := by rw [central_smul_eq_self_of_mem Γ hΓ hc x]
      _ = 1 * f x := (one_mul _).symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

theorem real_frequency_eq_of_character_multiples (a b : ℝ)
    (h : ∀ t : ℝ, character ((t * a : ℝ) : CircleFourier.Circle) =
      character ((t * b : ℝ) : CircleFourier.Circle)) : a = b := by
  have hinj : Function.Injective character := by
    intro x y hxy
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.ext hxy
  have hzero (t : ℝ) : ((t * (a - b) : ℝ) : CircleFourier.Circle) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr (hinj (h t))
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  have ht : (1 / (2 * (a - b))) * (a - b) = (1 : ℝ) / 2 := by
    field_simp
  have hhalf := hzero (1 / (2 * (a - b)))
  rw [ht] at hhalf
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hhalf
  have hn' : (n : ℝ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem vertical_frequency_on_real_direction
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (ξ : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (y : L) (hy : y ∈ F.layer s) (a : ℝ)
    (hcharacter : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    (ξ y : ℝ) = a := by
  obtain ⟨x, hx⟩ := hne
  apply real_frequency_eq_of_character_multiples
  intro t
  apply mul_right_cancel₀ hx
  have hz : (⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) ∈ F.realification.subgroup s :=
    Submodule.tmul_mem_baseChange_of_mem t hy
  have heq := (hvert _ hz x).symm.trans (hcharacter t x)
  simpa only [realifyFunctional_tmul] using heq

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem square_mode_relative_frequency (hs : 1 ≤ s)
    (Γ : Subgroup F.squareFiltration.quotientTop.realification.Group)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (f : F.squareFiltration.quotientTop.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hrelative : ∀ k : F.squareFiltration.realification.Group,
      F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) →
      F.realSquareSndHom k = 1 → ∀ y,
      f (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • y) =
        character ((realifyFunctional η (F.realSquareFstHom k).coord : ℝ) : CircleFourier.Circle) * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  let z : F.squareLieSubalgebra := (F.squareRelativeLayer s hs x).val
  let q := lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) z
  have hq : q ∈ F.squareFiltration.quotientTop.layer s :=
    F.squareFiltration.quotientLie_mem _ le_rfl (F.squareRelativeLayer s hs x).property
  have h := vertical_frequency_on_real_direction F.squareFiltration.quotientTop Γ ξ f
    hvert hne q hq (η x : ℝ) (by
      intro t y
      let k : F.squareFiltration.realification.Group := ⟨t ⊗ₜ[ℚ] z⟩
      have hf : F.realSquareFstHom k = (⟨t ⊗ₜ[ℚ] (x : L)⟩ : F.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) := by
        rw [hf]
        exact Submodule.tmul_mem_baseChange_of_mem t x.property
      have hkzero : F.realSquareSndHom k = 1 := by
        apply NilpotentLieBCHGroup.ext
        change t ⊗ₜ[ℚ] (0 : L) = 0
        simp only [TensorProduct.tmul_zero]
      have hπ : F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k =
          (⟨t ⊗ₜ[ℚ] q⟩ : F.squareFiltration.quotientTop.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have he := hrelative k hk hkzero y
      rw [hπ, hf] at he
      simpa only [realifyFunctional_tmul] using he)
  exact_mod_cast h

theorem descended_square_mode_frequency_restriction (hs : 1 ≤ s)
    (Γ : Subgroup F.Group) (ε : F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ y,
      u (z • y) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u y)
    (v f : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hpres : ∀ (z : F.squareFiltration.quotientTop.realification.Group) (c : ℂ),
      (∀ y, v (z • y) = c * v y) → ∀ y, f (z • y) = c * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  apply F.square_mode_relative_frequency hs _ η ξ f hvert hne
  intro k hk hkzero y
  exact hpres _ _
    (fun z => F.realSquare_descent_relative_character Γ ε u
      (fun a => ((realifyFunctional η a.coord : ℝ) : CircleFourier.Circle))
      hu v hv k hk hkzero z) y

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem vertical_frequency_eq_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s) (a : ℚ)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    η c = a := by
  exact_mod_cast vertical_frequency_on_real_direction F Γ η f hvert hne c hc (a : ℝ) hline

theorem vertical_frequency_eq_one_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character (t : CircleFourier.Circle) * f x) :
    η c = 1 := by
  apply vertical_frequency_eq_of_real_line F Γ η f hvert hne c hc 1
  simpa only [Rat.cast_one, mul_one] using hline

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalKernelInvariance
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem invariant_of_kernel_circles (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (b : Basis ι ℚ K) (f : D.Space → ℂ)
    (hf : let := D.metricSpace; ∀ i t x,
      f ((D.centralRationalCircle (b i) (hK (b i).property)).act t x) = f x)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    f (z • x) = f x := by
  let := D.metricSpace
  have hspan : Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (b i))) =
      K.baseChange ℝ :=
    (D.periodicRealDirection_span (fun i => (b i : L))).trans
      (real_span_rational_family K (fun i => (b i : L)) (span_submodule_basis K b))
  have h := central_span_character (fun i => D.periodicRealDirection (b i))
    (fun i => D.periodicRealDirection_central (b i) (hK (b i).property))
    (0 : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ) f (fun i r y => by
      have hi := hf i (r : CircleFourier.Circle) y
      rw [D.centralRationalCircle_act_coe] at hi
      simpa only [LinearMap.zero_apply, mul_zero, AddCircle.coe_zero, character_zero, one_mul] using hi)
    (hspan.symm ▸ hz) x
  simpa only [LinearMap.zero_apply, AddCircle.coe_zero, character_zero, one_mul] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def averageCircles (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) : D.Niltest w := by
  let := D.metricSpace
  exact {
    orbit := T.orbit
    observable := iteratedCircleAverage A is T.observable
    normBound := T.normBound
    lipBound := T.lipBound
    norm_le := iteratedCircleAverage_norm_le A is T.norm_le
    lipschitz := iteratedCircleAverage_lipschitz A is T.lipschitz }

theorem averageCircles_unit_interval (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hT : T.UnitIntervalValued) : (T.averageCircles A is).UnitIntervalValued := by
  let := D.metricSpace
  exact iteratedCircleAverage_unit_interval A is T.lipschitz hT

theorem averageCircles_invariant (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (j : α) (hj : j ∈ is) (t : CircleFourier.Circle) (x : D.Space) :
    let := D.metricSpace
    (T.averageCircles A is).observable ((A j).act t x) = (T.averageCircles A is).observable x := by
  let := D.metricSpace
  exact iteratedCircleAverage_invariant A is hcomm T.observable j hj t x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open Module

theorem RationalHeightLE.inv {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (hne : q ≠ 0) :
    RationalHeightLE q⁻¹ H := by
  have hn : q.num ≠ 0 := by
    intro hn
    apply hne
    rw [← q.num_div_den, hn, Int.cast_zero, zero_div]
  have h := rationalHeightLE_fraction (q.den : ℤ) q.num hn
    (by simpa only [Int.natAbs_natCast] using hq.2) hq.1
  have he : q⁻¹ = (q.den : ℚ) / q.num := by
    calc
      q⁻¹ = ((q.num : ℚ) / q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
      _ = _ := inv_div _ _
  simpa only [he, Int.cast_natCast] using h

theorem exists_bounded_frequency_direction {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ (v : V) (m : ℕ), 0 < m ∧ m ≤ H ∧ η v = 1 ∧
      (∀ i, RationalHeightLE (b.repr v i) H) ∧
      (fun i => b.repr v i) ∈ denominatorGrid m := by
  classical
  have hex : ∃ i, η (b i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    apply b.ext
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let c := (η (b i))⁻¹
  let v := c • b i
  have hc : RationalHeightLE c H := (hheight i).inv hi
  have hcoord (j : ι) : b.repr v j = if i = j then c else 0 := by
    simp only [v, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨v, c.den, c.den_pos, hc.2, ?_, ?_, ?_⟩
  · change η (c • b i) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hi
  · intro j
    rw [hcoord]
    split_ifs
    · exact hc
    · exact rationalHeightLE_zero hH
  · refine ⟨fun j => if i = j then c.num else 0, ?_⟩
    intro j
    change (c.den : ℚ) * b.repr v j = ((if i = j then c.num else 0 : ℤ) : ℚ)
    rw [hcoord]
    by_cases hj : i = j
    · simp only [hj, ite_true]
      have hcden := (div_eq_iff (show (c.den : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
      simpa only [mul_comm] using hcden.symm
    · simp only [hj, ite_false, mul_zero, Int.cast_zero]

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul (n : ℕ) (hn : 0 < n) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ)⁻¹ * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hnheight : RationalHeightLE (n : ℚ) (n + 1) := by simp [RationalHeightLE]
  have hinv := hnheight.inv (by exact_mod_cast hn.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dividedFrequency (n : ℕ) (η : L →ₗ[ℚ] ℚ) : L →ₗ[ℚ] ℚ := (n : ℚ)⁻¹ • η

theorem dividedFrequency_height (n : ℕ) (hn : 0 < n) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (x : L) (hx : rationalLogHeight (η x) ≤ p) :
    rationalLogHeight (dividedFrequency n η x) ≤ p + n + 1 :=
  rationalLogHeight_nat_inv_mul n hn hx

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def frequencyKernelProjection (η : V →ₗ[ℚ] ℚ) (v : V) : V →ₗ[ℚ] V :=
  LinearMap.id - η.smulRight v

@[simp] theorem frequencyKernelProjection_apply (η : V →ₗ[ℚ] ℚ) (v x : V) :
    frequencyKernelProjection η v x = x - η x • v := rfl

theorem frequencyKernelProjection_range (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    LinearMap.range (frequencyKernelProjection η v) = LinearMap.ker η := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change η (y - η y • v) = 0
    simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change x - η x • v = x
    rw [show η x = 0 from hx, zero_smul, sub_zero]

theorem frequencyKernel_spanning (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    Submodule.span ℚ (Set.range (fun i => b i - η (b i) • v)) = LinearMap.ker η := by
  change Submodule.span ℚ (Set.range (frequencyKernelProjection η v ∘ b)) = _
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    frequencyKernelProjection_range η v hv]

theorem frequencyKernel_spanning_height (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V)
    {H : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (hv : ∀ i, RationalHeightLE (b.repr v i) H) :
    ∀ i j, RationalHeightLE (b.repr (b i - η (b i) • v) j) (2 * H ^ 2) := by
  classical
  intro i j
  rw [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hbase : RationalHeightLE (b.repr (b i) j) 1 := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one le_rfl
    · exact rationalHeightLE_zero le_rfl
  have h := hbase.sub ((hη i).mul (hv j))
  convert h using 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyFunctional_eq_rid (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional η x = TensorProduct.rid ℚ ℝ (η.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
    simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
      Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_realified_frequency_kernel_iff (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker η).baseChange ℝ ↔ realifyFunctional η x = 0 := by
  rw [realification_ker, LinearMap.mem_ker, realifyFunctional_eq_rid]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (TensorProduct.rid ℚ ℝ).injective
    simpa only [map_zero] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) :
    List J → Submodule ℚ V
  | [] => P
  | j :: js => LinearMap.ker (eta j) ⊓ finiteFrequencyKernel P eta js

theorem mem_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : V) :
    v ∈ finiteFrequencyKernel P eta js ↔ v ∈ P ∧ ∀ j ∈ js, eta j v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, Submodule.mem_inf, LinearMap.mem_ker, ih,
      List.forall_mem_cons]
    tauto

theorem finiteFrequencyKernel_le (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js ≤ P := fun v hv => (mem_finiteFrequencyKernel P eta js v).mp hv |>.1

def restrictedFrequencySpan (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    Submodule ℚ (Module.Dual ℚ P) :=
  Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})

theorem mem_restrictedFrequencySpan_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (v : P) :
    v ∈ (restrictedFrequencySpan P eta js).dualCoannihilator ↔
      (v : V) ∈ finiteFrequencyKernel P eta js := by
  change v ∈ ((Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})).dualCoannihilator : Set P) ↔ _
  rw [Submodule.coe_dualCoannihilator_span, mem_finiteFrequencyKernel]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_image, LinearMap.comp_apply,
    Submodule.subtype_apply, v.property, true_and]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_comp {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (eta : W →ₗ[ℚ] ℚ) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (eta.comp f) x = realifyFunctional eta (f.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedPieceMap_grade_fixed (j : ℕ) (x : F.layer j) :
    basisGradeProjection (F.associatedGradedBasis b w hF) w j (F.associatedGradedPieceMap j x) =
      F.associatedGradedPieceMap j x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b w hF j x]
  apply (F.associatedGradedBasis b w hF).repr.injective
  ext i
  simp only [basisGradeProjection_repr, F.gradedPieceProjection_coordinate]
  split_ifs <;> rfl

theorem frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.gradedRefiltrationLayer U s, eta x = 0 := by
  intro x hx
  obtain ⟨hxs, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  rw [← F.gradedFrequency_top_piece b w hF eta ⟨x, hxs⟩]
  exact hzero _ hxU (F.associatedGradedPieceMap_grade_fixed b w hF s ⟨x, hxs⟩)

theorem real_frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.realGradedRefiltrationLayer U s, realifyFunctional eta x = 0 := by
  have hle : F.gradedRefiltrationLayer U s ≤ LinearMap.ker eta :=
    F.frequency_zero_on_refiltered_top b w hF U eta hzero
  intro x hx
  exact (mem_realified_frequency_kernel_iff eta x).mp (Submodule.baseChange_mono ℝ hle hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_eq_map_coannihilator (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js =
      (restrictedFrequencySpan P eta js).dualCoannihilator.map P.subtype := by
  ext v
  constructor
  · intro hv
    let x : P := ⟨v, finiteFrequencyKernel_le P eta js hv⟩
    exact ⟨x, (mem_restrictedFrequencySpan_coannihilator P eta js x).mpr hv, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_restrictedFrequencySpan_coannihilator P eta js x).mp hx

theorem finiteFrequencyKernel_eq_of_span_eq (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) (xi : I → V →ₗ[ℚ] ℚ) (is : List I)
    (hspan : restrictedFrequencySpan P eta js = restrictedFrequencySpan P xi is) :
    finiteFrequencyKernel P eta js = finiteFrequencyKernel P xi is := by
  rw [finiteFrequencyKernel_eq_map_coannihilator, finiteFrequencyKernel_eq_map_coannihilator, hspan]

theorem exists_restricted_frequency_basis [FiniteDimensional ℚ V] (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ m : ℕ, m ≤ finrank ℚ P ∧ ∃ indices : Fin m → J,
      (∀ i, indices i ∈ js) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      Submodule.span ℚ (Set.range (fun i => (eta (indices i)).comp P.subtype)) =
        restrictedFrequencySpan P eta js := by
  classical
  let W := restrictedFrequencySpan P eta js
  obtain ⟨u, hu, hspan, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})
  have hex (i : Fin (finrank ℚ W)) :
      ∃ j, j ∈ js ∧ (eta j).comp P.subtype = u i := hu i
  choose indices hindices heq using hex
  have hfun : (fun i => (eta (indices i)).comp P.subtype) = u := funext heq
  refine ⟨finrank ℚ W, ?_, indices, hindices, ?_, ?_⟩
  · have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    omega
  · rw [hfun]
    exact hlin
  · rw [hfun]
    exact hspan

theorem restrictedFrequencySpan_finRange (P : Submodule ℚ V) {m : ℕ}
    (eta : Fin m → V →ₗ[ℚ] ℚ) :
    restrictedFrequencySpan P eta (List.finRange m) =
      Submodule.span ℚ (Set.range (fun i => (eta i).comp P.subtype)) := by
  unfold restrictedFrequencySpan
  congr 1
  ext x
  simp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

def pivotAnnihilatorIdeal : LieIdeal ℚ L :=
  F.topSubspaceIdeal (finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js)
    ((finiteFrequencyKernel_le _ _ _).trans inf_le_left)

theorem mem_pivotAnnihilatorIdeal (x : L) :
    x ∈ F.pivotAnnihilatorIdeal π eta js ↔
      x ∈ F.layer s ∧ π x = 0 ∧ ∀ j ∈ js, eta j x = 0 := by
  change x ∈ finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js ↔ _
  rw [mem_finiteFrequencyKernel]
  change ((x ∈ F.layer s ∧ π x = 0) ∧ ∀ j ∈ js, eta j x = 0) ↔ _
  exact and_assoc

noncomputable def pivotQuotientMarkedMap : (L ⧸ F.pivotAnnihilatorIdeal π eta js) →ₗ⁅ℚ⁆ Y :=
  lieQuotientDescend (F.pivotAnnihilatorIdeal π eta js) π
    (fun x hx => ((F.mem_pivotAnnihilatorIdeal π eta js x).mp hx).2.1)

noncomputable def pivotQuotientFrequency (j : J) (hj : j ∈ js) :
    (L ⧸ F.pivotAnnihilatorIdeal π eta js) →ₗ[ℚ] ℚ :=
  (F.pivotAnnihilatorIdeal π eta js).toSubmodule.liftQ (eta j)
    (fun x hx => ((F.mem_pivotAnnihilatorIdeal π eta js x).mp hx).2.2 j hj)

@[simp] theorem pivotQuotientMarkedMap_mk (x : L) :
    F.pivotQuotientMarkedMap π eta js (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js) x) =
      π x := rfl

@[simp] theorem pivotQuotientFrequency_mk (j : J) (hj : j ∈ js) (x : L) :
    F.pivotQuotientFrequency π eta js j hj
      (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js) x) = eta j x := rfl

noncomputable def pivotProductQuotientMap :
    (L × W) →ₗ⁅ℚ⁆ (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W :=
  (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js)).prodMap (LieHom.id : W →ₗ⁅ℚ⁆ W)

noncomputable def pivotProductMarkedMap :
    ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) →ₗ⁅ℚ⁆ (Y × W) :=
  (F.pivotQuotientMarkedMap π eta js).prodMap (LieHom.id : W →ₗ⁅ℚ⁆ W)

@[simp] theorem pivotProductMarkedMap_quotient (x : L × W) :
    F.pivotProductMarkedMap π eta js (F.pivotProductQuotientMap π eta js x) =
      (π x.1, x.2) := rfl

variable (partner : J → W →ₗ[ℚ] ℚ)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realifyCoordinateMap (ℓ : V →ₗ[ℚ] (J → ℚ)) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.pi (fun j => realifyFunctional ((LinearMap.proj j).comp ℓ))

noncomputable def coordinateFunctionalMatrix (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) : Matrix J I ℚ := fun j i => ℓ (b i) j

theorem realifyCoordinateMap_tmul (ℓ : V →ₗ[ℚ] (J → ℚ)) (a : ℝ) (v : V) (j : J) :
    realifyCoordinateMap ℓ (a ⊗ₜ[ℚ] v) j = a * (ℓ v j : ℝ) :=
  realifyFunctional_tmul ((LinearMap.proj j).comp ℓ) a v

theorem realifyCoordinateMap_comp {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ℓ : W →ₗ[ℚ] (J → ℚ)) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap (ℓ.comp f) x = realifyCoordinateMap ℓ (f.baseChange ℝ x) := by
  funext j
  exact realifyFunctional_comp ((LinearMap.proj j).comp ℓ) f x

theorem realifyCoordinateMap_eq_matrix [Fintype I] (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap ℓ x =
      (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) *ᵥ
        (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realifyCoordinateMap ℓ).comp (b.baseChange ℝ).equivFun.symm.toLinearMap =
      Matrix.mulVecLin (fun j i => (coordinateFunctionalMatrix b ℓ j i : ℝ)) := by
    apply (Pi.basisFun ℝ I).ext
    intro i
    change realifyCoordinateMap ℓ ((b.baseChange ℝ).equivFun.symm (Pi.single i 1)) =
      Matrix.of (fun j k => (coordinateFunctionalMatrix b ℓ j k : ℝ)) *ᵥ Pi.single i 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext j
    rw [realifyCoordinateMap_tmul, one_mul]
    rfl
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

theorem realifyCoordinateMap_norm_bound [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H : ℕ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (x : ℝ ⊗[ℚ] V) :
    ‖realifyCoordinateMap ℓ x‖ ≤
      ((Fintype.card I : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun j i => (hℓ j i).abs_real_le) _

theorem realifyCoordinateMap_grid [Fintype I] [Fintype J]
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realifyCoordinateMap ℓ x ∈
      realDenominatorGrid (matrixDenominator (coordinateFunctionalMatrix b ℓ) * l) := by
  rw [realifyCoordinateMap_eq_matrix b ℓ x]
  exact real_matrix_denominator_grid (coordinateFunctionalMatrix b ℓ) l _ hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealCoordinateImageSpan
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J B : Type*} [AddCommGroup V] [Module ℚ V]

theorem coordinateImage_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    U.map ℓ = Submodule.span ℚ (Set.range (fun j => ℓ (g j))) := by
  rw [← hg, Submodule.map_span, ← Set.range_comp]
  rfl

theorem realifyCoordinateMap_image_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    (U.baseChange ℝ).map (realifyCoordinateMap ℓ) =
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← hg, Submodule.baseChange_span, Submodule.map_span, Set.image_image, ← Set.range_comp]
  apply congrArg (Submodule.span ℝ)
  apply congrArg Set.range
  funext j i
  exact (realifyCoordinateMap_tmul ℓ 1 (g j) i).trans (one_mul _)

theorem realifyCoordinateMap_mem_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) :
    realifyCoordinateMap ℓ x ∈
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← realifyCoordinateMap_image_eq_span U g hg ℓ]
  exact ⟨x, hx, rfl⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def baseLinear : PolynomialTranslationLie σ →ₗ[ℚ] (σ → ℚ) where
  toFun x := x.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { A.range.comap baseLinear with
    lie_mem' := by
      intro x y _ _
      change (0 : σ → ℚ) ∈ A.range
      exact Submodule.zero_mem _ }

omit [Fintype τ] in
@[simp] theorem mem_baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (x : PolynomialTranslationLie σ) : x ∈ baseRange A ↔ x.base ∈ A.range := Iff.rfl

noncomputable def baseRangeBase (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    baseRange A →ₗ[ℚ] A.range where
  toFun x := ⟨x.val.base, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ[ℚ] (τ → ℚ) :=
  (LinearEquiv.ofInjective A hA).symm.toLinearMap.comp (baseRangeBase A)

omit [Fintype τ] in
@[simp] theorem apply_projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    A (projectedBaseCoordinates A hA x) = x.val.base := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective A hA).apply_symm_apply
    ⟨x.val.base, x.property⟩)

noncomputable def projectedRestriction (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ⁅ℚ⁆ PolynomialTranslationLie τ where
  toFun x := ⟨projectedBaseCoordinates A hA x, polynomialLinearRestriction A x.val.polynomial⟩
  map_add' x y := by
    apply PolynomialTranslationLie.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_smul' r x := by
    apply PolynomialTranslationLie.ext
    · exact map_smul _ _ _
    · exact map_smul _ _ _
  map_lie' := by
    intro x y
    apply PolynomialTranslationLie.ext
    · apply hA
      rw [apply_projectedBaseCoordinates]
      change (0 : σ → ℚ) = A 0
      exact (map_zero A).symm
    · change polynomialLinearRestriction A (scalarDirectionalDerivative x.val.base y.val.polynomial -
        scalarDirectionalDerivative y.val.base x.val.polynomial) =
        scalarDirectionalDerivative (projectedBaseCoordinates A hA x)
          (polynomialLinearRestriction A y.val.polynomial) -
        scalarDirectionalDerivative (projectedBaseCoordinates A hA y)
          (polynomialLinearRestriction A x.val.polynomial)
      rw [map_sub, scalarDirectionalDerivative_linearRestriction,
        scalarDirectionalDerivative_linearRestriction,
        apply_projectedBaseCoordinates, apply_projectedBaseCoordinates]

@[simp] theorem projectedRestriction_base (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).base = projectedBaseCoordinates A hA x := rfl

@[simp] theorem projectedRestriction_polynomial (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).polynomial = polynomialLinearRestriction A x.val.polynomial := rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open Module
open scoped TensorProduct

variable {B : Type*} [Fintype B]

theorem weightedTranslationBase_real_image_graded
    {J : Type*} (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    (g : J → weightedSubalgebra w d) (hg : Submodule.span ℚ (Set.range g) = U) :
    BasisGradedSubmodule (Pi.basisFun ℝ B) w
      ((U.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) := by
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  rw [realifyCoordinateMap_image_eq_span U g hg ℓ]
  intro j z hz
  let K := Submodule.span ℝ (Set.range (fun a i => ((g a).val.base i : ℝ)))
  change basisGradeProjection (Pi.basisFun ℝ B) w j z ∈ K
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    have hga : g a ∈ U := by rw [← hg]; exact Submodule.subset_span ⟨a, rfl⟩
    have hproj := hU j (g a) hga
    have ht := Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) hproj
    have hm := realifyCoordinateMap_mem_span U g hg ℓ ht
    change _ ∈ K at hm
    convert hm using 1
    funext i
    have hp := basisGradeProjection_repr (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ)) i
    simp only [Pi.basisFun_repr] at hp
    change (basisGradeProjection (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ))) i = _
    rw [hp, realifyCoordinateMap_tmul, one_mul]
    change (if w i = j then ((g a).val.base i : ℝ) else 0) =
      ((basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j (g a)).val.base i : ℝ)
    rw [weightedBasis_projection_base]
    split_ifs <;> simp
  | zero => simpa only [map_zero] using K.zero_mem
  | add x y hx hy hxp hyp =>
    rw [map_add]
    exact K.add_mem hxp hyp
  | smul c x hx hxp =>
    rw [map_smul]
    exact K.smul_mem c hxp

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProjectedPotentialGroupIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def projectedSubalgebra (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie τ) :=
  (U.comap (baseRange A).incl).map (projectedRestriction A hA)

theorem projected_pure_constant_zero
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial τ ℚ)
    (hP : (⟨0,P⟩ : PolynomialTranslationLie τ) ∈ projectedSubalgebra A hA U) :
    P.coeff 0 = 0 := by
  obtain ⟨x,hx,hxP⟩ := hP
  have hb : x.val.base = 0 := by
    rw [← apply_projectedBaseCoordinates A hA x]
    have hz : projectedBaseCoordinates A hA x = 0 := congrArg PolynomialTranslationLie.base hxP
    rw [hz, map_zero]
  have hpure : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) ∈ U := by
    have he : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) = x.val :=
      PolynomialTranslationLie.ext hb.symm rfl
    rw [he]
    exact hx
  have hz := pure_constant_zero_of_top_frequency w d U hgraded frequency hfrequency hkill
    x.val.polynomial hpure
  have hp : polynomialLinearRestriction A x.val.polynomial = P :=
    congrArg PolynomialTranslationLie.polynomial hxP
  rw [← hp, coeff_zero_polynomialLinearRestriction, hz]

noncomputable def projectedPotentialRelation
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    Erdos3.PolynomialPotentialRelation τ where
  space := relationSpace (projectedSubalgebra A hA U)
  bracket_mem := by
    intro x P z Q hx hz
    exact (mem_relationSpace _ _ _).mpr (raw_lie_mem _ x z P Q
      ((mem_relationSpace _ _ _).mp hx) ((mem_relationSpace _ _ _).mp hz))
  pure_constant_zero := fun P hP => projected_pure_constant_zero A hA w d U hgraded
    frequency hfrequency hkill P ((mem_relationSpace _ _ _).mp hP)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RealProjectedPotentialGroupIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem continuous_pair_pullback {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] {f : X × B → ℝ} {b : X → B}
    (hf : Continuous f) (hb : Continuous b) :
    Continuous (fun z : X × X => f (z.1, b z.2)) :=
  hf.comp (continuous_id.prodMap hb)

omit [Fintype σ] in
theorem continuous_pair_potential_difference {X B : Type*}
    [TopologicalSpace X] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] {a b : X → B} {v : B → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) :
    Continuous (fun z : X × X => v (b z.2) - v (b z.2 - a z.1)) :=
  (hv.comp (hb.comp continuous_snd)).sub
    (hv.comp ((hb.comp continuous_snd).sub (ha.comp continuous_fst)))

omit [Fintype σ] in
theorem realification_pair_eq_of_rational
    {V Y : Type*} [AddCommGroup V] [Module ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [TopologicalSpace Y] [T2Space Y]
    (U : Submodule ℚ V)
    {f g : (ℝ ⊗[ℚ] V) × (ℝ ⊗[ℚ] V) → Y}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x y : U, f ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)) =
      g ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)))
    {x y : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) (hy : y ∈ U.baseChange ℝ) :
    f (x, y) = g (x, y) := by
  apply realification_submodule_eq_of_rational U
    (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) _ hy
  intro y
  exact realification_submodule_eq_of_rational U
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (fun x => h x y) hx

omit [Fintype σ] in
theorem eval_real_map_at_rational (P : MvPolynomial σ ℚ) (z : σ → ℚ) :
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      (eval z P : ℝ) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap ℚ ℝ) z P).symm

theorem bchRealTranslationHom_rational_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (x : weightedSubalgebra w d) (hx : x ∈ U) (z : σ → ℚ)
    (hz : z ∈ U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype)) :
    eval (fun i => (z i : ℝ))
        (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).polynomial =
      eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval ((fun i => (z i : ℝ)) -
          (bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  have hq := polynomialExponentialCoordinate_eval_potential_on_submodule
    (U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype))
    x.val.base ⟨x, hx, rfl⟩ x.val.polynomial V (hderiv x hx) z hz
  have hr : bchRealTranslationHom w d hwd ⟨(1 : ℝ) ⊗ₜ[ℚ] x⟩ =
      PolynomialTranslationGroupOver.map (algebraMap ℚ ℝ)
        (PolynomialTranslationGroupOver.rationalEquiv
          (bchTranslationHom w d hw hwd ⟨x⟩)) :=
    bchRealTranslationHom_rational w d hw hwd ⟨x⟩
  rw [hr]
  change eval (fun i => (z i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) (polynomialExponentialCoordinate x.val.base x.val.polynomial)) =
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ)))
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hzsub : ((fun i => (z i : ℝ)) - (fun i => (x.val.base i : ℝ))) =
      (fun i => ((z - x.val.base) i : ℝ)) := by
    ext i
    simp only [Pi.sub_apply, Rat.cast_sub]
  rw [hzsub, eval_real_map_at_rational, eval_real_map_at_rational, eval_real_map_at_rational]
  exact_mod_cast hq

theorem bchRealTranslationHom_eval_potential_on_real_base_image
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  let B := realifyCoordinateMap ℓ
  have hB : Continuous B := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) B
  obtain ⟨y, hy, rfl⟩ := hb
  let f : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial
  let r : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (ℝ ⊗[ℚ] weightedSubalgebra w d) → ℝ :=
    fun z => eval (B z.2) (MvPolynomial.map (algebraMap ℚ ℝ) V) -
      eval (B z.2 - (bchRealTranslationHom w d hwd ⟨z.1⟩).base)
        (MvPolynomial.map (algebraMap ℚ ℝ) V)
  have hf0 := continuous_bchRealTranslationHom_polynomial_eval w d hw hd hwd
  have hf : Continuous f := continuous_pair_pullback hf0 hB
  have hr : Continuous r := continuous_pair_potential_difference
    (continuous_bchRealTranslationHom_base w d hw hd hwd) hB
    (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) V))
  have hrat (x y : U.toSubmodule) :
      f ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
      r ((1 : ℝ) ⊗ₜ[ℚ] (x : weightedSubalgebra w d),
        (1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) := by
    have hBy : B ((1 : ℝ) ⊗ₜ[ℚ] (y : weightedSubalgebra w d)) =
        (fun i => (y.val.val.base i : ℝ)) := by
      funext i
      exact (realifyCoordinateMap_tmul ℓ 1 y.val i).trans (one_mul _)
    dsimp only [f, r]
    rw [hBy]
    exact bchRealTranslationHom_rational_eval_potential w d hw hwd U V hderiv
      x.val x.property y.val.val.base ⟨y.val, y.property, rfl⟩
  exact realification_pair_eq_of_rational U.toSubmodule hf hr hrat hg hy

theorem bchRealTranslationHom_eval_potential
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial σ ℚ)
    (hderiv : ∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial)
    (g : (weightedFiltration w d hwd).realification.Group)
    (hg : g.coord ∈ U.toSubmodule.baseChange ℝ) (b : σ → ℝ)
    (hb : b ∈ (U.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) :
    eval b (bchRealTranslationHom w d hwd g).polynomial =
      eval b (MvPolynomial.map (algebraMap ℚ ℝ) V) -
        eval (b - (bchRealTranslationHom w d hwd g).base)
          (MvPolynomial.map (algebraMap ℚ ℝ) V) := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  exact bchRealTranslationHom_eval_potential_on_real_base_image
    w d hw hd hwd U V hderiv g hg b hb

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedVectorLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {rho : ℝ} (hrho : 0 < rho) (x y : V) (hx : rho ≤ ‖x‖) (hy : rho ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / rho) * ‖x - y‖ := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hrho.trans_le hy)
  have hid : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hscale : ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
      _ = ‖(x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := congrArg norm hid
      _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
      _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by
        rw [norm_smul, NormedSpace.norm_normalize hy0, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le x y
        rw [abs_sub_comm] at h
        linarith
  have hsmall := (mul_le_mul_of_nonneg_right hx
    (norm_nonneg (NormedSpace.normalize x - NormedSpace.normalize y))).trans hscale
  calc
    _ ≤ (2 * ‖x - y‖) / rho := (le_div_iff₀ hrho).mpr (by nlinarith [hsmall])
    _ = _ := by ring

theorem lipschitzWith_normalize {X V : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (u : X → V) {rho K : ℝ≥0}
    (hrho : 0 < rho) (hLip : LipschitzWith K u) (hlower : ∀ x, (rho : ℝ) ≤ ‖u x‖) :
    LipschitzWith (2 / rho * K) (fun x => NormedSpace.normalize (u x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  calc
    _ ≤ (2 / (rho : ℝ)) * ‖u x - u y‖ := norm_normalize_sub_le hrho _ _ (hlower x) (hlower y)
    _ ≤ (2 / (rho : ℝ)) * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y) (by positivity)
    _ = ((2 / rho * K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteNormalizedFrame
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem euclidean_norm_le_card_add_one_mul {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    ‖v‖ ≤ (Fintype.card I + 1 : ℝ) * M := by
  have hsq : ‖v‖ ^ 2 ≤ (Fintype.card I : ℝ) * M ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (Fintype.card I : ℝ) ≤ (Fintype.card I + 1 : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hbound := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
  nlinarith [norm_nonneg v, mul_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card I + 1) hM]

theorem lipschitzWith_complex_vector {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {K : ℝ≥0} (hu : ∀ i, LipschitzWith K (u i)) :
    LipschitzWith ((Fintype.card I + 1 : ℝ≥0) * K)
      (fun x => (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have h := euclidean_norm_le_card_add_one_mul
    ((WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I) - WithLp.toLp 2 (fun i => u i y))
    (M := (K : ℝ) * dist x y) (by positivity) (fun i => by
      simpa only [PiLp.sub_apply, PiLp.toLp_apply, dist_eq_norm] using (hu i).dist_le_mul x y)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_assoc] using h

theorem normalize_complex_unit_smul {I : Type*} [Fintype I]
    (c : ℂ) (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ I) :
    NormedSpace.normalize (c • v) = c • NormedSpace.normalize v := by
  unfold NormedSpace.normalize
  rw [norm_smul, hc, one_mul]
  exact smul_comm _ _ _

theorem exists_normalized_complex_family {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {rho K : ℝ≥0} (hrho : 0 < rho)
    (hLip : ∀ i, LipschitzWith K (u i)) (hlower : ∀ x, ∃ i, (rho : ℝ) ≤ ‖u i x‖) :
    ∃ v : I → X → ℂ,
      (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖v i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (2 / rho * ((Fintype.card I + 1 : ℝ≥0) * K)) (v i)) ∧
      ∀ x y c, ‖c‖ = 1 → (∀ i, u i x = c * u i y) → ∀ i, v i x = c * v i y := by
  let U (x : X) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => u i x)
  have hnorm (x : X) : (rho : ℝ) ≤ ‖U x‖ := by
    obtain ⟨i, hi⟩ := hlower x
    exact hi.trans (PiLp.norm_apply_le (U x) i)
  have hne (x : X) : U x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hrho (hnorm x))
  have hone (x : X) : ‖NormedSpace.normalize (U x)‖ = 1 := NormedSpace.norm_normalize (hne x)
  let v (i : I) (x : X) := NormedSpace.normalize (U x) i
  have hvLip := lipschitzWith_normalize U hrho (lipschitzWith_complex_vector u hLip) hnorm
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [← EuclideanSpace.norm_sq_eq, hone, one_pow]
  · intro i x
    exact (PiLp.norm_apply_le (NormedSpace.normalize (U x)) i).trans_eq (hone x)
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (PiLp.dist_apply_le (NormedSpace.normalize (U x)) (NormedSpace.normalize (U y)) i).trans
      (hvLip.dist_le_mul x y)
  · intro x y c hc hu i
    have heq : U x = c • U y := by
      ext j
      exact hu j
    change NormedSpace.normalize (U x) i = c * NormedSpace.normalize (U y) i
    rw [heq, normalize_complex_unit_smul c hc]
    rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem vector_approximation_precision {I : Type*} [Fintype I] {q epsilon : ℝ}
    (a : ℕ) (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hepsilon : 0 < epsilon) (hscale : 1 / epsilon ≤ Real.exp ((q + 2) ^ a)) :
    0 < epsilon / (Fintype.card I + 1 : ℝ) ∧
      1 / (epsilon / (Fintype.card I + 1 : ℝ)) ≤ Real.exp ((q + 2) ^ (a + 1)) := by
  have hcard : (0 : ℝ) < Fintype.card I + 1 := by positivity
  refine ⟨div_pos hepsilon hcard, ?_⟩
  have hcount : (Fintype.card I + 1 : ℝ) ≤ Real.exp (q + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq, Real.add_one_le_exp (1 : ℝ)]
  have hpow : 1 ≤ (q + 2) ^ a := one_le_pow₀ (by linarith)
  have hexponent : q + 1 + (q + 2) ^ a ≤ (q + 2) ^ (a + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ = (Fintype.card I + 1 : ℝ) * (1 / epsilon) := by field_simp
    _ ≤ Real.exp (q + 1) * Real.exp ((q + 2) ^ a) :=
      mul_le_mul hcount hscale (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (q + 1 + (q + 2) ^ a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem euclidean_coefficient_norm_le_exp {I : Type*} [Fintype I] {q : ℝ}
    (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (c : EuclideanSpace ℂ I) (hc : ∀ i, ‖c i‖ ≤ 2) :
    ‖c‖ ≤ Real.exp (q + 2) := by
  have h := euclidean_norm_le_card_add_one_mul c (by norm_num : (0 : ℝ) ≤ 2) hc
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.one_le_exp hq,
    mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg q)]

theorem euclidean_error_le_of_coordinate_errors {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hv : ∀ i, ‖v i‖ ≤ epsilon / (Fintype.card I + 1 : ℝ)) :
    ‖v‖ ≤ epsilon := by
  have h := euclidean_norm_le_card_add_one_mul v (div_nonneg hepsilon (by positivity)) hv
  have hcard : (Fintype.card I + 1 : ℝ) ≠ 0 := by positivity
  simpa only [mul_div_cancel₀ _ hcard] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalar_error_le_of_vector_error {I J S : Type*} [Fintype I] [Fintype J]
    (u : I → S → ℂ) (w : J → S → ℂ) (c : J → EuclideanSpace ℂ I)
    {epsilon : ℝ}
    (herror : ∀ x, ‖(WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) -
      ∑ j, w j x • c j‖ ≤ epsilon) (k : I) :
    ∀ x, ‖u k x - ∑ j, w j x * c j k‖ ≤ epsilon := by
  intro x
  have h := (PiLp.norm_apply_le
    ((WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) - ∑ j, w j x • c j) k).trans (herror x)
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h

theorem norm_complex_half_le_one {c : ℂ} (hc : ‖c‖ ≤ 2) : ‖c / 2‖ ≤ 1 := by
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [norm_div, htwo]
  linarith only [hc]

theorem sum_double_half_products {J : Type*} [Fintype J] (a b c : J → ℂ) :
    (∑ j : Bool × J, (c j.2 / 2 * a j.2) * b j.2) = ∑ j, (a j * b j) * c j := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vector_approximation_precompose {I J S X : Type*} [Fintype I] [Fintype J]
    [PseudoMetricSpace X] (f : X → X) (y z : S → X) (w : J → S → ℂ)
    {A : ℝ≥0} (hf : LipschitzWith A f) (heval : ∀ x, f (y x) = z x)
    {p q B B' epsilon : ℝ} (hscale : Real.exp p * (A : ℝ) ≤ Real.exp q) (hB : B ≤ B')
    (happrox : ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B) ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (y x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon) :
    ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B') ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (z x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon := by
  intro u ell hell hu hub
  have hbound : ((ell * A : ℝ≥0) : ℝ) ≤ Real.exp q :=
    (mul_le_mul_of_nonneg_right hell A.coe_nonneg).trans hscale
  obtain ⟨c, hc, hcB, herr⟩ := happrox (fun k x => u k (f x)) (ell * A) hbound
    (fun k => (hu k).comp hf) (fun k x => hub k (f x))
  refine ⟨c, hc, fun j => (hcB j).trans hB, ?_⟩
  intro x
  simpa only [heval x] using herr x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TwistedBufferedTranslationPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ}

noncomputable def bufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  (Ψ.value (fun i => g.base i - (β i : ℝ)) : ℂ) *
    (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ)

noncomputable def bufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, bufferedTranslationTerm Ψ D₀ g β

theorem bufferedTranslationTerm_nonzero_iff (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀ g β ≠ 0 ↔
      Ψ.value (fun i => g.base i - (β i : ℝ)) ≠ 0 := by
  simp only [bufferedTranslationTerm, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
    Circle.coe_ne_zero, or_false]

theorem bufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : bufferedTranslationTerm Ψ D₀ g β ≠ 0)
    (hγ : bufferedTranslationTerm Ψ D₀ g γ ≠ 0) : β = γ := by
  have hβ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g β).mp hβ
  have hγ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hγ
  exact (Ψ.buffered_lift_unique g.base β γ
    (fun i => (Ψ.support _ hβ' i).trans (by norm_num)) hγ').symm

theorem bufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ g = bufferedTranslationTerm Ψ D₀ g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hn))

theorem bufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖bufferedTranslationPhase Ψ D₀ g‖ ≤ 1 := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
  exact Ψ.le_one _

theorem bufferedTranslationPhase_eq_phaseFunction (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationPhase Ψ D₀ g =
      (Ψ.value (fun i => g.base i - (⌊g.base i + 1 / 2⌋ : ℝ)) : ℂ) *
        translationPhaseFunction D₀ g := by
  apply bufferedTranslationPhase_eq_chart Ψ D₀ g (fun i => ⌊g.base i + 1 / 2⌋)
  intro i
  apply abs_le.mpr
  have hl := Int.floor_le (g.base i + 1 / 2)
  have hu := Int.lt_floor_add_one (g.base i + 1 / 2)
  constructor <;> linarith

theorem bufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ (algebraicMajorSymbol D D₀ A u) =
      (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ _ β hβ]
  unfold bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol]
  rfl

theorem bufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        bufferedTranslationTerm Ψ D₀ g β := by
  unfold bufferedTranslationTerm
  have hweight : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  rw [hweight]
  congr 1
  exact translationPhaseArgument_fourier_integer D₀ g γ.base β γ.polynomial

theorem bufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) :
    bufferedTranslationPhase Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        bufferedTranslationPhase Ψ D₀ g := by
  unfold bufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (bufferedTranslationTerm Ψ D₀
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  refine he.symm.trans (tsum_congr fun β => ?_)
  exact bufferedTranslationTerm_integer_lattice Ψ D₀ g γ β

theorem bufferedTranslationPhase_integerSubgroup (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationSubgroup) :
    bufferedTranslationPhase Ψ D₀ (g * γ) = bufferedTranslationPhase Ψ D₀ g := by
  obtain ⟨γ, rfl⟩ := hγ
  exact bufferedTranslationPhase_integer_lattice Ψ D₀ g γ

theorem bufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    bufferedTranslationPhase Ψ D₀ (g * ⟨0, C a⟩) =
      bufferedTranslationPhase Ψ D₀ g * (Real.fourierChar a : ℂ) := by
  rw [bufferedTranslationPhase_eq_phaseFunction, bufferedTranslationPhase_eq_phaseFunction,
    translationPhaseFunction_central]
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb, mul_assoc]

noncomputable def bufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) → ℂ :=
  Quotient.lift (bufferedTranslationPhase Ψ D₀) (fun g h hgh => by
    have hi := bufferedTranslationPhase_integerSubgroup Ψ D₀ g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem bufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationQuotientPhase Ψ D₀ (QuotientGroup.mk g) = bufferedTranslationPhase Ψ D₀ g := rfl

theorem bufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) :
    ‖bufferedTranslationQuotientPhase Ψ D₀ g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact bufferedTranslationPhase_norm_le_one Ψ D₀

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

noncomputable def twistedBufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  T (fun i => g.base i - (β i : ℝ)) (fun i => (β i : ZMod M)) *
    bufferedTranslationTerm Ψ D₀ g β

noncomputable def twistedBufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, twistedBufferedTranslationTerm M Ψ D₀ T g β

theorem twistedBufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : twistedBufferedTranslationTerm M Ψ D₀ T g β ≠ 0)
    (hγ : twistedBufferedTranslationTerm M Ψ D₀ T g γ ≠ 0) : β = γ :=
  bufferedTranslationTerm_unique Ψ D₀ g β γ
    (mul_ne_zero_iff.mp hβ).2 (mul_ne_zero_iff.mp hγ).2

theorem twistedBufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T g = twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  have hb := (mul_ne_zero_iff.mp hn).2
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hb))

theorem twistedBufferedTranslationTerm_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    ‖twistedBufferedTranslationTerm M Ψ D₀ T g β‖ ≤ 1 := by
  have hb : ‖bufferedTranslationTerm Ψ D₀ g β‖ ≤ 1 := by
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  rw [twistedBufferedTranslationTerm, norm_mul]
  exact (mul_le_mul (hT _ _) hb (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem twistedBufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖twistedBufferedTranslationPhase M Ψ D₀ T g‖ ≤ 1 := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT g _

theorem twistedBufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T (algebraicMajorSymbol D D₀ A u) =
      T (fun i => eval u (A i) - (β i : ℝ)) (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T _ β hβ]
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol, mul_assoc]
  rfl

theorem twistedBufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  rw [twistedBufferedTranslationTerm, bufferedTranslationTerm_integer_lattice]
  have hx : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  have hr : (fun i => ((β + γ.base) i : ZMod M)) = (fun i => (β i : ZMod M)) := by
    funext i
    simp only [Pi.add_apply, Int.cast_add, hγ i, add_zero]
  rw [hx, hr]
  rfl

theorem twistedBufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) :
    twistedBufferedTranslationPhase M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        twistedBufferedTranslationPhase M Ψ D₀ T g := by
  unfold twistedBufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (twistedBufferedTranslationTerm M Ψ D₀ T
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  exact he.symm.trans (tsum_congr fun β =>
    twistedBufferedTranslationTerm_integer_lattice M Ψ D₀ T g γ hγ β)

theorem twistedBufferedTranslationPhase_residueCover (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationResidueCover M) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * γ) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := by
  obtain ⟨γ, hγ, rfl⟩ := hγ
  exact twistedBufferedTranslationPhase_integer_lattice M Ψ D₀ T g γ hγ

theorem twistedBufferedTranslationTerm_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T (g * ⟨0, C a⟩) β =
      twistedBufferedTranslationTerm M Ψ D₀ T g β * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m)) (fun i => (β i : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  simp only [Circle.coe_mul, mul_assoc]

theorem twistedBufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * ⟨0, C a⟩) =
      twistedBufferedTranslationPhase M Ψ D₀ T g * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationPhase
  simp_rw [twistedBufferedTranslationTerm_central]
  exact tsum_mul_right

noncomputable def twistedBufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) → ℂ :=
  Quotient.lift (twistedBufferedTranslationPhase M Ψ D₀ T) (fun g h hgh => by
    have hi := twistedBufferedTranslationPhase_residueCover M Ψ D₀ T g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem twistedBufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    twistedBufferedTranslationQuotientPhase M Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := rfl

theorem twistedBufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) :
    ‖twistedBufferedTranslationQuotientPhase M Ψ D₀ T g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact twistedBufferedTranslationPhase_norm_le_one M Ψ D₀ T hT

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedTranslationIncrement
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {m : ℕ}

theorem translation_cutoff_increment_bound (Ψ : PatchKernel m)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {ε : ℝ} (hε : 0 ≤ ε) (hbase : ∀ i, |z.base i| ≤ ε) :
    |Ψ.value (fun i => (z * g).base i - (β i : ℝ)) -
      Ψ.value (fun i => g.base i - (β i : ℝ))| ≤ Ψ.lip * ε := by
  have hdist : dist (fun i => (z * g).base i - (β i : ℝ))
      (fun i => g.base i - (β i : ℝ)) ≤ ε := by
    apply (dist_pi_le_iff hε).mpr
    intro i
    simp only [Real.dist_eq, PolynomialTranslationGroupOver.base_mul, Pi.add_apply]
    rw [show z.base i + g.base i - (β i : ℝ) - (g.base i - (β i : ℝ)) = z.base i by ring]
    exact hbase i
  exact (Ψ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hdist Ψ.lip.coe_nonneg)

theorem bufferedTranslationTerm_increment_bound (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {d : ℕ} {M ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (heval : ∀ x : Fin m → ℝ, (∀ i, |x i| ≤ 1) → |eval x z.polynomial| ≤ ε) :
    ‖bufferedTranslationTerm Ψ D₀ (z * g) β - bufferedTranslationTerm Ψ D₀ g β‖ ≤
      (Ψ.lip + (2 * Real.pi) * (1 + M * m * d)) * ε := by
  let a := Ψ.value (fun i => (z * g).base i - (β i : ℝ))
  let b := Ψ.value (fun i => g.base i - (β i : ℝ))
  let v : ℂ := Real.fourierChar (translationPhaseArgument D₀ (z * g) (fun i => (β i : ℝ)))
  let u : ℂ := Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ)))
  have hv : ‖v‖ = 1 := Circle.norm_coe _
  have hdiff : |a - b| ≤ Ψ.lip * ε := translation_cutoff_increment_bound Ψ z g β hε hbase
  have hM : 0 ≤ M := (realPolynomialMass_nonneg D₀).trans hD
  change ‖(a : ℂ) * v - (b : ℂ) * u‖ ≤ _
  by_cases hb : b = 0
  · rw [hb, Complex.ofReal_zero, zero_mul, sub_zero, norm_mul, hv, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have ha : |a| ≤ Ψ.lip * ε := by simpa only [hb, sub_zero] using hdiff
    apply ha.trans
    have hn : 0 ≤ (2 * Real.pi) * (1 + M * m * d) := by positivity
    nlinarith
  · have hres (i : Fin m) : |(β i : ℝ) - g.base i| ≤ 1 / 4 := by
      rw [abs_sub_comm]
      exact Ψ.support _ hb i
    have he : |eval ((fun i => (β i : ℝ)) - g.base) z.polynomial| ≤ ε :=
      heval _ (fun i => (hres i).trans (by norm_num))
    have hc : ‖v - u‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      simpa only [Fintype.card_fin] using
        translationPhaseCharacter_left_increment_quarter_point_bound D₀ z g
          (fun i => (β i : ℝ)) hε hεsmall hdegree hD hres hbase he
    have hid : (a : ℂ) * v - (b : ℂ) * u = ((a - b : ℝ) : ℂ) * v + (b : ℂ) * (v - u) := by
      push_cast
      ring
    rw [hid]
    have h1 : ‖((a - b : ℝ) : ℂ) * v‖ ≤ Ψ.lip * ε := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one] using hdiff
    have h2 : ‖(b : ℂ) * (v - u)‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Ψ.le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hc)
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def translationDisplacementNN : ℝ≥0 :=
  ⟨weightedTranslationDisplacementConstant d m (Fintype.card (WeightedBasisIndex w d)),
    (weightedTranslationDisplacementConstant_pos _ _ _).le⟩

noncomputable def bufferedTranslationTermLip (Ψ : PatchKernel m) (M : ℝ≥0) : ℝ≥0 :=
  let C := translationDisplacementNN w d
  max (8 * C) ((Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C)

theorem bufferedTranslationTerm_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let L : ℝ≥0 := (Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  have heq : bufferedTranslationTermLip w d Ψ M = max (2 * (4 * C)) L := by
    dsimp [bufferedTranslationTermLip, L]
    congr 1
    ring
  rw [heq]
  apply lipschitzWith_of_complex_unit_near _ (4 * C) L
  · intro g
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hsmall : (C : ℝ) * dist x y ≤ 1 / 4 := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat] at hnear
      linarith
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      nlinarith
    have hnearz' : dist 1 z ≤ 1 / weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)) := hnearz
    have hb := bchRealTranslation_bounds_near_one w d hw hd hwd z
      (by simpa only [Fintype.card_fin] using hnearz')
    simp only [Fintype.card_fin] at hb
    change (∀ i, |(bchRealTranslationHom w d hwd z).base i| ≤ (C : ℝ) * dist 1 z) ∧
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        |eval a (bchRealTranslationHom w d hwd z).polynomial| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    have h := bufferedTranslationTerm_increment_bound Ψ D₀
      (bchRealTranslationHom w d hwd z) (bchRealTranslationHom w d hwd y) β
      (mul_nonneg hC.le dist_nonneg) hsmall hdegree hD hb.1 hb.2
    rw [← map_mul, hz] at h
    change _ ≤ ((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
      (C : ℝ) * dist x y
    simpa only [mul_assoc] using h

theorem bufferedTranslationPhase_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β)
    (fun β => bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD β)
    (fun g β γ => bufferedTranslationTerm_unique Ψ D₀ (bchRealTranslationHom w d hwd g) β γ)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

theorem complex_mul_sub_mul_le_unit (a b c e : ℂ)
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b - c * e‖ ≤ ‖a - c‖ + ‖b - e‖ := by
  rw [show a * b - c * e = (a - c) * b + c * (b - e) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg (a - c)))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (b - e)))

namespace PolynomialTranslationLie

open _root_.MvPolynomial NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def twistedBufferedTranslationTermLip (Ψ : PatchKernel m) (A K : ℝ≥0) : ℝ≥0 :=
  max (2 * translationDisplacementNN w d)
    (bufferedTranslationTermLip w d Ψ A + K * translationDisplacementNN w d)

theorem twistedBufferedTranslationTerm_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let B := bufferedTranslationTermLip w d Ψ A
  let ρ := bchRealTranslationHom w d hwd
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  apply lipschitzWith_of_complex_unit_near _ C (B + K * C)
  · intro g
    exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT (ρ g) β
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      simpa only [mul_comm] using hnear.le
    have hbounds := bchRealTranslation_bounds_near_one w d hw hd hwd z
    simp only [Fintype.card_fin] at hbounds
    have hb := (hbounds hnearz).1
    change ∀ i, |(ρ z).base i| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    let rx := fun i => (ρ x).base i - (β i : ℝ)
    let ry := fun i => (ρ y).base i - (β i : ℝ)
    have hres : dist rx ry ≤ (C : ℝ) * dist x y := by
      apply (dist_pi_le_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mpr
      intro i
      have hbase : (ρ x).base i = (ρ z).base i + (ρ y).base i := by
        rw [← hz, map_mul]
        rfl
      dsimp [rx, ry]
      rw [Real.dist_eq, hbase]
      rw [show (ρ z).base i + (ρ y).base i - (β i : ℝ) -
        ((ρ y).base i - (β i : ℝ)) = (ρ z).base i by ring]
      exact hb i
    have hmult : ‖T rx (fun i => (β i : ZMod M)) - T ry (fun i => (β i : ZMod M))‖ ≤
        (K : ℝ) * ((C : ℝ) * dist x y) := by
      simpa only [dist_eq_norm] using
        ((hLip (fun i => (β i : ZMod M))).dist_le_mul rx ry).trans
          (mul_le_mul_of_nonneg_left hres K.coe_nonneg)
    have hphase : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β -
        bufferedTranslationTerm Ψ D₀ (ρ y) β‖ ≤ (B : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using
        (bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ A hdegree hD β).dist_le_mul x y
    have hbx : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β‖ ≤ 1 := by
      simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact Ψ.le_one _
    have hmul := complex_mul_sub_mul_le_unit
      (T rx (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ x) β)
      (T ry (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ y) β)
      hbx (hT _ _)
    apply hmul.trans
    apply (add_le_add hmult hphase).trans_eq
    simp only [NNReal.coe_add, NNReal.coe_mul]
    ring

theorem twistedBufferedTranslationPhase_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β)
    (fun β => twistedBufferedTranslationTerm_lipschitz w d hw hd hwd M Ψ D₀ A K
      hdegree hD T hT hLip β)
    (fun g β γ => twistedBufferedTranslationTerm_unique M Ψ D₀ T
      (bchRealTranslationHom w d hwd g) β γ)

end PolynomialTranslationLie

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolFactorizationTransport
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem SymbolFactorizationIn.dilate_ratio
    {S T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {D : ℕ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF S X p D U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.SymbolFactorizationIn b ω hF T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * q) (D * d ^ s) U := by
  have hr : (a : ℚ) / d ≠ 0 := div_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hd.ne')
  let φ := F.realPolynomialSymbolDilationHom (fun _ : σ => 1) ((a : ℚ) / d)
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  refine ⟨φ E, φ P, φ R, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg φ hprod
  · exact F.symbolSlowBound_dilation_physical b ω hF S T hS hT p q hq _ hr hphysical E hE
  · exact F.symbolRationalGrid_dilation_ratio b ω hF (fun _ => 1) D d a hd R hR
  · exact F.realSymbolDilation_mem_pointwise b ω hF (fun _ => 1) U _ P.coord hP

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev SquarefreeBasisIndex := Σ a : SquarefreeIndex (ReplicatedIndex bound),
  Fin (finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

noncomputable def squarefreeBasis (p : ℝ) : Basis M.SquarefreeBasisIndex ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p)

theorem squarefreeBasisIndex_card_le (p : ℝ) :
    Fintype.card M.SquarefreeBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.squarefreeBasis p)]
  simpa only [replicatedIndex_card, finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.squarefreeAlgebra_finrank_le (fun j : ReplicatedIndex bound => j.1)

theorem squarefreeCoefficientBasis_card_le (a : SquarefreeIndex (ReplicatedIndex bound)) :
    finrank ℚ (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a).finrank_le

theorem squarefreeBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.SquarefreeBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.squarefreeBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.squarefreeBasis_structure_height
    (fun j : ReplicatedIndex bound => j.1) (M.squarefreeCoefficientBasis p) D.basis
    (one_le_ceil_exp p) (M.squarefreeCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.squarefreeCoefficientBasis_card_le a) i j k
  simp only [Fintype.card_fin] at h
  exact h

theorem squarefreeBasis_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (j : M.SquarefreeBasisIndex) :
    ∃ k, M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he
      (M.squarefreeBasis p j) = M.squarefreeBasis p k := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact M.filtration.squarefreeBasis_permute (fun j : ReplicatedIndex bound => j.1)
    (chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊) e he j

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLayerBasis (p : ℝ) (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem comparisonLayerBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≤ bound) (j k) :
    RationalHeightLE (D.basis.repr (M.comparisonLayerBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  apply chosenBoundedSubmoduleBasis_height
  obtain ⟨b, hb⟩ := M.exists_layer_basis a ha hM
  exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeSquarefreeGrids
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeGrid_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    {x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hx : x ∈ coordinateGridModule (M.squarefreeBasis p) B) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B :=
  coordinateGridModule_map_of_basis (M.squarefreeBasis p) (M.squarefreeBasis p)
    (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLinearEquiv.toLinearMap
    (M.squarefreeBasis_permute p e he) B hx

theorem squarefreeGrid_permute_iff (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    (x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B ↔ x ∈ coordinateGridModule (M.squarefreeBasis p) B := by
  constructor
  · intro hx
    have h := M.squarefreeGrid_permute p e.symm
      (MultidegreeLieFiltration.blockPermutation_symm _ e he) B hx
    have heq : M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e.symm
        (MultidegreeLieFiltration.blockPermutation_symm _ e he)
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x) = x :=
      Subtype.ext (squarefreePermute_symm_apply e x.val)
    rwa [heq] at h
  · exact M.squarefreeGrid_permute p e he B

theorem exists_squarefree_stable_grid {p : ℝ} (hM : M.ComplexityLE p) (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound (Fintype.card (ReplicatedIndex bound)) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.SquarefreeBasisIndex ^ 3) * l ∧
      ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
        ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
          lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B :=
  exists_bch_stable_integral_grid (M.squarefreeBasis p)
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    l hl (M.squarefreeBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeSquarefreeLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def SquarefreeGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
    ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
      lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B

noncomputable def squarefreeLattice (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    Subgroup (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group :=
  coordinateGridBCHSubgroup (M.squarefreeBasis p) B
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    hstable

theorem squarefreeLattice_coordinates (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    bchSubgroupCoordinates (M.squarefreeBasis p) (M.squarefreeLattice p B hstable) = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates _ _ _ hstable

theorem squarefreeLattice_permute (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B)
    (e : Equiv.Perm (ReplicatedIndex bound)) (he : ∀ j, (e j).1 = j.1)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group) :
    NilpotentLieBCHGroup.map
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLieHom g ∈
        M.squarefreeLattice p B hstable ↔ g ∈ M.squarefreeLattice p B hstable :=
  M.squarefreeGrid_permute_iff p e he B g.coord

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraph (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] (L × F.SquarefreeAlgebra π) :=
  (F.layer a).subtype.prod (F.blockLayerMap π a ha)

theorem comparisonGraph_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a)
    (n : ℕ) (hn : n ≤ ∑ i, a i) :
    F.comparisonGraph π a ha x ∈ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) :=
  ⟨F.ordinary.antitone hn (F.layer_le_ordinary a x.property),
    F.squarefreeDegreeLayer_antitone π hn (F.blockLayerMap_mem_degree π a ha x)⟩

theorem comparisonGraph_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.comparisonGraph π a ha x, F.comparisonGraph π b hb y⁆ =
      F.comparisonGraph π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ :=
  Prod.ext rfl (F.blockLayerMap_lie π a b ha hb hab x y)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) := by
  classical
  exact ⨆ a : {a : σ → ℕ // a ≠ 0},
    if n ≤ ∑ i, a.val i then LinearMap.range (F.comparisonGraph π a.val a.property) else ⊥

theorem comparisonGraph_mem_graphLayer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonGraphLayer π n := by
  classical
  have hle : LinearMap.range (F.comparisonGraph π a ha) ≤ F.comparisonGraphLayer π n := by
    unfold comparisonGraphLayer
    apply le_iSup_of_le (⟨a, ha⟩ : {a : σ → ℕ // a ≠ 0})
    rw [if_pos hn]
  exact hle ⟨x, rfl⟩

theorem comparisonGraphLayer_induction (n : ℕ) {P : L × F.SquarefreeAlgebra π → Prop}
    {x : L × F.SquarefreeAlgebra π} (hx : x ∈ F.comparisonGraphLayer π n)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), n ≤ ∑ i, a i →
      ∀ y : F.layer a, P (F.comparisonGraph π a ha y))
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
  classical
  refine Submodule.iSup_induction (motive := P) _ hx ?_ hzero hadd
  intro a y hy
  by_cases hn : n ≤ ∑ i, a.val i
  · rw [if_pos hn] at hy
    obtain ⟨z, rfl⟩ := hy
    exact hgraph a.val a.property hn z
  · rw [if_neg hn, Submodule.mem_bot] at hy
    simpa only [hy] using hzero

theorem comparisonGraphLayer_antitone : Antitone (F.comparisonGraphLayer π) := by
  intro n m hnm x hx
  apply F.comparisonGraphLayer_induction π m hx
  · intro a ha hm y
    exact F.comparisonGraph_mem_graphLayer π n a ha (hnm.trans hm) y
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

theorem comparisonGraphLayer_le_degree (n : ℕ) :
    F.comparisonGraphLayer π n ≤ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) := by
  intro x hx
  apply F.comparisonGraphLayer_induction π n hx
  · intro a ha hn y
    exact F.comparisonGraph_mem_degree π a ha y n hn
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  F.comparisonProductLayer π (n + 1) ⊔ F.comparisonGraphLayer π n

theorem comparisonLayer_antitone : Antitone (F.comparisonLayer π) := by
  intro n m h
  exact sup_le_sup (F.comparisonProductLayer_antitone π (Nat.add_le_add_right h 1))
    (F.comparisonGraphLayer_antitone π h)

theorem comparisonLayer_le_product (n : ℕ) :
    F.comparisonLayer π n ≤ F.comparisonProductLayer π n :=
  sup_le (F.comparisonProductLayer_antitone π (Nat.le_succ n)) (F.comparisonGraphLayer_le_degree π n)

theorem comparisonLayer_terminal : F.comparisonLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  apply bot_unique
  exact (F.comparisonLayer_le_product π _).trans (F.comparisonProductLayer_terminal π).le

theorem comparisonGraph_mem_layer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonLayer π n :=
  (le_sup_right : F.comparisonGraphLayer π n ≤ F.comparisonLayer π n)
    (F.comparisonGraph_mem_graphLayer π n a ha hn x)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem map_mem_submodule_of_basis {κ V W : Type*} [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis κ ℚ V) (f : V →ₗ[ℚ] W) (P : Submodule ℚ W)
    (h : ∀ i, f (b i) ∈ P) (x : V) : f x ∈ P := by
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact P.smul_mem _ (h i)

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonLayer_le_of_generators (n : ℕ) (P : Submodule ℚ (L × F.SquarefreeAlgebra π))
    (hfirst : ∀ x ∈ F.ordinary.layer (n + 1), (x, 0) ∈ P)
    (hsecond : ∀ y ∈ F.squarefreeDegreeLayer π (n + 1), (0, y) ∈ P)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), a ≤ bound → n ≤ ∑ i, a i →
      ∀ x : F.layer a, F.comparisonGraph π a ha x ∈ P) :
    F.comparisonLayer π n ≤ P := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  apply P.add_mem
  · simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      P.add_mem (hfirst u.1 hu.1) (hsecond u.2 hu.2)
  · refine F.comparisonGraphLayer_induction π n (P := fun v => v ∈ P) hv ?_ P.zero_mem ?_
    · intro a ha hn x
      by_cases hab : a ≤ bound
      · exact hgraph a ha hab hn x
      · have hx : x = 0 := by
          apply Subtype.ext
          exact (Submodule.mem_bot ℚ).mp (F.terminal a hab ▸ x.property)
        rw [hx, map_zero]
        exact P.zero_mem
    · exact fun x y hx hy => P.add_mem hx hy

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeFinBasis (p : ℝ) : Basis (Fin (Fintype.card M.SquarefreeBasisIndex)) ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  (M.squarefreeBasis p).reindex (Fintype.equivFin M.SquarefreeBasisIndex)

theorem squarefreeFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.squarefreeFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, lieStructureConstants_reindex]
  exact M.squarefreeBasis_structure_height hM _ _ _

theorem squarefreeFinBasis_multidegree_height (p : ℝ) (c : ReplicatedIndex bound → ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) c j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeMultidegreeBasis_height _ (M.squarefreeCoefficientBasis p) c j _

theorem squarefreeFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) n j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeDegreeBasis_height _ (M.squarefreeCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem blockLayerMap_chosen_height (p : ℝ) (a : σ → ℕ) (ha : a ≠ 0)
    (j : Fin (finrank ℚ (M.filtration.layer a))) (k : M.SquarefreeBasisIndex) :
    RationalHeightLE ((M.squarefreeBasis p).repr
      (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (multidegreeFactorial a) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let π := fun i : ReplicatedIndex bound => i.1
  let v := M.filtration.squarefreeAlgebraEquiv π
    (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)) k.1
  change RationalHeightLE
    ((chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊
      (M.filtration.squarefreeCoefficientLayer π k.1)).repr v k.2) _
  by_cases hka : blockDegree π k.1.val = a
  · have hk : k.1.val ≠ 0 := by
      intro h
      apply ha
      rw [h, blockDegree_zero] at hka
      exact hka.symm
    have hUV : M.filtration.layer a = M.filtration.squarefreeCoefficientLayer π k.1 := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, if_neg hk, hka]
    have hq : RationalHeightLE (multidegreeFactorial a : ℚ) (multidegreeFactorial a) := by
      constructor
      · simp
      · simpa using Nat.succ_le_of_lt (multidegreeFactorial_pos a)
    apply chosenBasis_smul_coordinate_height D.basis ⌈Real.exp p⌉₊
      (M.filtration.layer a) (M.filtration.squarefreeCoefficientLayer π k.1)
      hUV j v (multidegreeFactorial a) hq
    change squarefreePolynomialEquiv
      (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = _
    rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, if_pos hka]
    rfl
  · have hv : v = 0 := by
      apply Subtype.ext
      change squarefreePolynomialEquiv
        (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = 0
      rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, if_neg hka]
    rw [hv, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (multidegreeFactorial_pos a)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonGraph_chosen_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≠ 0) (hab : a ≤ bound)
    (j : Fin (finrank ℚ (M.filtration.layer a)))
    (k : Fin d ⊕ Fin (Fintype.card M.SquarefreeBasisIndex)) :
    RationalHeightLE ((D.basis.prod (M.squarefreeFinBasis p)).repr
      (M.filtration.comparisonGraph (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (comparisonBasisHeight bound p) := by
  cases k with
  | inl k =>
      exact (M.comparisonLayerBasis_height hM a hab j k).mono
        (comparisonBasisHeight_ge_ceil bound p)
  | inr k =>
      change RationalHeightLE ((M.squarefreeFinBasis p).repr
        (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
          (M.comparisonLayerBasis p a j)) k) _
      rw [squarefreeFinBasis, Basis.repr_reindex_apply]
      exact (M.blockLayerMap_chosen_height p a ha j _).mono
        ((multidegreeFactorial_mono hab).trans (comparisonBasisHeight_ge_factorial bound p))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeModel (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) :
    RationalFilteredNilmanifold (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      (Fintype.card (ReplicatedIndex bound)) (Fintype.card M.SquarefreeBasisIndex) where
  filtration := M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)
  basis := M.squarefreeFinBasis p
  layerBasis i := M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (i.val + 1)
  lattice := M.squarefreeLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.squarefreeLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.squarefreeLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def squarefreeModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    (M.squarefreeModel p B hB hstable).MultidegreeStructure (fun _ : ReplicatedIndex bound => 1) where
  filtration := M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)
  ordinary := rfl
  basis a := M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (fun j => (a j).val)

theorem squarefreeModel_complexity {p q : ℝ} (hM : M.ComplexityLE p) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hq : 0 ≤ q)
    (hd : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ q) (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp_iff.mpr hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.squarefreeFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis_height {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, RationalHeightLE
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k)
        (comparisonBasisHeight bound p) := by
  classical
  let π := fun i : ReplicatedIndex bound => i.1
  let A := M.filtration.SquarefreeAlgebra π
  let e := D.basis.prod (M.squarefreeFinBasis p)
  let U := M.filtration.comparisonLayer π n
  let S : Set (L × A) := {z | z ∈ U ∧ ∀ k,
    RationalHeightLE (e.repr z k) (comparisonBasisHeight bound p)}
  have hpos := comparisonBasisHeight_pos bound p
  have hspan : Submodule.span ℚ S = U := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun z hz => hz.1)
    · apply M.filtration.comparisonLayer_le_of_generators π n
      · intro x hx
        obtain ⟨b, hb⟩ : ∃ b : Basis
            (Fin (finrank ℚ (M.filtration.ordinary.layer (n + 1)))) ℚ
            (M.filtration.ordinary.layer (n + 1)),
            ∀ j k, rationalLogHeight (D.basis.repr (b j).val k) ≤ p := by
          rw [M.ordinary]
          exact D.exists_positive_layer_basis (n + 1) (by omega) hM.1
        let f := (LinearMap.inl ℚ L A).comp (M.filtration.ordinary.layer (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨x, hx⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨(b j).property, Submodule.zero_mem _⟩
        · intro k
          cases k with
          | inl k =>
              exact (rationalHeightLE_ceil_exp (hb j k)).mono
                (comparisonBasisHeight_ge_ceil bound p)
          | inr k =>
              change RationalHeightLE ((M.squarefreeFinBasis p).repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
      · intro y hy
        let b := M.filtration.squarefreeDegreeBasis π (M.squarefreeCoefficientBasis p) (n + 1)
        let f := (LinearMap.inr ℚ L A).comp (M.filtration.squarefreeDegreeLayer π (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨y, hy⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨Submodule.zero_mem _, (b j).property⟩
        · intro k
          cases k with
          | inl k =>
              change RationalHeightLE (D.basis.repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
          | inr k =>
              exact (M.squarefreeFinBasis_degree_height p (n + 1) j k).mono hpos
      · intro a ha hab hn x
        apply map_mem_submodule_of_basis (M.comparisonLayerBasis p a)
          (M.filtration.comparisonGraph π a ha) (Submodule.span ℚ S) _ x
        intro j
        exact Submodule.subset_span
          ⟨M.filtration.comparisonGraph_mem_layer π n a ha hn _,
            M.comparisonGraph_chosen_height hM a ha hab j⟩
  have hrange : Set.range (Subtype.val : S → L × A) = S := by
    ext z
    simp only [Subtype.range_coe_subtype, Set.mem_ofPred_eq]
  exact exists_bounded_submodule_basis_from_spanning e U
    (Subtype.val : S → L × A) (by rw [hrange]; exact hspan) (fun z => z.property.2)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeRealPermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).RealGroup →*
      (M.squarefreeModel p B hB hstable).RealGroup :=
  realificationMap
    (hnil := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (M.filtration.replicatedLiePermute e).toLieHom

theorem squarefreeRealPermute_one (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable 1 g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self _ M.filtration.replicatedLiePermute_one g.coord

theorem squarefreeRealPermute_mul (e f : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable (e * f) g =
      M.squarefreeRealPermute p B hB hstable e (M.squarefreeRealPermute p B hB hstable f g) := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_comp_apply _ _ _ (M.filtration.replicatedLiePermute_mul e f) g.coord

theorem squarefreeRealPermute_lattice (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).realLattice ≤
      (M.squarefreeModel p B hB hstable).realLattice.comap
        (M.squarefreeRealPermute p B hB hstable e) := by
  apply realificationMap_subgroup
  intro g hg
  exact (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) g).mpr hg

theorem squarefreeRealPermute_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) :
    M.squarefreeRealPermute p B hB hstable e g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self_on _ _
    (M.filtration.replicatedLiePermute_ordinary_top e) g.coord hg

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeQuotientAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeSpacePermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap _ _ (M.squarefreeRealPermute p B hB hstable e)
    (M.squarefreeRealPermute_lattice p B hB hstable e)

theorem squarefreeSpacePermute_mk (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeSpacePermute p B hB hstable e (QuotientGroup.mk g) =
      QuotientGroup.mk (M.squarefreeRealPermute p B hB hstable e g) := rfl

theorem squarefreeSpacePermute_one (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable 1 x = x := by
  induction x using Quotient.inductionOn with
  | h g => rw [M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_one]

theorem squarefreeSpacePermute_mul (e f : ReplicatedPermutation bound)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable (e * f) x =
      M.squarefreeSpacePermute p B hB hstable e (M.squarefreeSpacePermute p B hB hstable f x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [M.squarefreeSpacePermute_mk, M.squarefreeSpacePermute_mk,
      M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_mul]

@[instance_reducible]
noncomputable def squarefreeSpaceAction :
    MulAction (ReplicatedPermutation bound) (M.squarefreeModel p B hB hstable).Space where
  smul := M.squarefreeSpacePermute p B hB hstable
  one_smul := M.squarefreeSpacePermute_one p B hB hstable
  mul_smul := M.squarefreeSpacePermute_mul p B hB hstable

theorem squarefreeSpacePermute_smul (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      M.squarefreeRealPermute p B hB hstable e g • M.squarefreeSpacePermute p B hB hstable e x :=
  cosetMap_smul _ _ _ _ _ _

theorem squarefreeSpacePermute_commutes_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      g • M.squarefreeSpacePermute p B hB hstable e x := by
  rw [M.squarefreeSpacePermute_smul, M.squarefreeRealPermute_top p B hB hstable e g hg]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationResidueNilmanifold
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationResidueNilmanifold (M : ℕ) (hM : 0 < M) :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationResidueLattice w d hw hwd M
  grid := d.factorial * M
  grid_pos := Nat.mul_pos (Nat.factorial_pos d) hM
  inner_grid := weightedTranslationResidueLattice_inner_grid w d hw hwd M
  outer_grid := weightedTranslationResidueLattice_outer_grid w d hw hwd M

theorem weightedTranslationResidueNilmanifold_complexity_add_log
    (M : ℕ) (hM : 0 < M) {p : ℝ}
    (hG : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
      (p + Real.log (M : ℝ)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hM))
  have hp : p ≤ p + Real.log (M : ℝ) := le_add_of_nonneg_right hlog
  obtain ⟨hdim, hgrid, hstructure, hlayer⟩ := hG
  refine ⟨hdim.trans hp, ?_, fun i j k => (hstructure i j k).trans hp,
    fun i j k => (hlayer i j k).trans hp⟩
  change ((d.factorial * M : ℕ) : ℝ) ≤ Real.exp (p + Real.log (M : ℝ))
  rw [Nat.cast_mul, Real.exp_add, Real.exp_log hMr]
  exact mul_le_mul_of_nonneg_right hgrid hMr.le

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedTranslationResiduePhase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_rational_residue
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (r : (weightedFiltration w d hwd).Group)
    (hr : bchTranslationHom w d hw hwd r ∈
      (integerTranslationResidueSubgroup M).map PolynomialTranslationGroup.fromInteger) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom r) ∈
      integerPolynomialTranslationResidueCover M := by
  obtain ⟨z, hz, he⟩ := hr
  refine ⟨z, hz, ?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← he]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

theorem realResidueLattice_translation_residue_map
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationResidueLattice w d hw hwd M).map
      NilpotentLieBCHGroup.realificationHom) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationResidueCover M := by
  obtain ⟨r, hr, rfl⟩ := hg
  exact bchRealTranslationHom_rational_residue w d hw hwd M r hr

noncomputable def weightedTranslationResidueQuotientMap
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    ((weightedFiltration w d hwd).realification.Group ⧸
      (weightedTranslationResidueLattice w d hw hwd M).map NilpotentLieBCHGroup.realificationHom) →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realResidueLattice_translation_residue_map w d hw hwd M
      (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul, map_inv] using h)

@[simp] theorem weightedTranslationResidueQuotientMap_mk
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResidueQuotientMap w d hw hwd M (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

section Nilmanifold

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

noncomputable def weightedTranslationResiduePhaseQuotientMap :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  weightedTranslationResidueQuotientMap w d hw hwd M

@[simp] theorem weightedTranslationResiduePhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

end Nilmanifold

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedTwistedTranslationBudget
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_weightedTranslationBuffered_scalar_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n N : ℕ) (p L M : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → N ≤ n + (n + 1) ^ d →
      0 ≤ L → 0 ≤ M → L ≤ Real.exp p → M ≤ Real.exp p →
      ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ (p + C) ^ C ∧
      2 * max (8 * weightedTranslationDisplacementConstant d n N)
        ((L + 2 * Real.pi * (1 + M * n * d)) *
          weightedTranslationDisplacementConstant d n N) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨Z, hZ, hlog⟩ := exists_bchLogMetricConstant_exp_bound d
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 1) ^ d + Polynomial.C (d.factorial + 2 * d + 1)
  let K := Polynomial.C d *
    (1 + (X + 1) * (Polynomial.C (d + 1) * (X + 2) ^ d) * Polynomial.C d) ^ d
  let P := Q + K + (Q + Polynomial.C Z) ^ Z + 3 * X + Polynomial.C (d + 15)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro n N p L M hp hn hN hL hM hLp hMp
  let q : ℝ := p + (p + 1) ^ d + (d.factorial + 2 * d + 1 : ℕ)
  let k : ℝ := d * (1 + (p + 1) * (((d : ℝ) + 1) * (p + 2) ^ d) * d) ^ d
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have htotal : q + k + (q + Z) ^ Z + 3 * p + (d + 15 : ℕ) ≤ (p + C) ^ C := by
    simpa [X, Q, K, P, q, k, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbudget p hp
  have hgeom : ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ q := by
    have hpow : ((n : ℝ) + 1) ^ d ≤ (p + 1) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    dsimp [q]
    push_cast
    linarith
  have hdim : (N : ℝ) ≤ q := by
    apply (Nat.cast_le.mpr hN).trans
    have hh : ((n + (n + 1) ^ d : ℕ) : ℝ) ≤
        ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + (n + 1)^d ≤ n + (n+1)^d + d.factorial + 2*d + 1)
    exact hh.trans hgeom
  have hHq : ((2 * d + 1 : ℕ) : ℝ) ≤ q := by
    dsimp [q]
    have hd0 := Nat.cast_nonneg (α := ℝ) d.factorial
    have hpow : 0 ≤ (p + 1) ^ d := by positivity
    push_cast
    linarith
  have hHexp : ((2 * d + 1 : ℕ) : ℝ) ≤ Real.exp q :=
    hHq.trans (by linarith [Real.add_one_le_exp q])
  have hlogbound := hlog N (2 * d + 1) q hq hdim hHexp
  have hshear : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) ≤ k := by
    dsimp [polynomialShearDisplacementBound, k]
    push_cast
    simp only [one_pow, mul_one]
    simp only [add_assoc, one_add_one_eq_two]
    gcongr
  have hshear1 : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) + 1 ≤ Real.exp k := by
    linarith [Real.add_one_le_exp k]
  have hv : 0 ≤ (q + Z) ^ Z + 1 := by positivity
  have hlog1 : (bchLogMetricConstant d N (2 * d + 1) 1 : ℝ) + 1 ≤
      Real.exp ((q + Z) ^ Z + 2) := by
    have hh := one_add_le_exp_succ hv hlogbound
    simpa only [add_comm (1 : ℝ), add_assoc, one_add_one_eq_two] using hh
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hdisp : weightedTranslationDisplacementConstant d n N ≤
      Real.exp (k + (q + Z) ^ Z + 3) := by
    unfold weightedTranslationDisplacementConstant
    calc
      _ ≤ Real.exp 1 * Real.exp k * Real.exp ((q + Z) ^ Z + 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hprod : M * (n : ℝ) * d ≤ Real.exp (2 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod1 : 1 + M * (n : ℝ) * d ≤ Real.exp (2 * p + d + 1) :=
    one_add_le_exp_succ (by positivity) hprod
  have hpi : 2 * Real.pi ≤ Real.exp 8 := by
    have hp4 := Real.pi_le_four
    linarith [Real.add_one_le_exp (8 : ℝ)]
  have hphase : 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (2 * p + d + 9) := by
    calc
      _ ≤ Real.exp 8 * Real.exp (2 * p + d + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : L + 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (3 * p + d + 10) := by
    have hh := add_le_exp_add_one hp (by positivity : 0 ≤ 2 * p + d + 9) hLp hphase
    convert hh using 1; congr 1; ring
  have height : (8 : ℝ) ≤ Real.exp (3 * p + d + 10) := by
    have hh := Real.add_one_le_exp (3 * p + d + 10)
    have hd0 := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hmax : max (8 * weightedTranslationDisplacementConstant d n N)
      ((L + 2 * Real.pi * (1 + M * n * d)) * weightedTranslationDisplacementConstant d n N) ≤
        Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3) := by
    apply max_le
    · exact mul_le_mul height hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
    · exact mul_le_mul hsum hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
  constructor
  · apply hgeom.trans
    have hz : 0 ≤ (q + Z) ^ Z := by positivity
    have hd0 := Nat.cast_nonneg (α := ℝ) (d + 15)
    linarith
  · calc
      _ ≤ 2 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ ≤ Real.exp 1 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (k + (q + Z) ^ Z + 3 * p + d + 14) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((p + C) ^ C) := by
        apply Real.exp_le_exp.mpr
        push_cast at htotal
        linarith

theorem exists_weightedTranslationBuffered_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (Ψ : PatchKernel m) (M : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (Ψ.lip : ℝ) ≤ Real.exp p → (M : ℝ) ≤ Real.exp p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE ((p + C) ^ C) ∧
      ((2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedTranslationBuffered_scalar_budget d
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ Ψ M p hp hm hΨ hM
  have hcard : Fintype.card (WeightedBasisIndex w d) ≤ m + (m + 1) ^ d := by
    simpa only [Fintype.card_fin] using weightedBasisIndex_card_le w d hw
  obtain ⟨hgeometry, hlip⟩ := hbound m (Fintype.card (WeightedBasisIndex w d)) p
    Ψ.lip M hp hm hcard Ψ.lip.coe_nonneg M.coe_nonneg hΨ hM
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationNilmanifold w d hw hwd)
      (weightedTranslationNilmanifold_complexity_budget w d hw hwd)
    simpa only [Fintype.card_fin] using hgeometry
  · change 2 * max (8 * weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)))
      (((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
        weightedTranslationDisplacementConstant d m
          (Fintype.card (WeightedBasisIndex w d))) ≤ _
    exact hlip

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal TensorProduct

theorem twistedBufferedTranslation_log_bound {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] (Ψ : PatchKernel m) (A K : ℝ≥0)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hB : ((2 * bufferedTranslationTermLip w d Ψ A : ℝ≥0) : ℝ) ≤ Real.exp r)
    (hK : (K : ℝ) ≤ Real.exp p) :
    Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
      p + r + 6 := by
  let B : ℝ := bufferedTranslationTermLip w d Ψ A
  let C : ℝ := translationDisplacementNN w d
  have hBn : 0 ≤ B := NNReal.coe_nonneg _
  have hCn : 0 ≤ C := NNReal.coe_nonneg _
  have hCB : C ≤ B := by
    have hh : 8 * C ≤ B := le_max_left _ _
    linarith
  change 2 * B ≤ Real.exp r at hB
  have hBe : B ≤ Real.exp r := by linarith
  have hCe : C ≤ Real.exp r := hCB.trans hBe
  have hBpr : B ≤ Real.exp (p + r) :=
    hBe.trans (Real.exp_le_exp.mpr (by linarith))
  have hCpr : C ≤ Real.exp (p + r) := hCB.trans hBpr
  have hKC : (K : ℝ) * C ≤ Real.exp (p + r) := by
    rw [Real.exp_add]
    exact mul_le_mul hK hCe hCn (Real.exp_nonneg _)
  have hmax : max (2 * C) (B + (K : ℝ) * C) ≤ 2 * Real.exp (p + r) := by
    exact max_le (by linarith) (by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hLip : ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ) ≤
      Real.exp (p + r + 3) := by
    change 2 * max (2 * C) (B + (K : ℝ) * C) ≤ _
    calc
      _ ≤ 4 * Real.exp (p + r) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + r) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + r + 3) := by
      linarith [Real.one_le_exp (show 0 ≤ p + r + 3 by linarith)]
    _ ≤ Real.exp 3 * Real.exp (p + r + 3) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_weightedTwistedTranslation_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m) (A K : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (M : ℝ) ≤ Real.exp p →
      (Ψ.lip : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p → (K : ℝ) ≤ Real.exp p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
        (p + C) ^ C := by
  obtain ⟨a, _, hbuffer⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + X + 6)
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ M hM Ψ A K p hp hm hMp hΨ hA hK
  obtain ⟨hG, hB⟩ := hbuffer w hw hwd Ψ A p hp hm hΨ hA
  have hbound : (p + a) ^ a + p + 6 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hlogM : Real.log (M : ℝ) ≤ p :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hM)).mpr hMp
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (weightedTranslationResidueNilmanifold_complexity_add_log w d hw hwd M hM hG)
    linarith
  · exact (twistedBufferedTranslation_log_bound w d Ψ A K hp (by positivity) hB hK).trans
      (by linarith)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_majorRationalLift_detection_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      (Ψ : PatchKernel m) (a : Fin m → ℤ) (p : ℝ),
      0 ≤ p → ((Fintype.card U + m : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d)
        (rationalLiftCharacterTwistLip M a) : ℝ≥0) : ℝ)) ≤ (p + C) ^ C := by
  obtain ⟨b, _, htwisted⟩ := exists_weightedTwistedTranslation_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ :=
    (Polynomial.C (d + 2) * (X + 1) + 8 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ M hM Ψ a p hp hdim hMexp hΨ ha
  let q : ℝ := majorRationalLiftInputScale d p
  have hq := majorRationalLiftInputScale_bounds d p hp
  have hmp : (m : ℝ) ≤ p := by
    have hsum : (m : ℝ) ≤ ((Fintype.card U + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hsum.trans hdim
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hB : (B : ℝ) ≤ Real.exp q :=
    majorRationalLiftInputScale_mass d p hp (Fintype.card U) m hdim
  have hK : (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp q := by
    apply (rationalLiftCharacterTwistLip_le_exp_of_dim M hM a p p hmp ha).trans
    apply Real.exp_le_exp.mpr
    change p + p + 8 ≤ majorRationalLiftInputScale d p
    linarith [hq.2.2]
  obtain ⟨hgeometry, hlog⟩ := htwisted w hw hwd M hM Ψ B
    (rationalLiftCharacterTwistLip M a) q hq.1 (hmp.trans hq.2.1)
    (hMexp.trans (Real.exp_le_exp.mpr hq.2.1))
    (hΨ.trans (Real.exp_le_exp.mpr hq.2.1)) hB hK
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, X, q, majorRationalLiftInputScale, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _ hgeometry hcost,
    hlog.trans hcost⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorCorrelationBudget
namespace OAI

section

namespace Erdos3

def translationMajorPairBudget (a : ℕ) (p : ℝ) : ℝ :=
  (raisedNiltestBudget p + (a : ℝ)) ^ a

theorem translationMajorPairBudget_controls (a : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : 2 ≤ a) :
    p ≤ raisedNiltestBudget p ∧
      raisedNiltestBudget p ≤ translationMajorPairBudget a p ∧
      2 ≤ translationMajorPairBudget a p := by
  have hq : (2 : ℝ) ≤ raisedNiltestBudget p := by
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (p + 2)]
  have hbase : (1 : ℝ) ≤ raisedNiltestBudget p + a := by
    linarith [Nat.cast_nonneg a (α := ℝ)]
  have hpow : raisedNiltestBudget p + a ≤ translationMajorPairBudget a p := by
    exact (pow_one (raisedNiltestBudget p + a)).symm.le.trans
      (pow_le_pow_right₀ hbase (by omega : 1 ≤ a))
  have hqr : raisedNiltestBudget p ≤ translationMajorPairBudget a p :=
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow
  exact ⟨le_raisedNiltestBudget p, hqr, hq.trans hqr⟩

theorem exists_translationMajorCorrelationBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      translationMajorPairBudget a p ≤ (p + C) ^ C ∧
        (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
  let R : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + 2) ^ 2 + 3 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : translationMajorPairBudget a p +
      (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
    simpa [R, translationMajorPairBudget, raisedNiltestBudget, Polynomial.eval₂_pow]
      using hbound p hp
  have hr : 0 ≤ translationMajorPairBudget a p := by
    unfold translationMajorPairBudget raisedNiltestBudget
    positivity
  have hproduct : 0 ≤ (translationMajorPairBudget a p + (b : ℝ)) ^ b := by positivity
  exact ⟨(le_add_of_nonneg_right hproduct).trans htotal,
    (le_add_of_nonneg_left hr).trans htotal⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedPatchKernel
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_unit_interval {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {L M : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hfI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hgI : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (L + M) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h₁ : dist (f x * g x) (f y * g x) ≤ dist (f x) (f y) := by
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (hgI x).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hgI x).2
  have h₂ : dist (f y * g x) (f y * g y) ≤ dist (g x) (g y) := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hfI y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hfI y).2
  exact (dist_triangle _ (f y * g x) _).trans
    ((add_le_add (h₁.trans (hf.dist_le_mul _ _)) (h₂.trans (hg.dist_le_mul _ _))).trans_eq
      (by simp [add_mul]))

namespace PatchKernel

variable {d : ℕ}

def weight (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : PatchKernel d where
  value x := Φ.value x * f x
  nonneg x := mul_nonneg (Φ.nonneg x) (hI x).1
  le_one x := (mul_le_of_le_one_left (hI x).1 (Φ.le_one x)).trans (hI x).2
  support x hx := Φ.support x (mul_ne_zero_iff.mp hx).1
  lip := Φ.lip + L
  lipschitz := lipschitz_mul_unit_interval Φ.lipschitz hf (fun x => ⟨Φ.nonneg x, Φ.le_one x⟩) hI

@[simp] theorem weight_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (Φ.weight f L hf hI).lip = Φ.lip + L := rfl

@[simp] theorem weight_value (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : Fin d → ℝ) :
    (Φ.weight f L hf hI).value x = Φ.value x * f x := rfl

def weightAlong {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) : PatchKernel d :=
  Φ.weight (fun x => Ψ.value (g x)) (Ψ.lip * K) (Ψ.lipschitz.comp hg)
    (fun x => ⟨Ψ.nonneg (g x), Ψ.le_one (g x)⟩)

@[simp] theorem weightAlong_lip {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) :
    (Φ.weightAlong Ψ g K hg).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem weightAlong_value {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
    (x : Fin d → ℝ) : (Φ.weightAlong Ψ g K hg).value x = Φ.value x * Ψ.value (g x) := rfl

end PatchKernel
end Erdos3

end

end OAI

end


