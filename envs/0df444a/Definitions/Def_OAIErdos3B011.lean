-- Prove2me | Definitions.Def_OAIErdos3B011
-- name    : OAIErdos3B011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:51:39.510127+00:00
-- url     : https://prove2.me/theorems/9c508c87-6fe4-4782-a97a-613a7388fb23
-- title:
--   OpenAI Erdős-3 split, definitions bundle 12 of 88
-- statement:
--   Definitions bundle 12 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B010`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 12 available.
--
--   Modules: `OAI.Erdos3.CircleFourier.IsometricCircleAction.Commutes`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.casesOn`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_character`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_equivariant`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_lipschitz`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_norm_le`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_preserves_character`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.component_sum`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.smooth`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.smooth_eq_sum`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.smooth_error`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.smooth_lipschitz`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.toAddAction`, `OAI.Erdos3.CircleFourier.IsometricCircleAction.toContinuousVAdd`, `OAI.Erdos3.CircleFourier.abs_lt_of_mem_fejerFrequencies`, `OAI.Erdos3.CircleFourier.card_fejerFrequencies_le`, `OAI.Erdos3.CircleFourier.circleAct_joint_lipschitz`, `OAI.Erdos3.CircleFourier.circleFejerSum`, `OAI.Erdos3.CircleFourier.circleFejerSum_approximation`, `OAI.Erdos3.CircleFourier.circleFejerSum_eq_average`, `OAI.Erdos3.CircleFourier.circleFourierComponent`, `OAI.Erdos3.CircleFourier.circleFourierComponent_vadd`, `OAI.Erdos3.CircleFourier.circle_integrable_of_continuous`, `OAI.Erdos3.CircleFourier.exists_fejer_cutoff`, `OAI.Erdos3.CircleFourier.fejerAverage`, `OAI.Erdos3.CircleFourier.fejerAverage_eq_sum`, `OAI.Erdos3.CircleFourier.fejerAverage_sub`, `OAI.Erdos3.CircleFourier.fejerAverage_sub_const`, `OAI.Erdos3.CircleFourier.fejerComponent`, `OAI.Erdos3.CircleFourier.fejerComponent_vadd`, `OAI.Erdos3.CircleFourier.fejerFirstMoment`, `OAI.Erdos3.CircleFourier.fejerFirstMoment_le`, `OAI.Erdos3.CircleFourier.fejer_cutoff_bound`, `OAI.Erdos3.CircleFourier.fejer_error_le_of_cutoff`, `OAI.Erdos3.CircleFourier.integrable_circleFourierComponent`, `OAI.Erdos3.CircleFourier.isometricCircleActionOfFlow`, `OAI.Erdos3.CircleFourier.lipschitz_circleFejerSum`, `OAI.Erdos3.CircleFourier.lipschitz_circleFourierComponent`, `OAI.Erdos3.CircleFourier.lipschitz_fejerComponent`, `OAI.Erdos3.CircleFourier.norm_circleFourierComponent_le`, `OAI.Erdos3.CircleFourier.norm_fejerAverage_le`, `OAI.Erdos3.CircleFourier.norm_fejerAverage_sub_average_le`, `OAI.Erdos3.CircleFourier.norm_fejerAverage_sub_le`, `OAI.Erdos3.CircleFourier.norm_fejerAverage_sub_le_explicit`, `OAI.Erdos3.CircleFourier.norm_fejerComponent_le`, `OAI.Erdos3.CircleFourier.ofReal_fejerPolynomial_eq`, `OAI.Erdos3.CircleFourier.periodicFlowAct`, `OAI.Erdos3.CircleFourier.periodicFlowAct_add`, `OAI.Erdos3.CircleFourier.periodicFlowAct_coe`, `OAI.Erdos3.CircleFourier.periodicFlowAct_displacement`, `OAI.Erdos3.CircleFourier.periodicFlowAct_isometry`, `OAI.Erdos3.CircleFourier.periodicFlowAct_zero`, `OAI.Erdos3.CircleFourier.realFlow_periodic`, `OAI.Erdos3.CircleFourier.torusCoordinateAction`, `OAI.Erdos3.CircleFourier.torusCoordinateAction_commutes`, `OAI.Erdos3.CircleFourier.torus_character_of_coordinate_characters`, `OAI.Erdos3.CoordinateDecisionTree.leafCylinders`, `OAI.Erdos3.CoordinateDecisionTree.leafCylinders_contains_iff`, `OAI.Erdos3.CoordinateDecisionTree.leafCylinders_indicator_sum`, `OAI.Erdos3.CoordinateDecisionTree.leafCylinders_mass_sum`, `OAI.Erdos3.CoordinateDecisionTree.leafSourceAssignments`, `OAI.Erdos3.CoordinateDecisionTree.mem_leafCylinders`, `OAI.Erdos3.CoordinateDecisionTree.traceCylinder`, `OAI.Erdos3.CoordinateDecisionTree.traceCylinder_contains`, `OAI.Erdos3.CoordinateDecisionTree.traceCylinder_contains_iff`, `OAI.Erdos3.CoordinateDecisionTree.trace_eq_of_agree`, `OAI.Erdos3.CylinderRemovalChain`, `OAI.Erdos3.FiniteProbabilityWeights.abs_mean_le_mean_abs`, `OAI.Erdos3.FiniteProbabilityWeights.abs_mean_le_on_support`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_div`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_prod`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_sum`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_weighted_expansion`, `OAI.Erdos3.FiniteProbabilityWeights.condition_condition`, `OAI.Erdos3.FiniteProbabilityWeights.eventProbability_mem`, `OAI.Erdos3.FiniteProbabilityWeights.excessMass`, `OAI.Erdos3.FiniteProbabilityWeights.excessMass_antitone_cap`, `OAI.Erdos3.FiniteProbabilityWeights.excessMass_le_of_mass_le`, `OAI.Erdos3.FiniteProbabilityWeights.excessMass_max_one_le`, `OAI.Erdos3.FiniteProbabilityWeights.excessMass_nonneg`, `OAI.Erdos3.FiniteProbabilityWeights.exists_positive_weight_ge_complexMean_re`, `OAI.Erdos3.FiniteProbabilityWeights.exists_positive_weight_ge_mean`, `OAI.Erdos3.FiniteProbabilityWeights.exists_weight_pos`, `OAI.Erdos3.FiniteProbabilityWeights.ext_weight`, `OAI.Erdos3.FiniteProbabilityWeights.fiberLaw_weight_eq_mass`, `OAI.Erdos3.FiniteProbabilityWeights.imageMeasure`, `OAI.Erdos3.FiniteProbabilityWeights.joint`, `OAI.Erdos3.FiniteProbabilityWeights.joint_mean`, `OAI.Erdos3.FiniteProbabilityWeights.mass_above_double_cap_le`, `OAI.Erdos3.FiniteProbabilityWeights.mass_above_double_cap_le_of_excess`, `OAI.Erdos3.FiniteProbabilityWeights.mass_inter_pos_of_condition`, `OAI.Erdos3.FiniteProbabilityWeights.mean_equiv`, `OAI.Erdos3.FiniteProbabilityWeights.mean_mono_on_support`, `OAI.Erdos3.FiniteProbabilityWeights.mean_relativeDensity`, `OAI.Erdos3.FiniteProbabilityWeights.mem_piRestrictionSet`, `OAI.Erdos3.FiniteProbabilityWeights.norm_complexMean_weighted_lower_of_perturbation`, `OAI.Erdos3.FiniteProbabilityWeights.norm_complexMean_weighted_sub_le`, `OAI.Erdos3.FiniteProbabilityWeights.norm_weighted_complexMean_sub_le_mean_norm`, `OAI.Erdos3.FiniteProbabilityWeights.ofPMF`, `OAI.Erdos3.FiniteProbabilityWeights.ofPMF_weight`, `OAI.Erdos3.FiniteProbabilityWeights.ofSupportedPMF`, `OAI.Erdos3.FiniteProbabilityWeights.ofSupportedPMF_map_event`, `OAI.Erdos3.FiniteProbabilityWeights.ofSupportedPMF_map_mean`, `OAI.Erdos3.FiniteProbabilityWeights.ofSupportedPMF_weight`, `OAI.Erdos3.FiniteProbabilityWeights.piRestrictionSet`, `OAI.Erdos3.FiniteProbabilityWeights.piRestriction_mass`, `OAI.Erdos3.FiniteProbabilityWeights.pi_fiber_mass`, `OAI.Erdos3.FiniteProbabilityWeights.pi_fiber_set`, `OAI.Erdos3.FiniteProbabilityWeights.prod`, `OAI.Erdos3.FiniteProbabilityWeights.relativeDensity`, `OAI.Erdos3.FiniteProbabilityWeights.relativeDensity_nonneg`, `OAI.Erdos3.FiniteProbabilityWeights.relativeDensity_tail_mass`, `OAI.Erdos3.FiniteProbabilityWeights.reweight`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_apply`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_condition_condition_mean`, `OAI.Erdos3.FiniteProbabilityWeights.uniform_mean_equiv`, `OAI.Erdos3.FiniteProbabilityWeights.weighted_expansion_discard_error`, `OAI.Erdos3.FiniteProbabilityWeights.weighted_projection_comparison`, `OAI.Erdos3.FixedDensity.BooleanCutAssignment`, `OAI.Erdos3.FixedDensity.BooleanCutTest`, `OAI.Erdos3.FixedDensity.BooleanCutTest.eval`, `OAI.Erdos3.FixedDensity.BooleanCutTest.eval_le_one`, `OAI.Erdos3.FixedDensity.BooleanCutTest.eval_of_mem`, `OAI.Erdos3.FixedDensity.BooleanCutTest.eval_of_not_mem`, `OAI.Erdos3.FixedDensity.BooleanCutTest.eval_sq`, `OAI.Erdos3.FixedDensity.CutTestCoordinate`, `OAI.Erdos3.FixedDensity.CutTestFamily`, `OAI.Erdos3.FixedDensity.DeletedVector`, `OAI.Erdos3.FixedDensity.DiagonalAPParameter`, `OAI.Erdos3.FixedDensity.FaceRegularityState`, `OAI.Erdos3.FixedDensity.FaceRegularityState.IsFaceCutRegular`, `OAI.Erdos3.FixedDensity.FaceRegularityState.IsRegularAgainst`, `OAI.Erdos3.FixedDensity.FaceRegularityState.booleanCutCorrelation`, `OAI.Erdos3.FixedDensity.FaceRegularityState.booleanCutCorrelation_eq_projection`, `OAI.Erdos3.FixedDensity.FaceRegularityState.booleanCutCorrelation_sq_le_energyIncrement`, `OAI.Erdos3.FixedDensity.FaceRegularityState.booleanCut_measurable_refineBy`, `OAI.Erdos3.FixedDensity.FaceRegularityState.chosenIrregularCut`, `OAI.Erdos3.FixedDensity.FaceRegularityState.conditionalMean_residual`, `OAI.Erdos3.FixedDensity.FaceRegularityState.conditionalMean_residual_refineBy`, `OAI.Erdos3.FixedDensity.FaceRegularityState.energy`, `OAI.Erdos3.FixedDensity.FaceRegularityState.energy_increment_of_booleanCut`, `OAI.Erdos3.FixedDensity.FaceRegularityState.energy_refineBy_sub_eq_mean_sq`, `OAI.Erdos3.FixedDensity.FaceRegularityState.exists_booleanCut_of_not_regular`, `OAI.Erdos3.FixedDensity.FaceRegularityState.faceCutCorrelation`, `OAI.Erdos3.FixedDensity.FaceRegularityState.lowStructuredOneFinset`, `OAI.Erdos3.FixedDensity.FaceRegularityState.mean_booleanCut_sq_le_one`, `OAI.Erdos3.FixedDensity.FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul`, `OAI.Erdos3.FixedDensity.FaceRegularityState.mean_mul_sq_le_sq_mul_sq`, `OAI.Erdos3.FixedDensity.FaceRegularityState.mean_residual`, `OAI.Erdos3.FixedDensity.FaceRegularityState.mem_lowStructuredOneFinset`, `OAI.Erdos3.FixedDensity.FaceRegularityState.partition_refineBy`, `OAI.Erdos3.FixedDensity.FaceRegularityState.refineBy`, `OAI.Erdos3.FixedDensity.FaceRegularityState.refineBy_le`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRun`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRunCuts`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRunCuts_succ`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRunCuts_zero`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRun_succ`, `OAI.Erdos3.FixedDensity.FaceRegularityState.regularityRun_zero`, `OAI.Erdos3.FixedDensity.FaceRegularityState.residual`, `OAI.Erdos3.FixedDensity.FaceRegularityState.structured`, `OAI.Erdos3.FixedDensity.GeneratorBranch`, `OAI.Erdos3.FixedDensity.HasDenseAPCount`, `OAI.Erdos3.FixedDensity.HasUniformCyclicPartiteSimplexRemoval`, `OAI.Erdos3.FixedDensity.HasUniformDenseAPCount`, `OAI.Erdos3.FixedDensity.HasUniformOrderedPatternRemoval`, `OAI.Erdos3.FixedDensity.IsBoundedCutTest`, `OAI.Erdos3.FixedDensity.IsBoundedCutTest.le_one`, `OAI.Erdos3.FixedDensity.IsPartitionMeasurable`, `OAI.Erdos3.FixedDensity.IsPartitionMeasurable.of_le`, `OAI.Erdos3.FixedDensity.IsUnitBounded`, `OAI.Erdos3.FixedDensity.IsUnitBounded.le_one`, `OAI.Erdos3.FixedDensity.NatGrowthFunction`, `OAI.Erdos3.FixedDensity.NatGrowthFunction.instCoeFunForallNat`, `OAI.Erdos3.FixedDensity.NatGrowthFunction.monotone`, `OAI.Erdos3.FixedDensity.NatGrowthFunction.one_le`, `OAI.Erdos3.FixedDensity.NatGrowthFunction.positive`, `OAI.Erdos3.FixedDensity.OrderedFace`, `OAI.Erdos3.FixedDensity.OrderedFaceComplement`, `OAI.Erdos3.FixedDensity.OrderedPattern.DeletionFamily`, `OAI.Erdos3.FixedDensity.OrderedPattern.IsCover`, `OAI.Erdos3.FixedDensity.OrderedPattern.IsOccurrence`, `OAI.Erdos3.FixedDensity.OrderedPattern.emptyDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.faceDeletionDensity`, `OAI.Erdos3.FixedDensity.OrderedPattern.faceDeletionDensity_empty`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_occurrenceFinset`, `OAI.Erdos3.FixedDensity.OrderedPattern.occurrenceFinset`, `OAI.Erdos3.FixedDensity.OrderedPattern.rec`, `OAI.Erdos3.FixedDensity.OrderedPattern.toWeighted`, `OAI.Erdos3.FixedDensity.OrderedRegularitySystem`, `OAI.Erdos3.FixedDensity.SimplexHypergraph`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.DeletionFamily`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.IsSimplexCover`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.card_deletedVector_fin`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.colorDeletionDensity`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.colorDeletionDensity_fin`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deleteEdges`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deleteEdges_edge`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deleteEdges_empty_simplexFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deletionCapacity`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deletionCapacity_fin`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deletionCount`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deletionCount_empty`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.deletionSlotFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.edgeFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.emptyDeletion`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.mem_deleteEdges_simplexFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.mem_edgeFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.mem_emptyDeletion`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.mem_simplexFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.normalizedDeletionCost`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.normalizedDeletionCost_empty`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.simplexFinset`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.toOrderedPattern`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.toOrderedPattern_edge_orderedFacet`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.toWeighted`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.toWeighted_edgeWeight_of_edge`, `OAI.Erdos3.FixedDensity.SimplexHypergraph.toWeighted_edgeWeight_of_not_edge`, `OAI.Erdos3.FixedDensity.WeightedOrderedPattern.patternCount`, `OAI.Erdos3.FixedDensity.WeightedOrderedPattern.patternWeight`, `OAI.Erdos3.FixedDensity.WeightedOrderedPattern.rec`, `OAI.Erdos3.FixedDensity.WeightedSimplexSystem.noConfusion`, `OAI.Erdos3.FixedDensity.WeightedSimplexSystem.simplexCount`, `OAI.Erdos3.FixedDensity.WeightedSimplexSystem.simplexWeight`, `OAI.Erdos3.FixedDensity.apCoefficientAddEquiv`, `OAI.Erdos3.FixedDensity.apCoefficientAddEquiv_apply`, `OAI.Erdos3.FixedDensity.apCoefficient_isUnit_of_coprime_factorial`, `OAI.Erdos3.FixedDensity.apFaceScalingEquiv`, `OAI.Erdos3.FixedDensity.apFaceScalingEquiv_apply`, `OAI.Erdos3.FixedDensity.apSetHypergraph`, `OAI.Erdos3.FixedDensity.apSetHypergraph_edge`, `OAI.Erdos3.FixedDensity.apSetHypergraph_toWeighted_edgeWeight`, `OAI.Erdos3.FixedDensity.apSimplexForm`, `OAI.Erdos3.FixedDensity.apSimplexForm_deleteCoordinate`, `OAI.Erdos3.FixedDensity.apSimplexForm_diagonalAPSimplex`, `OAI.Erdos3.FixedDensity.apSimplexSystem`, `OAI.Erdos3.FixedDensity.bernoulliAssignmentWeight`, `OAI.Erdos3.FixedDensity.booleanCut_measurable_generatedBy`, `OAI.Erdos3.FixedDensity.booleanFaceCutSupport`, `OAI.Erdos3.FixedDensity.booleanFaceCutSupports`, `OAI.Erdos3.FixedDensity.booleanValue`, `OAI.Erdos3.FixedDensity.card_diagonalAPParameter`, `OAI.Erdos3.FixedDensity.card_generatorBranch`, `OAI.Erdos3.FixedDensity.card_orderedDeletionToSimplex`, `OAI.Erdos3.FixedDensity.coordinatewiseAddEquiv`, `OAI.Erdos3.FixedDensity.coordinatewiseAddEquiv_apply`, `OAI.Erdos3.FixedDensity.coordinatewiseAddEquiv_symm_apply`, `OAI.Erdos3.FixedDensity.cutCorrelation`, `OAI.Erdos3.FixedDensity.cutCorrelation_one`, `OAI.Erdos3.FixedDensity.cutCorrelation_self`, `OAI.Erdos3.FixedDensity.cutTestCoordinateValue`, `OAI.Erdos3.FixedDensity.cutTestFamilyOfBooleanAssignment`, `OAI.Erdos3.FixedDensity.cutTestProduct`, `OAI.Erdos3.FixedDensity.cutTestProduct_mul`, `OAI.Erdos3.FixedDensity.cutTestProduct_one`, `OAI.Erdos3.FixedDensity.cyclicAPDiagonalMass`, `OAI.Erdos3.FixedDensity.cyclicAPMass`, `OAI.Erdos3.FixedDensity.cyclicAPOffDiagMass`, `OAI.Erdos3.FixedDensity.cyclicAPProduct_zero_difference`, `OAI.Erdos3.FixedDensity.deleteCoordinate`, `OAI.Erdos3.FixedDensity.deletedVectorFinTupleEquiv`, `OAI.Erdos3.FixedDensity.deletedVectorToFinTuple`, `OAI.Erdos3.FixedDensity.deletedVectorToFinTuple_deleteCoordinate`, `OAI.Erdos3.FixedDensity.deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple`, `OAI.Erdos3.FixedDensity.deletedVectorToFinTuple_finTupleToDeletedVector`, `OAI.Erdos3.FixedDensity.deletionCapacity_zmod`, `OAI.Erdos3.FixedDensity.diagonalAPSimplex`, `OAI.Erdos3.FixedDensity.diagonalAPSimplex_mem_simplexFinset`, `OAI.Erdos3.FixedDensity.diagonalCoverColor`, `OAI.Erdos3.FixedDensity.diagonalCoverColor_mem`, `OAI.Erdos3.FixedDensity.diagonalCoveredSlot`, `OAI.Erdos3.FixedDensity.eraseCoordinate`, `OAI.Erdos3.FixedDensity.eraseCoordinate_apply`, `OAI.Erdos3.FixedDensity.eraseCoordinate_insertNth`, `OAI.Erdos3.FixedDensity.fiberConvolution`, `OAI.Erdos3.FixedDensity.fiberConvolution_arity_zero`, `OAI.Erdos3.FixedDensity.fiberConvolution_const_succ`, `OAI.Erdos3.FixedDensity.fiberConvolution_smul`, `OAI.Erdos3.FixedDensity.fiberConvolution_succ`, `OAI.Erdos3.FixedDensity.fiberConvolution_zero_weight`, `OAI.Erdos3.FixedDensity.finSuccAboveEquiv`, `OAI.Erdos3.FixedDensity.finSuccAboveEquiv_apply_val`, `OAI.Erdos3.FixedDensity.finTupleToDeletedVector`, `OAI.Erdos3.FixedDensity.finTupleToDeletedVector_deletedVectorToFinTuple`, `OAI.Erdos3.FixedDensity.finTupleToDeletedVector_orderedFaceTuple`, `OAI.Erdos3.FixedDensity.finTupleToDeletedVector_succAbove`, `OAI.Erdos3.FixedDensity.finitePairing`, `OAI.Erdos3.FixedDensity.finitePairingCLM`, `OAI.Erdos3.FixedDensity.finitePairingCLM_apply`, `OAI.Erdos3.FixedDensity.finitePairingLinearMap`, `OAI.Erdos3.FixedDensity.finitePairing_add_left`, `OAI.Erdos3.FixedDensity.finitePairing_one_left`, `OAI.Erdos3.FixedDensity.finitePairing_smul_left`, `OAI.Erdos3.FixedDensity.finiteTestCombination`, `OAI.Erdos3.FixedDensity.finiteTestCombination_apply`, `OAI.Erdos3.FixedDensity.finiteTestCombination_zero`, `OAI.Erdos3.FixedDensity.finiteTestProfile`, `OAI.Erdos3.FixedDensity.finiteTestProfile_apply`, `OAI.Erdos3.FixedDensity.generalizedConvolution`, `OAI.Erdos3.FixedDensity.generalizedConvolution_arity_zero`, `OAI.Erdos3.FixedDensity.generalizedConvolution_one_succ`, `OAI.Erdos3.FixedDensity.generalizedConvolution_succ`, `OAI.Erdos3.FixedDensity.generalizedConvolution_zero_succ`, `OAI.Erdos3.FixedDensity.growthRegularityBudget`, `OAI.Erdos3.FixedDensity.growthRegularityBudget_eq`, `OAI.Erdos3.FixedDensity.growthRegularityComplexity`, `OAI.Erdos3.FixedDensity.growthRegularityComplexity_succ`, `OAI.Erdos3.FixedDensity.growthRegularityComplexity_zero`, `OAI.Erdos3.FixedDensity.growthRegularityLength`, `OAI.Erdos3.FixedDensity.growthRegularityStepBudget`, `OAI.Erdos3.FixedDensity.growthRegularityStepTolerance`, `OAI.Erdos3.FixedDensity.growthRegularityTolerance`, `OAI.Erdos3.FixedDensity.growthRegularityTolerance_eq`, `OAI.Erdos3.FixedDensity.isBoundedCutTest_const`, `OAI.Erdos3.FixedDensity.isBoundedCutTest_one`, `OAI.Erdos3.FixedDensity.isBoundedCutTest_zero`, `OAI.Erdos3.FixedDensity.lowerGeneratorCell`, `OAI.Erdos3.FixedDensity.mem_booleanFaceCutSupport`, `OAI.Erdos3.FixedDensity.mem_lowerGeneratorCell`, `OAI.Erdos3.FixedDensity.mem_orderedDeletionToSimplex_iff`, `OAI.Erdos3.FixedDensity.mulAddEquivOfIsUnit`, `OAI.Erdos3.FixedDensity.mulAddEquivOfIsUnit_apply`, `OAI.Erdos3.FixedDensity.orderedDeletionToSimplex`, `OAI.Erdos3.FixedDensity.orderedFaceComplementTuple`, `OAI.Erdos3.FixedDensity.orderedFaceComplementTuple_splitOrderedFaceEquiv_symm`, `OAI.Erdos3.FixedDensity.orderedFaceDecidableEq`, `OAI.Erdos3.FixedDensity.orderedFaceSumEquiv`, `OAI.Erdos3.FixedDensity.orderedFaceTuple`, `OAI.Erdos3.FixedDensity.orderedFaceTuple_splitOrderedFaceEquiv_symm`, `OAI.Erdos3.FixedDensity.orderedFacet`, `OAI.Erdos3.FixedDensity.orderedFacetEquiv`, `OAI.Erdos3.FixedDensity.orderedFacetEquiv_apply`, `OAI.Erdos3.FixedDensity.orderedRemovalRegularityBudget`, `OAI.Erdos3.FixedDensity.positivePart`, `OAI.Erdos3.FixedDensity.positivePart_apply`, `OAI.Erdos3.FixedDensity.positivePart_of_nonneg`, `OAI.Erdos3.FixedDensity.positivePart_of_nonpos`, `OAI.Erdos3.FixedDensity.positivePart_zero`, `OAI.Erdos3.FixedDensity.positiveSupportIndicator`, `OAI.Erdos3.FixedDensity.positiveSupportIndicator_mul`, `OAI.Erdos3.FixedDensity.regularizedOrderedPattern`, `OAI.Erdos3.FixedDensity.representingBooleanFaceCutAssignment`, `OAI.Erdos3.FixedDensity.simplexAPEquiv`, `OAI.Erdos3.FixedDensity.simplexCoordinateMoment`, `OAI.Erdos3.FixedDensity.simplexCoordinateMoment_coordinatesOfAP`, `OAI.Erdos3.FixedDensity.simplexCoordinateMoment_decompose`, `OAI.Erdos3.FixedDensity.simplexCoordinateMoment_diagonalAPSimplex`, `OAI.Erdos3.FixedDensity.simplexCoordinateSum`, `OAI.Erdos3.FixedDensity.simplexCoordinateSum_coordinatesOfAP`, `OAI.Erdos3.FixedDensity.simplexCoordinateSum_decompose`, `OAI.Erdos3.FixedDensity.simplexCoordinateSum_diagonalAPSimplex`, `OAI.Erdos3.FixedDensity.simplexCoordinatesOfAP`, `OAI.Erdos3.FixedDensity.simplexCoordinatesOfAP_one`, `OAI.Erdos3.FixedDensity.simplexCoordinatesOfAP_succ_succ`, `OAI.Erdos3.FixedDensity.simplexCoordinatesOfAP_zero`, `OAI.Erdos3.FixedDensity.simplexTailMoment`, `OAI.Erdos3.FixedDensity.simplexTailSum`, `OAI.Erdos3.FixedDensity.splitOrderedFaceEquiv`, `OAI.Erdos3.FixedDensity.splitOrderedFaceEquiv_fst`, `OAI.Erdos3.FixedDensity.splitOrderedFaceEquiv_snd`, `OAI.Erdos3.FixedDensity.sumFiberTuple`, `OAI.Erdos3.FixedDensity.sumFiberTuple_succ`, `OAI.Erdos3.FixedDensity.sumFiberTuple_zero`, `OAI.Erdos3.FixedDensity.sum_sumFiberTuple`, `OAI.Erdos3.FixedDensity.testMonomial`, `OAI.Erdos3.FixedDensity.testMonomial_apply`, `OAI.Erdos3.FixedDensity.usedCutTestCoordinateEmbedding`, `OAI.Erdos3.FixedDensity.usedCutTestCoordinateEmbedding_apply`, `OAI.Erdos3.FixedDensity.zeroFiberDelta`, `OAI.Erdos3.FixedDensity.zeroFiberDelta_of_ne`, `OAI.Erdos3.FixedDensity.zeroFiberDelta_zero`, `OAI.Erdos3.FreimanModel.FourfoldPresentation.Mem`, `OAI.Erdos3.FreimanModel.FourfoldPresentation.casesOn`, `OAI.Erdos3.FreimanModel.FourfoldPresentation.eval`, `OAI.Erdos3.FreimanModel.add_fourfold_sub_eq_iff_cross_add`, `OAI.Erdos3.FreimanModel.badMultipliers`, `OAI.Erdos3.FreimanModel.card_badMultipliers_le`, `OAI.Erdos3.FreimanModel.card_biUnion_badMultipliers_le`, `OAI.Erdos3.FreimanModel.defaultFourfoldPresentation`, `OAI.Erdos3.FreimanModel.exists_fourfold_lift_of_eight_iso`, `OAI.Erdos3.FreimanModel.exists_good_multiplier`, `OAI.Erdos3.FreimanModel.exists_large_cyclic_freiman_model`, `OAI.Erdos3.FreimanModel.exists_nonempty_large_color_fiber_mul`, `OAI.Erdos3.FreimanModel.fourfoldMapValue`, `OAI.Erdos3.FreimanModel.fourfoldMapValue_eq_iff_eval_eq`, `OAI.Erdos3.FreimanModel.fourfold_sub_eq_iff_cross_add`, `OAI.Erdos3.FreimanModel.freimanFourfoldLift`, `OAI.Erdos3.FreimanModel.freimanFourfoldLift_add_eq_add`, `OAI.Erdos3.FreimanModel.freimanFourfoldLift_eq_of_presentation`, `OAI.Erdos3.FreimanModel.freimanFourfoldLift_injOn`, `OAI.Erdos3.FreimanModel.freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul`, `OAI.Erdos3.FreimanModel.intCast_zmod_ne_zero_of_natAbs_lt`, `OAI.Erdos3.FreimanModel.int_natAbs_lt_of_neg_lt_and_lt`, `OAI.Erdos3.FreimanModel.isAddFreimanIso_ruzsaModelMap`, `OAI.Erdos3.FreimanModel.mem_badMultipliers`, `OAI.Erdos3.FreimanModel.mem_two_nsmul_sub_two_nsmul_iff`, `OAI.Erdos3.FreimanModel.multiplier_union_card_lt`, `OAI.Erdos3.FreimanModel.multiset_sum_mem_nsmul`, `OAI.Erdos3.FreimanModel.ruzsaBlockWidth_lt`, `OAI.Erdos3.FreimanModel.ruzsaColor`, `OAI.Erdos3.FreimanModel.ruzsaColor_lt`, `OAI.Erdos3.FreimanModel.ruzsaModelMap`, `OAI.Erdos3.FreimanModel.ruzsaModelMap_multiset_sum_eq_iff`, `OAI.Erdos3.FreimanModel.ruzsaModelMap_sum`, `OAI.Erdos3.FreimanModel.ruzsaModelMap_sum_eq_iff_dvd`, `OAI.Erdos3.FreimanModel.ruzsaRepresentative`, `OAI.Erdos3.FreimanModel.ruzsaRepresentativeSum`, `OAI.Erdos3.FreimanModel.ruzsaRepresentativeSum_bounds`, `OAI.Erdos3.FreimanModel.ruzsaRepresentativeSum_cast`, `OAI.Erdos3.FreimanModel.ruzsaRepresentativeSum_sub_abs_lt`, `OAI.Erdos3.FreimanModel.ruzsaRepresentativeSum_sub_cast`, `OAI.Erdos3.FreimanModel.ruzsaRepresentative_bounds_of_color_eq`, `OAI.Erdos3.FreimanModel.ruzsaRepresentative_cast`, `OAI.Erdos3.FreimanModel.ruzsaRepresentative_lt`, `OAI.Erdos3.FreimanModel.selectedFourfoldPresentation`, `OAI.Erdos3.FreimanModel.selectedFourfoldPresentation_spec`, `OAI.Erdos3.FreimanModel.zmod_val_eq_natAbs_of_nonneg`, `OAI.Erdos3.IntegerScalarCube`, `OAI.Erdos3.IntegerScalarCubeBox`, `OAI.Erdos3.IsIntegerMassInterpolation`, `OAI.Erdos3.IsIntegerMassInterpolation.lipschitz`, `OAI.Erdos3.IsIntegerMassInterpolation.mono`, `OAI.Erdos3.MissesBoxCoordinate`, `OAI.Erdos3.PatchKernel.abs_translateSum_sub_le`, `OAI.Erdos3.PatchKernel.kernel_le_translateSum`, `OAI.Erdos3.PatchKernel.normalizedTranslate`, `OAI.Erdos3.PatchKernel.periodicValue_le_translateSum`, `OAI.Erdos3.PatchKernel.translateSum`, `OAI.Erdos3.PatchKernel.translateSum_nonneg`, `OAI.Erdos3.PolynomialPatch.weightedParameters`, `OAI.Erdos3.PolynomialPatch.weightedParameters_value`, `OAI.Erdos3.PolynomialSlots.insertLifts`, `OAI.Erdos3.ProductBoundedMarginals`, `OAI.Erdos3.ProductCylinder`, `OAI.Erdos3.ProductCylinder.Contains`, `OAI.Erdos3.ProductCylinder.Maximizes`, `OAI.Erdos3.ProductCylinder.assignment`, `OAI.Erdos3.ProductCylinder.assignment_mem`, `OAI.Erdos3.ProductCylinder.bounded`, `OAI.Erdos3.ProductCylinder.containsDecidable`, `OAI.Erdos3.ProductCylinder.contains_iff`, `OAI.Erdos3.ProductCylinder.cut`, `OAI.Erdos3.ProductCylinder.erase`, `OAI.Erdos3.ProductCylinder.mass`, `OAI.Erdos3.ProductCylinder.normalizedSection`, `OAI.Erdos3.ProductCylinder.ofAssignment`, `OAI.Erdos3.ProductCylinder.positiveCandidates`, `OAI.Erdos3.ProductCylinder.score`, `OAI.Erdos3.ProductDependsOn`, `OAI.Erdos3.ProductMarginalsClose`, `OAI.Erdos3.RepresentativeWindow.crtPatch`, `OAI.Erdos3.RepresentativeWindow.crtPatch_lip`, `OAI.Erdos3.RepresentativeWindow.kernel`, `OAI.Erdos3.RepresentativeWindow.patch`, `OAI.Erdos3.RepresentativeWindow.patch_lip`, `OAI.Erdos3.RepresentativeWindow.rec`, `OAI.Erdos3.SlicedProductBlock.FourInput`, `OAI.Erdos3.SlicedProductBlock.PairInput`, `OAI.Erdos3.SlicedProductBlock.fourDensity`, `OAI.Erdos3.SlicedProductBlock.fourSource`, `OAI.Erdos3.SlicedProductBlock.fourSource_probability`, `OAI.Erdos3.SlicedProductBlock.fourValue`, `OAI.Erdos3.SlicedProductBlock.pairCapNN`, `OAI.Erdos3.SlicedProductBlock.pairDensity`, `OAI.Erdos3.SlicedProductBlock.pairSource`, `OAI.Erdos3.SlicedProductBlock.pairSource_probability`, `OAI.Erdos3.SlicedProductBlock.pairValue`, `OAI.Erdos3.SlicedProductBlock.uniformCap`, `OAI.Erdos3.VectorPolynomial.allocatedTupleSpatialError`, `OAI.Erdos3.WeightedParameterPatch.rec`, `OAI.Erdos3.WeightedParameterPatch.reparam`, `OAI.Erdos3.WeightedParameterPatch.reparam_lip`, `OAI.Erdos3.WeightedParameterPatch.value`, `OAI.Erdos3.WeightedParameterSlots`, `OAI.Erdos3.WeightedParameterSlots.insertCenter`, `OAI.Erdos3.WeightedParameterSlots.insertCenter_degree`, `OAI.Erdos3.WeightedParameterSlots.insertSubstitution`, `OAI.Erdos3.WeightedParameterSlots.insertSubstitution_degree`, `OAI.Erdos3.WeightedParameterSlots.parameterSubstitution`, `OAI.Erdos3.WeightedParameterSlots.parameterSubstitution_degree`, `OAI.Erdos3.WeightedParameterSlots.reparam`, `OAI.Erdos3.WeightedParameterSlots.slots`, `OAI.Erdos3.aeval_monomial_update`, `OAI.Erdos3.aeval_monomial_update_add`, `OAI.Erdos3.aeval_monomial_update_eq_of_zero`, `OAI.Erdos3.affineBooleanCubeCutoff`, `OAI.Erdos3.affineBooleanCubeDeterminant`, `OAI.Erdos3.affineBooleanCubeGoodWeight`, `OAI.Erdos3.affineCubeMinorThreshold`, `OAI.Erdos3.affineJetUnitMap`, `OAI.Erdos3.affineProductProfileLip`, `OAI.Erdos3.affineProductProfile_cap`, `OAI.Erdos3.affineProductProfile_lipschitz`, `OAI.Erdos3.affineProductProfile_sample`, `OAI.Erdos3.affineProductProfile_sample_sum`, `OAI.Erdos3.affineProductProfile_sample_sum_pos`, `OAI.Erdos3.affineProfile_sample_coordinate`, `OAI.Erdos3.affineSelectedJetDensity`, `OAI.Erdos3.affineSelectedJetProfile`, `OAI.Erdos3.anisotropicSpatialCapLog`, `OAI.Erdos3.anisotropicSpatialCapLog_nonneg`, `OAI.Erdos3.anisotropicSpatialDensityCap`, `OAI.Erdos3.anisotropicSpatialDensityCap_exp_bound`, `OAI.Erdos3.anisotropicSpatialDensityCap_nonneg`, `OAI.Erdos3.anisotropicSpatialDensityLip`, `OAI.Erdos3.anisotropicSpatialDensityLip_nonneg`, `OAI.Erdos3.anisotropicSpatialDetAllowance`, `OAI.Erdos3.anisotropicSpatialDiscretizationCost`, `OAI.Erdos3.anisotropicSpatialError`, `OAI.Erdos3.anisotropicSpatialKernelDensity`, `OAI.Erdos3.anisotropicSpatialMeshThreshold`, `OAI.Erdos3.anisotropicSpatialOutputLaw`, `OAI.Erdos3.anisotropicSpatialScale`, `OAI.Erdos3.anisotropicSpatialScale_pos`, `OAI.Erdos3.anisotropicTupleEarlyBudget`, `OAI.Erdos3.anisotropicTupleEarlyBudget_bounds`, `OAI.Erdos3.anovaKernelMatrix`, `OAI.Erdos3.assignedBoxTest`, `OAI.Erdos3.assignedBoxTest_misses`, `OAI.Erdos3.assignedBoxTest_norm`, `OAI.Erdos3.assignedBoxTest_prod`, `OAI.Erdos3.assigned_site_cauchySchwarz`, `OAI.Erdos3.binaryWordSupport`, `OAI.Erdos3.binaryWordSupportEquiv`, `OAI.Erdos3.binaryWordSupport_card`, `OAI.Erdos3.binaryWordSupport_zero`, `OAI.Erdos3.bounded_weight_cutoff_lipschitz`, `OAI.Erdos3.boxCorner`, `OAI.Erdos3.boxCornerAnchor`, `OAI.Erdos3.boxCornerAnchor_map`, `OAI.Erdos3.boxCornerAnchor_norm_le_one`, `OAI.Erdos3.boxCornerAnchor_prod_equiv`, `OAI.Erdos3.boxCornerProduct`, `OAI.Erdos3.boxCornerProduct_eq_mul_anchor`, `OAI.Erdos3.boxCornerProduct_map`, `OAI.Erdos3.boxCornerProduct_mul`, `OAI.Erdos3.boxCornerProduct_star`, `OAI.Erdos3.boxCornerProduct_succ`, `OAI.Erdos3.boxCorner_cons_false`, `OAI.Erdos3.boxCorner_cons_true`, `OAI.Erdos3.boxPhaseMoment`, `OAI.Erdos3.boxPhaseMoment_eq_expect_cornerProduct`, `OAI.Erdos3.boxPhaseMoment_succ`, `OAI.Erdos3.boxPhaseMoment_zero`, `OAI.Erdos3.boxTailAmplitude`, `OAI.Erdos3.boxTailAmplitude_cross`, `OAI.Erdos3.boxTailPhase`, `OAI.Erdos3.boxTailTests`, `OAI.Erdos3.boxTailTests_misses`, `OAI.Erdos3.boxTailTests_norm`, `OAI.Erdos3.boxTestCorrelation`, `OAI.Erdos3.boxTestCorrelation_head`, `OAI.Erdos3.boxTestCorrelation_square_le`, `OAI.Erdos3.boxTestCorrelation_zero`, `OAI.Erdos3.boxTest_cauchySchwarz`, `OAI.Erdos3.boxTest_cauchySchwarz_of_pos`, `OAI.Erdos3.bufferedCoordinateProjection`, `OAI.Erdos3.canonicalAffineCubeMinorThreshold`, `OAI.Erdos3.canonicalBooleanMinorLog`, `OAI.Erdos3.canonicalSpatialKernelDensity`, `OAI.Erdos3.canonicalSpatialKernelMap`, `OAI.Erdos3.canonicalSpatialSiteDensity`, `OAI.Erdos3.canonicalZeroSpatialInputMap`, `OAI.Erdos3.centeredKernelMatrix`, `OAI.Erdos3.coefficientCRTEquiv`, `OAI.Erdos3.coefficientErrorPeriod_exp_sq`, `OAI.Erdos3.coefficientErrorSpatialLog`, `OAI.Erdos3.coefficientErrorSpatialLog_nonneg`, `OAI.Erdos3.coefficientErrorVolumeLog`, `OAI.Erdos3.coefficientFrontLog`, `OAI.Erdos3.coefficientReplacementErrorLog`, `OAI.Erdos3.commonPolynomialGapRatio`, `OAI.Erdos3.commonPolynomialGapRatio_le`, `OAI.Erdos3.commonPolynomialGapRatio_one_le`, `OAI.Erdos3.commonPolynomialInitialScale`, `OAI.Erdos3.commonPolynomialInitialScale_le`, `OAI.Erdos3.commonPolynomialInitialScale_pos`, `OAI.Erdos3.conjugationPower_eq_if_mod`, `OAI.Erdos3.constantCoefficientDensity`, `OAI.Erdos3.constantCoefficientDensity_cap`, `OAI.Erdos3.constantIntegerInterpolation`, `OAI.Erdos3.constantIntegerInterpolationCap`, `OAI.Erdos3.constantIntegerInterpolationLip`, `OAI.Erdos3.constantIntegerInterpolation_spec`, `OAI.Erdos3.constantIntegerPMF`, `OAI.Erdos3.constantIntegerPMF_cap`, `OAI.Erdos3.constantIntegerPMF_large`, `OAI.Erdos3.constantIntegerPMF_small`, `OAI.Erdos3.constantIntegerPMF_support`, `OAI.Erdos3.coordinateDenominatorGrid`, `OAI.Erdos3.coordinateRescaledDensity`, `OAI.Erdos3.coordinateUnionWeight`, `OAI.Erdos3.cubeMinorConstantLog`, `OAI.Erdos3.cubeMinorScaleLog`, `OAI.Erdos3.cubeMinorThresholdLog`, `OAI.Erdos3.disjointCoordinateLevel`, `OAI.Erdos3.euclideanDerivative_covolume_density_bound`, `OAI.Erdos3.exists_box_corner_anchor_correlation`, `OAI.Erdos3.exists_common_polynomial_scale`, `OAI.Erdos3.exists_coordinate_rounding_moduli`, `OAI.Erdos3.exists_finite_descending_rank_equiv`, `OAI.Erdos3.exists_forecast_detecting_atom`, `OAI.Erdos3.exists_mode_threshold_exp_budget`, `OAI.Erdos3.exists_partially_bounded_grid_normalization`, `OAI.Erdos3.exists_true_of_ne_false`, `OAI.Erdos3.exists_unrounded_scalar`, `OAI.Erdos3.exists_variable_unrounded_affine`, `OAI.Erdos3.finiteCoefficientLift`, `OAI.Erdos3.finiteCoefficientLift_mem_Ico`, `OAI.Erdos3.finiteDensityMass`, `OAI.Erdos3.finiteDensityMass_complex`, `OAI.Erdos3.finiteDensityMass_eq_div`, `OAI.Erdos3.finiteDensityMass_raw_pos`, `OAI.Erdos3.finiteDensityMass_sum_le_of_weight_lower`, `OAI.Erdos3.finiteDensityTiltPMF`, `OAI.Erdos3.finiteDensityTiltPMF_complexMean`, `OAI.Erdos3.finiteDensityTiltPMF_toReal`, `OAI.Erdos3.finiteSupportProbability`, `OAI.Erdos3.finiteSupportProbability_complexMean`, `OAI.Erdos3.finiteTaggedTupleEquiv`, `OAI.Erdos3.finiteWeightDensity`, `OAI.Erdos3.finite_normalized_test_sum`, `OAI.Erdos3.finite_supported_normalized_mixture`, `OAI.Erdos3.finite_supported_normalized_mixture_bound`, `OAI.Erdos3.finite_supported_weight_sum_tsum`, `OAI.Erdos3.floor_four_difference_bound`, `OAI.Erdos3.forecastBoundedSignalTransfer`, `OAI.Erdos3.frequency_code_count_bound`, `OAI.Erdos3.frequency_projection_error_bound`, `OAI.Erdos3.functional_eq_sum_coordinates`, `OAI.Erdos3.functional_eq_weighted_inner`, `OAI.Erdos3.idealSiteBoxRadius`, `OAI.Erdos3.idealSiteBoxRadius_buffer_le_exp`, `OAI.Erdos3.idealSiteBoxRadius_pos`, `OAI.Erdos3.idealSiteEnvelopeRadius`, `OAI.Erdos3.idealSiteEnvelopeRadius_le_exp`, `OAI.Erdos3.idealSiteEnvelopeRadius_pos`, `OAI.Erdos3.integerAxisPrincipalPMF`, `OAI.Erdos3.integerAxisPrincipalPMF_active`, `OAI.Erdos3.integerAxisPrincipalPMF_bound`, `OAI.Erdos3.integerAxisPrincipalPMF_inactive`, `OAI.Erdos3.integerAxisPrincipal_width`, `OAI.Erdos3.integerAxisSideLength`, `OAI.Erdos3.integerAxisSideLength_le`, `OAI.Erdos3.integerAxisSideLength_pos`, `OAI.Erdos3.integerCoordinate_count`, `OAI.Erdos3.integerMassTent`, `OAI.Erdos3.integerMassTent_difference`, `OAI.Erdos3.integerMassTent_grid`, `OAI.Erdos3.integerMassTent_range`, `OAI.Erdos3.integerMassTent_spec`, `OAI.Erdos3.integerPolynomialInitialScale`, `OAI.Erdos3.integerPolynomialInitialScale_width`, `OAI.Erdos3.integerRowMassInterpolation`, `OAI.Erdos3.integerRowMassTent`, `OAI.Erdos3.integerScalarCubeBoxZero`, `OAI.Erdos3.integerScalarCubeBox_card`, `OAI.Erdos3.integerScalarCubeDensityCap`, `OAI.Erdos3.integerScalarCubeEquiv`, `OAI.Erdos3.integerScalarCubeReference`, `OAI.Erdos3.integerScalarCubeReference_mass`, `OAI.Erdos3.integerScalarCubeReference_mass_pos`, `OAI.Erdos3.integerScalarCubeSet`, `OAI.Erdos3.integerScalarCubeSet_nonempty`, `OAI.Erdos3.integerScalarCubeValue`, `OAI.Erdos3.integerScalarCubeWeights`, `OAI.Erdos3.integerScalarCube_coordinates`, `OAI.Erdos3.integerScalarCube_iff_supported`, `OAI.Erdos3.integerScalarCube_small_positive`, `OAI.Erdos3.intervalSiteCenter`, `OAI.Erdos3.intervalSiteCount`, `OAI.Erdos3.intervalSiteCount_bound`, `OAI.Erdos3.intervalSiteCount_le_exp`, `OAI.Erdos3.intervalSiteLipschitz_le_exp`, `OAI.Erdos3.intervalSiteWeight`, `OAI.Erdos3.intervalSiteWeight_lipschitz`, `OAI.Erdos3.intervalSiteWeight_near`, `OAI.Erdos3.intervalSiteWeight_range`, `OAI.Erdos3.iteratedBoxDifference_eq_cornerProduct`, `OAI.Erdos3.jointAffineBooleanCutoff`, `OAI.Erdos3.jointAffineBooleanErrorBudget`, `OAI.Erdos3.jointAffineBooleanGoodWeight`, `OAI.Erdos3.jointAffineBooleanInverseBudget`, `OAI.Erdos3.jointAffineBooleanTranslationBudget`, `OAI.Erdos3.jointAffinePolynomialTolerance`, `OAI.Erdos3.jointAffineSourceBoundaryRadius`, `OAI.Erdos3.jointAffineSourceMinorThreshold`, `OAI.Erdos3.jointAffineSourceRadius`, `OAI.Erdos3.jointAffineSourceTolerance`, `OAI.Erdos3.jointBooleanDerivativeBudget`, `OAI.Erdos3.jointBooleanDerivativeLog`, `OAI.Erdos3.jointUnitCoefficientSource`, `OAI.Erdos3.jointUnitCoefficientSource_probability`, `OAI.Erdos3.localizedRepresentativeWindow`, `OAI.Erdos3.majorArcBaseLogs_nonneg`, `OAI.Erdos3.majorArcBiasLog`, `OAI.Erdos3.majorArcCoverLog`, `OAI.Erdos3.majorArcCoverLog_nonneg`, `OAI.Erdos3.majorArcErrorLog`, `OAI.Erdos3.majorArcLengthLog`, `OAI.Erdos3.majorArcLocalizationLog`, `OAI.Erdos3.majorArcSpectrumLog`, `OAI.Erdos3.map_integer_coordinates`, `OAI.Erdos3.marginalCap_max_one_exp_bound`, `OAI.Erdos3.mass_div_frequency_count`, `OAI.Erdos3.mem_integerScalarCubeSet`, `OAI.Erdos3.mem_scalarCubeResidueSet`, `OAI.Erdos3.missesBoxCoordinate_head`, `OAI.Erdos3.mixedCoefficientDensity`, `OAI.Erdos3.mixedCoefficientDensity_nonneg`, `OAI.Erdos3.mixedCoefficientDensity_support`, `OAI.Erdos3.mixedCoefficientLaw`, `OAI.Erdos3.mixedCoefficientLaw_count_density`, `OAI.Erdos3.mixedCoefficientLaw_density`, `OAI.Erdos3.mixedCoefficientLaw_probability`, `OAI.Erdos3.mixedDensityInterpolation`, `OAI.Erdos3.mixedDensityInterpolation_bounds`, `OAI.Erdos3.mixedDensityInterpolation_grid`, `OAI.Erdos3.mixedInterpolation_constants_exp_bounds`, `OAI.Erdos3.modeBiasLogPolynomial`, `OAI.Erdos3.modeBiasLogPolynomial_eval`, `OAI.Erdos3.modeProfileLogPolynomial`, `OAI.Erdos3.modeProfileLogPolynomial_eval`, `OAI.Erdos3.modeRankLog`, `OAI.Erdos3.modeRankLogPolynomial`, `OAI.Erdos3.modeRankLogPolynomial_eval`, `OAI.Erdos3.modeRankLog_nonneg`, `OAI.Erdos3.modeRemovalRankThreshold_le_exp`, `OAI.Erdos3.modeShrinkLogPolynomial`, `OAI.Erdos3.modeShrinkLogPolynomial_eval`, `OAI.Erdos3.modeSideLogPolynomial`, `OAI.Erdos3.modeSideLogPolynomial_eval`, `OAI.Erdos3.modeling_dual_zero_weight`, `OAI.Erdos3.nat_div_half_lower`, `OAI.Erdos3.normalizedCoefficientCoordinates_lipschitz`, `OAI.Erdos3.normalizedCoordinateCutoff`, `OAI.Erdos3.normalizedIntegerInterpolation`, `OAI.Erdos3.normalizedIntegerInterpolation_difference`, `OAI.Erdos3.normalizedIntegerInterpolation_grid`, `OAI.Erdos3.normalizedIntegerInterpolation_lipschitz_bound`, `OAI.Erdos3.normalizedIntegerInterpolation_range`, `OAI.Erdos3.normalizedIntegerInterpolation_spec`, `OAI.Erdos3.normalizedIntegerPMF`, `OAI.Erdos3.normalizedIntegerPMF_apply`, `OAI.Erdos3.normalizedIntegerPMF_cap`, `OAI.Erdos3.normalizedIntegerPMF_support`, `OAI.Erdos3.normalizedIntegerRowInterpolation`, `OAI.Erdos3.normalizedJetDensity`, `OAI.Erdos3.normalizedJetOutputRadius`, `OAI.Erdos3.normalizedObservedDensity`, `OAI.Erdos3.normalizedOrthogonalChart`, `OAI.Erdos3.normalizedOrthogonalChart_apply`, `OAI.Erdos3.normalizedOrthogonalChart_integer_coordinates`, `OAI.Erdos3.normalizedOrthogonalChart_norm_le`, `OAI.Erdos3.normalizedOrthogonalChart_symm_norm_le`, `OAI.Erdos3.normalized_finite_weight_approximation`, `OAI.Erdos3.normalized_finite_weight_discard_error`, `OAI.Erdos3.observedProductDensity`, `OAI.Erdos3.orderedFamilyTensor`, `OAI.Erdos3.partitionedIdealRadius_add_one_le_exp`, `OAI.Erdos3.physicalSpatialInverseBound_eq_scalar`, `OAI.Erdos3.physicalSpatialSplitEquiv`, `OAI.Erdos3.polynomialLinearRestriction_denominator_le`, `OAI.Erdos3.polynomialLinearRestriction_denominator_pos`, `OAI.Erdos3.positiveModerateAccuracyLog`, `OAI.Erdos3.positiveModerateAccuracyScale`, `OAI.Erdos3.positiveModerateCoverConstant`, `OAI.Erdos3.positiveModerateCoverExponent`, `OAI.Erdos3.positiveModerateCoverLog`, `OAI.Erdos3.positiveModerateLengthConstant`, `OAI.Erdos3.positiveModerateLengthExponent`, `OAI.Erdos3.positiveModerateLengthLog`, `OAI.Erdos3.positiveModerateLogs_nonneg`, `OAI.Erdos3.positiveModerateRetainedBias`, `OAI.Erdos3.positiveModerateSpectrumBlockCount`, `OAI.Erdos3.positiveModerateSpectrumCardBudget`, `OAI.Erdos3.positiveModerateSpectrumConstant`, `OAI.Erdos3.positiveModerateSpectrumCover`, `OAI.Erdos3.positiveModerateSpectrumExponent`, `OAI.Erdos3.positiveModerateSpectrumLog`, `OAI.Erdos3.positiveRetainedBiasLog`, `OAI.Erdos3.positiveRetainedComplexityLog`, `OAI.Erdos3.positiveRetainedComplexityLog_bounds`, `OAI.Erdos3.positiveRetainedDenominatorBound`, `OAI.Erdos3.positiveRetainedDenominatorLog`, `OAI.Erdos3.positiveRetainedDenominatorLog_nonneg`, `OAI.Erdos3.positiveRetainedFrequencyBound`, `OAI.Erdos3.positiveRetainedFrequencyLog`, `OAI.Erdos3.positiveRetainedLogs_nonneg`, `OAI.Erdos3.positiveSpectrumCardLog`, `OAI.Erdos3.pow_le_exp_mul_of_le_exp`, `OAI.Erdos3.principalIntegerInterpolation`, `OAI.Erdos3.principalIntegerInterpolation_difference`, `OAI.Erdos3.principalIntegerInterpolation_grid`, `OAI.Erdos3.principalIntegerInterpolation_range`, `OAI.Erdos3.principalIntegerInterpolation_spec`, `OAI.Erdos3.principalIntegerPMF`, `OAI.Erdos3.principalIntegerPMF_support`, `OAI.Erdos3.productANOVA`, `OAI.Erdos3.productANOVAEnergy`, `OAI.Erdos3.productANOVASectionEnergy`, `OAI.Erdos3.productANOVASectionTensor`, `OAI.Erdos3.productANOVATensor`, `OAI.Erdos3.productANOVATensorChoices`, `OAI.Erdos3.productANOVATruncation`, `OAI.Erdos3.productConditionalMean`, `OAI.Erdos3.productFiberIndicator`, `OAI.Erdos3.productFiberIndicator_subtype`, `OAI.Erdos3.productFiberIndicator_sum_subtype`, `OAI.Erdos3.productFiberMass`, `OAI.Erdos3.productFiberMass_empty`, `OAI.Erdos3.productFiberMass_nonneg`, `OAI.Erdos3.productKernelApply`, `OAI.Erdos3.productMinorDerivativeLog`, `OAI.Erdos3.productMinorDeterminantLog`, `OAI.Erdos3.productMinorEntryLog`, `OAI.Erdos3.productMinorInverseLog`, `OAI.Erdos3.productMinorPartialLog`, `OAI.Erdos3.productNormalizedSection`, `OAI.Erdos3.productNormalizedSectionWeight`, `OAI.Erdos3.productSectionAverage`, `OAI.Erdos3.productSectionDensityWeight`, `OAI.Erdos3.productSubtypePoint`, `OAI.Erdos3.productSubtypePoint_apply_mem`, `OAI.Erdos3.productTupleIndexEquiv`, `OAI.Erdos3.productTuplePoint`, `OAI.Erdos3.profileWidthFactor_le`, `OAI.Erdos3.progressionSliceLengthLog`, `OAI.Erdos3.rectangular_profile_mass_lower`, `OAI.Erdos3.regularizedTentPartition`, `OAI.Erdos3.regularizedTentPartition_approx`, `OAI.Erdos3.regularizedTentPartition_lipschitz`, `OAI.Erdos3.regularizedTentPartition_range`, `OAI.Erdos3.regularizedTentPartition_sum`, `OAI.Erdos3.regularizedTentPartition_sum_le`, `OAI.Erdos3.regularizedTentPartition_zero`, `OAI.Erdos3.reindexedAffineSource`, `OAI.Erdos3.removedCylinderWeights`, `OAI.Erdos3.representativeWindowCount`, `OAI.Erdos3.representativeWindowPartitionLip`, `OAI.Erdos3.residueIntervalSiteWeight`, `OAI.Erdos3.residueSiteIndicator`, `OAI.Erdos3.retainedSelectedOutputEquiv`, `OAI.Erdos3.scalarCubeDifferenceMatrix`, `OAI.Erdos3.scalarCubeGridDensity`, `OAI.Erdos3.scalarCubeGrid_small_error_of_length`, `OAI.Erdos3.scalarCubeLargeCokernelEvent`, `OAI.Erdos3.scalarCubeProbabilityDensity`, `OAI.Erdos3.scalarCubeResidueDensityCap`, `OAI.Erdos3.scalarCubeResidueDensityCap_pos`, `OAI.Erdos3.scalarCubeResidueReference_mass_lower`, `OAI.Erdos3.scalarCubeResidueSet`, `OAI.Erdos3.scalarCubeResidueSet_card_lower`, `OAI.Erdos3.scalarCubeResidueWeights`, `OAI.Erdos3.scalarCubeResidueWeights_mean`, `OAI.Erdos3.scalarCubeResidue_mass_lower`, `OAI.Erdos3.scalarCubeResidue_mass_pos`, `OAI.Erdos3.scalarCubeRiemannLog`, `OAI.Erdos3.scalarResiduePoint_bound`, `OAI.Erdos3.scalarResiduePoint_cast`, `OAI.Erdos3.scalarSpatialIndexAllowance_le_exp`, `OAI.Erdos3.scalarSpatialInverseAllowance_le_exp`, `OAI.Erdos3.selectedColumn_card`, `OAI.Erdos3.selectedOutputSlice`, `OAI.Erdos3.selectedSplitMeasurableEquiv`, `OAI.Erdos3.shiftedSmoothCoefficientPMF_le`, `OAI.Erdos3.shiftedSmoothCoefficientPMF_support`, `OAI.Erdos3.shiftedSmoothProductFiniteWeights`, `OAI.Erdos3.shiftedSmoothProductFiniteWeights_weight`, `OAI.Erdos3.shiftedSmoothProductMass`, `OAI.Erdos3.shiftedSmoothProductMass_eq_prod`, `OAI.Erdos3.shiftedSmoothProductMass_lower`, `OAI.Erdos3.shiftedSmoothProductPMF`, `OAI.Erdos3.shiftedSmoothProductPMF_shift_transfer`, `OAI.Erdos3.shiftedSmoothProductPMF_shift_transfer_amplitude`, `OAI.Erdos3.shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude`, `OAI.Erdos3.shiftedSmoothProductPMF_toReal`, `OAI.Erdos3.shiftedSmoothProductPMF_toReal_sum`, `OAI.Erdos3.shiftedSmoothProductPMF_toReal_zero_off`, `OAI.Erdos3.shiftedSmoothProductPMF_translation_test_le`, `OAI.Erdos3.shiftedSmoothSampleSum_bounds`, `OAI.Erdos3.sigmaAxisOperatorMap`, `OAI.Erdos3.sigmaAxisOperator_apply`, `OAI.Erdos3.sigmaAxisOperator_norm_le`, `OAI.Erdos3.sigmaAxisProjection_norm_apply_le`, `OAI.Erdos3.siteCoefficientAllowance_le_exp`, `OAI.Erdos3.slicedGridSiteLog`, `OAI.Erdos3.slicedGridSiteLog_bounds`, `OAI.Erdos3.smoothCoefficientResidueWeights`, `OAI.Erdos3.smoothIntegerImagePMF`, `OAI.Erdos3.smoothMatrixImagePMF`, `OAI.Erdos3.smoothResiduePrimeBad`, `OAI.Erdos3.smoothSamplingScale_pos`, `OAI.Erdos3.smoothSourceFiniteWeights`, `OAI.Erdos3.smoothSpatialDiscretizationCost`, `OAI.Erdos3.smoothSpatialDisplacementCost`, `OAI.Erdos3.spatialDiscretizationLog`, `OAI.Erdos3.spatialDisplacementLog`, `OAI.Erdos3.spatialProfileLog`, `OAI.Erdos3.spatialProfileLog_bounds`, `OAI.Erdos3.spatialProfileLog_nonneg`, `OAI.Erdos3.spatialTupleEarlyWidth_inv_bound`, `OAI.Erdos3.spatialTupleTolerance`, `OAI.Erdos3.spatialTupleToleranceLog`, `OAI.Erdos3.spatialTupleToleranceLog_nonneg`, `OAI.Erdos3.spatialTupleTolerance_inv_bound`, `OAI.Erdos3.spatialTupleTolerance_spec`, `OAI.Erdos3.squarefreeEmbeddingHeadEquiv`, `OAI.Erdos3.squarefreePermanent`, `OAI.Erdos3.sum_support_eq_tsum`, `OAI.Erdos3.supportedPMF_event_eq_map_true`, `OAI.Erdos3.trimmedIntegerBox_card_ratio_le_two`, `OAI.Erdos3.twoTermErrorWidth_spec`, `OAI.Erdos3.uniformBlockAccuracyLog`, `OAI.Erdos3.uniformBlockRetainedBias`, `OAI.Erdos3.uniformDualVector`, `OAI.Erdos3.uniformRetainedBiasLog`, `OAI.Erdos3.uniformRetainedDenominatorLog`, `OAI.Erdos3.uniformRetainedFrequencyLog`, `OAI.Erdos3.uniformRetainedLogs_nonneg`, `OAI.Erdos3.uniformSpectrumCardLog`, `OAI.Erdos3.uniformSpectrumLogs_nonneg`, `OAI.Erdos3.uniformSpectrumSizeConstant`, `OAI.Erdos3.uniformSpectrumSizeLog`, `OAI.Erdos3.variableCoefficientLift`, `OAI.Erdos3.variableCoefficientLift_mem_Ico`, `OAI.Erdos3.variableRoundedCoefficient`, `OAI.Erdos3.variableRoundedCoefficient_four_mem`, `OAI.Erdos3.variableRoundingErrors`, `OAI.Erdos3.variableRoundingErrors_card_le`, `OAI.Erdos3.variable_graph_energy`, `OAI.Erdos3.variable_graph_energy_density`, `OAI.Erdos3.vectorSiteAllowance_le_exp`, `OAI.Erdos3.weightedDualVector`, `OAI.Erdos3.weightedDualVector_cap`, `OAI.Erdos3.weightedDualVector_detectable`, `OAI.Erdos3.weightedDualVector_norm`, `OAI.Erdos3.weightedPatchVariableWeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisProjection_norm_apply_le (d : D) (x : (Σ d, I d) → ℝ) :
    ‖sigmaAxisProjection I d x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x ⟨d, i⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaAxisOperator
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] in
theorem sigmaAxisOperator_apply (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) :
    sigmaAxisOperator A x s = A s.1 (sigmaAxisProjection I s.1 x) s.2 := rfl

theorem sigmaAxisOperator_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ d, ‖A d‖ ≤ K) : ‖sigmaAxisOperator A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg x))).mpr
  intro s
  calc
    ‖sigmaAxisOperator A x s‖ ≤ ‖A s.1 (sigmaAxisProjection I s.1 x)‖ := norm_le_pi_norm _ s.2
    _ ≤ ‖A s.1‖ * ‖sigmaAxisProjection I s.1 x‖ := (A s.1).le_opNorm _
    _ ≤ K * ‖x‖ := mul_le_mul (hA s.1) (sigmaAxisProjection_norm_apply_le I s.1 x)
      (norm_nonneg _) hK

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedPairDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def pairDensity (A B : SlicedProductBlock ι) : ℝ → ℝ :=
  affinePairDensity ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (fun p => A.slope p.1) (fun p => B.slope p.2) (fun p => A.base p.1 + B.base p.2)

end Erdos3.SlicedProductBlock

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def pairCapNN {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) : ℝ≥0 := ⟨pairCap A B, (pairCap_pos hA hB).le⟩

noncomputable def fourDensity (A B C D : SlicedProductBlock ι) : ℝ → ℝ :=
  scalarDensityConvolution (pairDensity A B) (pairDensity C D)

noncomputable def uniformCap (ι : Type*) [Fintype ι] (r : ℝ) (hr : 0 < r) : ℝ≥0 :=
  ⟨r⁻¹ * 4 ^ Fintype.card ι, mul_nonneg (inv_nonneg.mpr hr.le) (by positivity)⟩

end Erdos3.SlicedProductBlock

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SpatialProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {P T : Type*} [MeasurableSpace P] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {P ι : Type*} [MeasurableSpace P] [Fintype ι]

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {P ι : Type*} [MeasurableSpace P] [Fintype ι]

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

abbrev PairInput (ι : Type*) := ((ι → ℝ) × (ι → ℝ)) × (ℝ × ℝ)

noncomputable def pairSource (ι : Type*) [Fintype ι] : Measure (PairInput ι) :=
  ((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod
    (unitScalarMeasure.prod unitScalarMeasure)

instance pairSource_probability : IsProbabilityMeasure (pairSource ι) := by
  unfold pairSource
  infer_instance

noncomputable def pairValue (A B : SlicedProductBlock ι) (p : PairInput ι) : ℝ :=
  A.value p.1.1 p.2.1 + B.value p.1.2 p.2.2

abbrev FourInput (ι : Type*) := PairInput ι × PairInput ι

noncomputable def fourSource (ι : Type*) [Fintype ι] : Measure (FourInput ι) :=
  (pairSource ι).prod (pairSource ι)

instance fourSource_probability : IsProbabilityMeasure (fourSource ι) := by
  unfold fourSource
  infer_instance

noncomputable def fourValue (A B C D : SlicedProductBlock ι) (p : FourInput ι) : ℝ :=
  pairValue A B p.2 + pairValue C D p.1

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators NNReal

variable {I : Type*} [Fintype I] {P J : I → Type*}
  [∀ i, MeasurableSpace (P i)] [∀ i, Fintype (J i)]

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

variable {P : Type*} [MeasurableSpace P]

end Erdos3.SlicedProductBlock

end

section

namespace Erdos3

open MeasureTheory SlicedProductBlock
open scoped BigOperators NNReal

variable {η I : Type*} [Fintype η] [Fintype I] {P J : I → Type*}
  [∀ i, MeasurableSpace (P i)] [∀ i, Fintype (J i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def MissesBoxCoordinate {n : ℕ} {X : Type*} (U : (Fin n → X) → ℂ) (i : Fin n) : Prop :=
  ∀ x a, U (Function.update x i a) = U x

theorem missesBoxCoordinate_head {n : ℕ} {X : Type*}
    {U : (Fin (n + 1) → X) → ℂ} (hU : MissesBoxCoordinate U 0)
    (a b : X) (x : Fin n → X) : U (Fin.cons a x) = U (Fin.cons b x) := by
  simpa only [Fin.update_cons_zero] using hU (Fin.cons b x) a

noncomputable def boxTailPhase {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (a b : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * star (F (Fin.cons b x))

noncomputable def boxTailTests {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ) (a b : X)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  U i.succ (Fin.cons a x) * star (U i.succ (Fin.cons b x))

theorem boxTailTests_misses {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i, MissesBoxCoordinate (U i) i) (a b : X) (i : Fin n) :
    MissesBoxCoordinate (boxTailTests U a b i) i := by
  intro x c
  simp only [boxTailTests, Fin.cons_update]
  rw [hU i.succ (Fin.cons a x) c, hU i.succ (Fin.cons b x) c]

theorem boxTailTests_norm {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (a b : X) (i : Fin n) (x : Fin n → X) :
    ‖boxTailTests U a b i x‖ ≤ 1 := by
  rw [boxTailTests, norm_mul, norm_star]
  exact (mul_le_mul (hU _ _) (hU _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

noncomputable def boxTestCorrelation {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) (U : Fin n → (Fin n → X) → ℂ) : ℂ :=
  𝔼 x, F x * ∏ i, U i x

theorem boxTestCorrelation_zero {X : Type*} [Fintype X]
    (F : (Fin 0 → X) → ℂ) (U : Fin 0 → (Fin 0 → X) → ℂ) :
    boxTestCorrelation F U = F (fun i => Fin.elim0 i) := by
  simp only [boxTestCorrelation, Fin.prod_univ_zero, mul_one, expect_empty_tuple]

noncomputable def boxPhaseMoment {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin n → X) → ℂ) : ℂ :=
  𝔼 u, 𝔼 v, iteratedBoxDifference n (fun x (_ : Unit) => F x) u v ()

theorem boxPhaseMoment_zero {X : Type*} [Fintype X] (F : (Fin 0 → X) → ℂ) :
    boxPhaseMoment 0 F = F (fun i => Fin.elim0 i) := by
  simp only [boxPhaseMoment, iteratedBoxDifference, Fintype.expect_const]

theorem boxPhaseMoment_succ {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin (n + 1) → X) → ℂ) :
    boxPhaseMoment (n + 1) F = 𝔼 a, 𝔼 b, boxPhaseMoment n (boxTailPhase F a b) := by
  rw [boxPhaseMoment, expect_two_dependent_fin_cons]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxCorner {n : ℕ} {X : Type*} (u v : Fin n → X) (ω : Fin n → Bool) : Fin n → X :=
  fun i => if ω i then v i else u i

def boxCornerProduct {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) : ℂ :=
  ∏ ω : Fin n → Bool, conjugationPower (booleanWeight ω) (F (boxCorner u v ω))

theorem conjugationPower_eq_if_mod (n : ℕ) (z : ℂ) :
    conjugationPower n z = if n % 2 = 0 then z else star z := by
  induction n with
  | zero => simp [conjugationPower]
  | succ n ih =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;>
      simp [conjugationPower, ih, Nat.add_mod, hn]

theorem boxCorner_cons_false {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons false ω) = Fin.cons (u 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem boxCorner_cons_true {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons true ω) = Fin.cons (v 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem boxCornerProduct_mul {n : ℕ} {X : Type*} (F G : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F x * G x) u v = boxCornerProduct F u v * boxCornerProduct G u v := by
  simp only [boxCornerProduct, map_mul, Finset.prod_mul_distrib]

theorem boxCornerProduct_star {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => star (F x)) u v = star (boxCornerProduct F u v) := by
  simp only [boxCornerProduct, conjugationPower_star, star_prod]

theorem boxCornerProduct_succ {n : ℕ} {X : Type*} (F : (Fin (n + 1) → X) → ℂ)
    (u v : Fin (n + 1) → X) :
    boxCornerProduct F u v =
      boxCornerProduct (fun x => F (Fin.cons (u 0) x)) (Fin.tail u) (Fin.tail v) *
        star (boxCornerProduct (fun x => F (Fin.cons (v 0) x)) (Fin.tail u) (Fin.tail v)) := by
  simp only [boxCornerProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true, boxCorner_cons_false,
    boxCorner_cons_true, conjugationPower, RingHom.comp_apply, starRingEnd_apply, star_prod]

theorem iteratedBoxDifference_eq_cornerProduct {X Z : Type*} (n : ℕ)
    (F : (Fin n → X) → Z → ℂ) (u v : Fin n → X) (z : Z) :
    iteratedBoxDifference n F u v z = boxCornerProduct (fun x => F x z) u v := by
  induction n with
  | zero =>
    rw [boxCornerProduct, Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
    simp only [booleanWeight, Fin.sum_univ_zero, conjugationPower, RingHom.id_apply, iteratedBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [iteratedBoxDifference, ih, boxCornerProduct_mul, boxCornerProduct_star, boxCornerProduct_succ]

theorem boxPhaseMoment_eq_expect_cornerProduct {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) :
    boxPhaseMoment n F = 𝔼 u, 𝔼 v, boxCornerProduct F u v := by
  simp only [boxPhaseMoment, iteratedBoxDifference_eq_cornerProduct]

theorem boxCornerProduct_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F (fun i => φ (x i))) u v =
      boxCornerProduct F (fun i => φ (u i)) (fun i => φ (v i)) := by
  unfold boxCornerProduct
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  change F (fun i => φ (boxCorner u v ω i)) =
    F (boxCorner (fun i => φ (u i)) (fun i => φ (v i)) ω)
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def boxTailAmplitude {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * ∏ i : Fin n, U i.succ (Fin.cons a x)

theorem boxTailAmplitude_cross {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a b : X) (x : Fin n → X) :
    boxTailAmplitude F U a x * star (boxTailAmplitude F U b x) =
      boxTailPhase F a b x * ∏ i, boxTailTests U a b i x := by
  simp only [boxTailAmplitude, boxTailPhase, boxTailTests, star_mul, star_prod,
    Finset.prod_mul_distrib]
  ring

theorem boxTestCorrelation_head {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : MissesBoxCoordinate (U 0) 0) (base : X) :
    boxTestCorrelation F U =
      𝔼 x : Fin n → X, U 0 (Fin.cons base x) * (𝔼 a, boxTailAmplitude F U a x) := by
  rw [boxTestCorrelation, expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro a _
  rw [Fin.prod_univ_succ, missesBoxCoordinate_head hU a base x]
  unfold boxTailAmplitude
  ring

theorem boxTestCorrelation_square_le {n : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ x, ‖U 0 x‖ ≤ 1) (hmiss : MissesBoxCoordinate (U 0) 0) :
    ‖boxTestCorrelation F U‖ ^ 2 ≤
      (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re := by
  let base : X := Classical.choice inferInstance
  have h := finite_family_cauchy_schwarz_re
    (fun x : Fin n → X => U 0 (Fin.cons base x)) (boxTailAmplitude F U)
    (fun x => hU (Fin.cons base x))
  rw [← boxTestCorrelation_head F U hmiss base] at h
  simp only [one_pow, one_mul] at h
  simp_rw [boxTailAmplitude_cross] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxCornerAnchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) : ℂ := by
  classical
  exact ∏ ω ∈ (Finset.univ.erase (fun _ : Fin n => false)),
    conjugationPower (booleanWeight ω) (F (boxCorner z a ω))

theorem boxCornerProduct_eq_mul_anchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (z a : Fin n → X) :
    boxCornerProduct F z a = F z * boxCornerAnchor F a z := by
  classical
  have h := (Finset.mul_prod_erase Finset.univ
    (fun ω => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))
    (Finset.mem_univ (fun _ : Fin n => false))).symm
  have hz : boxCorner z a (fun _ => false) = z := rfl
  simpa [boxCornerProduct, boxCornerAnchor, booleanWeight, hz, conjugationPower] using h

theorem boxCornerAnchor_norm_le_one {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (hF : ∀ z, ‖F z‖ ≤ 1) (a z : Fin n → X) :
    ‖boxCornerAnchor F a z‖ ≤ 1 := by
  classical
  unfold boxCornerAnchor
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_eq_if_mod]
  split_ifs <;> simpa only [norm_star] using hF (boxCorner z a ω)

theorem boxCornerAnchor_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (a z : Fin n → X) :
    boxCornerAnchor (fun x => F (fun i => φ (x i))) a z =
      boxCornerAnchor F (fun i => φ (a i)) (fun i => φ (z i)) := by
  classical
  unfold boxCornerAnchor
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

theorem boxCornerAnchor_prod_equiv {n m : ℕ} {X : Type*}
    (e : Fin m ≃ (Finset.univ.erase (fun _ : Fin n => false)))
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) :
    (∏ l, conjugationPower (booleanWeight (e l).val) (F (boxCorner z a (e l).val))) =
      boxCornerAnchor F a z := by
  classical
  calc
    _ = ∏ ω : (Finset.univ.erase (fun _ : Fin n => false)),
        conjugationPower (booleanWeight ω.val) (F (boxCorner z a ω.val)) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      unfold boxCornerAnchor
      exact Finset.prod_coe_sort (Finset.univ.erase (fun _ : Fin n => false))
        (fun ω : Fin n → Bool => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))

theorem exists_box_corner_anchor_correlation {n : ℕ} {X : Type*}
    [Fintype X] [Nonempty X] (F : (Fin n → X) → ℂ) :
    ∃ a : Fin n → X, (boxPhaseMoment n F).re ≤
      ‖𝔼 z : Fin n → X, F z * boxCornerAnchor F a z‖ := by
  have hm : boxPhaseMoment n F =
      𝔼 a : Fin n → X, 𝔼 z : Fin n → X, F z * boxCornerAnchor F a z := by
    rw [boxPhaseMoment_eq_expect_cornerProduct, Finset.expect_comm]
    simp_rw [boxCornerProduct_eq_mul_anchor]
  have hmean : (boxPhaseMoment n F).re =
      𝔼 a : Fin n → X, (𝔼 z : Fin n → X, F z * boxCornerAnchor F a z).re := by
    rw [hm, expect_re]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

theorem exists_true_of_ne_false {n : ℕ} {ω : Fin n → Bool}
    (h : ω ≠ fun _ => false) : ∃ k, ω k = true := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  refine ⟨k, ?_⟩
  cases he : ω k <;> simp_all

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boxTest_cauchySchwarz {X : Type*} [Fintype X] [Nonempty X] (n : ℕ) :
    ∀ (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ),
      (∀ i x, ‖U i x‖ ≤ 1) → (∀ i, MissesBoxCoordinate (U i) i) →
      ‖boxTestCorrelation F U‖ ^ (2 ^ (n + 1)) ≤ (boxPhaseMoment (n + 1) F).re := by
  induction n with
  | zero =>
    intro F U hU hmiss
    simpa only [Nat.zero_add, pow_one, boxPhaseMoment_succ,
      boxPhaseMoment_zero, boxTestCorrelation_zero] using
      boxTestCorrelation_square_le F U (hU 0) (hmiss 0)
  | succ n ih =>
    intro F U hU hmiss
    have hr : (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re ≤
        𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ := by
      simp only [expect_re]
      apply Finset.expect_le_expect
      intro a _
      apply Finset.expect_le_expect
      intro b _
      exact Complex.re_le_norm _
    have hcs := (boxTestCorrelation_square_le F U (hU 0) (hmiss 0)).trans hr
    calc
      _ = (‖boxTestCorrelation F U‖ ^ 2) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]
        congr 1
        omega
      _ ≤ (𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖) ^
          (2 ^ (n + 1)) := pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ ^
          (2 ^ (n + 1)) := expect_double_pow_two_pow_le (n + 1) _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a, 𝔼 b, (boxPhaseMoment (n + 1) (boxTailPhase F a b)).re := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih _ _ (boxTailTests_norm U hU a b) (boxTailTests_misses U hmiss a b)
      _ = _ := by rw [boxPhaseMoment_succ]; simp only [expect_re]

theorem boxTest_cauchySchwarz_of_pos {X : Type*} [Fintype X] [Nonempty X] {h : ℕ}
    (hh : 0 < h) (F : (Fin h → X) → ℂ) (U : Fin h → (Fin h → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (hmiss : ∀ i, MissesBoxCoordinate (U i) i) :
    ‖boxTestCorrelation F U‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  exact boxTest_cauchySchwarz n F U hU hmiss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def assignedBoxTest {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  ∏ s, if assignment s = i then U s x else 1

theorem assignedBoxTest_prod {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ) (x : Fin n → X) :
    (∏ i, assignedBoxTest assignment U i x) = ∏ s, U s x := by
  unfold assignedBoxTest
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  simp

theorem assignedBoxTest_norm {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s x, ‖U s x‖ ≤ 1) (i : Fin n) (x : Fin n → X) :
    ‖assignedBoxTest assignment U i x‖ ≤ 1 := by
  rw [assignedBoxTest, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro s _
  split_ifs
  · exact hU s x
  · simp only [norm_one, le_refl]

theorem assignedBoxTest_misses {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s, MissesBoxCoordinate (U s) (assignment s)) (i : Fin n) :
    MissesBoxCoordinate (assignedBoxTest assignment U i) i := by
  intro x a
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : assignment s = i
  · simp only [hs, ite_true]
    simpa only [hs] using hU s x a
  · simp only [hs, ite_false]

theorem assigned_site_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (F : (Fin h → X) → ℂ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, F x * ∏ s, U s x‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  have hc := boxTest_cauchySchwarz_of_pos hh F (assignedBoxTest assignment U)
    (assignedBoxTest_norm assignment U hU) (assignedBoxTest_misses assignment U hmiss)
  simpa only [boxTestCorrelation, assignedBoxTest_prod] using hc

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds
namespace OAI

section

namespace Erdos3

theorem smoothSamplingScale_pos {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  linarith

theorem shiftedSmoothSampleSum_bounds (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    S / 2 ≤ shiftedSmoothSampleSum a S ∧ shiftedSmoothSampleSum a S ≤ 3 * S / 2 := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have hS0 := smoothSamplingScale_pos hS
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ hS0).mpr (by linarith)
  have hb := abs_le.mp (he.trans hsmall)
  have hlo : (1 / 2 : ℝ) ≤ shiftedSmoothSampleSum a S / S := by linarith [hb.1]
  have hhi : shiftedSmoothSampleSum a S / S ≤ (3 / 2 : ℝ) := by linarith [hb.2]
  constructor
  · linarith [(le_div_iff₀ hS0).mp hlo]
  · linarith [(div_le_iff₀ hS0).mp hhi]

theorem shiftedSmoothCoefficientPMF_le (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S (smoothSamplingScale_pos hS)
      (shiftedSmoothSampleSum_pos a hS) k).toReal ≤ 2 / S := by
  rw [shiftedSmoothCoefficientPMF_apply]
  have hZ := shiftedSmoothSampleSum_pos a hS
  calc
    _ ≤ 1 / shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right (smoothProbabilityProfile_range _).2 hZ.le
    _ ≤ 2 / S := (div_le_div_iff₀ hZ (smoothSamplingScale_pos hS)).mpr
      (by linarith [(shiftedSmoothSampleSum_bounds a hS).1])

theorem shiftedSmoothCoefficientPMF_support (a : ℝ) {S : ℝ} (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) {k : ℤ}
    (hk : k ∈ (shiftedSmoothCoefficientPMF a S hS hZ).support) :
    |(k : ℝ) - a| < 3 * S / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hS]
    apply (le_div_iff₀ hS).mpr
    linarith
  apply hk
  change ENNReal.ofReal (smoothProbabilityProfile (((k : ℝ) - a) / S) /
    shiftedSmoothSampleSum a S) = 0
  simp only [hz, zero_div, ENNReal.ofReal_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem rectangular_profile_mass_lower {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hintegral : (∫ x, f x) = 1)
    (hsmall : (2 * R + 2) ^ Fintype.card I * L * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ ∑' k, rectangularWeight f a S k := by
  have he := rectangularLattice_quadrature f hf a S hS hR hδ hδ1 hmesh hsupport
  rw [hintegral] at he
  have hp : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => hS i)
  have hnorm : (1 / 2 : ℝ) ≤ (∑' k, rectangularWeight f a S k) / ∏ i, S i := by
    have hh := (abs_le.mp he).1
    change -((2 * R + 2) ^ Fintype.card I * L * δ) ≤
      (∑' k, rectangularWeight f a S k) / (∏ i, S i) - 1 at hh
    linarith
  have h := (le_div_iff₀ hp).mp hnorm
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def shiftedSmoothProductMass {I : Type*} [Fintype I]
    (a S : I → ℝ) : ℝ := ∑' x, rectangularWeight (smoothProductProfile I) a S x

theorem shiftedSmoothProductMass_eq_prod {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    shiftedSmoothProductMass a S = ∏ i, shiftedSmoothSampleSum (a i) (S i) :=
  shiftedSmoothProductSamples_sum a S hS

theorem shiftedSmoothProductMass_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2) :
    (∏ i, S i) / 2 ≤ shiftedSmoothProductMass a S := by
  apply rectangular_profile_mass_lower (smoothProductProfile I) (smoothProductProfile_lipschitz I)
    a S hS zero_le_one hδ hδ1 hmesh (smoothProductProfile_zero_outside I)
    (smoothProductProfile_integral I)
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, show 2 * (1 : ℝ) + 2 = 4 by norm_num] using hsmall

noncomputable def shiftedSmoothProductPMF {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) : PMF (I → ℤ) :=
  realWeightPMF (rectangularWeight (smoothProductProfile I) a S)
    (fun _ => (smoothProductProfile_range I _).1)
    (rectangularWeight_summable _ a S hS (smoothProductProfile_zero_outside I)) hZ

theorem shiftedSmoothProductPMF_toReal {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (x : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal =
      rectangularWeight (smoothProductProfile I) a S x / shiftedSmoothProductMass a S :=
  realWeightPMF_apply _ _ _ _ x

theorem shiftedSmoothProductPMF_toReal_sum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    (∑' x, (shiftedSmoothProductPMF a S hS hZ x).toReal) = 1 := by
  simp only [shiftedSmoothProductPMF_toReal, tsum_div_const]
  exact div_self hZ.ne'

theorem shiftedSmoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : I → ℤ) (hx : x ∉ rectangularWeightIndices a S 1) :
    (shiftedSmoothProductPMF a S hS hZ x).toReal = 0 := by
  rw [shiftedSmoothProductPMF_toReal,
    rectangularWeight_zero_off_indices _ a S hS (smoothProductProfile_zero_outside I) x hx,
    zero_div]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ext_weight {Ω : Type*} [Fintype Ω] {p q : FiniteProbabilityWeights Ω}
    (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem mass_inter_pos_of_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) : 0 < p.mass (G ∩ R) := by
  rw [condition_mass] at hR
  exact (div_pos_iff_of_pos_right hG).mp hR

theorem condition_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) :
    (p.condition G hG).condition R hR =
      p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR) := by
  have hw : ((p.condition G hG).condition R hR).weight =
      (p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR)).weight := by
    funext x
    change (if x ∈ R then (if x ∈ G then p.weight x else 0) / p.mass G else 0) /
        (p.condition G hG).mass R =
      (if x ∈ G ∩ R then p.weight x else 0) / p.mass (G ∩ R)
    rw [condition_mass]
    by_cases hxG : x ∈ G <;> by_cases hxR : x ∈ R <;>
      simp [hxG, hxR, div_div_div_cancel_right₀ hG.ne']
  exact ext_weight hw

theorem uniform_condition_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] (G R : Finset Ω) (hG : 0 < (uniform Ω).mass G)
    (hR : 0 < ((uniform Ω).condition G hG).mass R) (f : Ω → ℝ) :
    (((uniform Ω).condition G hG).condition R hR).mean f = 𝔼 x : ↥(G ∩ R), f x := by
  rw [condition_condition]
  exact uniform_condition_mean _ _ f

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_mem {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) :
    p.eventProbability (fun x => x ∈ G) = p.mass G := by
  classical
  simp [eventProbability, mean, mass, mul_ite]

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

def piRestrictionSet (G : ∀ j, Finset (Ω j)) : Finset (∀ j, Ω j) :=
  Finset.univ.filter (fun x => ∀ j, x j ∈ G j)

theorem mem_piRestrictionSet (G : ∀ j, Finset (Ω j)) (x : ∀ j, Ω j) :
    x ∈ piRestrictionSet G ↔ ∀ j, x j ∈ G j := by
  simp only [piRestrictionSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem piRestriction_mass (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) : (pi p).mass (piRestrictionSet G) = ∏ j, (p j).mass (G j) := by
  classical
  rw [← eventProbability_mem]
  have hE : (fun x : ∀ j, Ω j => x ∈ piRestrictionSet G) =
      (fun x => ∀ j, x j ∈ G j) := by
    funext x
    exact propext (mem_piRestrictionSet G x)
  rw [hE, eventProbability_pi]
  exact Finset.prod_congr rfl (fun j _ => eventProbability_mem (p j) (G j))

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

def integerScalarCubeValue {I : Type*} [Fintype I] (x : Option I → ℤ) (t : Finset I) : ℤ :=
  x none + ∑ i ∈ t, x (some i)

def IntegerScalarCube {I : Type*} [Fintype I] (L : ℕ) (x : Option I → ℤ) : Prop :=
  ∀ t : Finset I, 0 ≤ integerScalarCubeValue x t ∧ integerScalarCubeValue x t < L

abbrev IntegerScalarCubeBox (I : Type*) (L : ℕ) :=
  Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)

noncomputable def integerScalarCubeSet (I : Type*) [Fintype I] (L : ℕ) :
    Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => IntegerScalarCube L (fun i => (x i : ℤ)))

theorem mem_integerScalarCubeSet {I : Type*} [Fintype I] (L : ℕ)
    (x : IntegerScalarCubeBox I L) :
    x ∈ integerScalarCubeSet I L ↔ IntegerScalarCube L (fun i => (x i : ℤ)) := by
  classical
  simp [integerScalarCubeSet]

theorem integerScalarCube_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} {x : Option I → ℤ} (hx : IntegerScalarCube L x) (i : Option I) :
    -(L : ℤ) < x i ∧ x i < L := by
  have h0 := hx ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
  cases i with
  | none => omega
  | some i =>
    have h1 := hx {i}
    simp only [integerScalarCubeValue, Finset.sum_singleton] at h1
    omega

theorem integerScalarCube_small_positive {I : Type*} [Fintype I] {L H : ℕ}
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) (x : Option I → Fin H) :
    IntegerScalarCube L (fun i => ((x i).val : ℤ)) := by
  intro t
  have ht : t.card ≤ Fintype.card I := Finset.card_le_univ t
  have hx (i : Option I) : (0 : ℤ) ≤ (x i).val ∧ ((x i).val : ℤ) ≤ (H : ℤ) - 1 := by
    exact ⟨Nat.cast_nonneg _, by have := (x i).isLt; omega⟩
  have hsum0 : (0 : ℤ) ≤ ∑ i ∈ t, ((x (some i)).val : ℤ) :=
    Finset.sum_nonneg (fun i _ => (hx (some i)).1)
  have hsum : (∑ i ∈ t, ((x (some i)).val : ℤ)) ≤ (t.card : ℤ) * ((H : ℤ) - 1) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i (_ : i ∈ t) => (hx (some i)).2))
  have hHL' : ((Fintype.card I : ℤ) + 1) * H ≤ L := by exact_mod_cast hHL
  have ht' : (t.card : ℤ) ≤ Fintype.card I := by exact_mod_cast ht
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  dsimp [integerScalarCubeValue]
  constructor
  · exact add_nonneg (hx none).1 hsum0
  · have h0 := (hx none).2
    have hmul := mul_le_mul_of_nonneg_right ht' (sub_nonneg.mpr hH')
    nlinarith [show (0 : ℤ) ≤ Fintype.card I from Nat.cast_nonneg _]

end Erdos3

namespace Erdos3

def integerScalarCubeBoxZero (I : Type*) (L : ℕ) (hL : 0 < L) : IntegerScalarCubeBox I L :=
  fun _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast hL⟩⟩

theorem integerScalarCubeSet_nonempty (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeSet I L).Nonempty := by
  refine ⟨integerScalarCubeBoxZero I L hL, (mem_integerScalarCubeSet L _).mpr ?_⟩
  intro t
  simp only [integerScalarCubeValue, integerScalarCubeBoxZero, Finset.sum_const_zero, add_zero]
  exact ⟨le_rfl, by exact_mod_cast hL⟩

theorem integerScalarCubeBox_card (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) :
    Fintype.card (IntegerScalarCubeBox I L) = (2 * L) ^ (Fintype.card I + 1) := by
  change Fintype.card (Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)) = _
  rw [Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Int.card_Ico]
  congr 1
  omega

theorem nat_div_half_lower {L n : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    L ≤ 2 * n * (L / n) := by
  have hd : 0 < L / n := Nat.div_pos hL hn
  have hm := Nat.mod_lt L hn
  have he := Nat.div_add_mod L n
  nlinarith

theorem integerScalarCube_iff_supported (q L : ℕ) (x : Option (Fin q) → ℤ) :
    IntegerScalarCube L x ↔ ∀ ω : Fin q → Bool,
      x none + cubeShift (fun i => x (some i)) ω ∈ Set.Ico (0 : ℤ) (L : ℤ) := by
  classical
  constructor
  · intro h ω
    have hx := h (Finset.univ.filter (fun i => ω i))
    simpa only [integerScalarCubeValue, Finset.sum_filter, cubeShift, Set.mem_Ico] using hx
  · intro h t
    have hx := h (fun i => decide (i ∈ t))
    simpa [integerScalarCubeValue, cubeShift] using hx

noncomputable def integerScalarCubeEquiv (q L : ℕ) :
    ↥(integerScalarCubeSet (Fin q) L) ≃ SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := ⟨(fun i => (x.val (some i) : ℤ), (x.val none : ℤ)),
    (integerScalarCube_iff_supported q L _).mp ((mem_integerScalarCubeSet L _).mp x.property)⟩
  invFun p := by
    let v : Option (Fin q) → ℤ := fun | none => p.val.2 | some i => p.val.1 i
    have hv : IntegerScalarCube L v := (integerScalarCube_iff_supported q L v).mpr p.property
    let x : IntegerScalarCubeBox (Fin q) L := fun i =>
      ⟨v i, Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hv i).1.le,
        (integerScalarCube_coordinates hv i).2⟩⟩
    exact ⟨x, (mem_integerScalarCubeSet L x).mpr hv⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

noncomputable def integerScalarCubeReference (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform _

theorem integerScalarCubeReference_mass (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) =
      ((integerScalarCubeSet I L).card : ℝ) / Fintype.card (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  unfold integerScalarCubeReference
  exact FiniteProbabilityWeights.uniform_mass _

theorem integerScalarCubeReference_mass_pos (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    0 < (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
  exact div_pos (by exact_mod_cast (integerScalarCubeSet_nonempty I L hL).card_pos)
    (by positivity)

noncomputable def integerScalarCubeDensityCap (I : Type*) [Fintype I] : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) : ℝ) ^ (Fintype.card I + 1)

noncomputable def integerScalarCubeWeights (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeReference I L hL).condition (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL)

noncomputable def scalarCubeResidueSet (I : Type*) [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => ∀ i, ((x i : ℤ) : ZMod (m i)) = r i)

theorem mem_scalarCubeResidueSet {I : Type*} [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (x : IntegerScalarCubeBox I L) :
    x ∈ scalarCubeResidueSet I L m r ↔ ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  simp only [scalarCubeResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem scalarResiduePoint_bound (m H : ℕ) (hm : 0 < m) (r : ZMod m) (x : Fin H) :
    r.val + m * x.val < m * H := by
  let : NeZero m := ⟨hm.ne'⟩
  have hr := ZMod.val_lt r
  have hx := x.isLt
  nlinarith

theorem scalarResiduePoint_cast (m : ℕ) (hm : 0 < m) (r : ZMod m) (x : ℕ) :
    ((r.val + m * x : ℕ) : ZMod m) = r := by
  let : NeZero m := ⟨hm.ne'⟩
  simp

theorem scalarCubeResidueSet_card_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M H : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hH : 0 < H)
    (hbudget : (Fintype.card I + 1) * (M * H) ≤ L) :
    H ^ (Fintype.card I + 1) ≤ ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  classical
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hML : M * H ≤ L := by nlinarith
  let point (x : Option I → Fin H) (i : Option I) : Fin (M * H) :=
    ⟨(r i).val + m i * (x i).val,
      (scalarResiduePoint_bound (m i) H (hm i) (r i) (x i)).trans_le (Nat.mul_le_mul_right H (hmM i))⟩
  let tuple (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((point x i).val : ℤ), Finset.mem_Ico.mpr
      ⟨by omega, by have := (point x i).isLt; omega⟩⟩
  have hmem (x : Option I → Fin H) :
      tuple x ∈ (integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_integerScalarCubeSet L _).mpr
        (integerScalarCube_small_positive (Nat.mul_pos hM hH) hbudget (point x))
    · apply (mem_scalarCubeResidueSet L m r _).mpr
      intro i
      change ((((r i).val + m i * (x i).val : ℕ) : ℤ) : ZMod (m i)) = r i
      simpa only [Int.cast_natCast] using scalarResiduePoint_cast (m i) (hm i) (r i) (x i).val
  let e : (Option I → Fin H) → ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) :=
    fun x => ⟨tuple x, hmem x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h
    change (((r i).val + m i * (x i).val : ℕ) : ℤ) = (((r i).val + m i * (y i).val : ℕ) : ℤ) at hi
    have hi' : (r i).val + m i * (x i).val = (r i).val + m i * (y i).val := by exact_mod_cast hi
    exact mul_left_cancel₀ (hm i).ne' (Nat.add_left_cancel hi')
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc

open scoped BigOperators Classical

end Erdos3

namespace Erdos3

def scalarCubeDifferenceMatrix {I J : Type*} {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) : Matrix I J ℤ :=
  sampledColumnMatrix (fun _j y i => (y (some i) : ℤ)) x

def scalarCubeLargeCokernelEvent {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  (∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
    B < integerCokernelExponent (scalarCubeDifferenceMatrix x).mulVecLin.range

open scoped BigOperators

end Erdos3

namespace Erdos3

noncomputable def scalarCubeResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  (4 * (Fintype.card I + 1 : ℕ) * (M : ℝ)) ^ (Fintype.card I + 1)

theorem scalarCubeResidueDensityCap_pos (I : Type*) [Fintype I] (M : ℕ) (hM : 0 < M) :
    0 < scalarCubeResidueDensityCap I M := by
  unfold scalarCubeResidueDensityCap
  positivity

theorem scalarCubeResidueReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass
        ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let n := Fintype.card I + 1
  let H := L / (n * M)
  have hn : 0 < n := by dsimp [n]; omega
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hH : 0 < H := Nat.div_pos hsize (Nat.mul_pos hn hM)
  have hHL : n * (M * H) ≤ L := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le L (n * M)
  have hc := scalarCubeResidueSet_card_lower I L M H m r hm hmM hH hHL
  have hfloor : (L : ℝ) ≤ 2 * ((n : ℝ) * M) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower (Nat.mul_pos hn hM) hsize
  have hratio : 1 / (4 * (n : ℝ) * M) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  calc
    _ = (1 / (4 * (n : ℝ) * M)) ^ n := by
      simp only [scalarCubeResidueDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      unfold integerScalarCubeReference
      rw [FiniteProbabilityWeights.uniform_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem scalarCubeResidue_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) := by
  exact (scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize).trans
    (FiniteProbabilityWeights.mass_inter_le_condition_mass _ _ _ _)

theorem scalarCubeResidue_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) :=
  (inv_pos.mpr (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))).trans_le
    (scalarCubeResidue_mass_lower I L M hL m r hm hmM hsize)

open scoped BigOperators

noncomputable def scalarCubeResidueWeights (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeWeights I L hL).condition (scalarCubeResidueSet I L m r)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize)

theorem scalarCubeResidueWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) (f : IntegerScalarCubeBox I L → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean f =
      𝔼 x : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r), f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_condition_mean _ _
    (integerScalarCubeReference_mass_pos I L hL)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize) f

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def normalizedJetDensity {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : P → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity A
    (splitFreeColumns F (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x))
    (splitFreeProfile f g)

end Erdos3

namespace Erdos3

open scoped NNReal

noncomputable def normalizedJetOutputRadius {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) : ℝ≥0 :=
  (‖A.toContinuousLinearMap‖₊+‖F‖₊)*R + (Fintype.card N * normalizedJetMass α degree)*S

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerImage
namespace OAI

section

namespace Erdos3

open scoped Matrix

noncomputable def smoothMatrixImagePMF {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (S : J → ℝ) (hS : ∀ j, 0 < S j) : PMF (O → ℤ) :=
  (smoothProductPMF S hS).map (fun z => A *ᵥ z)

noncomputable def smoothIntegerImagePMF {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) : PMF (I → ℤ) :=
  integerImagePMF A B (smoothSplitProfile J I)
    (fun p => (smoothSplitProfile_range J I p).1) S T hS hT
    (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem profileWidthFactor_le {I : Type*} [Fintype I] (w : I → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    profileWidthFactor w ≤ δ⁻¹ ^ Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, δ⁻¹ := Finset.prod_le_prod
      (fun i _ => inv_nonneg.mpr (hδ.le.trans (hw i))) (fun i _ => inv_anti₀ hδ (hw i))
    _ = _ := by simp

theorem normalizedCoefficientCoordinates_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith δ⁻¹ (fun x : I → ℝ => fun i => (x i - c i) / w i) := by
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖(x i-c i)/w i - (y i-c i)/w i‖ ≤ _
  rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div,
    abs_of_pos (hδr.trans_le (hw i))]
  calc
    _ ≤ ‖x-y‖ / w i := div_le_div_of_nonneg_right
      (norm_le_pi_norm (x-y) i) (hδr.le.trans (hw i))
    _ ≤ ‖x-y‖ / (δ : ℝ) := div_le_div_of_nonneg_left (norm_nonneg _) hδr (hw i)
    _ = _ := by simp only [NNReal.coe_inv, dist_eq_norm, div_eq_mul_inv]; ring

noncomputable def affineProductProfileLip (I : Type*) [Fintype I] (δ : ℝ≥0) : ℝ≥0 :=
  Fintype.card I * probabilityProfileLipschitz * δ⁻¹ ^ (Fintype.card I + 1)

theorem affineProductProfile_lipschitz {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) :
    LipschitzWith (affineProductProfileLip I δ) (affineProductProfile c w) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwp := profileWidthFactor_pos w (fun i => hδr.trans_le (hw i))
  have hl := (smoothProductProfile_lipschitz I).comp
    (normalizedCoefficientCoordinates_lipschitz c w hδ hw)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hl.dist_le_mul x y
  rw [Real.dist_eq] at hb ⊢
  rw [affineProductProfile_eq, affineProductProfile_eq, ← mul_sub, abs_mul, abs_of_pos hwp]
  calc
    _ ≤ profileWidthFactor w *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left hb hwp.le
    _ ≤ (δ : ℝ)⁻¹ ^ Fintype.card I *
        (((Fintype.card I * probabilityProfileLipschitz * δ⁻¹ : ℝ≥0) : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_right (profileWidthFactor_le w hδr hw) (by positivity)
    _ = _ := by
      simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
        NNReal.coe_inv, pow_succ]
      ring

theorem affineProductProfile_cap {I : Type*} [Fintype I]
    (c w : I → ℝ) {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    ∀ x, ‖affineProductProfile c w x‖ ≤ δ⁻¹ ^ Fintype.card I :=
  fun x => (affineProductProfile_norm_le c w (fun i => hδ.trans_le (hw i)) x).trans
    (profileWidthFactor_le w hδ hw)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem pow_le_exp_mul_of_le_exp {x Q P : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp Q)
    (hQ : 0 ≤ Q) (n : ℕ) (hn : (n : ℝ) ≤ P) : x^n ≤ Real.exp (P*Q) := by
  calc
    _ ≤ (Real.exp Q)^n := pow_le_pow_left₀ hx0 hx _
    _ = Real.exp ((n : ℝ)*Q) := (Real.exp_nat_mul Q n).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn hQ)

theorem mixedInterpolation_constants_exp_bounds {I : Type*} [Fintype I] (n : ℕ)
    {δ B L : ℝ≥0} {P W Q : ℝ} (hP : 0 ≤ P) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hI : (Fintype.card I : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hδ : ((δ⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp W)
    (hB : (B : ℝ) ≤ Real.exp Q) (hL : (L : ℝ) ≤ Real.exp Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    ((δ⁻¹^Fintype.card I * B^n : ℝ≥0) : ℝ) ≤ Real.exp (P*(W+Q)) ∧
      ((δ⁻¹^Fintype.card I * (n*L*B^n) + B^n*affineProductProfileLip I δ : ℝ≥0) : ℝ) ≤
        Real.exp ((2*P+1)*(W+Q)+3*P+1) := by
  have hδ0 : 0 ≤ ((δ⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hd := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I) hI
  have hb := pow_le_exp_mul_of_le_exp B.coe_nonneg hB hQ n hn
  have hd1 := pow_le_exp_mul_of_le_exp hδ0 hδ hW (Fintype.card I + 1)
    (by push_cast; linarith : ((Fintype.card I + 1 : ℕ) : ℝ) ≤ P+1)
  have hIE : (Fintype.card I : ℝ) ≤ Real.exp P := hI.trans (by linarith [Real.add_one_le_exp P])
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  constructor
  · simp only [NNReal.coe_mul, NNReal.coe_pow]
    calc
      _ ≤ Real.exp (P*W) * Real.exp (P*Q) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      affineProductProfileLip]
    have hfirst : (((δ⁻¹ : ℝ≥0) : ℝ)^Fintype.card I) * ((n : ℝ)*L*(B : ℝ)^n) ≤
        Real.exp (P*W+P+Q+P*Q) := by
      calc
        _ ≤ Real.exp (P*W) * (Real.exp P * Real.exp Q * Real.exp (P*Q)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : (B : ℝ)^n * ((Fintype.card I : ℝ)*probabilityProfileLipschitz*
        ((δ⁻¹ : ℝ≥0) : ℝ)^(Fintype.card I+1)) ≤ Real.exp (P*Q+2*P+(P+1)*W) := by
      calc
        _ ≤ Real.exp (P*Q) * (Real.exp P * Real.exp P * Real.exp ((P+1)*W)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    exact hsum.trans_eq (congrArg Real.exp (by ring))

end Erdos3

end

section

namespace Erdos3

noncomputable def coefficientReplacementErrorLog {A : Type*} [Semiring A] (D L : A) : A :=
  3 * (D + 1) * (L + 3)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
namespace OAI

section

namespace Erdos3

theorem twoTermErrorWidth_spec {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < twoTermErrorWidth B ε ∧ twoTermErrorWidth B ε ≤ 1 ∧
      B * twoTermErrorWidth B ε ≤ ε / 2 := by
  have hden : 0 < 2 * (1 + B) := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hε hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (ε / (2 * (1 + B))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ ε / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

noncomputable def spatialTupleTolerance (n : ℕ) (G V ε : ℝ) : ℝ :=
  min (1 / 4) (ε / (2 * (n + 1) * (2 + G) ^ n * (1 + V)))

theorem spatialTupleTolerance_spec (n : ℕ) {G V ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) :
    0 < spatialTupleTolerance n G V ε ∧ spatialTupleTolerance n G V ε ≤ 1 / 4 ∧
      spatialTupleTolerance n G V ε * (2 * (n + 1) * (2 + G) ^ n * (1 + V)) ≤ ε := by
  have hden : 0 < 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) := by positivity
  refine ⟨lt_min (by norm_num) (div_pos hε hden), min_le_left _ _, ?_⟩
  exact (le_div_iff₀ hden).mp (min_le_right _ _)

end Erdos3

end

section

namespace Erdos3

def spatialTupleToleranceLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 + 5 * P + 6

theorem spatialTupleToleranceLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ spatialTupleToleranceLog P := by unfold spatialTupleToleranceLog; positivity

theorem spatialTupleTolerance_inv_bound (n : ℕ) {G V ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleTolerance n G V ε)⁻¹ ≤ Real.exp (spatialTupleToleranceLog P) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 2 + G ≤ Real.exp (P + 2) := by
    calc
      _ ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 2 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hpower := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 + G) hbase
    (by positivity : 0 ≤ P + 2) n hn
  have hn1 : (n : ℝ) + 1 ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hV1 : 1 + V ≤ Real.exp (P + 1) := one_add_le_exp_succ hP hVP
  have hden : 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) ≤
      Real.exp (P ^ 2 + 4 * P + 3) := by
    calc
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P * (P + 2)) * Real.exp (P + 1) := by
        gcongr
        linarith
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  unfold spatialTupleTolerance
  apply inv_min_le_of_inv_le
  · norm_num only [one_div, inv_inv]
    have h := Real.add_one_le_exp (spatialTupleToleranceLog P)
    unfold spatialTupleToleranceLog at *
    nlinarith
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (P ^ 2 + 4 * P + 3) * Real.exp P := by gcongr
      _ = Real.exp (P ^ 2 + 5 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialTupleToleranceLog; linarith)

theorem spatialTupleEarlyWidth_inv_bound (n : ℕ) {G V B ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hB : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hBP : B ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (twoTermErrorWidth B (spatialTupleTolerance n G V ε))⁻¹ ≤
      Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) := by
  let R := P + spatialTupleToleranceLog P
  have hT := spatialTupleToleranceLog_nonneg hP
  have hR : 0 ≤ R := add_nonneg hP hT
  have hPR : P ≤ R := le_add_of_nonneg_right hT
  have hTR : spatialTupleToleranceLog P ≤ R := le_add_of_nonneg_left hP
  have ht := (spatialTupleTolerance_spec n hG hV hε).1
  have hit := (spatialTupleTolerance_inv_bound n hG hV hε hP hn hGP hVP hεP).trans
    (Real.exp_le_exp.mpr hTR)
  exact (twoTermErrorChoices_log_bounds (A := 0) (T := 0) (by norm_num) hB ht hR
    (Real.exp_nonneg R) (Real.exp_nonneg R) (hBP.trans (Real.exp_le_exp.mpr hPR)) hit).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CircleFejerAverage
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators

theorem abs_lt_of_mem_fejerFrequencies {N : ℕ} {h : ℤ} (hh : h ∈ fejerFrequencies N) :
    |h| < (N : ℤ) := by
  classical
  obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hh
  unfold fejerPairFrequency
  rw [abs_lt]
  constructor <;> omega

theorem card_fejerFrequencies_le (N : ℕ) : (fejerFrequencies N).card ≤ N ^ 2 := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp [pow_two])

theorem circle_integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : Circle → E} (hf : Continuous f) : Integrable f circleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def fejerFirstMoment (N : ℕ) : ℝ :=
  ∫ x : Circle, ‖x‖ * fejerPolynomial N x ∂circleHaar

theorem fejerFirstMoment_le {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    fejerFirstMoment N ≤ η + 1 / (8 * N * η ^ 2) := by
  have hpoint (x : Circle) : ‖x‖ * fejerPolynomial N x ≤
      η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) := by
    by_cases hx : ‖x‖ < η
    · have h := mul_le_mul_of_nonneg_right hx.le (fejerPolynomial_nonneg N x)
      exact h.trans (le_add_of_nonneg_right (by positivity))
    · have htail := fejerPolynomial_le_of_distance hN hη (le_of_not_gt hx)
      have hnorm : ‖x‖ ≤ 1 / 2 := integerDistance_le_half x
      have hprod := mul_le_mul hnorm htail (fejerPolynomial_nonneg N x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have heq : (1 / 2 : ℝ) * (1 / (4 * N * η ^ 2)) = 1 / (8 * N * η ^ 2) := by ring
      rw [heq] at hprod
      exact hprod.trans (le_add_of_nonneg_left (mul_nonneg hη.le (fejerPolynomial_nonneg N x)))
  have hi : Integrable (fun x : Circle => ‖x‖ * fejerPolynomial N x) circleHaar :=
    circle_integrable_of_continuous (continuous_norm.mul (continuous_fejerPolynomial N))
  have hj : Integrable (fun x : Circle => η * fejerPolynomial N x + 1 / (8 * N * η ^ 2)) circleHaar :=
    circle_integrable_of_continuous ((continuous_const.mul (continuous_fejerPolynomial N)).add continuous_const)
  calc
    fejerFirstMoment N ≤ ∫ x : Circle,
        η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) ∂circleHaar := integral_mono hi hj hpoint
    _ = η + 1 / (8 * N * η ^ 2) := by
      have hk : Integrable (fun x : Circle => η * fejerPolynomial N x) circleHaar :=
        circle_integrable_of_continuous (continuous_const.mul (continuous_fejerPolynomial N))
      rw [integral_add hk (integrable_const _),
        integral_const_mul, integral_fejerPolynomial hN]
      simp

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def fejerAverage (N : ℕ) (f : Circle → E) : E :=
  ∫ t : Circle, fejerPolynomial N t • f t ∂circleHaar

theorem fejerAverage_sub_const {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) (c : E) :
    fejerAverage N f - c = fejerAverage N (fun t => f t - c) := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hc : Integrable (fun t : Circle => fejerPolynomial N t • c) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul continuous_const)
  rw [integral_sub hi hc,
    integral_smul_const, integral_fejerPolynomial hN, one_smul]

theorem norm_fejerAverage_sub_le {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * fejerFirstMoment N := by
  rw [fejerAverage_sub_const hN hf (f 0)]
  calc
    ‖fejerAverage N (fun t => f t - f 0)‖ ≤
        ∫ t : Circle, ‖fejerPolynomial N t • (f t - f 0)‖ ∂circleHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : Circle, L * (‖t‖ * fejerPolynomial N t) ∂circleHaar := by
      apply integral_mono
      · exact circle_integrable_of_continuous
          (((continuous_fejerPolynomial N).smul (hf.sub continuous_const)).norm)
      · exact circle_integrable_of_continuous
          (continuous_const.mul (continuous_norm.mul (continuous_fejerPolynomial N)))
      · intro t
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
        nlinarith [mul_le_mul_of_nonneg_left (hbound t) (fejerPolynomial_nonneg N t)]
    _ = L * fejerFirstMoment N := integral_const_mul L _

theorem norm_fejerAverage_sub_le_explicit {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) :=
  (norm_fejerAverage_sub_le hN hf hL hbound).trans
    (mul_le_mul_of_nonneg_left (fejerFirstMoment_le hN hη) hL)

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CircleActionFourierMetric
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def circleFourierComponent (n : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ t : Circle, character ((-n) • t) * f (t +ᵥ x) ∂circleHaar

theorem circleFourierComponent_vadd (n : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    circleFourierComponent n f (a +ᵥ x) = character (n • a) * circleFourierComponent n f x := by
  unfold circleFourierComponent
  calc
    _ = ∫ t : Circle, character (n • a) *
        (character ((-n) • (t + a)) * f ((t + a) +ᵥ x)) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← add_vadd]
      have hchar : character ((-n) • t) = character (n • a) * character ((-n) • (t + a)) := by
        rw [← character_add]
        congr 1
        simp only [smul_add, neg_smul]
        abel
      rw [hchar, mul_assoc]
    _ = character (n • a) * ∫ t : Circle,
        character ((-n) • (t + a)) * f ((t + a) +ᵥ x) ∂circleHaar := integral_const_mul _ _
    _ = _ := by rw [integral_add_right_eq_self
      (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) a]

theorem norm_circleFourierComponent_le (n : ℤ) (f : X → ℂ) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖circleFourierComponent n f x‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (character ((-n) • t) * f (t +ᵥ x))))
    (integrable_const B) (ae_of_all circleHaar (fun t : Circle => by
      simpa only [norm_mul, norm_character, one_mul] using hB (t +ᵥ x)))
  simpa using h

variable [TopologicalSpace X] [ContinuousVAdd Circle X]

theorem integrable_circleFourierComponent (n : ℤ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) circleHaar := by
  exact circle_integrable_of_continuous
    ((fourier (-n)).continuous.mul (hf.comp (continuous_id.vadd continuous_const)))

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem lipschitz_circleFourierComponent (n : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFourierComponent n f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold circleFourierComponent
  rw [← integral_sub (integrable_circleFourierComponent n hf.continuous x)
    (integrable_circleFourierComponent n hf.continuous y)]
  apply (norm_integral_le_integral_norm _).trans
  have hpoint (t : Circle) :
      ‖character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y)‖ ≤
        (L : ℝ) * dist x y := by
    rw [← mul_sub, norm_mul, norm_character, one_mul, ← dist_eq_norm]
    exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg
      (character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y))))
    (integrable_const ((L : ℝ) * dist x y)) (ae_of_all circleHaar hpoint)
  simpa using h

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

theorem ofReal_fejerPolynomial_eq (N : ℕ) (t : Circle) :
    (fejerPolynomial N t : ℂ) =
      ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * character (h • t) := by
  rw [fejerPolynomial_eq, complex_fejerPolynomial_eq]

theorem fejerAverage_eq_sum (N : ℕ) {f : Circle → ℂ} (hf : Continuous f) :
    fejerAverage N f = ∑ h ∈ fejerFrequencies N,
      (fejerCoefficient N h : ℂ) * ∫ t : Circle, character (h • t) * f t ∂circleHaar := by
  classical
  unfold fejerAverage
  simp_rw [Complex.real_smul, ofReal_fejerPolynomial_eq, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro h _
    exact circle_integrable_of_continuous
      (continuous_const.mul ((fourier h).continuous.mul hf))

variable {X : Type*} [TopologicalSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

noncomputable def circleFejerSum (N : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

theorem circleFejerSum_eq_average (N : ℕ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    circleFejerSum N f x = fejerAverage N (fun t : Circle => f (t +ᵥ x)) := by
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  rw [fejerAverage_eq_sum N hc]
  simp only [circleFejerSum, circleFourierComponent, neg_neg]

theorem circleFejerSum_approximation {N : ℕ} (hN : 0 < N) {f : X → ℂ} (hf : Continuous f)
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (horbit : ∀ (t : Circle) x, ‖f (t +ᵥ x) - f x‖ ≤ L * ‖t‖) (x : X) :
    ‖circleFejerSum N f x - f x‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) := by
  rw [circleFejerSum_eq_average N hf]
  have hc : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.comp (continuous_id.vadd continuous_const)
  have h := norm_fejerAverage_sub_le_explicit hN hc hL hη
    (fun t : Circle => by simpa only [zero_vadd] using horbit t x)
  simpa only [zero_vadd] using h

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

theorem fejer_error_le_of_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N) (hcut : (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ)) :
    L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) ≤ δ := by
  have hS : 0 < L + 1 := by linarith
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (L + 1) ^ 3 ≤ (N : ℝ) * δ ^ 3 :=
    (div_le_iff₀ (pow_pos hδ 3)).mp hcut
  have hfirst : L * δ / (2 * (L + 1)) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsecond : L * (L + 1) ^ 2 / (2 * N * δ ^ 2) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      L * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [sq_nonneg (L + 1)]
      _ ≤ (N : ℝ) * δ ^ 3 := hpow
      _ = δ / 2 * (2 * N * δ ^ 2) := by ring
  have heq : L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) =
      L * δ / (2 * (L + 1)) + L * (L + 1) ^ 2 / (2 * N * δ ^ 2) := by
    field_simp [ne_of_gt hS, ne_of_gt hδ, ne_of_gt hNr]
    ring
  rw [heq]
  linarith

theorem exists_fejer_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (L + 1) ^ 3 / δ ^ 3 + 2 := by
  let R := (L + 1) ^ 3 / δ ^ 3
  refine ⟨⌈R⌉₊ + 1, by omega, ?_, ?_⟩
  · have h := Nat.le_ceil R
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (show 0 ≤ R by dsimp [R]; positivity)
    push_cast
    linarith

theorem fejer_cutoff_bound {L δ p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hLp : L ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    (L + 1) ^ 3 / δ ^ 3 + 2 ≤ Real.exp ((p + 2) ^ 4) := by
  have hexp : 1 ≤ Real.exp p := Real.one_le_exp hp
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hS : L + 1 ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith
  have hR : (L + 1) ^ 3 / δ ^ 3 ≤ Real.exp (6 * p + 3) := by
    calc
      _ = (L + 1) ^ 3 * (δ⁻¹) ^ 3 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ (Real.exp (p + 1)) ^ 3 * (Real.exp p) ^ 3 := by gcongr
      _ = Real.exp (6 * p + 3) := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hbase : 1 ≤ Real.exp (6 * p + 3) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp (6 * p + 3) * Real.exp 2 := by nlinarith
    _ = Real.exp (6 * p + 5) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hsq : 4 ≤ (p + 2) ^ 2 := by nlinarith
      nlinarith [sq_nonneg p, mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (p + 2))]

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def fejerComponent (N : ℕ) (h : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

theorem fejerComponent_vadd (N : ℕ) (h : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    fejerComponent N h f (a +ᵥ x) = character ((-h) • a) * fejerComponent N h f x := by
  unfold fejerComponent
  rw [circleFourierComponent_vadd]
  ring

theorem norm_fejerComponent_le {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {B : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖fejerComponent N h f x‖ ≤ B := by
  unfold fejerComponent
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (norm_circleFourierComponent_le (-h) f hf x)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

variable [PseudoMetricSpace X] [ContinuousVAdd Circle X]

theorem lipschitz_fejerComponent {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (fejerComponent N h f) := by
  have hc := lipschitz_circleFourierComponent (-h) hf hact
  apply LipschitzWith.of_dist_le_mul
  intro x y
  unfold fejerComponent
  rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h), ← dist_eq_norm]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (hc.dist_le_mul x y)
    dist_nonneg zero_le_one).trans_eq (one_mul _)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fejerAverage_le {N : ℕ} (hN : 0 < N) (f : Circle → E) {B : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ B) : ‖fejerAverage N f‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun t : Circle => fejerPolynomial N t * B) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).mul continuous_const)
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (fejerPolynomial N t • f t))) hi
    (ae_of_all circleHaar (fun t : Circle => by
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
      exact mul_le_mul_of_nonneg_left (hf t) (fejerPolynomial_nonneg N t)))
  simpa only [integral_mul_const, integral_fejerPolynomial hN, one_mul] using h

theorem fejerAverage_sub (N : ℕ) {f g : Circle → E} (hf : Continuous f) (hg : Continuous g) :
    fejerAverage N (fun t => f t - g t) = fejerAverage N f - fejerAverage N g := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hj : Integrable (fun t : Circle => fejerPolynomial N t • g t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hg)
  exact integral_sub hi hj

theorem norm_fejerAverage_sub_average_le {N : ℕ} (hN : 0 < N) {f g : Circle → E}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hfg : ∀ t, ‖f t - g t‖ ≤ B) :
    ‖fejerAverage N f - fejerAverage N g‖ ≤ B := by
  rw [← fejerAverage_sub N hf hg]
  exact norm_fejerAverage_le hN _ hfg

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem lipschitz_circleFejerSum {N : ℕ} (hN : 0 < N) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFejerSum N f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, circleFejerSum_eq_average N hf.continuous, circleFejerSum_eq_average N hf.continuous]
  have hx : Continuous (fun t : Circle => f (t +ᵥ x)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  have hy : Continuous (fun t : Circle => f (t +ᵥ y)) :=
    hf.continuous.comp (continuous_id.vadd continuous_const)
  apply norm_fejerAverage_sub_average_le hN hx hy
  intro t
  rw [← dist_eq_norm]
  exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

structure IsometricCircleAction (X : Type*) [PseudoMetricSpace X] where
  act : Circle → X → X
  zero_act : ∀ x, act 0 x = x
  add_act : ∀ t u x, act (t + u) x = act t (act u x)
  continuous_act : Continuous (fun p : Circle × X => act p.1 p.2)
  isometry_act : ∀ t, Isometry (act t)

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

@[instance_reducible] def toAddAction (A : IsometricCircleAction X) : AddAction Circle X where
  vadd := A.act
  zero_vadd := A.zero_act
  add_vadd := A.add_act

theorem toContinuousVAdd (A : IsometricCircleAction X) :
    letI := A.toAddAction
    ContinuousVAdd Circle X := by
  let := A.toAddAction
  exact ⟨A.continuous_act⟩

noncomputable def component (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  fejerComponent N h f

noncomputable def smooth (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFejerSum N f

theorem smooth_eq_sum (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) (x : X) :
    A.smooth N f x = ∑ h ∈ fejerFrequencies N, A.component N h f x := rfl

theorem component_character (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.component N h f (A.act t x) = character ((-h) • t) * A.component N h f x := by
  let := A.toAddAction
  exact fejerComponent_vadd N h f t x

theorem component_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (A.component N h f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_fejerComponent hN h hf A.isometry_act

theorem component_norm_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ‖A.component N h f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_fejerComponent_le hN h hf x

theorem smooth_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) : LipschitzWith L (A.smooth N f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFejerSum hN hf A.isometry_act

theorem smooth_error (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    {f : X → ℂ} (hf : Continuous f) {O η : ℝ} (hO : 0 ≤ O) (hη : 0 < η)
    (ho : ∀ t x, ‖f (A.act t x) - f x‖ ≤ O * ‖t‖) (x : X) :
    ‖A.smooth N f x - f x‖ ≤ O * (η + 1 / (8 * N * η ^ 2)) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact circleFejerSum_approximation hN hf hO hη ho x

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open Function
open scoped NNReal

variable {X : Type*}

theorem realFlow_periodic (flow : ℝ → X → X)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (x : X) : Periodic (fun r => flow r x) 1 := by
  intro r
  change flow (r + 1) x = flow r x
  rw [hadd, hperiod]

noncomputable def periodicFlowAct (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (t : Circle) (x : X) : X :=
  (hper x).lift t

theorem periodicFlowAct_coe (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (r : ℝ) (x : X) :
    periodicFlowAct flow hper (r : Circle) x = flow r x := (hper x).lift_coe r

theorem periodicFlowAct_zero (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hzero : ∀ x, flow 0 x = x) (x : X) :
    periodicFlowAct flow hper 0 x = x := by
  change periodicFlowAct flow hper ((0 : ℝ) : Circle) x = x
  rw [periodicFlowAct_coe, hzero]

theorem periodicFlowAct_add (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x)) (t u : Circle) (x : X) :
    periodicFlowAct flow hper (t + u) x = periodicFlowAct flow hper t (periodicFlowAct flow hper u x) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [← QuotientAddGroup.mk_add]
  simp only [periodicFlowAct_coe, hadd]

variable [PseudoMetricSpace X]

theorem periodicFlowAct_isometry (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hiso : ∀ r, Isometry (flow r)) (t : Circle) :
    Isometry (periodicFlowAct flow hper t) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) = flow r := funext (periodicFlowAct_coe flow hper r)
  rw [heq]
  exact hiso r

theorem periodicFlowAct_displacement (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) (t : Circle) (x : X) :
    dist (periodicFlowAct flow hper t x) x ≤ D * ‖t‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) x = flow (r - round r) x := by
    rw [show (r : Circle) = ((r - round r : ℝ) : Circle) by simp [sub_eq_add_neg]]
    exact periodicFlowAct_coe flow hper _ x
  rw [heq, UnitAddCircle.norm_eq]
  exact hbound _ x

theorem circleAct_joint_lipschitz (act : Circle → X → X)
    (_hzero : ∀ x, act 0 x = x) (hadd : ∀ t u x, act (t + u) x = act t (act u x))
    (hiso : ∀ t, Isometry (act t)) (D : ℝ≥0)
    (hbound : ∀ t x, dist (act t x) x ≤ D * ‖t‖) :
    LipschitzWith (D + 1) (fun p : Circle × X => act p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨t, x⟩ ⟨u, y⟩
  have htime : dist (act t y) (act u y) ≤ D * dist t u := by
    calc
      dist (act t y) (act u y) = dist (act u (act (t - u) y)) (act u y) := by
        rw [← hadd, show u + (t - u) = t by abel]
      _ = dist (act (t - u) y) y := (hiso u).dist_eq _ _
      _ ≤ D * ‖t - u‖ := hbound (t - u) y
      _ = D * dist t u := by rw [dist_eq_norm]
  calc
    dist (act t x) (act u y) ≤ dist (act t x) (act t y) + dist (act t y) (act u y) := dist_triangle _ _ _
    _ ≤ dist x y + D * dist t u := by rw [(hiso t).dist_eq]; exact add_le_add le_rfl htime
    _ ≤ dist (t, x) (u, y) + D * dist (t, x) (u, y) := by
      gcongr
      · exact le_max_right _ _
      · exact le_max_left _ _
    _ = (D + 1 : ℝ≥0) * dist (t, x) (u, y) := by push_cast; ring

noncomputable def isometricCircleActionOfFlow (flow : ℝ → X → X)
    (hzero : ∀ x, flow 0 x = x)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (hiso : ∀ r, Isometry (flow r)) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) : IsometricCircleAction X where
  act := periodicFlowAct flow (realFlow_periodic flow hadd hperiod)
  zero_act := periodicFlowAct_zero flow _ hzero
  add_act := periodicFlowAct_add flow _ hadd
  continuous_act := (circleAct_joint_lipschitz _ (periodicFlowAct_zero flow _ hzero)
    (periodicFlowAct_add flow _ hadd) (periodicFlowAct_isometry flow _ hiso) D
    (periodicFlowAct_displacement flow _ D hbound)).continuous
  isometry_act := periodicFlowAct_isometry flow _ hiso

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCircleActions
namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

def Commutes (A B : IsometricCircleAction X) : Prop :=
  ∀ t u x, A.act t (B.act u x) = B.act u (A.act t x)

theorem component_equivariant (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f : X → ℂ} (g : X → X) (z : ℂ)
    (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.component N h f (g x) = z * A.component N h f x := by
  unfold component fejerComponent circleFourierComponent
  change (fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * ((fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar))
  have heq : (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
      z * (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hg, hf]
    ring
  rw [heq]
  ring

theorem component_preserves_character (A B : IsometricCircleAction X) (hAB : A.Commutes B)
    (N : ℕ) (h n : ℤ) {f : X → ℂ}
    (hf : ∀ t x, f (B.act t x) = character (n • t) * f x) (t : Circle) (x : X) :
    A.component N h f (B.act t x) = character (n • t) * A.component N h f x :=
  A.component_equivariant N h (B.act t) (character (n • t)) (fun u x => hAB u t x) (hf t) x

theorem component_sum {ι : Type*} (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.component N h (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.component N h (f i) x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  unfold component fejerComponent circleFourierComponent
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.mul_sum s _ _
  · intro i hi
    exact integrable_circleFourierComponent (-h) (hf i hi) x

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [AddAction (ι → Circle) X] [ContinuousVAdd (ι → Circle) X]

def torusCoordinateAction (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x))
    (i : ι) : IsometricCircleAction X where
  act t x := (Pi.single i t : ι → Circle) +ᵥ x
  zero_act x := by simp
  add_act t u x := by simp only [Pi.single_add, add_vadd]
  continuous_act := by
    have hs : Continuous (fun p : Circle × X => (Pi.single i p.1 : ι → Circle)) := by
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using (continuous_fst : Continuous (fun p : Circle × X => p.1))
      · simpa only [Pi.single_eq_of_ne h] using
          (continuous_const : Continuous (fun _p : Circle × X => (0 : Circle)))
    exact hs.vadd continuous_snd
  isometry_act t := hact (Pi.single i t)

omit [Fintype ι] in
theorem torusCoordinateAction_commutes
    (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x)) (i j : ι) :
    (torusCoordinateAction hact i).Commutes (torusCoordinateAction hact j) := by
  intro t u x
  change (Pi.single i t : ι → Circle) +ᵥ ((Pi.single j u : ι → Circle) +ᵥ x) =
    (Pi.single j u : ι → Circle) +ᵥ ((Pi.single i t : ι → Circle) +ᵥ x)
  rw [← add_vadd, ← add_vadd, add_comm]

omit [PseudoMetricSpace X] [ContinuousVAdd (ι → Circle) X] in

theorem torus_character_of_coordinate_characters (f : X → ℂ) (n : ι → ℤ)
    (hf : ∀ (i : ι) (t : Circle) x,
      f ((Pi.single i t : ι → Circle) +ᵥ x) = character (n i • t) * f x)
    (t : ι → Circle) (x : X) :
    f (t +ᵥ x) = (∏ i, character (n i • t i)) * f x := by
  have hs (s : Finset ι) : ∀ x, f ((∑ i ∈ s, Pi.single i (t i) : ι → Circle) +ᵥ x) =
      (∏ i ∈ s, character (n i • t i)) * f x := by
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      intro x
      rw [Finset.sum_insert hi, add_vadd, hf, ih, Finset.prod_insert hi, mul_assoc]
  simpa only [Finset.univ_sum_single] using hs Finset.univ x

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSubstitutionAlgebra
namespace OAI

section

namespace Erdos3

variable {σ R S : Type*} [DecidableEq σ] [CommRing R] [CommRing S] [Algebra R S]

theorem aeval_monomial_update (f : σ → S) (i : σ) (u : S) (a : σ →₀ ℕ) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      u ^ a i * (a.erase i).prod (fun j n => f j ^ n) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    ← Finsupp.mul_prod_erase' a i (fun j n => Function.update f i u j ^ n) (fun _ => pow_zero _)]
  rw [Function.update_self]
  congr 1
  apply Finsupp.prod_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    simp only [Finsupp.mem_support_iff, Finsupp.erase_same, ne_eq, not_true_eq_false] at hj
  rw [Function.update_of_ne hji]

theorem aeval_monomial_update_eq_of_zero (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i = 0) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) := by
  simp only [aeval_monomial_update, ha, pow_zero]

theorem aeval_monomial_update_add (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i ≤ 1) :
    MvPolynomial.aeval (R := R) (Function.update f i (u + v)) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) +
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) -
      MvPolynomial.aeval (R := R) (Function.update f i 0) (MvPolynomial.monomial a 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h <;>
    simp only [aeval_monomial_update, h, pow_zero, pow_one] <;> ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowWeightFibers
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def reweight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) : FiniteProbabilityWeights X where
  weight x := p.weight x * w x
  nonneg x := mul_nonneg (p.nonneg x) (hw x)
  total := htotal

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothProductAmplitudeTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_translation_test_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (v : I → ℤ) :
    ‖(∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ (x + v)) -
      ∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * φ x‖ ≤
        4 * (3 : ℝ) ^ Fintype.card I *
          (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * ‖rectangularLatticePoint 0 S v‖) := by
  have ht := normalized_rectangular_translation_test_le (smoothProductProfile I)
    (smoothProductProfile_lipschitz I) a S hS1 zero_le_one
    (smoothProductProfile_zero_outside I)
    (shiftedSmoothProductMass_lower a S hS hδ hδ1 hmesh hsmall) φ hφ v
  simpa only [shiftedSmoothProductPMF_toReal, NNReal.coe_mul, NNReal.coe_natCast,
    show 2 * (1 : ℝ) + 1 = 3 by norm_num] using ht

theorem shiftedSmoothProductPMF_shift_transfer {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r B : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * f x‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + B := by
  apply finite_probability_shift_transfer (fun x => (shiftedSmoothProductPMF a S hS hZ x).toReal)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (fun _ => ENNReal.toReal_nonneg) (shiftedSmoothProductPMF_toReal_sum a S hS hZ) shift f _ hlocal
  intro u
  apply (shiftedSmoothProductPMF_translation_test_le a S hS hZ hS1 hδ hδ1 hmesh hsmall f hf (shift u)).trans
  calc
    _ ≤ 4 * (3 : ℝ) ^ Fintype.card I *
        (((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r) := by
      gcongr
      exact hshift u
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_shift_transfer_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℤ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {η : ℝ} (hvariation : ∀ x u, ‖F (x + shift u) - F x‖ ≤ η) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * (F x * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + η + β := by
  have hproduct (x) : ‖F x * f x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hF x) (hf x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlocalProduct (x) : ‖𝔼 u, F (x + shift u) * f (x + shift u)‖ ≤ η + β :=
    norm_local_average_amplitude_le (fun u => x + shift u) f F x hf (hF x) (hvariation x) (hlocal x)
  simpa only [add_assoc] using shiftedSmoothProductPMF_shift_transfer a S hS hZ hS1
    hδ hδ1 hmesh hsmall shift hshift (fun x => F x * f x) hproduct hlocalProduct

theorem shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) *
      (F (rectangularLatticePoint a S x) * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r +
        (Lip : ℝ) * r + β := by
  exact shiftedSmoothProductPMF_shift_transfer_amplitude a S hS hZ hS1 hδ hδ1 hmesh hsmall
    shift hshift f hf hlocal (fun x => F (rectangularLatticePoint a S x)) (fun _ => hF _)
    (fun x u => normalizedSpatialAmplitude_shift_le_of_norm_le F hLip a S x (shift u) (hshift u))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TruncatedProjectionError
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_sum {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (f : J → X → ℂ) :
    p.complexMean (fun x => ∑ j, f j x) = ∑ j, p.complexMean (f j) := by
  simp only [complexMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem norm_weighted_complexMean_sub_le_mean_norm {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f g : X → ℂ) {ρ : ℝ}
    (he : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ ρ) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      ρ * p.mean (fun x => ‖w x‖) := by
  apply (p.norm_complexMean_sub_le _ _ (fun x => ρ * ‖w x‖) ?_).trans_eq
    (p.mean_const_mul ρ _)
  intro x hx
  rw [← mul_sub, norm_mul, mul_comm ρ]
  exact mul_le_mul_of_nonneg_left (he x hx) (norm_nonneg _)

theorem complexMean_weighted_expansion {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ) :
    p.complexMean (fun x => w x * ∑ j, c j * u j x) =
      ∑ j, c j * p.complexMean (fun x => w x * u j x) := by
  simp only [Finset.mul_sum]
  rw [p.complexMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← p.complexMean_mul_left]
  congr 1
  funext x
  ring

theorem weighted_expansion_discard_error {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j x)‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * ∑ j, c j * u j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have he : (fun x => w x * ∑ j, if keep j then c j * u j x else 0) =
      (fun x => w x * ∑ j, (if keep j then c j else 0) * u j x) := by
    funext x
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j <;> simp [hj]
  rw [he, p.complexMean_weighted_expansion, p.complexMean_weighted_expansion,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, ‖c j‖ * τ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : keep j
      · simp only [hj, ite_true, sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg _) hτ
      · simp only [hj, ite_false, zero_mul, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_left (hdiscard j hj) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * τ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * τ := mul_le_mul_of_nonneg_right hc hτ

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem weighted_projection_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f F G g : X → ℂ) {B η ε : ℝ}
    (hη : 0 ≤ η) (hw : p.mean (fun x => ‖w x‖) ≤ B)
    (hF : ∀ x, p.weight x ≠ 0 → ‖f x - F x‖ ≤ η)
    (hG : ∀ x, p.weight x ≠ 0 → ‖G x - g x‖ ≤ η)
    (hprojection : ‖p.complexMean (fun x => w x * F x) -
      p.complexMean (fun x => w x * G x)‖ ≤ ε) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      2 * B * η + ε := by
  have hfirst := (p.norm_weighted_complexMean_sub_le_mean_norm w f F hF).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have hlast := (p.norm_weighted_complexMean_sub_le_mean_norm w G g hG).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * F x))
    (p.complexMean (fun x => w x * g x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * F x)) (p.complexMean (fun x => w x * G x))
    (p.complexMean (fun x => w x * g x))
  linarith

end Erdos3.FiniteProbabilityWeights

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

open scoped Classical

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_supported_weight_sum_tsum {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0) :
    (∑' x, ∑ r, w r x) = ∑ r, ∑' x, w r x := by
  have hcut (v : X → ℝ) (hv : ∀ x ∉ S, v x = 0) : (∑' x, v x) = ∑ x ∈ S, v x :=
    (hasSum_sum_of_ne_finset_zero hv).tsum_eq
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcutEach (r : R) := hcut (w r) (hw r)
  rw [hcut (fun x => ∑ r, w r x) hsum]
  simp_rw [hcutEach]
  exact Finset.sum_comm

theorem finite_normalized_test_sum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (Z : ℝ) (φ : X → ℂ) :
    (∑' x, ((w x / Z : ℝ) : ℂ) * φ x) = ∑ x ∈ S, ((w x / Z : ℝ) : ℂ) * φ x := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
  intro x hx
  simp only [hw x hx, zero_div, Complex.ofReal_zero, zero_mul]

theorem finite_supported_normalized_mixture {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x) (φ : X → ℂ) :
    (∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ∑ r, (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
        (∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) := by
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcut := finite_normalized_test_sum (fun x => ∑ r, w r x) S hsum
    (∑ r, ∑' y, w r y) φ
  rw [hcut]
  simp_rw [finite_normalized_test_sum _ S (hw _) _ φ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hc r : (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
      (((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ((w r x / (∑ s, ∑' y, w s y) : ℝ) : ℂ) * φ x := by
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp [hZ.ne', (hZr r).ne']
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_div]

theorem finite_supported_normalized_mixture_bound {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x)
    (φ : X → ℂ) {ε : ℝ}
    (hφ : ∀ r, ‖∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε) :
    ‖∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε := by
  rw [finite_supported_normalized_mixture w S hw hZr hZ φ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, ((∑' y, w r y) / (∑ s, ∑' y, w s y)) * ε := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos (hZr r) hZ).le]
      exact mul_le_mul_of_nonneg_left (hφ r) (div_pos (hZr r) hZ).le
    _ = ε := by rw [← Finset.sum_mul, ← Finset.sum_div, div_self hZ.ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_support_eq_tsum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) : (∑ x : S, w x.val) = ∑' x, w x := by
  calc
    _ = ∑ x ∈ S, w x := Finset.sum_coe_sort S w
    _ = _ := (hasSum_sum_of_ne_finset_zero hw).tsum_eq.symm

noncomputable def finiteSupportProbability {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x) :
    FiniteProbabilityWeights S where
  weight x := w x.val / ∑' y, w y
  nonneg x := div_nonneg (hw0 x.val) hZ.le
  total := by
    rw [← Finset.sum_div, sum_support_eq_tsum w S hw, div_self hZ.ne']

theorem finiteSupportProbability_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (f : X → ℂ) :
    (finiteSupportProbability w S hw0 hw hZ).complexMean (fun x => f x.val) =
      ∑' x, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x := by
  change (∑ x : S, ((w x.val / (∑' y, w y) : ℝ) : ℂ) * f x.val) = _
  calc
    _ = ∑ x ∈ S, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x :=
      Finset.sum_coe_sort S _
    _ = _ := (finite_normalized_test_sum w S hw _ f).symm

theorem normalized_finite_weight_discard_error {X J : Type*} [Fintype J]
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have hdiscard' (j) (hj : ¬keep j) :
      ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * u j x.val)‖ ≤ τ := by
    rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * u j x)]
    exact hdiscard j hj
  have h := (finiteSupportProbability v S hv0 hv hZ).weighted_expansion_discard_error
    (fun x => w x.val) c (fun j x => u j x.val) keep hc hτ hdiscard'
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * ∑ j, c j * u j x),
    finiteSupportProbability_complexMean v S hv0 hv hZ
      (fun x => w x * ∑ j, if keep j then c j * u j x else 0)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteDensityMass {X : Type*} (w D : X → ℝ) : ℝ :=
  ∑' x, (w x / ∑' y, w y) * D x

theorem finiteDensityMass_eq_div {X : Type*} (w D : X → ℝ) :
    finiteDensityMass w D = (∑' x, w x * D x) / ∑' x, w x := by
  simp only [finiteDensityMass, div_mul_eq_mul_div, tsum_div_const]

theorem finiteDensityMass_complex {X : Type*} (w D : X → ℝ) :
    (finiteDensityMass w D : ℂ) = ∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * (D x : ℂ) := by
  simp only [finiteDensityMass, Complex.ofReal_tsum, Complex.ofReal_mul]

theorem finiteDensityMass_raw_pos {X : Type*} (w D : X → ℝ)
    (hw : 0 < ∑' x, w x) (hD : 0 < finiteDensityMass w D) :
    0 < ∑' x, w x * D x := by
  have he := (eq_div_iff hw.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  exact mul_pos hD hw

noncomputable def finiteDensityTiltPMF {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) : PMF X :=
  realWeightPMF (fun x => w x * D x) (fun x => mul_nonneg (hw0 x) (hD0 x))
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, zero_mul])).summable
    (finiteDensityMass_raw_pos w D hZ hD)

theorem finiteDensityTiltPMF_toReal {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (x : X) :
    (finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal =
      (w x / ∑' y, w y) * D x / finiteDensityMass w D := by
  rw [finiteDensityTiltPMF, realWeightPMF_apply]
  have he := (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  field_simp

theorem finiteDensityTiltPMF_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (f : X → ℂ) :
    (∑' x, ((finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * ((D x : ℂ) * f x)) /
        (finiteDensityMass w D : ℂ) := by
  simp only [finiteDensityTiltPMF_toReal, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteDensityMass_sum_le_of_weight_lower {X : Type*}
    (w D : X → ℝ) (support window : Finset X)
    (hw : ∀ x, 0 ≤ w x) (hoff : ∀ x ∉ support, w x = 0)
    (hD : ∀ x, 0 ≤ D x) (hZ : 0 < ∑' x, w x)
    {b : ℝ} (hb : 0 < b) (hlower : ∀ x ∈ window, b ≤ w x) :
    (∑ x ∈ window, D x) ≤ ((∑' x, w x) / b) * finiteDensityMass w D := by
  classical
  have hsub : window ⊆ support := by
    intro x hx
    by_contra h
    have hh := hlower x hx
    rw [hoff x h] at hh
    exact (not_le_of_gt hb) hh
  have hsum : (∑' x, w x * D x) = ∑ x ∈ support, w x * D x :=
    tsum_eq_sum (fun x hx => by rw [hoff x hx, zero_mul])
  have hbound : b * (∑ x ∈ window, D x) ≤ ∑' x, w x * D x := by
    rw [hsum, Finset.mul_sum]
    apply (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hlower x hx) (hD x))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg (hw x) (hD x))
  have he : finiteDensityMass w D * (∑' x, w x) = ∑' x, w x * D x :=
    (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he] at hbound
  calc
    (∑ x ∈ window, D x) ≤ (finiteDensityMass w D * (∑' x, w x)) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm b] using hbound)
    _ = ((∑' x, w x) / b) * finiteDensityMass w D := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSupportApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalized_finite_weight_approximation {X : Type*}
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w f g : X → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ S, ‖w x‖ ≤ 1) (he : ∀ x ∈ S, ‖f x - g x‖ ≤ η) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * f x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * g x)‖ ≤ η := by
  let p := finiteSupportProbability v S hv0 hv hZ
  have hm : p.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (p.mean_mono (fun x => hw x.val x.property)).trans_eq (p.mean_const 1)
  have h := (p.norm_weighted_complexMean_sub_le_mean_norm (fun x => w x.val)
    (fun x => f x.val) (fun x => g x.val) (fun x _ => he x.val x.property)).trans
      ((mul_le_mul_of_nonneg_left hm hη).trans_eq (mul_one η))
  change ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * f x.val) -
    (finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * g x.val)‖ ≤ η at h
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * f x),
    finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * g x)] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * q.weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

theorem complexMean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X × Y → ℂ) :
    (p.prod q).complexMean F = p.complexMean (fun x => q.complexMean (fun y => F (x, y))) := by
  simp only [complexMean, prod, Fintype.sum_prod_type, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

noncomputable def toPMF (p : FiniteProbabilityWeights X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.weight x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one])

@[simp] theorem toPMF_apply (p : FiniteProbabilityWeights X) (x : X) :
    p.toPMF x = ENNReal.ofReal (p.weight x) := rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def ofPMF {X : Type*} [Fintype X] (p : PMF X) :
    FiniteProbabilityWeights X where
  weight x := (p x).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    have ht : ∑ x, p x = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), ht, ENNReal.toReal_one]

@[simp] theorem ofPMF_weight {X : Type*} [Fintype X] (p : PMF X) (x : X) :
    (ofPMF p).weight x = (p x).toReal := rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

noncomputable def ofSupportedPMF {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) : FiniteProbabilityWeights T where
  weight x := (p x.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    calc
      _ = ∑ x ∈ T, (p x).toReal := Finset.sum_coe_sort T _
      _ = ∑' x, (p x).toReal := (hasSum_sum_of_ne_finset_zero hT).tsum_eq.symm
      _ = (∑' x, p x).toReal := (ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)).symm
      _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]

@[simp] theorem ofSupportedPMF_weight {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (x : T) :
    (ofSupportedPMF p T hT).weight x = (p x.val).toReal := rfl

theorem ofSupportedPMF_map_mean {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (g : Y → ℝ) :
    (ofSupportedPMF p T hT).mean (fun x => g (f x.val)) =
      (ofPMF (p.map f)).mean g := by
  have hmap (y : Y) : (p.map f y).toReal =
      ∑ x : T, (p x.val).toReal * (if f x.val = y then 1 else 0) := by
    rw [pmf_map_toReal_indicator,
      Finset.sum_coe_sort T (fun x => (p x).toReal * (if f x = y then 1 else 0))]
    exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hT x hx, zero_mul])).tsum_eq
  symm
  simp only [mean, ofPMF_weight, ofSupportedPMF_weight, hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem ofSupportedPMF_map_event {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (E : Y → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => E (f x.val)) =
      (ofPMF (p.map f)).eventProbability E :=
  ofSupportedPMF_map_mean p T hT f (fun y => if E y then 1 else 0)

end FiniteProbabilityWeights

noncomputable def shiftedSmoothProductFiniteWeights {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) :=
  FiniteProbabilityWeights.ofSupportedPMF (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)

@[simp] theorem shiftedSmoothProductFiniteWeights_weight {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (x : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight x =
      (shiftedSmoothProductPMF a S hS hZ x.val).toReal := rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

noncomputable def regularizedTentPartition (c : I → X) (r : ℝ) (i : I) (x : X) : ℝ :=
  metricTent (c i) r x / max r (metricTentSum c r x)

theorem regularizedTentPartition_range (c : I → X) {r : ℝ} (hr : 0 < r) (i : I) (x : X) :
    0 ≤ regularizedTentPartition c r i x ∧ regularizedTentPartition c r i x ≤ 1 := by
  have hd : 0 < max r (metricTentSum c r x) := hr.trans_le (le_max_left _ _)
  refine ⟨div_nonneg (metricTent_nonneg _ _ _) hd.le, (div_le_one hd).mpr ?_⟩
  exact (Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x)
    (Finset.mem_univ i)).trans (le_max_right _ _)

theorem regularizedTentPartition_sum (c : I → X) {r : ℝ} (hr : 0 < r) (x : X)
    (hx : ∃ i, dist x (c i) ≤ r) : ∑ i, regularizedTentPartition c r i x = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hs : r ≤ metricTentSum c r x := by
    calc
      r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
      _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)
  simp only [regularizedTentPartition, ← Finset.sum_div, max_eq_right hs]
  exact div_self (hr.trans_le hs).ne'

theorem regularizedTentPartition_zero (c : I → X) (r : ℝ) (i : I) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : regularizedTentPartition c r i x = 0 := by
  simp only [regularizedTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem regularizedTentPartition_lipschitz (c : I → X) {r : ℝ≥0} (hr : 0 < r) (i : I) :
    LipschitzWith ((2 * Fintype.card I + 1) / r) (regularizedTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : |max (r : ℝ) (metricTentSum c r x) - max (r : ℝ) (metricTentSum c r y)| ≤
      Fintype.card I * dist x y := by
    rw [max_comm (r : ℝ), max_comm (r : ℝ)]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_metricTentSum_sub_le c r x y)
  have hb : |metricTent (c i) (r : ℝ) y| ≤ 2 * (r : ℝ) := by
    rw [abs_of_nonneg (metricTent_nonneg _ _ _)]
    exact metricTent_le (c i) r.coe_nonneg y
  have h := abs_div_sub_div_bound (show (0 : ℝ) < r from hr)
    (le_max_left _ _) (le_max_left _ _) dist_nonneg
    (by positivity : (0 : ℝ) ≤ 2 * r) (by positivity : (0 : ℝ) ≤ Fintype.card I * dist x y)
    (abs_metricTent_sub_le (c i) r x y) hb hd
  rw [Real.dist_eq]
  apply h.trans_eq
  push_cast
  field_simp
  ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def intervalSiteCount (B r : ℝ) : ℕ := boxCoverMeshCount B 1 r + 1

noncomputable def intervalSiteCenter (B r : ℝ) (i : Fin (intervalSiteCount B r)) : ℝ :=
  uniformIntervalGrid B (boxCoverMeshCount B 1 r) i

noncomputable def intervalSiteWeight (B r : ℝ) : Fin (intervalSiteCount B r) → ℝ → ℝ :=
  regularizedTentPartition (intervalSiteCenter B r) r

theorem intervalSiteWeight_range (B : ℝ) {r : ℝ} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) (x : ℝ) :
    0 ≤ intervalSiteWeight B r i x ∧ intervalSiteWeight B r i x ≤ 1 :=
  regularizedTentPartition_range _ hr i x

theorem intervalSiteWeight_near (B r : ℝ) (i : Fin (intervalSiteCount B r)) (x : ℝ)
    (hx : 0 < intervalSiteWeight B r i x) : dist x (intervalSiteCenter B r i) < 2 * r := by
  by_contra! hn
  exact hx.ne' (regularizedTentPartition_zero _ _ i x hn)

theorem intervalSiteWeight_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) :
    LipschitzWith ((2 * intervalSiteCount B r + 1) / r) (intervalSiteWeight B r i) := by
  have h := regularizedTentPartition_lipschitz (intervalSiteCenter B r) hr i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (regularizedTentPartition (intervalSiteCenter B r) r i x)
    (regularizedTentPartition (intervalSiteCenter B r) r i y) ≤ _
  simpa only [Fintype.card_fin] using h.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_sum_le (c : I → X) {r : ℝ} (hr : 0 < r) (x : X) :
    (∑ i, regularizedTentPartition c r i x) ≤ 1 := by
  simp only [regularizedTentPartition, ← Finset.sum_div]
  apply (div_le_one (hr.trans_le (le_max_left _ _))).mpr
  exact le_max_right _ _

theorem regularizedTentPartition_approx (c : I → X) {r : ℝ} (hr : 0 < r)
    (f : X → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hcover : ∀ x, f x ≠ 0 → ∃ i, dist x (c i) ≤ r) (x : X) :
    |f x - ∑ i, regularizedTentPartition c r i x * f (c i)| ≤ 2 * L * r := by
  let w : I → ℝ := fun i => regularizedTentPartition c r i x
  have hw (i) : 0 ≤ w i := (regularizedTentPartition_range c hr i x).1
  have hsum : (∑ i, w i) ≤ 1 := regularizedTentPartition_sum_le c hr x
  have hidentity : f x = (∑ i, w i) * f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · rw [show (∑ i, w i) = 1 from regularizedTentPartition_sum c hr x (hcover x hx), one_mul]
  have hdiff : f x - ∑ i, w i * f (c i) = ∑ i, w i * (f x - f (c i)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hidentity]
  change |f x - ∑ i, w i * f (c i)| ≤ _
  rw [hdiff]
  calc
    _ ≤ ∑ i, |w i * (f x - f (c i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * (2 * L * r) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      by_cases hi : w i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hnear : dist x (c i) < 2 * r := by
          by_contra! hfar
          exact hi (regularizedTentPartition_zero c r i x hfar)
        apply mul_le_mul_of_nonneg_left _ (hw i)
        calc
          |f x - f (c i)| ≤ (L : ℝ) * dist x (c i) := hf.dist_le_mul x (c i)
          _ ≤ (L : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left hnear.le L.coe_nonneg
          _ = _ := by ring
    _ = (∑ i, w i) * (2 * L * r) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * L * r := mul_le_of_le_one_left (by positivity) hsum

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

theorem bounded_weight_cutoff_lipschitz {E : Type*} [PseudoMetricSpace E]
    (w b : E → ℝ) {B K Q : ℝ≥0} (hw : ∀ x, |w x| ≤ B)
    (hb : ∀ x, |b x| ≤ 1) (hwl : LipschitzWith K w) (hbl : LipschitzWith Q b) :
    LipschitzWith (K + B * Q) (fun x => w x * b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hwxy := hwl.dist_le_mul x y
  have hbxy := hbl.dist_le_mul x y
  rw [Real.dist_eq] at hwxy hbxy
  calc
    _ = |(w x - w y) * b x + w y * (b x - b y)| := by congr 1; ring
    _ ≤ |(w x - w y) * b x| + |w y * (b x - b y)| := abs_add_le _ _
    _ ≤ (K : ℝ) * dist x y * 1 + B * ((Q : ℝ) * dist x y) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hwxy (hb x) (abs_nonneg _) (by positivity))
        (mul_le_mul (hw y) hbxy (abs_nonneg _) B.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

structure RepresentativeWindow where
  center : ℝ
  value : ℝ → ℝ
  lip : ℝ≥0
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  interior : ∀ x, value x ≠ 0 → 0 < x ∧ x < 1
  small : ∀ x, value x ≠ 0 → |x - center| < 1 / 4
  lipschitz : LipschitzWith lip value

noncomputable def representativeWindowCount : ℕ := intervalSiteCount 1 (1 / 16)

noncomputable def representativeWindowPartitionLip : ℝ≥0 :=
  (2 * representativeWindowCount + 1) / (1 / 16)

noncomputable def localizedRepresentativeWindow (eta : ℝ≥0) (heta : 0 < eta)
    (i : Fin representativeWindowCount) : RepresentativeWindow where
  center := intervalSiteCenter 1 (1 / 16) i
  value x := interiorIntervalCutoff eta x * intervalSiteWeight 1 (1 / 16) i x
  lip := eta⁻¹ + representativeWindowPartitionLip
  nonneg x := mul_nonneg (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
  le_one x := (mul_le_of_le_one_right (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2).trans
      (interiorIntervalCutoff_range eta x).2
  interior x hx := by
    have h := interiorIntervalCutoff_support eta (mul_ne_zero_iff.mp hx).1
    exact ⟨lt_trans (show (0 : ℝ) < eta from heta) h.1, by linarith [eta.coe_nonneg]⟩
  small x hx := by
    have hi : 0 < intervalSiteWeight 1 (1 / 16) i x :=
      lt_of_le_of_ne (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
        (Ne.symm (mul_ne_zero_iff.mp hx).2)
    have h := intervalSiteWeight_near 1 (1 / 16) i x hi
    rw [Real.dist_eq] at h
    linarith
  lipschitz := by
    have h := bounded_weight_cutoff_lipschitz (interiorIntervalCutoff eta)
      (intervalSiteWeight 1 (1 / 16) i) (B := 1)
      (fun x => by rw [abs_of_nonneg (interiorIntervalCutoff_range eta x).1]
                   exact (interiorIntervalCutoff_range eta x).2)
      (fun x => by rw [abs_of_nonneg (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1]
                   exact (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2)
      (interiorIntervalCutoff_lipschitz eta heta)
      (intervalSiteWeight_lipschitz 1 (by norm_num : (0 : ℝ≥0) < 1 / 16) i)
    simpa only [one_mul, representativeWindowPartitionLip, representativeWindowCount,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

noncomputable def kernel (w : RepresentativeWindow) : PatchKernel 1 where
  value r := w.value (w.center - r 0)
  nonneg r := w.nonneg _
  le_one r := w.le_one _
  support r hr i := by
    have h := w.small _ hr
    have he : w.center - r 0 - w.center = -r 0 := by ring
    rw [he, abs_neg] at h
    fin_cases i
    exact h.le
  lip := w.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro r t
    apply (w.lipschitz.dist_le_mul _ _).trans
    rw [dist_sub_left]
    exact mul_le_mul_of_nonneg_left (dist_le_pi_dist r t 0) w.lip.coe_nonneg

noncomputable def patch {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    PolynomialPatch σ s 1 :=
  PolynomialPatch.ofCoordinates (fun _ => 1) (fun _ => le_rfl) (fun _ => hs)
    (fun _ _ _ => le_rfl) (fun _ => P - C w.center)
    (fun _ => (weightedSupportLE _ _).sub_mem hP (weightedSupportLE_C _ _ _)) w.kernel

@[simp] theorem patch_lip {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    (w.patch s hs P hP).kernel.lip = w.lip := rfl

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumSize
namespace OAI

section

namespace Erdos3

noncomputable def uniformBlockRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  min 1 (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1))

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformSpectrumSizeConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  (majorArcSpectrumConstant n j U V + W * majorArcLengthConstant n U ^ t) *
    (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) ^
      max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

noncomputable def uniformDualVector (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  (Fintype.card Ω : ℂ) * star (f (Pi.single x 1))

omit [Nonempty Ω] in
theorem functional_eq_sum_coordinates (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (v : Ω → ℂ) :
    f v = ∑ x, v x * f (Pi.single x 1) := by
  calc
    _ = f (∑ x, Pi.single x (v x)) := by rw [Finset.univ_sum_single]
    _ = ∑ x, f (Pi.single x (v x)) := map_sum f _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have h : Pi.single x (v x) = v x • Pi.single x (1 : ℂ) := by
        ext y
        by_cases hy : y = x <;> simp [hy]
      rw [h, map_smul, smul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def weightedDualVector (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) : ℂ :=
  star (f (Pi.single x 1)) / (p.weight x : ℂ)

theorem functional_eq_weighted_inner (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) (v : Ω → ℂ) :
    f v = p.correlation v (weightedDualVector p f) := by
  rw [functional_eq_sum_coordinates, FiniteProbabilityWeights.correlation]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp [weightedDualVector, hx, hzero x hx]
  · have hxC : (p.weight x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [weightedDualVector, star_div₀, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
    field_simp

theorem weightedDualVector_norm (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) :
    ‖weightedDualVector p f x‖ = ‖f (Pi.single x 1)‖ / p.weight x := by
  rw [weightedDualVector, norm_div, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (p.nonneg x)]

theorem modeling_dual_zero_weight (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (htau : 0 < tau) (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0 := by
  intro x hx
  have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
  rw [p.mean_single_norm, hx, mul_zero] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f (Pi.single x 1))]

theorem weightedDualVector_cap (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ}
    (hK : 0 ≤ K) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, ‖weightedDualVector p f x‖ ≤ K / tau := by
  intro x
  rw [weightedDualVector_norm]
  rcases (p.nonneg x).eq_or_lt with hx | hx
  · rw [← hx, div_zero]
    exact div_nonneg hK htau.le
  · have h := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
    rw [p.mean_single_norm] at h
    apply (div_le_iff₀ hx).mpr
    have h' : ‖f (Pi.single x 1)‖ ≤ (K * p.weight x) / tau :=
      (le_div_iff₀ htau).mpr (by nlinarith only [h])
    calc
      _ ≤ (K * p.weight x) / tau := h'
      _ = _ := by ring

theorem weightedDualVector_detectable (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (b : Ω → ℂ) {M tau : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hb : ∀ x, ‖b x‖ ≤ M)
    (hfb : 1 < (f b).re) (hdual : ∀ v, tau * ‖f v‖ ≤ X v)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) :
    tau / M ^ 2 < X (weightedDualVector p f) := by
  have hbMean : p.mean (fun x => ‖b x‖ ^ 2) ≤ M ^ 2 :=
    (p.mean_mono (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)).trans_eq
      (p.mean_const (M ^ 2))
  have hself : ‖f (weightedDualVector p f)‖ =
      p.mean (fun x => ‖weightedDualVector p f x‖ ^ 2) := by
    rw [functional_eq_weighted_inner p f hzero, p.correlation_self,
      Complex.norm_real, Real.norm_of_nonneg (p.mean_nonneg (fun x => sq_nonneg _))]
  have hcs := p.norm_correlation_sq_le b (weightedDualVector p f)
  rw [← functional_eq_weighted_inner p f hzero, ← hself] at hcs
  have hupper := mul_le_mul_of_nonneg_right hbMean
    (norm_nonneg (f (weightedDualVector p f)))
  have hnorm : 1 < ‖f b‖ := hfb.trans_le (Complex.re_le_norm _)
  have hlarge : 1 < M ^ 2 * ‖f (weightedDualVector p f)‖ := by
    nlinarith only [hcs, hupper, hnorm]
  have hscaled := mul_lt_mul_of_pos_left hlarge htau
  have hdom := mul_le_mul_of_nonneg_left (hdual (weightedDualVector p f)) (sq_nonneg M)
  apply (div_lt_iff₀ (pow_pos hM 2)).mpr
  nlinarith only [hscaled, hdom]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def normalizedOrthogonalChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := orthogonalBasisChart W (normalizedAxisBasis b)

theorem normalizedOrthogonalChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    normalizedOrthogonalChart W b x = (W.orthogonalProjectionOnto x,
      fun i => b.equivFun (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ)) := by
  rw [normalizedOrthogonalChart, orthogonalBasisChart_apply]
  refine Prod.ext rfl ?_
  funext i
  exact normalizedAxisBasis_coordinates b _ i

theorem normalizedOrthogonalChart_integer_coordinates (W : Submodule ℝ E)
    (b : Basis (Fin n) ℝ Wᗮ) (x : E)
    (hx : Wᗮ.orthogonalProjectionOnto x ∈ span ℤ (Set.range b)) :
    ∃ z : Fin n → ℤ, ∀ i,
      (normalizedOrthogonalChart W b x).2 i = (z i : ℝ) / (basisAxisScale b i : ℝ) := by
  have h := (b.mem_span_iff_repr_mem ℤ _).mp hx
  choose z hz using h
  refine ⟨z, ?_⟩
  intro i
  rw [normalizedOrthogonalChart_apply]
  change b.repr (Wᗮ.orthogonalProjectionOnto x) i / (basisAxisScale b i : ℝ) = _
  rw [← hz i]
  simp

variable [MeasurableSpace E] [BorelSpace E]

theorem normalizedOrthogonalChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis (Fin n) ℝ Wᗮ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) (x : E) :
    ‖normalizedOrthogonalChart W b x‖ ≤
      (1 + (n : ℝ) * n.factorial * (B + 1) ^ (n - 1) * D) * ‖x‖ := by
  apply orthogonalBasisChart_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_coordinates_bound o b hB hD hb hprod

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizedOrthogonalChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖b i‖ ≤ B) (p : W × (Fin n → ℝ)) :
    ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖ := by
  apply orthogonalBasisChart_symm_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_synthesis_bound b hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {D : Type*} [Fintype D] [IsEmpty D] {n : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem affineProfile_sample_coordinate (c x : ℝ) {w S : ℝ} (hw : 0 < w) (hS : 0 < S) :
    (x / S - c) / w = (x - c*S) / (w*S) := by
  field_simp [hw.ne', hS.ne']

theorem affineProductProfile_sample {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    coefficientWeight (affineProductProfile c w) S z = profileWidthFactor w *
      smoothProductProfile I (fun i => ((z i : ℝ) - c i * S i) / (w i * S i)) := by
  rw [coefficientWeight, affineProductProfile_eq]
  congr 1
  congr 1
  funext i
  exact affineProfile_sample_coordinate (c i) (z i) (hw i) (hS i)

theorem affineProductProfile_sample_sum {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    coefficientWeightSum (affineProductProfile c w) S =
      profileWidthFactor w * ∏ i, shiftedSmoothSampleSum (c i * S i) (w i * S i) := by
  unfold coefficientWeightSum
  simp_rw [affineProductProfile_sample c w S hw hS]
  rw [tsum_mul_left, shiftedSmoothProductSamples_sum _ _ (fun i => mul_pos (hw i) (hS i))]

theorem affineProductProfile_sample_sum_pos {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ w i * S i) :
    0 < coefficientWeightSum (affineProductProfile c w) S := by
  rw [affineProductProfile_sample_sum c w S hw hS]
  exact mul_pos (profileWidthFactor_pos w hw)
    (Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos _ (hlarge i)))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def normalizedIntegerPMF (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) : PMF ℤ :=
  shiftedSmoothCoefficientPMF (c * K) (δ * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge)

theorem normalizedIntegerPMF_apply (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal =
      smoothProbabilityProfile (((k : ℝ) - c * K) / (δ * K)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
  shiftedSmoothCoefficientPMF_apply _ _ _ _ _

theorem normalizedIntegerPMF_support (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K c δ hK hδ hlarge).support) :
    |(k : ℝ) / K - c| < 3 * δ / 4 := by
  have hb := shiftedSmoothCoefficientPMF_support (c * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge) hk
  rw [show (k : ℝ) / K - c = ((k : ℝ) - c * K) / K by field_simp,
    abs_div, abs_of_pos hK]
  apply (div_lt_iff₀ hK).mpr
  nlinarith

theorem normalizedIntegerPMF_cap (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal ≤ 2 / δ := by
  have hb := shiftedSmoothCoefficientPMF_le (c * K) hlarge k
  calc
    _ ≤ K * (2 / (δ * K)) := mul_le_mul_of_nonneg_left hb hK.le
    _ = 2 / δ := by field_simp

noncomputable def normalizedIntegerInterpolation (K c δ u : ℝ) : ℝ :=
  K * smoothProbabilityProfile ((u - c) / δ) / shiftedSmoothSampleSum (c * K) (δ * K)

theorem normalizedIntegerInterpolation_grid (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    normalizedIntegerInterpolation K c δ ((k : ℝ) / K) =
      K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal := by
  rw [normalizedIntegerInterpolation, affineProfile_sample_coordinate c (k : ℝ) hδ hK,
    normalizedIntegerPMF_apply, mul_div_assoc]

theorem normalizedIntegerInterpolation_range (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u : ℝ) :
    0 ≤ normalizedIntegerInterpolation K c δ u ∧
      normalizedIntegerInterpolation K c δ u ≤ 2 / δ := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  constructor
  · exact div_nonneg (mul_nonneg hK.le (smoothProbabilityProfile_range _).1) hZ.le
  · calc
      _ ≤ K / shiftedSmoothSampleSum (c * K) (δ * K) :=
        div_le_div_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range ((u-c)/δ)).2 hK.le)
          hZ.le
      _ ≤ 2 / δ := (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerPMF (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) : PMF ℤ :=
  if h : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then
    normalizedIntegerPMF K 0 δ hK hδ h
  else PMF.pure 0

theorem constantIntegerPMF_large (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    constantIntegerPMF K δ hK hδ = normalizedIntegerPMF K 0 δ hK hδ hlarge := by
  simp [constantIntegerPMF, hlarge]

theorem constantIntegerPMF_small (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hsmall : δ * K < 8 * (probabilityProfileLipschitz : ℝ)) :
    constantIntegerPMF K δ hK hδ = PMF.pure 0 ∧
      K < 8 * (probabilityProfileLipschitz : ℝ) / δ := by
  refine ⟨by simp [constantIntegerPMF, not_le.mpr hsmall], ?_⟩
  apply (lt_div_iff₀ hδ).mpr
  nlinarith

theorem constantIntegerPMF_support (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) {k : ℤ}
    (hk : k ∈ (constantIntegerPMF K δ hK hδ).support) :
    |(k : ℝ) / K| < 3 * δ / 4 := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge] at hk
    simpa only [sub_zero] using normalizedIntegerPMF_support K 0 δ hK hδ hlarge hk
  · rw [(constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).1] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero]
    positivity

theorem constantIntegerPMF_cap (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (k : ℤ) :
    K * (constantIntegerPMF K δ hK hδ k).toReal ≤
      8 * (probabilityProfileLipschitz : ℝ) / δ := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    refine (normalizedIntegerPMF_cap K 0 δ hK hδ hlarge k).trans ?_
    apply div_le_div_of_nonneg_right _ hδ.le
    have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
    linarith
  · have hKbound := (constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).2
    have hp : (constantIntegerPMF K δ hK hδ k).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((constantIntegerPMF K δ hK hδ).coe_le_one k)
    exact (mul_le_mul_of_nonneg_left hp hK.le).trans (by simpa only [mul_one] using hKbound.le)

end Erdos3

end

section

namespace Erdos3

def IsIntegerMassInterpolation (K : ℝ) (p : PMF ℤ) (B L : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ k : ℤ, f ((k : ℝ) / K) = K * (p k).toReal) ∧
  (∀ x, 0 ≤ f x ∧ f x ≤ B) ∧
  (∀ x y, |f x - f y| ≤ L * |x - y|)

theorem IsIntegerMassInterpolation.lipschitz {K B L : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using h.2.2 x y

theorem IsIntegerMassInterpolation.mono {K B L B' L' : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hB : B ≤ B') (hL : L ≤ L') :
    IsIntegerMassInterpolation K p B' L' f :=
  ⟨h.1, fun x => ⟨(h.2.1 x).1, (h.2.1 x).2.trans hB⟩,
    fun x y => (h.2.2 x y).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩

theorem normalizedIntegerInterpolation_difference (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (x y : ℝ) :
    |normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |x - y| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hlo := (shiftedSmoothSampleSum_bounds (c * K) hlarge).1
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith)
  have hprof := smoothProbabilityProfile_lipschitz.dist_le_mul ((x-c)/δ) ((y-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ] at hprof
  have he : normalizedIntegerInterpolation K c δ x - normalizedIntegerInterpolation K c δ y =
      (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        (smoothProbabilityProfile ((x-c)/δ) - smoothProbabilityProfile ((y-c)/δ)) := by
    unfold normalizedIntegerInterpolation
    ring
  rw [he, abs_mul, abs_of_pos (div_pos hK hZ)]
  calc
    _ ≤ (K / shiftedSmoothSampleSum (c*K) (δ*K)) *
        ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_left hprof (div_nonneg hK.le hZ.le)
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) * (|x-y| / δ)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

theorem normalizedIntegerInterpolation_spec (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    IsIntegerMassInterpolation K (normalizedIntegerPMF K c δ hK hδ hlarge)
      (2 / δ) (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) (normalizedIntegerInterpolation K c δ) :=
  ⟨normalizedIntegerInterpolation_grid K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_range K c δ hK hδ hlarge,
    normalizedIntegerInterpolation_difference K c δ hK hδ hlarge⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem normalizedIntegerInterpolation_lipschitz_bound (K c δ : ℝ)
    (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (u v : ℝ) :
    |normalizedIntegerInterpolation K c δ u - normalizedIntegerInterpolation K c δ v| ≤
      (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2) * |u - v| := by
  have hZ := shiftedSmoothSampleSum_pos (c * K) hlarge
  have hratio : K / shiftedSmoothSampleSum (c * K) (δ * K) ≤ 2 / δ :=
    (div_le_div_iff₀ hZ hδ).mpr (by nlinarith [(shiftedSmoothSampleSum_bounds (c * K) hlarge).1])
  have hb := smoothProbabilityProfile_lipschitz.dist_le_mul ((u-c)/δ) ((v-c)/δ)
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right,
    abs_div, abs_of_pos hδ] at hb
  rw [normalizedIntegerInterpolation, normalizedIntegerInterpolation,
    ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hZ]
  calc
    _ ≤ K * ((probabilityProfileLipschitz : ℝ) * (|u-v| / δ)) /
        shiftedSmoothSampleSum (c * K) (δ * K) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hK.le) hZ.le
    _ = (K / shiftedSmoothSampleSum (c * K) (δ * K)) *
        ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| := by ring
    _ ≤ (2 / δ) * ((probabilityProfileLipschitz : ℝ) / δ) * |u-v| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hratio
          (show 0 ≤ (probabilityProfileLipschitz : ℝ) / δ by positivity)) (abs_nonneg _)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

noncomputable def integerMassTent (K : ℝ) (a : ℤ) (x : ℝ) : ℝ :=
  K * max 0 (1 - 2 * |K * x - a|)

theorem integerMassTent_grid (K : ℝ) (hK : 0 < K) (a k : ℤ) :
    integerMassTent K a ((k : ℝ) / K) = K * ((PMF.pure a) k).toReal := by
  classical
  unfold integerMassTent
  rw [mul_div_cancel₀ _ hK.ne']
  by_cases h : k = a
  · subst k
    simp
  · have hn : (1 : ℤ) ≤ |k-a| := Int.one_le_abs (sub_ne_zero.mpr h)
    have hn' : (1 : ℝ) ≤ |(k : ℝ) - a| := by exact_mod_cast hn
    have hz : max 0 (1 - 2 * |(k : ℝ) - a|) = 0 := max_eq_left (by linarith)
    simp [hz, h]

theorem integerMassTent_range (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x : ℝ) :
    0 ≤ integerMassTent K a x ∧ integerMassTent K a x ≤ K := by
  refine ⟨mul_nonneg hK (le_max_left _ _), ?_⟩
  have ht : max 0 (1 - 2 * |K*x-a|) ≤ (1 : ℝ) :=
    max_le (by norm_num) (by linarith [abs_nonneg (K*x-a)])
  exact (mul_le_mul_of_nonneg_left ht hK).trans_eq (mul_one K)

theorem integerMassTent_difference (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x y : ℝ) :
    |integerMassTent K a x - integerMassTent K a y| ≤ (2 * K ^ 2) * |x-y| := by
  have hm : |max 0 (1 - 2 * |K*x-a|) - max 0 (1 - 2 * |K*y-a|)| ≤
      |(1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|)| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (1 - 2 * |K*x-a|) (1 - 2 * |K*y-a|) (0 : ℝ)
  have ha := abs_abs_sub_abs_le_abs_sub (K*x-a) (K*y-a)
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg hK] at ha
  have he : (1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|) =
      -(2 * (|K*x-a| - |K*y-a|)) := by ring
  rw [he, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm
  unfold integerMassTent
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  calc
    _ ≤ K * (2 * abs (|K*x-a| - |K*y-a|)) := mul_le_mul_of_nonneg_left hm hK
    _ ≤ K * (2 * (K * |x-y|)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ha (by norm_num)) hK
    _ = _ := by ring

theorem integerMassTent_spec (K : ℝ) (hK : 0 < K) (a : ℤ) :
    IsIntegerMassInterpolation K (PMF.pure a) K (2 * K ^ 2) (integerMassTent K a) :=
  ⟨integerMassTent_grid K hK a, integerMassTent_range K hK.le a, integerMassTent_difference K hK.le a⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerInterpolation (K δ : ℝ) : ℝ → ℝ :=
  if 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then normalizedIntegerInterpolation K 0 δ
  else integerMassTent K 0

noncomputable def constantIntegerInterpolationCap (δ : ℝ) : ℝ :=
  8 * (probabilityProfileLipschitz : ℝ) / δ

noncomputable def constantIntegerInterpolationLip (δ : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2)
    (2 * (constantIntegerInterpolationCap δ) ^ 2)

theorem constantIntegerInterpolation_spec (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    IsIntegerMassInterpolation K (constantIntegerPMF K δ hK hδ)
      (constantIntegerInterpolationCap δ) (constantIntegerInterpolationLip δ)
      (constantIntegerInterpolation K δ) := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (normalizedIntegerInterpolation_spec K 0 δ hK hδ hlarge).mono
    · apply div_le_div_of_nonneg_right _ hδ.le
      have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
      linarith
    · exact le_max_left _ _
  · obtain ⟨hp, hbound⟩ := constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)
    rw [hp]
    simp only [constantIntegerInterpolation, hlarge, ↓reduceIte]
    apply (integerMassTent_spec K hK 0).mono hbound.le
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK.le hbound.le 2) (by norm_num)).trans
      (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

noncomputable def integerRowMassTent (K : ℝ) (z : O → ℤ) (x : O → ℝ) : ℝ :=
  ∏ i, integerMassTent K (z i) (x i)

noncomputable def integerRowMassInterpolation (K : ℝ) (p : PMF (O → ℤ)) (x : O → ℝ) : ℝ :=
  ∫ z, integerRowMassTent K z x ∂p.toMeasure

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

noncomputable def normalizedIntegerRowInterpolation (K : ℝ) (p : PMF (O → ℤ))
    (x : O → ℝ) : ℝ := integerRowMassInterpolation K p x / K ^ Fintype.card O

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {O : Type*} [Fintype O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def mixedCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, (p j (x.2 j)).toReal

noncomputable def mixedCoefficientLaw {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) : Measure ((I → ℝ) × (J → ℤ)) :=
  (Measure.pi (fun i => affineCoefficientMeasure (c i) (w i))).prod
    (Measure.pi (fun j => (p j).toMeasure))

theorem mixedCoefficientLaw_probability {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    IsProbabilityMeasure (mixedCoefficientLaw c w p) := by
  let : ∀ i, IsProbabilityMeasure (affineCoefficientMeasure (c i) (w i)) :=
    fun i => affineCoefficientMeasure_probability (c i) (hw i)
  unfold mixedCoefficientLaw
  infer_instance

theorem mixedCoefficientDensity_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    0 ≤ mixedCoefficientDensity c w p x :=
  mul_nonneg (affineProductProfile_nonneg c w hw x.1)
    (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem mixedCoefficientLaw_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure
        ((volume : Measure (I → ℝ)).prod (Measure.pi (fun _ : J => (Measure.count : Measure ℤ))))
        (mixedCoefficientDensity c w p) := by
  have hc : Measure.pi (fun i => affineCoefficientMeasure (c i) (w i)) =
      realDensityMeasure volume (affineProductProfile c w) :=
    independentCoordinateDensity_measure (fun i => affineProbabilityProfile (c i) (w i))
      (fun i => affineProbabilityProfile_integrable (c i) (hw i))
      (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
      (fun i => affineProbabilityProfile_integral (c i) (hw i))
  rw [mixedCoefficientLaw, hc, independentIntegerLaw_density]
  exact binaryDensity_measure _ _ _ _ (affineProductProfile_contDiff c w).continuous.measurable
    (measurable_of_countable _) (affineProductProfile_nonneg c w hw)

theorem mixedCoefficientDensity_support {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) :
    mixedCoefficientDensity c w p x ≠ 0 ↔
      (∀ i, affineProbabilityProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ j, x.2 j ∈ (p j).support) := by
  classical
  simp only [mixedCoefficientDensity, affineProductProfile, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  constructor
  · intro h hz
    exact h (by rw [hz]; exact ENNReal.toReal_zero)
  · intro h
    exact (ENNReal.toReal_pos h ((p j).apply_ne_top _)).ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def constantCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (K δ : J → ℝ) (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) :
    ((I → ℝ) × (J → ℤ)) → ℝ :=
  mixedCoefficientDensity (fun _ => 0) w (fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j))

theorem constantCoefficientDensity_cap {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (K δ : J → ℝ)
    (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) {v B : ℝ}
    (hB : 0 ≤ B) (hvolume : v ≤ B * ∏ j, K j) (x : (I → ℝ) × (J → ℤ)) :
    v * constantCoefficientDensity w K δ hK hδ x ≤
      B * profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) := by
  let p : J → PMF ℤ := fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j)
  let f := affineProductProfile (fun _ => 0) w x.1
  have hf0 : 0 ≤ f := affineProductProfile_nonneg _ w hw x.1
  have hfcap : f ≤ profileWidthFactor w := by
    exact (le_abs_self f).trans (affineProductProfile_norm_le (fun _ => 0) w hw x.1)
  have hg0 : 0 ≤ ∏ j, (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hscaled0 : 0 ≤ ∏ j, K j * (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
  have hscaled : (∏ j, K j * (p j (x.2 j)).toReal) ≤
      ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) :=
    Finset.prod_le_prod (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
      (fun j _ => constantIntegerPMF_cap (K j) (δ j) (hK j) (hδ j) (x.2 j))
  change v * (f * ∏ j, (p j (x.2 j)).toReal) ≤ _
  calc
    _ ≤ (B * ∏ j, K j) * (f * ∏ j, (p j (x.2 j)).toReal) :=
      mul_le_mul_of_nonneg_right hvolume (mul_nonneg hf0 hg0)
    _ = B * (f * ∏ j, K j * (p j (x.2 j)).toReal) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ B * (profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hfcap hscaled hscaled0 (profileWidthFactor_pos w hw).le) hB
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {I Z : Type*} [Fintype I] [Fintype Z]

noncomputable def mixedDensityInterpolation (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (x : (I → ℝ) × (Z → ℝ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, f j (x.2 j)

theorem mixedDensityInterpolation_grid (c w : I → ℝ) (f : Z → ℝ → ℝ)
    (K : Z → ℝ) (p : Z → PMF ℤ) (hf : ∀ j (k : ℤ), f j ((k : ℝ) / K j) = K j * (p j k).toReal)
    (u : I → ℝ) (z : Z → ℤ) :
    mixedDensityInterpolation c w f (u, fun j => (z j : ℝ) / K j) =
      (∏ j, K j) * mixedCoefficientDensity c w p (u, z) := by
  simp only [mixedDensityInterpolation, mixedCoefficientDensity, hf, Finset.prod_mul_distrib]
  ring

theorem mixedDensityInterpolation_bounds (c w : I → ℝ) (f : Z → ℝ → ℝ)
    {δ B L : ℝ≥0} (hδ : 0 < δ) (hw : ∀ i, (δ : ℝ) ≤ w i) (hB : 1 ≤ B)
    (hf : ∀ j, LipschitzWith L (f j)) (hb : ∀ j x, 0 ≤ f j x ∧ f j x ≤ B) :
    (∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧
      mixedDensityInterpolation c w f x ≤ (δ : ℝ)⁻¹^Fintype.card I * (B : ℝ)^Fintype.card Z) ∧
    LipschitzWith (δ⁻¹^Fintype.card I * (Fintype.card Z * L * B^Fintype.card Z) +
      B^Fintype.card Z * affineProductProfileLip I δ) (mixedDensityInterpolation c w f) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hwpos : ∀ i, 0 < w i := fun i => hδr.trans_le (hw i)
  have hp (j : Z) : LipschitzWith L (fun x : (I → ℝ) × (Z → ℝ) => f j (x.2 j)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf j).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      ((dist_le_pi_dist x.2 y.2 j).trans (le_max_right _ _)) L.coe_nonneg)
  obtain ⟨hprod, hlprod⟩ := bounded_lipschitz_real_prod
    (fun j (x : (I → ℝ) × (Z → ℝ)) => f j (x.2 j)) hB hp
    (fun j x => by rw [abs_of_nonneg (hb j _).1]; exact (hb j _).2)
  have hlcont : LipschitzWith (affineProductProfileLip I δ)
      (fun x : (I → ℝ) × (Z → ℝ) => affineProductProfile c w x.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((affineProductProfile_lipschitz c w hδ hw).dist_le_mul x.1 y.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg _))
  have hc (x : (I → ℝ) × (Z → ℝ)) :
      |affineProductProfile c w x.1| ≤ ((δ⁻¹^Fintype.card I : ℝ≥0) : ℝ) := by
    simpa only [Real.norm_eq_abs, NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap c w hδr hw x.1
  refine ⟨?_, lipschitz_real_mul_of_bounds _ _ hlcont hlprod hc ?_⟩
  · intro x
    have h0 : 0 ≤ ∏ j, f j (x.2 j) := Finset.prod_nonneg (fun j _ => (hb j _).1)
    refine ⟨mul_nonneg (affineProductProfile_nonneg c w hwpos x.1) h0, ?_⟩
    have ha := hc x
    have hz := hprod x
    rw [abs_of_nonneg (affineProductProfile_nonneg c w hwpos x.1)] at ha
    rw [abs_of_nonneg h0] at hz
    exact mul_le_mul ha hz h0 (by positivity)
  · intro x
    simpa only [NNReal.coe_pow] using hprod x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoefficientCounting
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem integerCoordinate_count {J : Type*} [Fintype J] :
    Measure.pi (fun _ : J => (Measure.count : Measure ℤ)) = (Measure.count : Measure (J → ℤ)) := by
  apply Measure.ext_of_singleton
  intro z
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

theorem mixedCoefficientLaw_count_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure ((volume : Measure (I → ℝ)).prod (Measure.count : Measure (J → ℤ)))
        (mixedCoefficientDensity c w p) := by
  simpa only [integerCoordinate_count] using mixedCoefficientLaw_density c w hw p

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def principalIntegerPMF (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) : PMF ℤ :=
  normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) (div_pos hK hT) (by positivity) hlarge

theorem principalIntegerPMF_support {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    {k : ℤ} (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    γ < T * (k : ℝ) / K ∧ T * (k : ℝ) / K < 2 * γ := by
  have hb := normalizedIntegerPMF_support (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge hk
  have he : (k : ℝ) / (K / T) = T * (k : ℝ) / K := by field_simp
  rw [he] at hb
  constructor <;> nlinarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
namespace OAI

section

namespace Erdos3

noncomputable def integerAxisSideLength (h K L : ℕ) (γ : ℝ) : ℕ :=
  if L ^ h < K then L else inactiveSideLength h K (inactiveDenominator γ)

theorem integerAxisSideLength_pos {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    0 < integerAxisSideLength h K L γ := by
  unfold integerAxisSideLength
  split_ifs
  · exact hL
  · exact inactiveSideLength_pos hh (inactiveDenominator_pos γ)

theorem integerAxisSideLength_le {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    integerAxisSideLength h K L γ ≤ L := by
  unfold integerAxisSideLength
  split_ifs with ha
  · exact le_rfl
  · exact inactiveSideLength_le hh hL (Nat.le_of_not_gt ha)

theorem integerAxisPrincipal_width {h K L : ℕ} (hh : 0 < h) (hL : 0 < L)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : (principalSamplingGapRatio γ * L) ^ h ≤ K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * ((K : ℝ) / (L : ℝ) ^ h) := by
  apply coefficient_gap_principal_width (A := (principalSamplingGapRatio γ : ℝ)) (by exact_mod_cast hL)
    (by exact_mod_cast principalSamplingGapRatio_one_le γ) hγ hh
  · exact_mod_cast hgap
  · exact principalSamplingGapRatio_width hγ

noncomputable def integerAxisPrincipalPMF (h K L : ℕ) (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) (γ : ℝ) (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) : PMF ℤ :=
  if ha : L ^ h < K then
    principalIntegerPMF K ((L : ℝ) ^ h) γ (by exact_mod_cast hK)
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))
  else inactivePrincipalPMF K (inactiveDenominator γ)

theorem integerAxisPrincipalPMF_active {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : L ^ h < K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    γ < (L : ℝ) ^ h * (k : ℝ) / K ∧ (L : ℝ) ^ h * (k : ℝ) / K < 2 * γ := by
  simp only [integerAxisPrincipalPMF, ha, ↓reduceDIte] at hk
  exact principalIntegerPMF_support (by exact_mod_cast hK)
    (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha)) hk

theorem integerAxisPrincipalPMF_inactive {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : K ≤ L ^ h) :
    integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap =
      inactivePrincipalPMF K (inactiveDenominator γ) := by
  simp [integerAxisPrincipalPMF, Nat.not_lt.mpr ha]

theorem integerAxisPrincipalPMF_bound {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    |(k : ℝ) / K| * (integerAxisSideLength h K L γ : ℝ) ^ h ≤ 2 * γ := by
  by_cases ha : L ^ h < K
  · have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap ha hk
    have he : |(k : ℝ) / K| * (L : ℝ) ^ h = |(L : ℝ) ^ h * (k : ℝ) / K| := by
      calc
        _ = |((k : ℝ) / K) * (L : ℝ) ^ h| := by
          rw [abs_mul, abs_of_pos (pow_pos (show (0 : ℝ) < L by exact_mod_cast hL) h)]
        _ = _ := by congr 1; ring
    simp only [integerAxisSideLength, ha, ↓reduceIte]
    rw [he, abs_of_pos (hγ.trans hb.1)]
    exact hb.2.le
  · rw [integerAxisPrincipalPMF_inactive hh hK hL hγ hgap (Nat.le_of_not_gt ha)] at hk
    rw [inactivePrincipalPMF_support hk]
    simp only [integerAxisSideLength, ha, ↓reduceIte, abs_div,
      abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
    calc
      _ = |(inactivePrincipalCoefficient K (inactiveDenominator γ) : ℝ)| *
          (inactiveSideLength h K (inactiveDenominator γ) : ℝ) ^ h / K := by ring
      _ ≤ 1 / (inactiveDenominator γ : ℝ) :=
        inactivePrincipal_scaled_upper hh hK (inactiveDenominator_pos γ)
      _ ≤ γ := inactiveDenominator_bound hγ
      _ ≤ 2 * γ := by linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
namespace OAI

section

namespace Erdos3

def positiveModerateLengthExponent (n : ℕ) : ℕ :=
  majorArcLengthExponent n + majorArcLengthExponent (n + 1)

noncomputable def positiveModerateLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  1 + majorArcLengthConstant n U + majorArcLengthConstant (n + 1) U

def positiveModerateCoverExponent (n j : ℕ) : ℕ :=
  majorArcLengthExponent (n + 1) + majorArcCoverExponent n j +
    majorArcCoverExponent (n + 1) j

noncomputable def positiveModerateCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (1 + majorArcLengthConstant (n + 1) U) * majorArcCoverConstant n j U (4 * V) +
    majorArcCoverConstant (n + 1) j U V

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteExcessMassCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def excessMass {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : ℝ :=
  ∑ x, max (q.weight x - C * p.weight x) 0

theorem excessMass_nonneg {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) : 0 ≤ p.excessMass q C :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem excessMass_le_of_mass_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ}
    (h : ∀ G : Finset X, q.mass G ≤ C * p.mass G + ε) : p.excessMass q C ≤ ε := by
  let G := Finset.univ.filter (fun x => 0 < q.weight x - C * p.weight x)
  have he : p.excessMass q C = q.mass G - C * p.mass G := by
    have hsum : (∑ x, max (q.weight x - C * p.weight x) 0) =
        ∑ x ∈ G, (q.weight x - C * p.weight x) := by
      simp only [G, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < q.weight x - C * p.weight x
      · simp only [hx, ite_true, max_eq_left hx.le]
      · simp only [hx, ite_false, max_eq_right (le_of_not_gt hx)]
    rw [excessMass, hsum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [he]
  linarith [h G]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem excessMass_antitone_cap {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) :
    Antitone (reference.excessMass law) := by
  intro C D hCD
  apply Finset.sum_le_sum
  intro x _
  exact max_le_max (sub_le_sub_left
    (mul_le_mul_of_nonneg_right hCD (reference.nonneg x)) _) le_rfl

theorem excessMass_max_one_le {X : Type*} [Fintype X]
    (reference law : FiniteProbabilityWeights X) (C : ℝ) :
    reference.excessMass law (max 1 C) ≤ reference.excessMass law C :=
  reference.excessMass_antitone_cap law (le_max_right _ _)

end Erdos3.FiniteProbabilityWeights

namespace Erdos3

theorem marginalCap_max_one_exp_bound {C p : ℝ} (hp : 0 ≤ p)
    (hC : C ≤ Real.exp p) :
    1 ≤ max 1 C ∧ max 1 C ≤ Real.exp p :=
  ⟨le_max_left _ _, max_le (Real.one_le_exp hp) hC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_mono_on_support {f g : Ω → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

theorem abs_mean_le_mean_abs (f : Ω → ℝ) : |p.mean f| ≤ p.mean (fun x => |f x|) := by
  unfold mean
  calc
    _ ≤ ∑ x, |p.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]

theorem abs_mean_le_on_support (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ x, p.weight x ≠ 0 → |f x| ≤ C) : |p.mean f| ≤ C := by
  exact (p.abs_mean_le_mean_abs f).trans
    ((p.mean_mono_on_support hf).trans_eq (p.mean_const C))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

def ProductDependsOn {I : Type*} {X : I → Type*} (S : Finset I)
    (f : (∀ i, X i) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productConditionalMean (S : Finset I)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean (fun y => f (productCoordinateMix S x y))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def finiteWeightDensity (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (x : Ω) : ℝ := w x / p.weight x

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def productFiberIndicator {I : Type*} {X : I → Type*}
    (S : Finset I) (x y : ∀ i, X i) : ℝ :=
  if ∀ i ∈ S, y i = x i then 1 else 0

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

noncomputable def productFiberMass (w : (∀ i, X i) → ℝ) (S : Finset I)
    (x : ∀ i, X i) : ℝ := ∑ y, w y * productFiberIndicator S x y

theorem productFiberMass_nonneg (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : 0 ≤ productFiberMass w S x := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hw y)
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem productFiberMass_empty (w : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productFiberMass w ∅ x = ∑ y, w y := by
  simp [productFiberMass, productFiberIndicator]

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

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def observedProductDensity {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ) : (∀ i, X i) → ℝ :=
  finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun y => p.fiberMean F y f)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def smoothSourceFiniteWeights {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (rectangularWeightIndices a S 1) where
  weight z := (shiftedSmoothProductPMF a S hS hZ z.val).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
      (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal)]
    have h : (∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal) =
        ∑ z ∈ rectangularWeightIndices a S 1, (shiftedSmoothProductPMF a S hS hZ z).toReal :=
      (hasSum_sum_of_ne_finset_zero (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)).tsum_eq
    rw [← h]
    exact shiftedSmoothProductPMF_toReal_sum a S hS hZ

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PeriodicKernelPartition
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ} {ι : Type*} [Fintype ι]

noncomputable def translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ := ∑ i, Φ.periodicValue (x - c i)

theorem translateSum_nonneg (Φ : PatchKernel d) (c : ι → Fin d → ℝ) (x : Fin d → ℝ) :
    0 ≤ Φ.translateSum c x := Finset.sum_nonneg (fun i _ => (Φ.periodicValue_mem_Icc (x - c i)).1)

theorem periodicValue_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.periodicValue (x - c i) ≤ Φ.translateSum c x := by
  exact Finset.single_le_sum (f := fun j => Φ.periodicValue (x - c j))
    (fun j _ => (Φ.periodicValue_mem_Icc (x - c j)).1) (Finset.mem_univ i)

theorem abs_translateSum_sub_le (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x y : Fin d → ℝ) :
    |Φ.translateSum c x - Φ.translateSum c y| ≤ Fintype.card ι * Φ.lip * dist x y := by
  unfold translateSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Φ.periodicValue (x - c i) - Φ.periodicValue (y - c i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (Φ.lip : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.dist_eq, dist_sub_right] using Φ.periodicValue_lipschitz.dist_le_mul
        (x - c i) (y - c i)
    _ = _ := by simp [mul_assoc]

theorem kernel_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.value x ≤ Φ.translateSum c (c i - x) := by
  have hk := Φ.kernel_le_periodicValue (-x) 0
  have hs := Φ.periodicValue_le_translateSum c i (c i - x)
  have heq : c i - x - c i = -x := by abel
  rw [heq] at hs
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.neg_apply, zero_sub, neg_neg] using hk.trans hs

noncomputable def normalizedTranslate (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x) (i : ι) :
    PatchKernel d where
  value x := Φ.value x / Φ.translateSum c (c i - x)
  nonneg x := div_nonneg (Φ.nonneg x) (Φ.translateSum_nonneg c _)
  le_one x := by
    apply (div_le_one ((show (0 : ℝ) < δ from hδ).trans_le (hcover (c i - x)))).mpr
    exact Φ.kernel_le_translateSum c i x
  support x hx := Φ.support x (fun h => hx (by simp only [h, zero_div]))
  lip := Φ.lip / δ + Fintype.card ι * Φ.lip / (δ * δ)
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hnum := Φ.lipschitz.dist_le_mul x y
    have hden := Φ.abs_translateSum_sub_le c (c i - x) (c i - y)
    rw [dist_sub_left] at hden
    have h := abs_div_sub_div_bound (show (0 : ℝ) < δ from hδ) (hcover _) (hcover _)
      (mul_nonneg Φ.lip.coe_nonneg dist_nonneg) zero_le_one
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * Φ.lip * dist x y)
      hnum (by rw [abs_of_nonneg (Φ.nonneg _)]; exact Φ.le_one _) hden
    apply h.trans_eq
    push_cast
    ring

end Erdos3.PatchKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

def weightedPatchVariableWeight {σ : Type*} {d : ℕ}
    (p : σ → ℕ) (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim p (fun j => w (earlierSlot i j))

structure WeightedParameterSlots (σ : Type*) (p : σ → ℕ) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (weightedPatchVariableWeight p w i) (w i)

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : WeightedParameterSlots σ p d w) (t : σ → ℝ) :
    TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) j.isLt

end WeightedParameterSlots

structure WeightedParameterPatch (σ : Type*) (p : σ → ℕ) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : WeightedParameterSlots σ p d weight
  kernel : PatchKernel d

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

noncomputable def value (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

end WeightedParameterPatch

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

def weightedParameters (A : PolynomialPatch σ s d) :
    WeightedParameterPatch σ (fun _ => 1) s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := { center := A.form.center, degree := A.form.degree }
  kernel := A.kernel

@[simp] theorem weightedParameters_value (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.weightedParameters.value t = A.value t := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace SlotInterleaving

end SlotInterleaving

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertSubstitution (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) : (σ ⊕ Fin D) ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim
    (Sum.elim (fun a => X (Sum.inl a))
      (fun j => if h : (I.left j).val < k.val then X (Sum.inr ⟨_, h⟩) else 0))
    (fun j => PolynomialSlots.placementSubstitution I.right k i (Sum.inr j))

theorem insertSubstitution_degree (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) (a : (σ ⊕ Fin D) ⊕ Fin i.val) :
    insertSubstitution I k i a ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k)
      (weightedPatchVariableWeight (Sum.elim (fun _ : σ => 1) w) v i a) := by
  rcases a with (a | j) | j
  · exact weightedSupportLE_X _ (Sum.inl a)
  · simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) (I.fill w v) k)
        (Sum.inr (⟨(I.left j).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (I.fill w v (I.left j)) at hX
      rw [I.fill_left] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem
  · exact PolynomialSlots.placementSubstitution_degree I.right
      (fun j => I.fill_right w v j) k i (Sum.inr j)

noncomputable def insertCenter
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (insertSubstitution I k i) (B.center i)

theorem insertCenter_degree
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    B.insertCenter I k i ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k) (v i) :=
  weightedSupportLE_aeval _ _ _ (insertSubstitution_degree I k i) (B.degree i)

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertLifts (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) : PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using B.insertCenter_degree I k i

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (i : Fin d) (a : σ ⊕ Fin i.val) :
    parameterSubstitution f i a ∈ weightedSupportLE (weightedPatchVariableWeight q w i)
      (weightedPatchVariableWeight p w i a) := by
  cases a with
  | inl a =>
    apply weightedSupportLE_aeval q (weightedPatchVariableWeight q w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterSlots τ q d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

noncomputable def reparam (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterPatch τ q s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

@[simp] theorem reparam_lip (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) :
    (A.reparam f hf).kernel.lip = A.kernel.lip := rfl

end WeightedParameterPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

noncomputable def imageMeasure {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : Measure Y :=
  ∑ x, ENNReal.ofReal (p.weight x) • Measure.dirac (F x)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeProbabilityDensity (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := scalarCubeIndicator I x / volume.real (scalarCubeDomain I)

noncomputable def scalarCubeGridDensity (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (x : Option I → ℝ) : ℝ :=
  scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGrid_small_error_of_length (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} (hL : 0 < L)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L) :
    scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hV := scalarCubeDomain_volumeReal_pos I
  have h := (div_le_iff₀ hV).mp hlarge
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hLp).mpr
  nlinarith [mul_pos hLp hV]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

def scalarCubeRiemannLog {A : Type*} [Semiring A] (D : A) : A :=
  (D + 1) ^ 2 + 4 * D + 2

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def progressionSliceLengthLog {A : Type*} [Semiring A] (D E F T : A) : A :=
  E + F + T + D + scalarCubeRiemannLog D + 5

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productSubtypePoint (S : Finset I) (z : ∀ i : S, X i) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else base i

theorem productSubtypePoint_apply_mem (S : Finset I) (z : ∀ i : S, X i)
    (base : ∀ i, X i) (i : S) : productSubtypePoint S z base i = z i := by
  simp only [productSubtypePoint, dif_pos i.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

omit [Fintype ι] [∀ i, Fintype (X i)] in
theorem productFiberIndicator_subtype (I : Finset ι) (a : ∀ i : I, X i)
    (base x : ∀ i, X i) :
    productFiberIndicator I (productSubtypePoint I a base) x =
      if (fun i : I => x i) = a then 1 else 0 := by
  have he : (∀ i ∈ I, x i = productSubtypePoint I a base i) ↔
      (fun i : I => x i) = a := by
    constructor
    · intro h
      funext i
      exact (h i i.property).trans (productSubtypePoint_apply_mem I a base i)
    · intro h i hi
      exact (congrFun h ⟨i, hi⟩).trans (productSubtypePoint_apply_mem I a base ⟨i, hi⟩).symm
  simp only [productFiberIndicator, he]

omit [Fintype ι] in
theorem productFiberIndicator_sum_subtype (I : Finset ι) (base x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x) = 1 := by
  simp [productFiberIndicator_subtype]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

noncomputable abbrev productTupleIndexEquiv (a : J → I) (ha : Function.Injective a) :
    J ≃ ↥(Finset.univ.image a) :=
  Equiv.ofBijective (fun j => ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    ⟨fun _ _ h => ha (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩

noncomputable def productTuplePoint (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) : ∀ i, X i :=
  productSubtypePoint (Finset.univ.image a)
    (Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i)
      (productTupleIndexEquiv a ha) v) base

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonPolynomialScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerPolynomialInitialScale (ε : ℝ) : ℕ :=
  max 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊

theorem integerPolynomialInitialScale_width {ε : ℝ} (hε : 0 < ε) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ ε * integerPolynomialInitialScale ε := by
  have hb : 8 * (probabilityProfileLipschitz : ℝ) / ε ≤ (integerPolynomialInitialScale ε : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊))
  have hm := (div_le_iff₀ hε).mp hb
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonPolynomialGapRatio {I : Type*} [Fintype I] (γ : I → ℝ) : ℕ :=
  max 1 (Finset.univ.sup (fun i => principalSamplingGapRatio (γ i)))

theorem commonPolynomialGapRatio_one_le {I : Type*} [Fintype I] (γ : I → ℝ) :
    1 ≤ commonPolynomialGapRatio γ := le_max_left _ _

theorem commonPolynomialGapRatio_le {I : Type*} [Fintype I] (γ : I → ℝ) (i : I) :
    principalSamplingGapRatio (γ i) ≤ commonPolynomialGapRatio γ := by
  classical
  exact (Finset.le_sup (f := fun i => principalSamplingGapRatio (γ i)) (Finset.mem_univ i)).trans
    (le_max_right _ _)

noncomputable def commonPolynomialInitialScale {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) : ℕ :=
  max L₀ (max 1 (Finset.univ.sup (fun j => integerPolynomialInitialScale (ε j))))

theorem commonPolynomialInitialScale_pos {J : Type*} [Fintype J] (L₀ : ℕ) (ε : J → ℝ) :
    0 < commonPolynomialInitialScale L₀ ε :=
  Nat.zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_right _ _))

theorem commonPolynomialInitialScale_le {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) (j : J) :
    integerPolynomialInitialScale (ε j) ≤ commonPolynomialInitialScale L₀ ε := by
  classical
  exact (Finset.le_sup (f := fun j => integerPolynomialInitialScale (ε j)) (Finset.mem_univ j)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem exists_common_polynomial_scale {I J : Type*} [Fintype I] [Fintype J]
    (K h : I → ℕ) (γ : I → ℝ) (ε : J → ℝ) (hε : ∀ j, 0 < ε j) (L₀ : ℕ) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧
      L ≤ commonPolynomialInitialScale L₀ ε * commonPolynomialGapRatio γ ^ Fintype.card I ∧
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ ε j * L) ∧
      ∀ i, L ^ h i < K i → (principalSamplingGapRatio (γ i) * L) ^ h i ≤ K i := by
  obtain ⟨L, hL, hlo, hhi, hgap⟩ := exists_integer_coefficient_scale_gap
    (fun i => (K i : ℝ)) h (commonPolynomialInitialScale L₀ ε) (commonPolynomialGapRatio γ)
    (commonPolynomialInitialScale_pos L₀ ε) (commonPolynomialGapRatio_one_le γ)
  refine ⟨L, hL, (le_max_left _ _).trans hlo, hhi, ?_, ?_⟩
  · intro j
    apply (integerPolynomialInitialScale_width (hε j)).trans
    apply mul_le_mul_of_nonneg_left _ (hε j).le
    exact_mod_cast (commonPolynomialInitialScale_le L₀ ε j).trans hlo
  · intro i hi
    have hb : (commonPolynomialGapRatio γ * L) ^ h i ≤ K i := by
      have hg := hgap i (by exact_mod_cast hi)
      exact_mod_cast hg
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right L (commonPolynomialGapRatio_le γ i)) (h i)).trans hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalIntegerInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalIntegerInterpolation (K T γ x : ℝ) : ℝ :=
  T * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (T*x)

theorem principalIntegerInterpolation_grid (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (k : ℤ) :
    principalIntegerInterpolation K T γ ((k : ℝ) / K) =
      K * (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  unfold principalIntegerInterpolation principalIntegerPMF
  rw [show T*((k : ℝ)/K) = (k : ℝ)/(K/T) by field_simp,
    normalizedIntegerInterpolation_grid _ _ _ (div_pos hK hT) (by positivity) hlarge]
  field_simp

theorem principalIntegerInterpolation_range (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x : ℝ) :
    0 ≤ principalIntegerInterpolation K T γ x ∧ principalIntegerInterpolation K T γ x ≤ 4*T/γ := by
  have h := normalizedIntegerInterpolation_range (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x)
  refine ⟨mul_nonneg hT.le h.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left h.2 hT.le).trans_eq (by ring)

theorem principalIntegerInterpolation_difference (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x y : ℝ) :
    |principalIntegerInterpolation K T γ x - principalIntegerInterpolation K T γ y| ≤
      (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) * |x-y| := by
  have h := normalizedIntegerInterpolation_difference (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x) (T*y)
  rw [← mul_sub, abs_mul, abs_of_pos hT] at h
  unfold principalIntegerInterpolation
  rw [← mul_sub, abs_mul, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left h hT.le).trans_eq (by ring)

theorem principalIntegerInterpolation_spec (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    IsIntegerMassInterpolation K (principalIntegerPMF K T γ hK hT hγ hlarge)
      (4*T/γ) (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) (principalIntegerInterpolation K T γ) :=
  ⟨principalIntegerInterpolation_grid K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_range K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_difference K T γ hK hT hγ hlarge⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModeRankLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def modeRankLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + 1 + ∑ i : Fin m,
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)

theorem modeRankLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeRankLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  unfold modeRankLog
  positivity

theorem modeRemovalRankThreshold_le_exp (m n d : ℕ) {P C D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hd : (d : ℝ) ≤ P)
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalRankThreshold m n d C D S ρ ε ≤ Real.exp (modeRankLog m P) := by
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  let A := 2 * modeRemovalShrink m d D ρ ε
  have hB : B ≤ Real.exp (modeBiasLog m P) := chosenBiasBudget_le_exp m hP hε hεInv
  have hB0 : 0 ≤ B := zero_le_one.trans (finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε))
  have hT0 := modeRemovalShrink_one_le m d hD hρ hε
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hT := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hA : A ≤ Real.exp (modeShrinkLog m P + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (modeShrinkLog m P) := by dsimp [A]; gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hnp : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have hBL := modeBiasLog_nonneg m hP
  have hTL := modeShrinkLog_nonneg m hP
  let cost (i : Fin m) := ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
    (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) +
    (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B)
  let bound (i : Fin m) :=
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)
  have hbound i : 0 ≤ bound i := by dsimp [bound]; positivity
  have hcost (i : Fin m) : cost i ≤ Real.exp (bound i) := by
    have hf : ((i.val + 1).factorial : ℝ) ≤ Real.exp ((i.val + 1).factorial : ℝ) := by
      linarith [Real.add_one_le_exp ((i.val + 1).factorial : ℝ)]
    have hrow : ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤
        Real.exp (((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) := by
      calc
        _ ≤ Real.exp ((i.val + 1).factorial : ℝ) * (Real.exp P * (Real.exp P) ^ (i.val + 1)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hden : (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) ≤
        Real.exp (P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
      calc
        _ ≤ (Real.exp (modeBiasLog m P) * (Real.exp P) ^ (i.val + 1)) ^ (n ^ (i.val + 1)) := by gcongr
        _ = Real.exp ((n : ℝ) ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, Nat.cast_pow]
        _ ≤ _ := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _) (by positivity))
    have hcoeff : (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤
        Real.exp ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) := by
      calc
        _ ≤ (Real.exp P) ^ (i.val + 1) * ((Real.exp (modeShrinkLog m P + 2)) ^ (i.val + 1) *
          Real.exp (modeBiasLog m P)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hrow hden
    have hsum' := add_le_exp_add_one (by positivity) (by positivity) hsum hcoeff
    convert hsum' using 1
    congr 1
    dsimp [bound]
    ring
  have hsum := sum_le_exp_card_add_sum cost bound hbound hcost
  have hout := one_add_le_exp_succ (by positivity) hsum
  change 1 + ∑ i : Fin m, cost i ≤ _
  convert hout using 1
  congr 1
  simp only [modeRankLog, Fintype.card_fin]
  dsimp [bound]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ModeLogPolynomials
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def modeProfileLogPolynomial : Polynomial ℕ := 5 * X + C modeProfileBound + 4

noncomputable def modeBiasLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C (finiteLayerInverseConstant m) + C (finiteLayerInverseExponent m) * (C (2 ^ m) * (X + 2))

noncomputable def modeShrinkLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + modeProfileLogPolynomial + 3 * X + 4

noncomputable def modeSideLogPolynomial (m : ℕ) : Polynomial ℕ :=
  (X + modeShrinkLogPolynomial m + modeBiasLogPolynomial m + 1) + (X + modeProfileLogPolynomial + 3) + 2

noncomputable def modeRankLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + 1 + ∑ i : Fin m,
    ((C (i.val + 1).factorial + X + C (i.val + 1) * X) +
      X ^ (i.val + 1) * (modeBiasLogPolynomial m + C (i.val + 1) * X) +
      (C (i.val + 1) * X + C (i.val + 1) * (modeShrinkLogPolynomial m + 2) + modeBiasLogPolynomial m) + 2)

theorem modeProfileLogPolynomial_eval (P : ℝ) :
    modeProfileLogPolynomial.eval₂ (Nat.castRingHom ℝ) P = modeProfileLog P := by
  simp [modeProfileLogPolynomial, modeProfileLog]

theorem modeBiasLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeBiasLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeBiasLog m P := by
  simp [modeBiasLogPolynomial, modeBiasLog, finiteLayerInverseLog, Polynomial.eval₂_pow]

theorem modeShrinkLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeShrinkLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeShrinkLog m P := by
  simp [modeShrinkLogPolynomial, modeShrinkLog, modeProfileLogPolynomial_eval]

theorem modeSideLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeSideLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeSideLog m P := by
  simp [modeSideLogPolynomial, modeSideLog, modeProfileLogPolynomial_eval,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

theorem modeRankLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeRankLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeRankLog m P := by
  simp [modeRankLogPolynomial, modeRankLog, Polynomial.eval₂_finsetSum,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

theorem exists_mode_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget (modeSideLogPolynomial m + modeRankLogPolynomial m)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hp : modeSideLog m P + modeRankLog m P ≤ (P + K) ^ K := by
    simpa only [Polynomial.eval₂_add, modeSideLogPolynomial_eval, modeRankLogPolynomial_eval] using hpoly P hP
  have hs := modeSideLog_nonneg m hP
  have hr := modeRankLog_nonneg m hP
  constructor
  · exact (modeRemovalSideThreshold_le_exp m d hP hd hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))
  · exact (modeRemovalRankThreshold_le_exp m n d hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mass_above_double_cap_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤
      2 * p.excessMass q C := by
  let S := Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)
  calc
    q.mass S ≤ ∑ x ∈ S, 2 * max (q.weight x - C*p.weight x) 0 := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      have he := le_max_left (q.weight x - C*p.weight x) 0
      nlinarith
    _ = 2 * ∑ x ∈ S, max (q.weight x - C*p.weight x) 0 := by rw [Finset.mul_sum]
    _ ≤ 2 * p.excessMass q C := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => le_max_right _ _)

theorem mass_above_double_cap_le_of_excess {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ} (h : p.excessMass q C ≤ ε) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤ 2*ε :=
  (mass_above_double_cap_le p q C).trans (mul_le_mul_of_nonneg_left h (by norm_num))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {I K : Type*} [Fintype I] [Fintype K]
variable (root : K → ℤ) (stride : I → ℕ)
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
variable {C ε : ℝ}

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem trimmedIntegerBox_card_ratio_le_two {I : Type*} [Fintype I] [DecidableEq I]
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2) :
    ((integerBox N).card : ℝ) / (trimmedIntegerBox N R).card ≤ 2 := by
  have hA : (0 : ℝ) < (trimmedIntegerBox N R).card := by
    exact_mod_cast (trimmedIntegerBox_nonempty N R hR).card_pos
  have hN (i : I) : 0 < N i := lt_of_le_of_lt (Nat.zero_le _) (hR i)
  have hBnat : 0 < (integerBox N).card := by
    rw [card_integerBox]
    exact Finset.prod_pos (fun i _ => hN i)
  have hB : (0 : ℝ) < (integerBox N).card := by exact_mod_cast hBnat
  have h := (trimmedIntegerBox_card_deficit N R hN (fun i => (hR i).le)).trans hloss
  have hh : (1/2 : ℝ) ≤ ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card := by linarith
  have hm := (le_div_iff₀ hB).mp hh
  apply (div_le_iff₀ hA).mpr
  linarith

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteRelativeDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable def relativeDensity (p q : FiniteProbabilityWeights Ω) (x : Ω) : ℝ :=
  q.weight x / p.weight x

theorem relativeDensity_nonneg (p q : FiniteProbabilityWeights Ω) (x : Ω) :
    0 ≤ p.relativeDensity q x := div_nonneg (q.nonneg x) (p.nonneg x)

theorem mean_relativeDensity (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (f : Ω → ℝ) : p.mean (fun x => p.relativeDensity q x * f x) = q.mean f := by
  unfold mean relativeDensity
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(hp x).ne']

theorem relativeDensity_tail_mass (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (C : ℝ) :
    p.mean (fun x => if x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ C)
      then 0 else p.relativeDensity q x) =
      q.mass (Finset.univ.filter (fun x => C*p.weight x < q.weight x)) := by
  simp only [mean, mass, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : C*p.weight x < q.weight x
  · have hd : ¬p.relativeDensity q x ≤ C := by
      simpa only [relativeDensity, div_le_iff₀ (hp x), not_le] using hx
    simp only [hd, ite_false, hx, ite_true]
    change p.weight x * (q.weight x / p.weight x) = q.weight x
    field_simp [(hp x).ne']
  · have hd : p.relativeDensity q x ≤ C := (div_le_iff₀ (hp x)).mpr (le_of_not_gt hx)
    simp only [hd, ite_true, mul_zero, hx, ite_false]

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedOutputL1
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedOutputSlice {I J : Type*} [Fintype J]
    (s : J ↪ I) (f : (I → ℝ) → ℝ) (x : UnselectedColumn s → ℝ) (y : J → ℝ) : ℝ :=
  f (selectedCoefficientEquiv s ℝ (x, y))

noncomputable def retainedSelectedOutputEquiv {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) :
    (W × (UnselectedColumn s → ℝ)) × (J → ℝ) ≃ᵐ W × (I → ℝ) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl W).prodCongr (selectedCoefficientMeasurableEquiv s))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

def productMinorEntryLog (q h : ℕ) (P : ℝ) : ℝ := P+h+(h : ℝ)*q
def productMinorPartialLog (q h : ℕ) (P : ℝ) : ℝ := P+2*h+(h : ℝ)*q
def productMinorInverseLog (j q h : ℕ) (P E : ℝ) : ℝ :=
  j+(j : ℝ)^2+(j-1 : ℕ)*productMinorEntryLog q h P+E
def productMinorDerivativeLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+j+productMinorPartialLog q h P
def productMinorDeterminantLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+(j : ℝ)^2+j+productMinorPartialLog q h P+j*(productMinorEntryLog q h P+1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanDerivativeBudget (h : D → ℕ) (C : D → ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1)

end Erdos3

end

section

namespace Erdos3

def cubeMinorConstantLog (j q h N d : ℕ) : ℝ :=
  (j : ℝ)*h*((q : ℝ)+1)^2+3*N+(d+1 : ℝ)+d*(8+(d+1 : ℝ))

def cubeMinorScaleLog (j N d : ℕ) (P : ℝ) : ℝ := (N : ℝ)*d+j*P

def cubeMinorThresholdLog (m j q h N d : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorScaleLog j N d P+2+(N*d : ℕ)*(cubeMinorConstantLog j q h N d+m+E+2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def canonicalBooleanMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorThresholdLog 1 (Fintype.card O) (Fintype.card α) h
    (cubeMinorVariableCount O α h) (cubeMinorDegree O h) P E

noncomputable def jointBooleanDerivativeLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] (h : D → ℕ) (P : ℝ) : ℝ :=
  Fintype.card D+∑ d, productMinorDerivativeLog (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) P

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanRegularization
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisOperatorMap :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →L[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ)) :=
  ({ toFun := sigmaAxisOperator
     map_add' := by
       intro A B
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.add_apply, add_apply]
     map_smul' := by
       intro t A
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.smul_apply, smul_apply, RingHom.id_apply] } :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →ₗ[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ))).mkContinuous 1 (fun A => by
        rw [one_mul]
        exact sigmaAxisOperator_norm_le A (norm_nonneg A) (norm_le_pi_norm A))

end Erdos3

end

section

namespace Erdos3

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

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

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

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

open MeasureTheory
open scoped NNReal

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

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineSelectedJetDensity {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (x : X → ℝ) : (I → ℝ) → ℝ :=
  normalizedJetDensity A F e input z rows
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) x

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

open MeasureTheory
open scoped BigOperators NNReal

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

open scoped NNReal BigOperators

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
open scoped NNReal BigOperators

noncomputable def affineSelectedJetProfile {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (c w : J ⊕ N → ℝ) : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ) → ℝ :=
  splitFreeProfile
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))

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

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteCenteredKernel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def joint (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * (q z.1).weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) ((q z.1).nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, total, mul_one]

theorem joint_mean (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.joint q).mean f = p.mean (fun x => (q x).mean (fun y => f (x,y))) := by
  simp only [mean, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def centeredKernelMatrix (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (x : X) (y : Y) : ℝ := (K x).weight y - ν.weight y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteWeightedScorePerturbation
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {J : Type*} [Fintype J] (p : FiniteProbabilityWeights J)

theorem norm_complexMean_weighted_sub_le (c f g : J → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε) :
    ‖p.complexMean (fun j => c j * f j) - p.complexMean (fun j => c j * g j)‖ ≤
      B * ε := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * ε) ?_).trans_eq
    (p.mean_const (B * ε))
  intro j _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hc j) (hfg j) (norm_nonneg _) hB

theorem norm_complexMean_weighted_lower_of_perturbation (c f g : J → ℂ) {B ε δ : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε)
    (hscore : δ ≤ ‖p.complexMean (fun j => c j * g j)‖) :
    δ - B * ε ≤ ‖p.complexMean (fun j => c j * f j)‖ := by
  have he := p.norm_complexMean_weighted_sub_le c f g hB hc hfg
  have ht := norm_le_norm_sub_add (p.complexMean (fun j => c j * g j))
    (p.complexMean (fun j => c j * f j))
  rw [norm_sub_rev] at ht
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

abbrev ProductCylinder {ι : Type*} (X : ι → Type*) := Σ S : Finset ι, ∀ i : S, X i.val

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

def ofAssignment (S : Finset ι) (x : ∀ i, X i) : ProductCylinder X :=
  ⟨S, fun i => x i.val⟩

def assignment (c : ProductCylinder X) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if hi : i ∈ c.1 then c.2 ⟨i, hi⟩ else base i

def Contains (c : ProductCylinder X) (x : ∀ i, X i) : Prop :=
  ∀ i : c.1, x i.val = c.2 i

theorem assignment_mem (c : ProductCylinder X) (base : ∀ i, X i) (i : ι) (hi : i ∈ c.1) :
    c.assignment base i = c.2 ⟨i, hi⟩ := by
  simp only [assignment, hi, dite_true]

theorem contains_iff (c : ProductCylinder X) (base x : ∀ i, X i) :
    c.Contains x ↔ ∀ i ∈ c.1, x i = c.assignment base i := by
  constructor
  · intro h i hi
    rw [c.assignment_mem base i hi]
    exact h ⟨i, hi⟩
  · intro h i
    rw [h i.val i.property, c.assignment_mem base i.val i.property]

variable [Fintype ι] [∀ i, Fintype (X i)]

noncomputable def bounded (b : ℕ) : Finset (ProductCylinder X) := by
  classical
  exact Finset.univ.filter (fun c => c.1.card ≤ b)

noncomputable def mass (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (c : ProductCylinder X) : ℝ :=
  productConditionalMean μ c.1 f (c.assignment base)

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionAverage (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean
    (fun y => f (productCoordinateMix T (productCoordinateMix A z y) x))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def score (K : ℝ) (c : ProductCylinder X) : ℝ := c.mass μ base f / K ^ c.1.card

def Maximizes (K : ℝ) (b : ℕ) (c : ProductCylinder X) : Prop :=
  c.1.card ≤ b ∧ ∀ d : ProductCylinder X, d.1.card ≤ b → score μ base f K d ≤ score μ base f K c

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductBoundedMarginals (f : (∀ i, X i) → ℝ) (K : ℝ) (r : ℕ) : Prop :=
  ∀ J : Finset I, J.card ≤ r → ∀ x : ∀ i, X i,
    (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      productConditionalMean μ J f x ≤ K ^ J.card

noncomputable def productNormalizedSection (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionAverage μ T A z f x

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def normalizedSection (c : ProductCylinder X) (x : ∀ i, X i) : ℝ :=
  (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f x

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductMarginalsClose (rho : (∀ i, X i) → ℝ) (eta : ℝ) (s : ℕ) : Prop :=
  ∀ B : Finset I, B.card ≤ s → ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
    |productConditionalMean μ B rho x - 1| ≤ eta

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyProjectionBudget
namespace OAI

section

namespace Erdos3

theorem frequency_projection_error_bound {p v M : ℝ} (hp : 0 ≤ p)
    (hM : M ≤ Real.exp v) :
    2 * Real.exp p * Real.exp (-(2 * p + 8)) + M * Real.exp (-(p + v + 8)) ≤
      Real.exp (-p) / 2 := by
  have parameterNonneg := hp
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h8
  have hfirst : 2 * Real.exp p * Real.exp (-(2 * p + 8)) =
      2 * Real.exp (-p) * Real.exp (-8) := by
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsecond : Real.exp v * Real.exp (-(p + v + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hbound := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg (-(p + v + 8)))
  rw [hsecond] at hbound
  rw [hfirst]
  have hsmall := mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  linarith [parameterNonneg, Real.exp_pos (-p)]

theorem frequency_code_count_bound {p v : ℝ} {D M : ℕ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p) (hM : (M : ℝ) ≤ Real.exp v) :
    ((M : ℝ) + 1) ^ D ≤ Real.exp (p * (v + 1)) := by
  have parameterNonneg := hp
  have hbase : (M : ℝ) + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hv (le_refl (0 : ℝ)) hM
      (by simp : (1 : ℝ) ≤ Real.exp 0)
  calc
    _ ≤ (Real.exp (v + 1)) ^ D := pow_le_pow_left₀ (by positivity) hbase D
    _ = Real.exp ((D : ℝ) * (v + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by linarith [parameterNonneg]))

theorem mass_div_frequency_count {mass p v R : ℝ} {D M : ℕ}
    (hmass : 0 ≤ mass) (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p)
    (hM : (M : ℝ) ≤ Real.exp v) (hR : p * (v + 1) ≤ R) :
    mass * Real.exp (-R) ≤ mass / ((M : ℝ) + 1) ^ D := by
  have hden := (frequency_code_count_bound hp hv hD hM).trans (Real.exp_le_exp.mpr hR)
  have hi : Real.exp (-R) ≤ 1 / ((M : ℝ) + 1) ^ D := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi hmass

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueSiteIndicator {m : ℕ} (r : ZMod m) (u : ℤ) : ℝ :=
  if (u : ZMod m) = r then 1 else 0

noncomputable def residueIntervalSiteWeight (B r H : ℝ) {m : ℕ}
    (a : ZMod m) (k : Fin (intervalSiteCount B r)) (u : ℤ) : ℝ :=
  residueSiteIndicator a u * intervalSiteWeight B r k ((u : ℝ) / H)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

theorem selectedColumn_card {I J : Type*} [Fintype I] [Fintype J] (s : I ↪ J) :
    Fintype.card I + Fintype.card (UnselectedColumn s) = Fintype.card J := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (selectedColumnEquiv s)

theorem scalarSpatialIndexAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialIndexAllowance I B ≤ Real.exp ((Fintype.card I + 1 : ℝ) * R) := by
  unfold scalarSpatialIndexAllowance
  calc
    _ ≤ (Real.exp R)^(Fintype.card I + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem scalarSpatialInverseAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialInverseAllowance I B ≤
      Real.exp ((Fintype.card I + 1 : ℝ) + (Fintype.card I + 1 : ℝ)^2 + R) := by
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hf : ((Fintype.card I + 1).factorial : ℝ) ≤ Real.exp ((Fintype.card I + 1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_le_exp_sq (Fintype.card I + 1)
  unfold scalarSpatialInverseAllowance
  calc
    _ ≤ Real.exp (Fintype.card I + 1 : ℝ) * Real.exp ((Fintype.card I + 1 : ℝ)^2) * Real.exp R := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def smoothSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) : ℝ :=
  (normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    (scalarSpatialIndexAllowance I M) (scalarSpatialInverseAllowance I M)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
      (Fintype.card (Unit ⊕ I)).factorial) * (L : ℝ)^Fintype.card (Unit ⊕ I)

noncomputable def smoothSpatialDisplacementCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) : ℝ :=
  scalarSpatialIndexAllowance I M *
    spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (scalarSpatialInverseAllowance I M) 1
      ((Fintype.card (UnselectedColumn s)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
    Fintype.card N

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialProfileLog (j d : ℕ) (p : ℝ) : ℝ :=
  (j+1)*p+(j : ℝ)^2+2*j+d+probabilityProfileLipschitz+1

theorem spatialProfileLog_nonneg (j d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ spatialProfileLog j d p := by unfold spatialProfileLog; positivity

theorem spatialProfileLog_bounds {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    let j := Fintype.card (Unit ⊕ I)
    let d := Fintype.card (UnselectedColumn s ⊕ N)
    let P := spatialProfileLog j d p
    scalarSpatialIndexAllowance I M ≤ Real.exp P ∧
    scalarSpatialInverseAllowance I M ≤ Real.exp P ∧
    (d : ℝ) ≤ Real.exp P ∧
    ((d+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
  dsimp only
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  have hj : (Fintype.card I+1 : ℝ) = j := by
    simp only [j, Fintype.card_sum, Fintype.card_unit, Nat.cast_add, Nat.cast_one]
    ring
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hκ : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  have hG := scalarSpatialIndexAllowance_le_exp I hM
  have hU := scalarSpatialInverseAllowance_le_exp I hM
  rw [hj] at hG hU
  have hn : (d+j : ℝ) ≤ Real.exp (d+j : ℝ) := by
    linarith [Real.add_one_le_exp (d+j : ℝ)]
  have hk : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  refine ⟨hG.trans (Real.exp_le_exp.mpr ?_), hU.trans (Real.exp_le_exp.mpr ?_), ?_, ?_⟩
  · change (j : ℝ)*p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · change (j : ℝ)+j^2+p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · calc
      (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith
  · calc
      (d+j : ℝ)*probabilityProfileLipschitz ≤
          Real.exp (d+j : ℝ)*Real.exp probabilityProfileLipschitz :=
        mul_le_mul hn hk hκ (Real.exp_pos _).le
      _ = Real.exp ((d+j : ℝ)+probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith

noncomputable def spatialDiscretizationLog (j d : ℕ) (p l : ℝ) : ℝ :=
  let P := spatialProfileLog j d p
  2*(j : ℝ)^2+(2*j+4)*P+(j+2*d)*(P+4)+4+j*l

noncomputable def spatialDisplacementLog (j d e n : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ)^2+(j+3)*spatialProfileLog j d p+2*e+n

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_pos (p : FiniteProbabilityWeights Ω) : ∃ x, 0 < p.weight x := by
  by_contra h
  push Not at h
  have hs : (∑ x, p.weight x) ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
  rw [p.total] at hs
  norm_num at hs

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem complexMean_div (p : FiniteProbabilityWeights X) (f : X → ℂ) (z : ℂ) :
    p.complexMean (fun x => f x / z) = p.complexMean f / z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

theorem exists_positive_weight_ge_mean (p : FiniteProbabilityWeights X) (f : X → ℝ) :
    ∃ x, 0 < p.weight x ∧ p.mean f ≤ f x := by
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    obtain ⟨x, hx⟩ := p.exists_weight_pos
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image f hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  calc
    p.mean f ≤ p.mean (fun _ => f x) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left
          (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = f x := p.mean_const _

theorem exists_positive_weight_ge_complexMean_re (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ (p.complexMean f).re ≤ (f x).re := by
  rw [p.complexMean_re]
  exact p.exists_positive_weight_ge_mean _

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

theorem intervalSiteCount_bound {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) :
    (intervalSiteCount B r : ℝ) ≤ 2 * B / r + 3 := by
  have h := (Nat.ceil_lt_add_one (show 0 ≤ 2 * B / r by positivity)).le
  simp only [intervalSiteCount, boxCoverMeshCount, NNReal.coe_one, mul_one, Nat.cast_add, Nat.cast_one]
  linarith

theorem intervalSiteCount_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (intervalSiteCount B r : ℝ) ≤ Real.exp (2 * P + 4) := by
  have he : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 2 * B / r ≤ 2 * Real.exp (2 * P) := by
    calc
      _ = 2 * B * (1 / r) := by ring
      _ ≤ 2 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc
    _ ≤ 2 * B / r + 3 := intervalSiteCount_bound hB0 hr
    _ ≤ 5 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 4 * Real.exp (2 * P) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem intervalSiteLipschitz_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (2 * (intervalSiteCount B r : ℝ) + 1) / r ≤ Real.exp (3 * P + 6) := by
  have hn := intervalSiteCount_le_exp hB0 hr hP hB hri
  have he : 1 ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by positivity)
  have hnum : 2 * (intervalSiteCount B r : ℝ) + 1 ≤ 3 * Real.exp (2 * P + 4) := by linarith
  calc
    _ = (2 * (intervalSiteCount B r : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp (2 * P + 4)) * Real.exp P := by gcongr
    _ = 3 * Real.exp (3 * P + 4) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (3 * P + 4) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem siteCoefficientAllowance_le_exp (n : ℕ) {m M G C P : ℝ}
    (hm0 : 0 ≤ m) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hC0 : 0 ≤ C)
    (hm : m ≤ Real.exp P) (hM : M ≤ Real.exp (2 * P + 4))
    (hG : G ≤ Real.exp P) (hC : C ≤ Real.exp P) :
    m^n * M^n * (G * C) ≤ Real.exp ((3 * P + 4) * n + 2 * P) := by
  calc
    _ ≤ (Real.exp P)^n * (Real.exp (2 * P + 4))^n * (Real.exp P * Real.exp P) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

theorem vectorSiteAllowance_le_exp (d : ℕ) {A P : ℝ} (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) :
    A^d ≤ Real.exp (d * P) := by
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP d

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityRetained
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

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberLaw_weight_eq_mass (p : FiniteProbabilityWeights X) (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.mass (Finset.univ.filter (fun x => F x = r)) := by
  simpa only [fiberLaw_weight, fiberMean, Finset.mem_filter, Finset.mem_univ, true_and]
    using p.mean_indicator (Finset.univ.filter (fun x => F x = r))

end Erdos3.FiniteProbabilityWeights

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

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedSplitUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedSplitMeasurableEquiv {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    ((UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) ≃ᵐ (J ⊕ N → ℝ) :=
  (splitFreeCoordinates I (UnselectedColumn s) N).trans
    (((selectedCoefficientMeasurableEquiv s).prodCongr (MeasurableEquiv.refl (N → ℝ))).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineJetUnitMap {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (c w : J ⊕ N → ℝ) (x : X → ℝ) (r : J ⊕ N → ℝ) : I → ℝ :=
  A (fun i => c (.inl (s i))+w (.inl (s i))*r (.inl (s i))) +
    F (fun j => c (.inl j.val)+w (.inl j.val)*r (.inl j.val)) +
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x
        (fun n => c (.inr n)+w (.inr n)*r (.inr n))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def jointUnitCoefficientSource {Q : Type*} [Fintype Q]
    (J N : Q → Type*) [∀ q, Fintype (J q)] [∀ q, Fintype (N q)] :
    Measure (∀ q, J q ⊕ N q → ℝ) := Measure.pi (fun q => unitCoefficientSource (J q ⊕ N q))

instance jointUnitCoefficientSource_probability {Q : Type*} [Fintype Q]
    (J N : Q → Type*) [∀ q, Fintype (J q)] [∀ q, Fintype (N q)] :
    IsProbabilityMeasure (jointUnitCoefficientSource J N) := by
  unfold jointUnitCoefficientSource
  infer_instance

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def anisotropicSpatialScale (I : Type*) (A R : ℝ) : Unit ⊕ I → ℝ :=
  Sum.elim (fun _ => A) (fun _ => R)

theorem anisotropicSpatialScale_pos (I : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ i, 0 < anisotropicSpatialScale I A R i := by
  rintro (i | i)
  · exact hA
  · exact hR

noncomputable def anisotropicSpatialOutputLaw {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (C : Matrix (Unit ⊕ I) N ℤ)
    (A R : ℝ) (Q : N → ℝ) (hA : 0 < A) (hR : 0 < R) (hQ : ∀ j, 0 < Q j) :
    PMF ((Unit ⊕ I) → ℤ) :=
  smoothMatrixImagePMF (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j)

noncomputable def anisotropicSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (A R L : ℝ) (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  normalizedFiberDensity (selectedSpatialPivot root D s) hp (selectedSpatialFreeColumns root D s)
    (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L) (fun _ => R)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialDensityCap {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial *
    (physicalSpatialInverseBound I κ) ^ Fintype.card (Unit ⊕ I) * 2 ^ Fintype.card (UnselectedColumn s)

noncomputable def anisotropicSpatialDensityLip {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  anisotropicSpatialDensityCap s κ *
    ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz) *
      physicalSpatialInverseBound I κ

theorem anisotropicSpatialDensityCap_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityCap s κ := by
  unfold anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

theorem anisotropicSpatialDensityLip_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityLip s κ := by
  unfold anisotropicSpatialDensityLip anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

def anisotropicSpatialCapLog {A : Type*} [Semiring A] (P : A) : A :=
  P ^ 3 + 3 * P ^ 2 + 2 * P

theorem anisotropicSpatialCapLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anisotropicSpatialCapLog P := by
  unfold anisotropicSpatialCapLog
  positivity

theorem anisotropicSpatialDensityCap_exp_bound {α G : Type*} [Fintype α] [Fintype G]
    (selection : α ↪ G) {M : ℕ} {P : ℝ} (hP : 0 ≤ P) (hM : 0 < M)
    (hMP : (M : ℝ) ≤ Real.exp P)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P) :
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp (anisotropicSpatialCapLog P) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj2 : (j : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hα 2
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hU : physicalSpatialInverseBound α (1 / (M : ℝ)) ≤ Real.exp (P ^ 2 + 2 * P) :=
    (physicalSpatialInverseBound_le_exp α hκ (by simpa only [one_div, inv_inv] using hMP)).trans
      (Real.exp_le_exp.mpr (by change (j : ℝ) ^ 2 + j + P ≤ _; linarith))
  have hU0 : 0 ≤ physicalSpatialInverseBound α (1 / (M : ℝ)) := by
    unfold physicalSpatialInverseBound
    positivity
  have hpower := pow_le_exp_mul_of_le_exp hU0 hU (by positivity) j hα
  have hfact := (factorial_le_exp_sq j).trans (Real.exp_le_exp.mpr hj2)
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ P := by
    have hc := selectedColumn_card selection
    exact (Nat.cast_le.mpr (by omega)).trans hG
  have htwo : (2 : ℝ) ^ Fintype.card (UnselectedColumn selection) ≤ Real.exp (2 * P) := by
    simpa only [mul_comm P 2] using pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by norm_num : (0 : ℝ) ≤ 2) _ hfree
  unfold anisotropicSpatialDensityCap
  calc
    _ ≤ Real.exp (P ^ 2) * Real.exp (P * (P ^ 2 + 2 * P)) * Real.exp (2 * P) := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold anisotropicSpatialCapLog
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

noncomputable def anisotropicSpatialDetAllowance (I : Type*) [Fintype I] (C : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial * C ^ Fintype.card (Unit ⊕ I)

noncomputable def anisotropicSpatialMeshThreshold {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (C : ℝ) : ℝ :=
  2 * (1 + 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz)) *
      anisotropicSpatialDetAllowance I C

noncomputable def anisotropicSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) (κ C ρ ξ : ℝ) : ℝ :=
  normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    ((B : ℝ) ^ (Fintype.card I + 1)) (physicalSpatialInverseBound I κ)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
      anisotropicSpatialDetAllowance I C / ρ +
  (B : ℝ) ^ (Fintype.card I + 1) *
    (spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (physicalSpatialInverseBound I κ) 1
      ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
        (Fintype.card N * ξ))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

def physicalSpatialSplitEquiv (G N : Type*) : ((Unit ⊕ G) ⊕ N) ≃ Option (G ⊕ N) :=
  (Equiv.sumAssoc Unit G N).trans (physicalCubeOptionEquiv (G ⊕ N))

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α]

variable [DecidableEq α] [DecidableEq G]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coordinateRescaledDensity {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ := f (fun i => a i * x i)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {I : Type*} [Fintype I]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def canonicalSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  anisotropicSpatialKernelDensity s root D hp (1 + W) 1 L (by linarith) zero_lt_one hL

noncomputable def canonicalSpatialSiteDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  coordinateRescaledDensity (fun i => (1 + W) / physicalSpatialOutputScale I (1 + W) 1 L i)
    (canonicalSpatialKernelDensity s root D hp W L hW hL)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnisotropicTupleErrorChoice
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem physicalSpatialInverseBound_eq_scalar (I : Type*) [Fintype I] (M : ℕ) :
    physicalSpatialInverseBound I (1 / (M : ℝ)) = scalarSpatialInverseAllowance I M := by
  simp [physicalSpatialInverseBound, scalarSpatialInverseAllowance, div_eq_mul_inv,
    Fintype.card_sum, Nat.add_comm]

noncomputable def anisotropicSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) (C : ℝ) : ℝ :=
  smoothSpatialDiscretizationCost N s M 1 * C ^ Fintype.card (Unit ⊕ I)

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

def coefficientErrorVolumeLog {A : Type*} [Semiring A] (P : A) : A := P ^ 2 * (P + 61)

def coefficientErrorSpatialLog {A : Type*} [Semiring A] (P : A) : A :=
  P * (P ^ 3 + anisotropicSpatialCapLog P) + coefficientErrorVolumeLog P

theorem coefficientErrorSpatialLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coefficientErrorSpatialLog P := by
  have h := anisotropicSpatialCapLog_nonneg hP
  unfold coefficientErrorSpatialLog coefficientErrorVolumeLog
  positivity

theorem coefficientErrorPeriod_exp_sq {m M period : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ P) (hM : (M : ℝ) ≤ Real.exp P)
    (hperiod : period ≤ M ^ (m + 1)) : (period : ℝ) ≤ Real.exp (P ^ 2) := by
  have hcast : (period : ℝ) ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
  exact hcast.trans (by
    simpa only [pow_two] using pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hM hP (m + 1) hm)

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AnisotropicTupleChoiceBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicTupleEarlyBudget {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) (p E : ℝ) : ℝ :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
      (Fintype.card (UnselectedColumn s)) (Fintype.card N) p + E

theorem anisotropicTupleEarlyBudget_bounds {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := anisotropicTupleEarlyBudget N s p E
    0 ≤ Q ∧ p ≤ Q ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ Q ∧
      coefficientErrorVolumeLog p + 4 ≤ Q ∧
      spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
        (Fintype.card (UnselectedColumn s)) (Fintype.card N) p ≤ Q ∧ E ≤ Q := by
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hdis : 0 ≤ spatialDisplacementLog (Fintype.card (Unit ⊕ I))
      (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
      (Fintype.card N) p := by
    unfold spatialDisplacementLog spatialProfileLog
    positivity
  dsimp only [anisotropicTupleEarlyBudget]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientFrontBudget
namespace OAI

section

namespace Erdos3

noncomputable def coefficientFrontLog (i j : ℕ) (b t e : ℝ) : ℝ :=
  coefficientLogAllowance i j (affineCoefficientCommonBudget j j b t) + e + 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem partitionedIdealRadius_add_one_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    partitionedIdealRadius α degree + 1 ≤
      Real.exp (((degree : ℝ) + 1) * (Fintype.card α : ℝ) + 2) := by
  let n : ℝ := Fintype.card α
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ Fintype.card α ≤ Real.exp n := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one, n]
  have hbase : n + 1 ≤ Real.exp n := Real.add_one_le_exp n
  have hmain : (2 : ℝ) ^ Fintype.card α * (n + 1) ^ degree ≤
      Real.exp (((degree : ℝ) + 1) * n) := by
    calc
      _ ≤ Real.exp n * (Real.exp n) ^ degree := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (((degree : ℝ) + 1) * n) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (((degree : ℝ) + 1) * n) := by
      unfold partitionedIdealRadius
      change 1 / 4 + 2 ^ Fintype.card α * (n + 1) ^ degree + 1 ≤ _
      linarith
    _ ≤ Real.exp 2 * Real.exp (((degree : ℝ) + 1) * n) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IdealSiteBoxRadius
namespace OAI

section

namespace Erdos3

noncomputable def idealSiteBoxRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (partitionedIdealRadius α degree + 1)

theorem idealSiteBoxRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteBoxRadius α degree := by
  have h := partitionedIdealRadius_nonneg α degree
  unfold idealSiteBoxRadius
  positivity

theorem idealSiteBoxRadius_buffer_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    2 * idealSiteBoxRadius α degree ≤
      Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteBoxRadius
  calc
    _ ≤ Real.exp 1 * (Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 1) * Fintype.card α + 2)) := by
      have hr0 : 0 ≤ partitionedIdealRadius α degree + 1 := by
        have h := partitionedIdealRadius_nonneg α degree
        linarith
      exact mul_le_mul htwo
        (mul_le_mul hp (partitionedIdealRadius_add_one_le_exp α degree) hr0 (Real.exp_pos _).le)
        (mul_nonneg (by positivity) hr0) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IdealSiteEnvelopeBudget
namespace OAI

section

namespace Erdos3

noncomputable def idealSiteEnvelopeRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (2 * idealSiteBoxRadius α degree)

theorem idealSiteEnvelopeRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteEnvelopeRadius α degree := by
  have h := idealSiteBoxRadius_pos α degree
  unfold idealSiteEnvelopeRadius
  positivity

theorem idealSiteEnvelopeRadius_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    idealSiteEnvelopeRadius α degree ≤
      Real.exp (((degree : ℝ) + 3) * Fintype.card α + 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp (Fintype.card α : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  unfold idealSiteEnvelopeRadius
  calc
    _ ≤ Real.exp (Fintype.card α : ℝ) *
        Real.exp (((degree : ℝ) + 2) * Fintype.card α + 3) :=
      mul_le_mul hp (idealSiteBoxRadius_buffer_le_exp α degree)
        (mul_nonneg (by norm_num) (idealSiteBoxRadius_pos α degree).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

def positiveModerateSpectrumExponent (n j : ℕ) : ℕ :=
  4 * positiveModerateCoverExponent n j * j

noncomputable def positiveModerateSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * positiveModerateCoverConstant n j U V ^ 4) ^ j

def positiveModerateSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (positiveModerateSpectrumExponent n j) (positiveModerateLengthExponent n * t) + 1

noncomputable def positiveModerateSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (positiveModerateLengthConstant n U) L (positiveModerateLengthExponent n)
    (polynomialGridCover J M (positiveModerateCoverConstant n (Fintype.card J) U V)
      (positiveModerateCoverExponent n (Fintype.card J))) ζ

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

noncomputable def positiveModerateAccuracyScale (n j t : ℕ) (U V W : ℝ) : ℝ :=
  1 + (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
    W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t)

noncomputable def positiveModerateRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  ε / positiveModerateAccuracyScale n j t U V W

noncomputable def positiveModerateSpectrumCardBudget (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  positiveModerateSpectrumConstant n j U V /
      positiveModerateRetainedBias n j t U V W ε ^ positiveModerateSpectrumExponent n j +
    W * positiveModerateLengthConstant n U ^ t /
      positiveModerateRetainedBias n j t U V W ε ^ (positiveModerateLengthExponent n * t)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

noncomputable def positiveRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈positiveModerateCoverConstant n d U V / ζ ^ positiveModerateCoverExponent n d⌉₊ : ℝ)

noncomputable def positiveRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((positiveRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_fiber_set (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      piRestrictionSet (fun j => Finset.univ.filter (fun x => F j x = r j)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_piRestrictionSet, funext_iff]

theorem pi_fiber_mass (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      ∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r j)) := by
  rw [pi_fiber_set, piRestriction_mass]

variable [∀ j, Fintype (R j)]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtPatch (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    PolynomialPatch J s 1 :=
  w.patch s hs (crtRepresentativePolynomial N hN) (crtRepresentativePolynomial_degree N hN)

omit [NeZero (∏ j, N j)] in
@[simp] theorem crtPatch_lip (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) :
    (w.crtPatch N hN s hs).kernel.lip = w.lip := rfl

end Erdos3.RepresentativeWindow

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EuclideanDerivativeDensityCovolume
namespace OAI

section

namespace Erdos3

open Module

theorem euclideanDerivative_covolume_density_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T (fun i => (hT i).ne') scale hscale Y A l hl
    let d := finrank ℝ (shortVectorSpan Λ ρ)
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((d : ℝ) + 2) * ρ) ^ d / (δ * ∏ i, T i) := by
  obtain ⟨P, hcard, hP⟩ := exists_bounded_derivativeGridPoint_family T
    (fun i => (hT i).ne') scale Y (LinearMap.toMatrix' A.toLinearMap) l H 0 R
    (fun h hh => ⟨r h, hr h hh, by simpa only [sub_zero] using hnorm h hh⟩)
  apply euclideanDerivativeLattice_covolume_le T (fun i => (hT i).ne') scale hscale
    Y A l hl R (δ * ∏ i, T i) hR (mul_pos hδ (Finset.prod_pos (fun i _ => hT i))) P hP
  simpa only [hcard] using hdense

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartiallyBoundedNormalization
namespace OAI

section

namespace Erdos3

theorem exists_partially_bounded_grid_normalization {ι κ : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (e : κ → ι) (p : Fin k → κ)
    (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → κ, |(B.submatrix (e ∘ q) id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹ ∧
        Q.submatrix (e ∘ p) id = 1 ∧
        (∀ i j, RationalHeightLE (Q (e i) j) (Nat.ceil (C * (l : ℝ) ^ k))) := by
  obtain ⟨D, hD, hDle, Q, hQgrid, hQ, hQid⟩ :=
    exists_grid_row_normalization B l hl hgrid (e ∘ p) hp C (hminor p)
  let H := B.submatrix e id
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (e i), ?_⟩
    funext i
    exact congrFun hz (e i)
  obtain ⟨QH, hQH, hheight, _⟩ :=
    exists_bounded_rational_row_normalization H l hl hHgrid p hp C hminor
  have heq : Q.submatrix e id = QH := by
    ext i j
    apply Rat.cast_injective (α := ℝ)
    change (Q (e i) j : ℝ) = (QH i j : ℝ)
    calc
      _ = (B * (B.submatrix (e ∘ p) id)⁻¹) (e i) j :=
        congrArg (fun M : Matrix ι (Fin k) ℝ => M (e i) j) hQ
      _ = (H * (H.submatrix p id)⁻¹) i j := rfl
      _ = _ := (congrArg (fun M : Matrix κ (Fin k) ℝ => M i j) hQH).symm
  refine ⟨D, hD, hDle, Q, hQgrid, hQ, hQid, ?_⟩
  intro i j
  have h := congrArg (fun M : Matrix κ (Fin k) ℚ => M i j) heq
  change Q (e i) j = QH i j at h
  rw [h]
  exact hheight i j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastGoodPathMeanNorm
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem forecastBoundedSignalTransfer
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample)
    (target signal : Sample → ℂ) (coefficient : Term → ℂ)
    (atom : Term → Sample → ℂ) {M ε δ B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ δ)
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (hatom : ∀ t, ‖μ.complexMean (fun x => signal x * atom t x)‖ ≤ ε) :
    ‖μ.complexMean (fun x => signal x * target x)‖ ≤ M * ε + B * δ := by
  let model := fun x => ∑ t, coefficient t * atom t x
  have hmodel : μ.complexMean (fun x => signal x * model x) =
      ∑ t, coefficient t * μ.complexMean (fun x => signal x * atom t x) := by
    unfold FiniteProbabilityWeights.complexMean
    simp only [model, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmodelBound : ‖μ.complexMean (fun x => signal x * model x)‖ ≤ M * ε := by
    rw [hmodel]
    calc
      _ ≤ ∑ t, ‖coefficient t * μ.complexMean (fun x => signal x * atom t x)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ t, ‖coefficient t‖ * ε := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hatom t) (norm_nonneg _)
      _ = (∑ t, ‖coefficient t‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ M * ε := mul_le_mul_of_nonneg_right hmass hε
  have herror : ‖μ.complexMean (fun x => signal x * target x) -
      μ.complexMean (fun x => signal x * model x)‖ ≤ B * δ := by
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => B * δ) ?_).trans_eq (μ.mean_const (B * δ))
    intro x _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hsignal x) (happrox x) (norm_nonneg _) hB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (μ.complexMean (fun x => signal x * target x))
    (μ.complexMean (fun x => signal x * model x)) 0
  simp only [sub_zero] at htriangle
  exact (htriangle.trans (add_le_add herror hmodelBound)).trans_eq (add_comm (B * δ) (M * ε))

theorem exists_forecast_detecting_atom
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample) (target signal : Sample → ℂ)
    (coefficient : Term → ℂ) (atom : Term → Sample → ℂ)
    {a B M : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ a / (2 * (B + 1)))
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hlarge : a ≤ ‖μ.complexMean (fun x => signal x * target x)‖) :
    ∃ t, a / (4 * (M + 1)) ≤ ‖μ.complexMean (fun x => signal x * atom t x)‖ := by
  by_contra! hn
  have hu := forecastBoundedSignalTransfer μ target signal coefficient atom
    (show 0 ≤ a / (4 * (M + 1)) by positivity) hB happrox hmass hsignal
    (fun t => (hn t).le)
  have hm : M * (a / (4 * (M + 1))) ≤ a / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    nlinarith
  have hb : B * (a / (2 * (B + 1))) ≤ a / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * (B + 1))]
    nlinarith
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

universe uTerm

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

noncomputable def allocatedTupleSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    (Czero rho xi W delta mesh : ℝ) : ℝ :=
  let gamma := (period : ℝ) ^ Fintype.card (Unit ⊕ I)
  let K := anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * (1 + W)
  let Eone := anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho xi + gamma * K * delta
  (n : ℝ) * (Eone + 4 * gamma * K * mesh) *
    (1 + gamma * anisotropicSpatialDensityCap selection (1 / (M : ℝ)) + Eone) ^ n

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset (Fin dim))

variable (X : Type*) [Fintype X]

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (d : ℕ) [NeZero d]
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset (Fin dim))

variable (X : Type*) [Fintype X]

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (d : ℕ) [NeZero d]
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (L₀ : ℕ)
variable {dim : ℕ}
variable (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (c : ∀ j, U j)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreimanInverseLift
namespace OAI

section

open scoped BigOperators Pointwise

namespace Erdos3.FreimanModel

def badMultipliers (q M : ℕ) [NeZero q] (x : ℤ) : Finset (ZMod q) :=
  Finset.univ.filter fun lam => M ∣ (lam * (x : ZMod q)).val

@[simp] lemma mem_badMultipliers {q M : ℕ} [NeZero q] {x : ℤ} {lam : ZMod q} :
    lam ∈ badMultipliers q M x ↔ M ∣ (lam * (x : ZMod q)).val := by
  simp [badMultipliers]

lemma card_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (_hM : 0 < M) {x : ℤ} (hx : (x : ZMod q) ≠ 0) :
    (badMultipliers q M x).card ≤ q / M + 1 := by
  let f : ZMod q → ℕ := fun lam => (lam * (x : ZMod q)).val / M
  rw [← Finset.card_range (q / M + 1)]
  apply Finset.card_le_card_of_injOn f
      (s := badMultipliers q M x) (t := Finset.range (q / M + 1))
  · intro lam hlam
    dsimp only [f]
    have hval := (lam * (x : ZMod q)).val_lt
    have hdiv : (lam * (x : ZMod q)).val / M ≤ q / M :=
      Nat.div_le_div_right hval.le
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hdiv
  · intro lam hlam mu hmu heq
    have hlamDiv : M ∣ (lam * (x : ZMod q)).val :=
      mem_badMultipliers.mp hlam
    have hmuDiv : M ∣ (mu * (x : ZMod q)).val :=
      mem_badMultipliers.mp hmu
    dsimp only [f] at heq
    have hval : (lam * (x : ZMod q)).val = (mu * (x : ZMod q)).val := by
      calc
        (lam * (x : ZMod q)).val =
            M * ((lam * (x : ZMod q)).val / M) :=
              (Nat.mul_div_cancel' hlamDiv).symm
        _ = M * ((mu * (x : ZMod q)).val / M) := by rw [heq]
        _ = (mu * (x : ZMod q)).val := Nat.mul_div_cancel' hmuDiv
    have hprod : lam * (x : ZMod q) = mu * (x : ZMod q) := by
      rw [← ZMod.natCast_zmod_val (lam * (x : ZMod q)),
        ← ZMod.natCast_zmod_val (mu * (x : ZMod q)), hval]
    exact mul_right_cancel₀ hx hprod

lemma intCast_zmod_ne_zero_of_natAbs_lt {q : ℕ} [NeZero q]
    {x : ℤ} (hx0 : x ≠ 0) (hxq : x.natAbs < q) :
    (x : ZMod q) ≠ 0 := by
  intro hx
  have hdiv : (q : ℤ) ∣ x :=
    (CharP.intCast_eq_zero_iff (ZMod q) q x).mp hx
  have hqle : q ≤ x.natAbs := by
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hdiv hx0
  omega

lemma card_biUnion_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (hM : 0 < M) {D : Finset ℤ}
    (hx : ∀ x ∈ D, (x : ZMod q) ≠ 0) :
    (D.biUnion (badMultipliers q M)).card ≤ D.card * (q / M + 1) := by
  calc
    (D.biUnion (badMultipliers q M)).card ≤
        ∑ x ∈ D, (badMultipliers q M x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ D, (q / M + 1) := by
      gcongr with x hxD
      exact card_badMultipliers_le hM (hx x hxD)
    _ = D.card * (q / M + 1) := by simp

lemma multiplier_union_card_lt {N q : ℕ} (hN : 0 < N)
    (hq : 4 * N < q) :
    N * (q / (2 * N) + 1) < q := by
  have hden : 0 < 2 * N := by omega
  have hdiv := Nat.mul_div_le q (2 * N)
  have hmul : 2 * (N * (q / (2 * N))) ≤ q := by
    calc
      2 * (N * (q / (2 * N))) = (2 * N) * (q / (2 * N)) := by ring
      _ ≤ q := hdiv
  nlinarith

theorem exists_good_multiplier {D : Finset ℤ} {N q : ℕ}
    [NeZero q] [Fact q.Prime] (hN : 0 < N) (hcard : D.card ≤ N)
    (habs : ∀ x ∈ D, x.natAbs < q) (hq : 4 * N < q) :
    ∃ lam : ZMod q, lam ≠ 0 ∧
      ∀ x ∈ D, x ≠ 0 → ¬ (2 * N ∣ (lam * (x : ZMod q)).val) := by
  classical
  let D₀ := D.erase 0
  by_cases hD₀ : D₀.Nonempty
  · let U : Finset (ZMod q) := D₀.biUnion (badMultipliers q (2 * N))
    have hxcast : ∀ x ∈ D₀, (x : ZMod q) ≠ 0 := by
      intro x hxD
      have hxD' := Finset.mem_erase.mp hxD
      exact intCast_zmod_ne_zero_of_natAbs_lt hxD'.1 (habs x hxD'.2)
    have hUcard : U.card < q := by
      calc
        U.card ≤ D₀.card * (q / (2 * N) + 1) :=
          card_biUnion_badMultipliers_le (by omega) hxcast
        _ ≤ N * (q / (2 * N) + 1) := by
          gcongr
          exact Finset.card_erase_le.trans hcard
        _ < q := multiplier_union_card_lt hN hq
    have hUne : U ≠ Finset.univ := by
      intro hEq
      have : U.card = q := by simp [hEq]
      omega
    have hex : ∃ lam : ZMod q, lam ∉ U := by
      by_contra h
      push Not at h
      apply hUne
      ext lam
      simp [h lam]
    obtain ⟨lam, hlamU⟩ := hex
    refine ⟨lam, ?_, ?_⟩
    · intro hlam0
      have hxU : (0 : ZMod q) ∈ U := by
        obtain ⟨x, hxD₀⟩ := hD₀
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hxD₀, ?_⟩
        simp
      exact hlamU (by simpa [hlam0] using hxU)
    · intro x hxD hx0 hbad
      apply hlamU
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩,
        mem_badMultipliers.mpr hbad⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hxD hx0
    exfalso
    apply hD₀
    exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩⟩

lemma multiset_sum_mem_nsmul (A : Finset ℤ) {T : Multiset ℤ}
    (hT : ∀ x ∈ T, x ∈ A) : T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

def ruzsaRepresentative (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  (lam * (a : ZMod q)).val

def ruzsaColor (q s : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  ruzsaRepresentative q lam a / (q / (2 * s) + 1)

def ruzsaModelMap (q M : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ZMod M :=
  ruzsaRepresentative q lam a

lemma ruzsaRepresentative_lt (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    ruzsaRepresentative q lam a < q := by
  exact (lam * (a : ZMod q)).val_lt

lemma ruzsaRepresentative_cast (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    (ruzsaRepresentative q lam a : ZMod q) = lam * (a : ZMod q) := by
  exact ZMod.natCast_zmod_val _

lemma ruzsaColor_lt {q s : ℕ} [NeZero q] (lam : ZMod q)
    (hs : 0 < s) (_hq : 2 * s < q) (a : ℤ) :
    ruzsaColor q s lam a < 2 * s := by
  let L := q / (2 * s) + 1
  have hden : 0 < 2 * s := by omega
  have hqL : q < (2 * s) * L := by
    simp only [L]
    exact Nat.lt_mul_div_succ q hden
  have hrep : ruzsaRepresentative q lam a < q := ruzsaRepresentative_lt q lam a
  dsimp [ruzsaColor]
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
  simpa only [L] using hrep.trans hqL

lemma ruzsaRepresentative_bounds_of_color_eq {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {a : ℤ} (hcolor : ruzsaColor q s lam a = c) :
    c * (q / (2 * s) + 1) ≤ ruzsaRepresentative q lam a ∧
      ruzsaRepresentative q lam a < (c + 1) * (q / (2 * s) + 1) := by
  have hL : 0 < q / (2 * s) + 1 := Nat.succ_pos _
  have hdiv : ruzsaRepresentative q lam a / (q / (2 * s) + 1) = c := by
    simpa [ruzsaColor] using hcolor
  constructor
  · rw [← hdiv]
    simpa [mul_comm] using Nat.div_mul_le_self
      (ruzsaRepresentative q lam a) (q / (2 * s) + 1)
  · rw [← hdiv]
    simpa [mul_comm] using Nat.lt_mul_div_succ (ruzsaRepresentative q lam a) hL

def ruzsaRepresentativeSum (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) : ℕ :=
  (T.map (ruzsaRepresentative q lam)).sum

lemma ruzsaRepresentativeSum_bounds {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T : Multiset ℤ} (hcard : T.card = s) (hs : 0 < s)
    (hcolor : ∀ x ∈ T, ruzsaColor q s lam x = c) :
    s * (c * (q / (2 * s) + 1)) ≤ ruzsaRepresentativeSum q lam T ∧
      ruzsaRepresentativeSum q lam T < s * ((c + 1) * (q / (2 * s) + 1)) := by
  let L := q / (2 * s) + 1
  have hlo : T.card • (c * L) ≤ ruzsaRepresentativeSum q lam T := by
    have hlo' := Multiset.card_nsmul_le_sum
      (s := T.map (ruzsaRepresentative q lam)) (a := c * L) (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨x, hxT, rfl⟩ := hy
        simpa only [L] using
          (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).1)
    simpa only [ruzsaRepresentativeSum, Multiset.card_map] using hlo'
  have hTne : T ≠ 0 := by
    intro hT
    simp [hT] at hcard
    omega
  have hhi : ruzsaRepresentativeSum q lam T < T.card • ((c + 1) * L) := by
    have hhi' := Multiset.sum_lt_sum_of_nonempty hTne fun x hxT =>
      (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).2
    simpa only [ruzsaRepresentativeSum, Multiset.map_const',
      Multiset.sum_replicate, L] using hhi'
  simpa only [hcard, L, Nat.nsmul_eq_mul] using And.intro hlo hhi

lemma ruzsaRepresentativeSum_sub_abs_lt {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T U : Multiset ℤ}
    (hTcard : T.card = s) (hUcard : U.card = s) (hs : 0 < s)
    (hTcolor : ∀ x ∈ T, ruzsaColor q s lam x = c)
    (hUcolor : ∀ x ∈ U, ruzsaColor q s lam x = c) :
    (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U <
        s * (q / (2 * s) + 1) ∧
      -((s * (q / (2 * s) + 1) : ℕ) : ℤ) <
        (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U := by
  obtain ⟨hTlo, hThi⟩ :=
    ruzsaRepresentativeSum_bounds lam hTcard hs hTcolor
  obtain ⟨hUlo, hUhi⟩ :=
    ruzsaRepresentativeSum_bounds lam hUcard hs hUcolor
  have hTU : ruzsaRepresentativeSum q lam T <
      ruzsaRepresentativeSum q lam U + s * (q / (2 * s) + 1) := by
    nlinarith
  have hUT : ruzsaRepresentativeSum q lam U <
      ruzsaRepresentativeSum q lam T + s * (q / (2 * s) + 1) := by
    nlinarith
  have hTU' : (ruzsaRepresentativeSum q lam T : ℤ) <
      (ruzsaRepresentativeSum q lam U : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hTU
  have hUT' : (ruzsaRepresentativeSum q lam U : ℤ) <
      (ruzsaRepresentativeSum q lam T : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hUT
  constructor <;> omega

lemma ruzsaRepresentativeSum_cast (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) :
    (ruzsaRepresentativeSum q lam T : ZMod q) = lam * (T.sum : ZMod q) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      rw [show ruzsaRepresentativeSum q lam (a ::ₘ T) =
        ruzsaRepresentative q lam a + ruzsaRepresentativeSum q lam T by
          simp [ruzsaRepresentativeSum]]
      rw [Nat.cast_add, ruzsaRepresentative_cast, ih, Multiset.sum_cons,
        Int.cast_add]
      ring

lemma ruzsaModelMap_sum (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
      (ruzsaRepresentativeSum q lam T : ZMod M) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      simp only [ruzsaModelMap, ruzsaRepresentativeSum, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add, ih]

lemma ruzsaBlockWidth_lt {q s : ℕ} (_hs : 0 < s) (hq : 2 * s < q) :
    s * (q / (2 * s) + 1) < q := by
  have hdiv := Nat.mul_div_le q (2 * s)
  have hhalf : 2 * (s * (q / (2 * s))) ≤ q := by
    simpa only [mul_assoc] using hdiv
  nlinarith

lemma ruzsaRepresentativeSum_sub_cast (q : ℕ) [NeZero q]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q) =
      lam * ((T.sum - U.sum : ℤ) : ZMod q) := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    ruzsaRepresentativeSum_cast, ruzsaRepresentativeSum_cast, Int.cast_sub]
  ring

lemma ruzsaModelMap_sum_eq_iff_dvd (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔
      (M : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) := by
  rw [ruzsaModelMap_sum, ruzsaModelMap_sum]
  constructor
  · intro h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using hz

lemma zmod_val_eq_natAbs_of_nonneg {q : ℕ} [NeZero q]
    {y : ℤ} {z : ZMod q} (hy : 0 ≤ y) (hyq : y.natAbs < q)
    (hcast : (y : ZMod q) = z) : z.val = y.natAbs := by
  have hycoe : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg hy
  have hcastNat : (y.natAbs : ZMod q) = z := by
    rw [← hcast]
    simpa using congrArg (fun t : ℤ => (t : ZMod q)) hycoe
  rw [← hcastNat, ZMod.val_natCast_of_lt hyq]

lemma int_natAbs_lt_of_neg_lt_and_lt {y : ℤ} {B : ℕ}
    (hlo : -(B : ℤ) < y) (hhi : y < B) : y.natAbs < B := by
  by_cases hy : 0 ≤ y
  · have hcast : (y.natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hy]
      exact hhi
    exact_mod_cast hcast
  · have hyneg : 0 ≤ -y := by omega
    have hcast : ((-y).natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hyneg]
      omega
    rw [Int.natAbs_neg] at hcast
    exact_mod_cast hcast

lemma ruzsaModelMap_multiset_sum_eq_iff
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val))
    {T U : Multiset ℤ}
    (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
    (hTcard : T.card = s) (hUcard : U.card = s) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔ T.sum = U.sum := by
  have hTsum : T.sum ∈ s • A := by
    simpa only [hTcard] using multiset_sum_mem_nsmul A hTA
  have hUsum : U.sum ∈ s • A := by
    simpa only [hUcard] using multiset_sum_mem_nsmul A hUA
  have hTUmem : T.sum - U.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨T.sum, hTsum, U.sum, hUsum, rfl⟩
  have hUTmem : U.sum - T.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨U.sum, hUsum, T.sum, hTsum, rfl⟩
  have hshort := ruzsaRepresentativeSum_sub_abs_lt lam hTcard hUcard hs
    (fun x hx => hmono x (hTA x hx)) (fun x hx => hmono x (hUA x hx))
  have hwidth := ruzsaBlockWidth_lt hs hq
  have hsmall :
      (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs < q := by
    have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
      exact_mod_cast hwidth
    apply int_natAbs_lt_of_neg_lt_and_lt
    · exact (by omega : -(q : ℤ) <
        -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hshort.2
    · exact hshort.1.trans hwidthZ
  constructor
  · intro hmap
    by_contra hsum
    have hx : T.sum - U.sum ≠ 0 := sub_ne_zero.mpr hsum
    by_cases hy : 0 ≤ (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U
    · have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam T U).mp hmap
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((T.sum - U.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hy hsmall
        exact ruzsaRepresentativeSum_sub_cast q lam T U
      exact hgood (T.sum - U.sum) hTUmem hx (by rwa [hval])
    · have hswapNonneg : 0 ≤ (ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T := by omega
      have hswapShort := ruzsaRepresentativeSum_sub_abs_lt lam hUcard hTcard hs
        (fun x hx => hmono x (hUA x hx)) (fun x hx => hmono x (hTA x hx))
      have hswapSmall :
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs < q := by
        have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
          exact_mod_cast hwidth
        apply int_natAbs_lt_of_neg_lt_and_lt
        · exact (by omega : -(q : ℤ) <
            -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hswapShort.2
        · exact hswapShort.1.trans hwidthZ
      have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam U T).mp hmap.symm
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((U.sum - T.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hswapNonneg hswapSmall
        exact ruzsaRepresentativeSum_sub_cast q lam U T
      have hx' : U.sum - T.sum ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
      exact hgood (U.sum - T.sum) hUTmem hx' (by rwa [hval])
  · intro hsum
    have hcast : ((((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q)) = 0 := by
      rw [ruzsaRepresentativeSum_sub_cast, hsum, sub_self, Int.cast_zero, mul_zero]
    have hdiv : (q : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast
    have hzero : (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      simpa only [Int.natAbs_natCast] using hsmall
    have hrepeq : ruzsaRepresentativeSum q lam T =
        ruzsaRepresentativeSum q lam U := by omega
    rw [ruzsaModelMap_sum, ruzsaModelMap_sum, hrepeq]

theorem isAddFreimanIso_ruzsaModelMap
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val)) :
    IsAddFreimanIso s (A : Set ℤ)
      (A.image (ruzsaModelMap q M lam) : Set (ZMod M))
      (ruzsaModelMap q M lam) := by
  let f := ruzsaModelMap q M lam
  have hrel {T U : Multiset ℤ}
      (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
      (hTcard : T.card = s) (hUcard : U.card = s) :
      (T.map f).sum = (U.map f).sum ↔ T.sum = U.sum :=
    ruzsaModelMap_multiset_sum_eq_iff lam hs hq hmono hgood
      hTA hUA hTcard hUcard
  have hinj : Set.InjOn f (A : Set ℤ) := by
    intro a ha b hb hab
    have hrepl := hrel
      (T := Multiset.replicate s a) (U := Multiset.replicate s b)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using hb)
      (by simp) (by simp)
    have hsum := hrepl.mp (by simp [f, hab])
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hsum
    have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
    nlinarith
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, Finset.mem_coe.mpr ha, rfl⟩
  · intro T U hTA hUA hTcard hUcard
    apply hrel
    · intro x hx
      exact Finset.mem_coe.mp (hTA hx)
    · intro x hx
      exact Finset.mem_coe.mp (hUA hx)
    · exact hTcard
    · exact hUcard

lemma exists_nonempty_large_color_fiber_mul {A : Finset ℤ} {k : ℕ}
    (hA : A.Nonempty) (hk : 0 < k) (f : ℤ → ℕ)
    (hf : ∀ a ∈ A, f a < k) :
    ∃ c < k, let B := A.filter fun a => f a = c
      B.Nonempty ∧ A.card ≤ k * B.card := by
  classical
  let n := (A.card - 1) / k
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := by
      simpa only [n] using Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.range k) (f := f)
      (fun a ha => Finset.mem_range.mpr (hf a ha)) (by simpa using hkn)
  refine ⟨c, Finset.mem_range.mp hc, ?_⟩
  dsimp
  have hceil : A.card - 1 < k * (n + 1) := by
    simpa only [n] using Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤
      k * (A.filter fun a => f a = c).card := by
    exact Nat.mul_le_mul_left k (by omega)
  constructor
  · exact Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard)
  · have hpred : A.card - 1 + 1 = A.card :=
      Nat.sub_one_add_one hApos.ne'
    have hlt : A.card - 1 <
        k * (A.filter fun a => f a = c).card := hceil.trans_le hmul
    omega

theorem exists_large_cyclic_freiman_model (A : Finset ℤ) (s : ℕ)
    (hA : A.Nonempty) (hs : 0 < s) :
    let D := s • A - s • A
    ∃ (A' : Finset ℤ) (B : Finset (ZMod (2 * D.card)))
      (f : ℤ → ZMod (2 * D.card)),
      A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
        B = A'.image f ∧ IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hDcard : 0 < D.card := Finset.card_pos.mpr hD
  let R := D.sup Int.natAbs
  let K := max (max (4 * D.card) (2 * s)) R + 1
  obtain ⟨q, hKq, hqPrime⟩ := Nat.exists_infinite_primes K
  have h4q : 4 * D.card < q := by
    dsimp [K] at hKq
    omega
  have h2sq : 2 * s < q := by
    dsimp [K] at hKq
    omega
  have hRq : R < q := by
    dsimp [K] at hKq
    omega
  let : Fact q.Prime := ⟨hqPrime⟩
  let : NeZero q := ⟨hqPrime.ne_zero⟩
  obtain ⟨lam, hlam, hgood⟩ := exists_good_multiplier
    (D := D) (N := D.card) (q := q) hDcard le_rfl
    (fun x hx => (Finset.le_sup hx).trans_lt hRq) h4q
  obtain ⟨c, hc, hfiber⟩ :=
    exists_nonempty_large_color_fiber_mul hA (by omega)
      (ruzsaColor q s lam) (fun a _ha => ruzsaColor_lt lam hs h2sq a)
  let A' := A.filter fun a => ruzsaColor q s lam a = c
  have hA'ne : A'.Nonempty := hfiber.1
  have hA'card : A.card ≤ (2 * s) * A'.card := hfiber.2
  have hA'sub : A' ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hmono : ∀ a ∈ A', ruzsaColor q s lam a = c := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hsumSub : s • A' ⊆ s • A := by
    exact nsmul_le_nsmul_right hA'sub s
  have hdiffSub : s • A' - s • A' ⊆ D := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨u, hsumSub hu, v, hsumSub hv, rfl⟩
  have hgood' : ∀ x ∈ s • A' - s • A', x ≠ 0 →
      ¬ (2 * D.card ∣ (lam * (x : ZMod q)).val) := by
    intro x hx hx0
    exact hgood x (hdiffSub hx) hx0
  have hM : 0 < 2 * D.card := by omega
  let : NeZero (2 * D.card) := ⟨hM.ne'⟩
  let f : ℤ → ZMod (2 * D.card) := ruzsaModelMap q (2 * D.card) lam
  let B := A'.image f
  refine ⟨A', B, f, hA'ne, hA'sub, hA'card, rfl, ?_⟩
  exact isAddFreimanIso_ruzsaModelMap lam hs h2sq hmono hgood'

end Erdos3.FreimanModel

end

section

open scoped BigOperators Pointwise

namespace Erdos3.FreimanModel

noncomputable section

structure FourfoldPresentation (β : Type*) where
  pos₁ : β
  pos₂ : β
  neg₁ : β
  neg₂ : β

namespace FourfoldPresentation

variable {β : Type*} [AddCommGroup β]

def eval (p : FourfoldPresentation β) : β :=
  p.pos₁ + p.pos₂ - p.neg₁ - p.neg₂

def Mem (B : Finset β) (p : FourfoldPresentation β) : Prop :=
  p.pos₁ ∈ B ∧ p.pos₂ ∈ B ∧ p.neg₁ ∈ B ∧ p.neg₂ ∈ B

end FourfoldPresentation

variable {α β : Type*} [AddCommGroup α] [AddCommGroup β]
  [DecidableEq β]

lemma mem_two_nsmul_sub_two_nsmul_iff
    {B : Finset β} {x : β} :
    x ∈ 2 • B - 2 • B ↔
      ∃ p : FourfoldPresentation β,
        p.Mem B ∧ p.eval = x := by
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • B = B + B by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd⟩, ?_⟩
    dsimp only [FourfoldPresentation.eval]
    rw [← huv, ← hab, ← hcd]
    abel
  · rintro ⟨p, hp, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨p.pos₁ + p.pos₂, ?_, p.neg₁ + p.neg₂, ?_, ?_⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.pos₁, hp.1, p.pos₂, hp.2.1, rfl⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.neg₁, hp.2.2.1, p.neg₂, hp.2.2.2, rfl⟩
    · dsimp only [FourfoldPresentation.eval]
      abel

noncomputable def defaultFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) : FourfoldPresentation β :=
  let b := Classical.choose hB
  ⟨b, b, b, b⟩

noncomputable def selectedFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) (x : β) : FourfoldPresentation β := by
  classical
  exact if hx : ∃ p : FourfoldPresentation β, p.Mem B ∧ p.eval = x then
      Classical.choose hx
    else defaultFourfoldPresentation B hB

lemma selectedFourfoldPresentation_spec (B : Finset β)
    (hB : B.Nonempty) {x : β} (hx : x ∈ 2 • B - 2 • B) :
    (selectedFourfoldPresentation B hB x).Mem B ∧
      (selectedFourfoldPresentation B hB x).eval = x := by
  have hex := mem_two_nsmul_sub_two_nsmul_iff.mp hx
  simp only [selectedFourfoldPresentation, dif_pos hex]
  exact Classical.choose_spec hex

def fourfoldMapValue (g : β → α) (p : FourfoldPresentation β) : α :=
  g p.pos₁ + g p.pos₂ - g p.neg₁ - g p.neg₂

lemma fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a b c d e f g h : G) :
    a + b - c - d = e + f - g - h ↔
      a + b + g + h = e + f + c + d := by
  constructor
  · intro heq
    calc
      a + b + g + h = (a + b - c - d) + (c + d + g + h) := by abel
      _ = (e + f - g - h) + (c + d + g + h) := by rw [heq]
      _ = e + f + c + d := by abel
  · intro heq
    calc
      a + b - c - d =
          (a + b + g + h) - (c + d + g + h) := by abel
      _ = (e + f + c + d) - (c + d + g + h) := by rw [heq]
      _ = e + f - g - h := by abel

lemma add_fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a₁ a₂ c₁ c₂ b₁ b₂ d₁ d₂
      e₁ e₂ g₁ g₂ f₁ f₂ h₁ h₂ : G) :
    (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
        (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) ↔
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
        e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by
  constructor
  · intro heq
    calc
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
          ((a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = ((e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by abel
  · intro heq
    calc
      (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
          (a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = (e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) := by abel

omit [DecidableEq β] in
lemma fourfoldMapValue_eq_iff_eval_eq
    {A : Set α} {B : Finset β} {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {p r : FourfoldPresentation β} (hp : p.Mem B) (hr : r.Mem B) :
    fourfoldMapValue g p = fourfoldMapValue g r ↔ p.eval = r.eval := by
  let s : Multiset β :=
    p.pos₁ ::ₘ p.pos₂ ::ₘ r.neg₁ ::ₘ r.neg₂ ::ₘ 0
  let t : Multiset β :=
    r.pos₁ ::ₘ r.pos₂ ::ₘ p.neg₁ ::ₘ p.neg₂ ::ₘ 0
  have hsB : ∀ ⦃x⦄, x ∈ s → x ∈ (B : Set β) := by
    intro x hx
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hr.2.2.1, hr.2.2.2]
  have htB : ∀ ⦃x⦄, x ∈ t → x ∈ (B : Set β) := by
    intro x hx
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hr.1, hr.2.1, hp.2.2.1, hp.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = p.pos₁ + p.pos₂ + r.neg₁ + r.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = r.pos₁ + r.pos₂ + p.neg₁ + p.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g p.pos₁ + g p.pos₂ + g r.neg₁ + g r.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g r.pos₁ + g r.pos₂ + g p.neg₁ + g p.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  exact (fourfold_sub_eq_iff_cross_add
    (g p.pos₁) (g p.pos₂) (g p.neg₁) (g p.neg₂)
    (g r.pos₁) (g r.pos₂) (g r.neg₁) (g r.neg₂)).trans
      (hrel.trans (fourfold_sub_eq_iff_cross_add
        p.pos₁ p.pos₂ p.neg₁ p.neg₂ r.pos₁ r.pos₂ r.neg₁ r.neg₂).symm)

noncomputable def freimanFourfoldLift (B : Finset β) (hB : B.Nonempty)
    (g : β → α) (x : β) : α :=
  fourfoldMapValue g (selectedFourfoldPresentation B hB x)

lemma freimanFourfoldLift_eq_of_presentation
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {x : β} (hx : x ∈ 2 • B - 2 • B)
    {p : FourfoldPresentation β} (hp : p.Mem B) (hpx : p.eval = x) :
    freimanFourfoldLift B hB g x = fourfoldMapValue g p := by
  have hs := selectedFourfoldPresentation_spec B hB hx
  apply (fourfoldMapValue_eq_iff_eval_eq hg hs.1 hp).mpr
  exact hs.2.trans hpx.symm

lemma freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul [DecidableEq α]
    {A : Finset α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : Set.MapsTo g (B : Set β) (A : Set α))
    {x : β} (hx : x ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x ∈ 2 • A - 2 • A := by
  let p := selectedFourfoldPresentation B hB x
  have hp := selectedFourfoldPresentation_spec B hB hx
  rw [mem_two_nsmul_sub_two_nsmul_iff]
  refine ⟨⟨g p.pos₁, g p.pos₂, g p.neg₁, g p.neg₂⟩, ?_, rfl⟩
  exact ⟨hg hp.1.1, hg hp.1.2.1, hg hp.1.2.2.1, hg hp.1.2.2.2⟩

theorem freimanFourfoldLift_injOn
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g) :
    Set.InjOn (freimanFourfoldLift B hB g) (2 • B - 2 • B : Finset β) := by
  intro x hx y hy hxy
  have hsx := selectedFourfoldPresentation_spec B hB hx
  have hsy := selectedFourfoldPresentation_spec B hB hy
  have heval := (fourfoldMapValue_eq_iff_eval_eq hg hsx.1 hsy.1).mp hxy
  rw [hsx.2, hsy.2] at heval
  exact heval

lemma freimanFourfoldLift_add_eq_add
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 8 (B : Set β) A g)
    {x y z w : β}
    (hx : x ∈ 2 • B - 2 • B) (hy : y ∈ 2 • B - 2 • B)
    (hz : z ∈ 2 • B - 2 • B) (hw : w ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x + freimanFourfoldLift B hB g y =
        freimanFourfoldLift B hB g z + freimanFourfoldLift B hB g w ↔
      x + y = z + w := by
  let px := selectedFourfoldPresentation B hB x
  let py := selectedFourfoldPresentation B hB y
  let pz := selectedFourfoldPresentation B hB z
  let pw := selectedFourfoldPresentation B hB w
  have hpx := selectedFourfoldPresentation_spec B hB hx
  have hpy := selectedFourfoldPresentation_spec B hB hy
  have hpz := selectedFourfoldPresentation_spec B hB hz
  have hpw := selectedFourfoldPresentation_spec B hB hw
  let s : Multiset β := px.pos₁ ::ₘ px.pos₂ ::ₘ py.pos₁ ::ₘ py.pos₂ ::ₘ
    pz.neg₁ ::ₘ pz.neg₂ ::ₘ pw.neg₁ ::ₘ pw.neg₂ ::ₘ 0
  let t : Multiset β := pz.pos₁ ::ₘ pz.pos₂ ::ₘ pw.pos₁ ::ₘ pw.pos₂ ::ₘ
    px.neg₁ ::ₘ px.neg₂ ::ₘ py.neg₁ ::ₘ py.neg₂ ::ₘ 0
  have hsB : ∀ ⦃a⦄, a ∈ s → a ∈ (B : Set β) := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpx.1.1, hpx.1.2.1, hpy.1.1, hpy.1.2.1,
      hpz.1.2.2.1, hpz.1.2.2.2, hpw.1.2.2.1, hpw.1.2.2.2]
  have htB : ∀ ⦃a⦄, a ∈ t → a ∈ (B : Set β) := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpz.1.1, hpz.1.2.1, hpw.1.1, hpw.1.2.1,
      hpx.1.2.2.1, hpx.1.2.2.2, hpy.1.2.2.1, hpy.1.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = px.pos₁ + px.pos₂ + py.pos₁ + py.pos₂ +
      pz.neg₁ + pz.neg₂ + pw.neg₁ + pw.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = pz.pos₁ + pz.pos₂ + pw.pos₁ + pw.pos₂ +
      px.neg₁ + px.neg₂ + py.neg₁ + py.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g px.pos₁ + g px.pos₂ + g py.pos₁ + g py.pos₂ +
        g pz.neg₁ + g pz.neg₂ + g pw.neg₁ + g pw.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g pz.pos₁ + g pz.pos₂ + g pw.pos₁ + g pw.pos₂ +
        g px.neg₁ + g px.neg₂ + g py.neg₁ + g py.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  have hmapCross := add_fourfold_sub_eq_iff_cross_add
    (g px.pos₁) (g px.pos₂) (g px.neg₁) (g px.neg₂)
    (g py.pos₁) (g py.pos₂) (g py.neg₁) (g py.neg₂)
    (g pz.pos₁) (g pz.pos₂) (g pz.neg₁) (g pz.neg₂)
    (g pw.pos₁) (g pw.pos₂) (g pw.neg₁) (g pw.neg₂)
  have horiginalCross := add_fourfold_sub_eq_iff_cross_add
    px.pos₁ px.pos₂ px.neg₁ px.neg₂ py.pos₁ py.pos₂ py.neg₁ py.neg₂
    pz.pos₁ pz.pos₂ pz.neg₁ pz.neg₂ pw.pos₁ pw.pos₂ pw.neg₁ pw.neg₂
  have hvalues :
      px.eval + py.eval = pz.eval + pw.eval ↔ x + y = z + w := by
    rw [hpx.2, hpy.2, hpz.2, hpw.2]
  exact hmapCross.trans (hrel.trans (horiginalCross.symm.trans hvalues))

end

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_fourfold_lift_of_eight_iso {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (B : Finset H) (hB : B.Nonempty) (f : G → H)
    (hf : IsAddFreimanIso 8 (A : Set G) (B : Set H) f) :
    ∃ L : H → G,
      Set.MapsTo L (2 • B - 2 • B : Finset H) (2 • A - 2 • A : Finset G) ∧
      Set.InjOn L (2 • B - 2 • B : Finset H) ∧ L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  classical
  let g := Function.invFunOn f (A : Set G)
  have hg : IsAddFreimanIso 8 (B : Set H) (A : Set G) g := hf.invFunOn
  have hg4 : IsAddFreimanIso 4 (B : Set H) (A : Set G) g := hg.mono (hmn := by decide)
  let L := freimanFourfoldLift B hB g
  refine ⟨L, ?_, freimanFourfoldLift_injOn hB hg4, ?_, ?_⟩
  · intro x hx
    exact freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul hB hg.bijOn.mapsTo hx
  · obtain ⟨b, hb⟩ := hB.exists_mem
    let p : FourfoldPresentation H := ⟨b, b, b, b⟩
    have hp : p.Mem B := ⟨hb, hb, hb, hb⟩
    have hpx : p.eval = 0 := by simp [p, FourfoldPresentation.eval]
    have hz : (0 : H) ∈ 2 • B - 2 • B :=
      mem_two_nsmul_sub_two_nsmul_iff.mpr ⟨p, hp, hpx⟩
    change freimanFourfoldLift B hB g 0 = 0
    rw [freimanFourfoldLift_eq_of_presentation hB hg4 hz hp hpx]
    simp [fourfoldMapValue, p]
  · intro x hx y hy z hz w hw
    exact freimanFourfoldLift_add_eq_add hB hg hx hy hz hw

end Erdos3.FreimanModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearRestrictionDenominatorSize
namespace OAI

section

namespace Erdos3

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

theorem polynomialLinearRestriction_denominator_pos
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) (d : ℕ) :
    0 < polynomialDenominator P *
      matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d :=
  Nat.mul_pos (polynomialDenominator_pos P)
    (pow_pos (matrixDenominator_pos _) _)

theorem polynomialLinearRestriction_denominator_le
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) {d K H : ℕ}
    (hd : P.totalDegree ≤ d) (hP : RationalPolynomialHeightLE P K)
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) :
    polynomialDenominator P * matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d ≤
      K ^ ((Fintype.card σ + 1) ^ d) * H ^ ((Fintype.card σ * Fintype.card τ) * d) := by
  have hcard : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d
      (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hd)
  have hpoly : polynomialDenominator P ≤ K ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le P hP).trans (Nat.pow_le_pow_right hP.one_le hcard)
  have hmatrix := Nat.pow_le_pow_left
    (matrixDenominator_le (fun i j => A (Pi.single j 1) i) hA) d
  rw [← pow_mul] at hmatrix
  exact Nat.mul_le_mul hpoly hmatrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
namespace OAI

section

namespace Erdos3

theorem floor_four_difference_bound (c x₀ x₁ x₂ x₃ : ℝ) (z : ℤ)
    (h : |c + (x₁ + x₂ - x₀ - x₃) - z| ≤ 1) :
    |⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z| ≤ 6 := by
  have hc := Int.floor_le c
  have hc' := Int.sub_one_lt_floor c
  have h₀ := Int.floor_le x₀
  have h₀' := Int.sub_one_lt_floor x₀
  have h₁ := Int.floor_le x₁
  have h₁' := Int.sub_one_lt_floor x₁
  have h₂ := Int.floor_le x₂
  have h₂' := Int.sub_one_lt_floor x₂
  have h₃ := Int.floor_le x₃
  have h₃' := Int.sub_one_lt_floor x₃
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hh : |((⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z : ℤ) : ℝ)| ≤ 6 := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  exact_mod_cast hh

end Erdos3

end

section

namespace Erdos3

theorem exists_unrounded_scalar (M l : ℕ) [NeZero M] (hl : 0 < l)
    (a : ℝ) (u : ℤ) (h : ((⌊(M : ℝ) * l * a⌋ : ℤ) : ZMod M) = (u : ZMod M)) :
    ∃ k : ℤ, 0 ≤ a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l ∧
      a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l < 1 / ((M : ℝ) * l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u ⌊(M : ℝ) * l * a⌋ M).mp h.symm
  have hkR : (⌊(M : ℝ) * l * a⌋ : ℝ) = (u : ℝ) + (M : ℝ) * k := by
    have he : (⌊(M : ℝ) * l * a⌋ : ℝ) - (u : ℝ) = (M : ℝ) * k := by exact_mod_cast hk
    linarith
  have heq : a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l =
      ((M : ℝ) * l * a - ⌊(M : ℝ) * l * a⌋) / ((M : ℝ) * l) := by
    rw [hkR]
    field_simp
    ring
  refine ⟨k, ?_, ?_⟩
  · rw [heq]
    exact div_nonneg (sub_nonneg.mpr (Int.floor_le _)) (by positivity)
  · rw [heq]
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith [Int.lt_floor_add_one ((M : ℝ) * l * a)]

end Erdos3

end

section

namespace Erdos3

variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype I]

end Erdos3

end

section

namespace Erdos3

def coordinateDenominatorGrid {I : Type*} (l : I → ℕ) : Set (I → ℝ) :=
  {q | ∃ z : I → ℤ, ∀ i, (z i : ℝ) = (l i : ℝ) * q i}

noncomputable def variableRoundedCoefficient {I : Type*} (M l : I → ℕ)
    (a : I → ℝ) : ∀ i, ZMod (M i) :=
  fun i => ((⌊(M i : ℝ) * l i * a i⌋ : ℤ) : ZMod (M i))

noncomputable def variableRoundingErrors {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) : Finset (∀ i, ZMod (M i)) := by
  classical
  exact (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).image
    (fun b i => (b i : ZMod (M i)) - ((⌊(M i : ℝ) * l i * c i⌋ : ℤ) : ZMod (M i)))

theorem variableRoundingErrors_card_le {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) :
    (variableRoundingErrors M l c).card ≤ 13 ^ Fintype.card I := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).card := Finset.card_image_le
    _ = _ := by simp

theorem variableRoundedCoefficient_four_mem {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) (a : Fin 4 → I → ℝ) (q ε : I → ℝ)
    (hgrid : q ∈ coordinateDenominatorGrid l)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (herror : ∀ i, |c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i| ≤ ε i) :
    variableRoundedCoefficient M l (a 1) + variableRoundedCoefficient M l (a 2) -
      variableRoundedCoefficient M l (a 0) - variableRoundedCoefficient M l (a 3) ∈
        variableRoundingErrors M l c := by
  classical
  obtain ⟨z, hz⟩ := hgrid
  let k : I → ℝ := fun i => (M i : ℝ) * l i
  let b : I → ℤ := fun i => ⌊k i * c i⌋ +
    (⌊k i * a 1 i⌋ + ⌊k i * a 2 i⌋ - ⌊k i * a 0 i⌋ - ⌊k i * a 3 i⌋) - (M i : ℤ) * z i
  have hb (i : I) : b i ∈ Finset.Icc (-6 : ℤ) 6 := by
    have hk : 0 ≤ k i := by dsimp [k]; positivity
    have heq : k i * (c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i) =
        k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
          (M i : ℝ) * z i := by
      rw [hz i]
      dsimp [k]
      ring
    have hh : |k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
        (M i : ℝ) * z i| ≤ 1 := by
      rw [← heq, abs_mul, abs_of_nonneg hk]
      exact (mul_le_mul_of_nonneg_left (herror i) hk).trans (hsmall i)
    have hf := floor_four_difference_bound (k i * c i) (k i * a 0 i) (k i * a 1 i)
      (k i * a 2 i) (k i * a 3 i) ((M i : ℤ) * z i)
      (by simpa only [Int.cast_mul, Int.cast_natCast] using hh)
    exact Finset.mem_Icc.mpr (abs_le.mp hf)
  apply Finset.mem_image.mpr
  refine ⟨b, Fintype.mem_piFinset.mpr hb, ?_⟩
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, variableRoundedCoefficient, b, k, Int.cast_sub,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem map_integer_coordinates {r : ℕ} {G : Type*} [AddCommGroup G]
    (Φ : (Fin r → ℤ) →+ G) (x : Fin r → ℤ) :
    Φ x = ∑ j, x j • Φ (Pi.single j 1) := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin r → ℤ) := by
    funext i
    simp [Pi.single_apply]
  calc
    Φ x = Φ (∑ j, x j • (Pi.single j 1 : Fin r → ℤ)) := congrArg Φ hx
    _ = _ := by simp only [map_sum, map_zsmul]

noncomputable def finiteCoefficientLift {I : Type*} {M : ℕ}
    (l : ℕ) (b : I → ZMod M) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M : ℝ) * l)

theorem finiteCoefficientLift_mem_Ico {I : Type*} {M : ℕ} [NeZero M]
    (l : ℕ) (hl : 0 < l) (b : I → ZMod M) (i : I) :
    finiteCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · change ((b i).val : ℝ) / ((M : ℝ) * l) < 1 / l
    apply (div_lt_iff₀ (mul_pos hM hlR)).mpr
    have hv : ((b i).val : ℝ) < M := by exact_mod_cast (b i).val_lt
    have heq : (1 / (l : ℝ)) * ((M : ℝ) * l) = M := by field_simp
    rwa [heq]

end Erdos3

end

section

namespace Erdos3

variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype I]

theorem variable_graph_energy (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i) :
    S.card ≤ 13 ^ Fintype.card I *
      Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) := by
  classical
  have h := graph_energy_of_few_quadruple_differences H S
    (fun h => variableRoundedCoefficient M l (a h)) (variableRoundingErrors M l c) hH (by
      intro t ht
      obtain ⟨q, hq, herr⟩ := hnear t ht
      exact variableRoundedCoefficient_four_mem M l c
        ![a t.2.1, a (t.2.1 - t.1), a t.2.2, a (t.2.2 - t.1)] q ε hq hsmall herr)
  exact h.trans (Nat.mul_le_mul_right _ (variableRoundingErrors_card_le M l c))

theorem variable_graph_energy_density (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ) {p : ℝ}
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i)
    (hdensity : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤ S.card) :
    Real.exp (-(p + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  classical
  let E := Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
    (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
  have hcard := variable_graph_energy H S a c M l ε hH hsmall hnear
  have hcount : (13 : ℝ) ^ Fintype.card I ≤ Real.exp (13 * Fintype.card I) := by
    calc
      _ ≤ (Real.exp 13) ^ Fintype.card I :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (13 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlarge : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤
      Real.exp (13 * Fintype.card I) * E := by
    apply hdensity.trans
    have hc := (Nat.cast_le (α := ℝ)).mpr hcard
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg E))
  calc
    _ = Real.exp (-(13 * Fintype.card I)) * (Real.exp (-p) * (H.card : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(13 * Fintype.card I)) * (Real.exp (13 * Fintype.card I) * E) :=
      mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
    _ = E := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def variableCoefficientLift {I : Type*} {M : I → ℕ}
    (l : I → ℕ) (b : ∀ i, ZMod (M i)) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M i : ℝ) * l i)

theorem variableCoefficientLift_mem_Ico {I : Type*} {M : I → ℕ} [∀ i, NeZero (M i)]
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (b : ∀ i, ZMod (M i)) (i : I) :
    variableCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l i) := by
  exact finiteCoefficientLift_mem_Ico (l i) (hl i) (fun _ : Unit => b i) ()

theorem exists_variable_unrounded_affine {I : Type*} {M : I → ℕ} {r : ℕ}
    [∀ i, NeZero (M i)] (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (b : ∀ i, ZMod (M i)) (Φ : (Fin r → ℤ) →+ (∀ i, ZMod (M i)))
    (x : Fin r → ℤ) (a : I → ℝ) (h : variableRoundedCoefficient M l a = b + Φ x) :
    ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
      |a i - (variableCoefficientLift l b +
        ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1))) i - q i| ≤
          1 / ((M i : ℝ) * l i) := by
  let u : I → ℤ := fun i => ((b i).val : ℤ) + ∑ j, x j * ((Φ (Pi.single j 1) i).val : ℤ)
  have hu : variableRoundedCoefficient M l a = fun i => (u i : ZMod (M i)) := by
    rw [h, map_integer_coordinates Φ x]
    funext i
    simp only [u, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have heq : (fun i => (u i : ℝ) / ((M i : ℝ) * l i)) = variableCoefficientLift l b +
      ∑ j, (x j : ℝ) • variableCoefficientLift l (Φ (Pi.single j 1)) := by
    funext i
    simp only [u, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      variableCoefficientLift, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      add_div, Finset.sum_div, mul_div_assoc]
  have hi (i : I) := exists_unrounded_scalar (M i) (l i) (hl i) (a i) (u i) (congrFun hu i)
  choose k hk0 hk1 using hi
  let q : I → ℝ := fun i => (k i : ℝ) / l i
  refine ⟨q, ⟨k, ?_⟩, ?_⟩
  · intro i
    have hlR : (0 : ℝ) < l i := by exact_mod_cast hl i
    dsimp [q]
    field_simp
  · intro i
    rw [← heq]
    change |a i - (u i : ℝ) / ((M i : ℝ) * l i) - (k i : ℝ) / l i| ≤ _
    rw [abs_of_nonneg (hk0 i)]
    exact (hk1 i).le

theorem exists_coordinate_rounding_moduli {I : Type*}
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (ε : I → ℝ) (hε : ∀ i, 0 < ε i)
    (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1) :
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧ (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      ∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i := by
  have hi (i : I) := exists_rounding_modulus_with_recovery (l i) (hl i) (hε i) (hsmall i)
  choose M hM hscale herror using hi
  exact ⟨M, hM, hscale, herror⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

variable {s r N : ℕ}
  [NeZero N]
  {b p q P : ℝ}
  {H : Finset (ZMod N)}

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedSourceEquivalence
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (e : X ≃ Y)
    (hweight : ∀ x, q.weight (e x) = p.weight x) (f : Y → ℝ) :
    p.mean (fun x => f (e x)) = q.mean f := by
  calc
    _ = ∑ x, q.weight (e x) * f (e x) := by
      unfold mean
      simp only [hweight]
    _ = _ := e.sum_comp (fun y => q.weight y * f y)

theorem uniform_mean_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (e : X ≃ Y) (f : Y → ℝ) :
    (uniform X).mean (fun x => f (e x)) = (uniform Y).mean f := by
  simp only [uniform_mean]
  exact Fintype.expect_equiv e _ f (fun _ => rfl)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds
namespace OAI

section

namespace Erdos3

def majorArcBiasLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  (denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n : ℕ) +
    ((n + 1) * majorArcBiasExponent n : ℕ) * (1 + 2 * p)

def majorArcLocalizationLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  256 + 6 * p + ((n + 1) * 2 : ℕ) * (1 + 2 * p)

def majorArcLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLocalizationLog n p + majorArcBiasLog n p + 1

def majorArcErrorLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcBiasLog n p + (n + 1 : ℕ) * majorArcLocalizationLog n p

def majorArcCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (majorArcBiasLog n p + (n + 1 : ℕ) * p) + v + majorArcErrorLog n p + 2

theorem majorArcBaseLogs_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ majorArcBiasLog n p ∧ 0 ≤ majorArcLocalizationLog n p ∧
      0 ≤ majorArcLengthLog n p ∧ 0 ≤ majorArcErrorLog n p := by
  unfold majorArcLengthLog majorArcErrorLog majorArcBiasLog majorArcLocalizationLog
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem majorArcCoverLog_nonneg (n j : ℕ) {p v : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ majorArcCoverLog n j p v := by
  obtain ⟨hb, _, _, he⟩ := majorArcBaseLogs_nonneg n hp
  unfold majorArcCoverLog
  positivity

end Erdos3

end

section

namespace Erdos3

def majorArcSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * majorArcCoverLog n j p v)

def uniformBlockAccuracyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℕ) +
    (w + t * ((majorArcLengthExponent n : ℕ) + majorArcLengthLog n p)) + 2

def uniformSpectrumSizeLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  majorArcSpectrumLog n j p v + (w + t * majorArcLengthLog n p) + 1 +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) *
      uniformBlockAccuracyLog n j t p v w

theorem uniformSpectrumLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ majorArcSpectrumLog n j p v ∧ 0 ≤ uniformBlockAccuracyLog n j t p v w ∧
      0 ≤ uniformSpectrumSizeLog n j t p v w := by
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hS : 0 ≤ majorArcSpectrumLog n j p v := by
    unfold majorArcSpectrumLog
    positivity
  have hA : 0 ≤ uniformBlockAccuracyLog n j t p v w := by
    unfold uniformBlockAccuracyLog
    positivity
  refine ⟨hS, hA, ?_⟩
  unfold uniformSpectrumSizeLog
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveRetainedDenominatorLog
namespace OAI

section

namespace Erdos3

def positiveModerateLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLengthLog n p + majorArcLengthLog (n + 1) p + 2

def positiveModerateCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  majorArcLengthLog (n + 1) p + 1 + majorArcCoverLog n j p (v + 4) +
    majorArcCoverLog (n + 1) j p v + 1

def positiveModerateSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * positiveModerateCoverLog n j p v)

def positiveModerateAccuracyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w : A) : A :=
  1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) +
    (w + t * ((positiveModerateLengthExponent n : ℕ) + positiveModerateLengthLog n p)) + 2

theorem positiveModerateLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ positiveModerateLengthLog n p ∧ 0 ≤ positiveModerateCoverLog n j p v ∧
      0 ≤ positiveModerateSpectrumLog n j p v ∧ 0 ≤ positiveModerateAccuracyLog n j t p v w := by
  have hn := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hn1 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hc := majorArcCoverLog_nonneg n j hp (by positivity : 0 ≤ v + 4)
  have hc1 := majorArcCoverLog_nonneg (n + 1) j hp hv
  have hL : 0 ≤ positiveModerateLengthLog n p := by unfold positiveModerateLengthLog; positivity
  have hC : 0 ≤ positiveModerateCoverLog n j p v := by unfold positiveModerateCoverLog; positivity
  have hS : 0 ≤ positiveModerateSpectrumLog n j p v := by unfold positiveModerateSpectrumLog; positivity
  refine ⟨hL, hC, hS, ?_⟩
  unfold positiveModerateAccuracyLog
  positivity

end Erdos3

end

section

namespace Erdos3

def positiveRetainedBiasLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateAccuracyLog n j t p v w + E

def positiveSpectrumCardLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) *
      positiveRetainedBiasLog n j t p v w E +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E) + 1

def positiveRetainedFrequencyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateCoverLog n j p v + (positiveModerateCoverExponent n j : ℕ) *
    positiveRetainedBiasLog n j t p v w E + 1

theorem positiveRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedBiasLog n j t p v w E ∧
      0 ≤ positiveSpectrumCardLog n j t p v w E ∧
      0 ≤ positiveRetainedFrequencyLog n j t p v w E := by
  obtain ⟨hL, hC, hS, hA⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hB : 0 ≤ positiveRetainedBiasLog n j t p v w E := by
    unfold positiveRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_⟩
  · unfold positiveSpectrumCardLog
    positivity
  · unfold positiveRetainedFrequencyLog
    positivity

end Erdos3

end

section

namespace Erdos3

def positiveRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (positiveRetainedFrequencyLog n j t p v w E + 1) +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E)

def positiveRetainedComplexityLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  positiveSpectrumCardLog n j t p v w E + positiveRetainedFrequencyLog n j t p v w E +
    positiveRetainedDenominatorLog n j t p v w E

theorem positiveRetainedDenominatorLog_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedDenominatorLog n j t p v w E := by
  obtain ⟨hB, _, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hL := (positiveModerateLogs_nonneg n j t hp hv hw).1
  unfold positiveRetainedDenominatorLog
  positivity

theorem positiveRetainedComplexityLog_bounds (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveSpectrumCardLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E := by
  obtain ⟨_, hC, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hD := positiveRetainedDenominatorLog_nonneg n j t hp hv hw hE
  unfold positiveRetainedComplexityLog
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVA (S : Finset I) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVATruncation (D : Finset (Finset I))
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ S ∈ D, productANOVA μ S f x

noncomputable def productANOVAEnergy (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ S ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVATensorChoices
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def coordinateUnionWeight (z : Sigma X) : ℝ := (μ z.1).weight z.2

noncomputable def productANOVATensor (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    if (∏ j, coordinateUnionWeight μ (z j)) = 0 then 0 else
      productANOVA μ (Finset.univ.image (fun j => (z j).1)) f
        (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable def productANOVATensorChoices (k q : ℕ) : Finset ((Fin q × Fin k) → I) := by
  classical
  exact Finset.univ.filter (fun a => (∀ j, StrictMono (fun l => a (j, l))) ∧
    ∀ i, (Finset.univ.filter (fun j => ∃ l, a (j, l) = i)).card ≠ 1)

variable {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

def finiteTaggedTupleEquiv : (J → Sigma X) ≃ Σ a : J → I, ∀ j, X (a j) where
  toFun z := ⟨fun j => (z j).1, fun j => (z j).2⟩
  invFun z j := ⟨z.1 j, z.2 j⟩
  left_inv z := by funext j; exact Sigma.eta (z j)
  right_inv z := by cases z; rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

noncomputable def orderedFamilyTensor (k : ℕ) (base : ∀ i, X i)
    (F : Finset I → (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    F (Finset.univ.image (fun j => (z j).1))
      (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionDensityWeight (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  productSectionAverage μ T A z (fun y => rho y * F y) x /
    productSectionAverage μ T A z rho x

noncomputable def productNormalizedSectionWeight (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionDensityWeight μ T A z rho F x

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

noncomputable def normalizedObservedDensity (w : Ω → ℝ) (scale : ℝ) (x : ∀ i, X i) : ℝ :=
  scale⁻¹ * observedProductDensity μ p F w x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def cut (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then w z else 0

noncomputable def erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then 0 else w z

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

instance containsDecidable (c : ProductCylinder X) (x : ∀ i, X i) : Decidable (c.Contains x) := by
  unfold Contains
  infer_instance

end Erdos3.ProductCylinder

end

section

namespace Erdos3

inductive CylinderRemovalChain {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (K τ : ℝ) (j r : ℕ) :
    (Ω → ℝ) → (Ω → ℝ) → List (ProductCylinder X) → Prop where
  | nil (w : Ω → ℝ) : CylinderRemovalChain μ base p F K τ j r w w []
  | cons {w v : Ω → ℝ} {cs : List (ProductCylinder X)} (c : ProductCylinder X)
      (hsize : c.1.card ≤ j)
      (hmass : τ < c.mass μ base (observedProductDensity μ p F w))
      (hbounded : ProductBoundedMarginals μ
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F w) c) K r)
      (rest : CylinderRemovalChain μ base p F K τ j r (c.erase F w) v cs) :
      CylinderRemovalChain μ base p F K τ j r w v (c :: cs)

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

noncomputable def positiveCandidates (b : ℕ) (w : Ω → ℝ) : Finset (ProductCylinder X) := by
  classical
  exact (bounded (X := X) b).filter (fun c => 0 < c.mass μ base (observedProductDensity μ p F w))

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def removedCylinderWeights (F : Ω → ∀ i, X i) :
    (Ω → ℝ) → List (ProductCylinder X) → List (Ω → ℝ)
  | _, [] => []
  | w, c :: cs => c.cut F w :: removedCylinderWeights F (c.erase F w) cs

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformScaledRetainedLogBounds
namespace OAI

section

namespace Erdos3

def uniformRetainedBiasLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformBlockAccuracyLog n j t p v w + E

def uniformSpectrumCardLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformSpectrumSizeLog n j t p v w +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) * E

def uniformRetainedFrequencyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  1 + majorArcCoverLog n j p v + (majorArcCoverExponent n j : ℕ) *
    uniformRetainedBiasLog n j t p v w E

def uniformRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (3 + majorArcCoverLog n j p v) + (majorArcCoverExponent n j * j : ℕ) *
      uniformRetainedBiasLog n j t p v w E +
    (w + t * majorArcLengthLog n p + (majorArcLengthExponent n * t : ℕ) *
      uniformRetainedBiasLog n j t p v w E) + 2

theorem uniformRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ uniformRetainedBiasLog n j t p v w E ∧
      0 ≤ uniformSpectrumCardLog n j t p v w E ∧
      0 ≤ uniformRetainedFrequencyLog n j t p v w E ∧
      0 ≤ uniformRetainedDenominatorLog n j t p v w E := by
  obtain ⟨_, hA, hS⟩ := uniformSpectrumLogs_nonneg n j t hp hv hw
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hB : 0 ≤ uniformRetainedBiasLog n j t p v w E := by
    unfold uniformRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_, ?_⟩
  · unfold uniformSpectrumCardLog
    positivity
  · unfold uniformRetainedFrequencyLog
    positivity
  · unfold uniformRetainedDenominatorLog
    positivity

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.PolynomialApproximation
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped Pointwise

noncomputable def finitePairing
    {Ω : Type*} [Fintype Ω] (f q : Ω → ℝ) : ℝ :=
  mean (fun x => f x * q x)

theorem finitePairing_add_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f + g) q =
      finitePairing f q + finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePairing_smul_left
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing (c • f) q = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2

noncomputable def finitePairingLinearMap
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := finitePairing f q
  map_add' f g := finitePairing_add_left f g q
  map_smul' c f := by
    simpa [smul_eq_mul] using finitePairing_smul_left c f q

noncomputable def finitePairingCLM
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] ℝ :=
  (finitePairingLinearMap q).toContinuousLinearMap

@[simp]
theorem finitePairingCLM_apply
    {Ω : Type*} [Fintype Ω] (q f : Ω → ℝ) :
    finitePairingCLM q f = finitePairing f q :=
  rfl

noncomputable def finiteTestProfile
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] (τ → ℝ) :=
  ContinuousLinearMap.pi (fun t => finitePairingCLM (q t))

@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl

noncomputable def finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) : Ω → ℝ :=
  ∑ t, c t • q t

@[simp]
theorem finiteTestCombination_zero
    {Ω τ : Type*} [Fintype τ] (q : τ → Ω → ℝ) :
    finiteTestCombination q 0 = 0 := by
  classical
  ext x
  simp [finiteTestCombination]

def positivePart {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => max (q x) 0

@[simp]
theorem positivePart_apply
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positivePart q x = max (q x) 0 :=
  rfl

@[simp]
theorem positivePart_of_nonneg
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : 0 ≤ q x) :
    positivePart q x = q x :=
  max_eq_left hx

@[simp]
theorem positivePart_of_nonpos
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : q x ≤ 0) :
    positivePart q x = 0 :=
  max_eq_right hx

@[simp]
theorem positivePart_zero {Ω : Type*} :
    positivePart (0 : Ω → ℝ) = 0 := by
  ext x
  simp [positivePart]

noncomputable def positiveSupportIndicator
    {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => if 0 ≤ q x then 1 else 0

@[simp]
theorem positiveSupportIndicator_mul
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positiveSupportIndicator q x * q x =
      positivePart q x := by
  by_cases hx : 0 ≤ q x
  · simp [positiveSupportIndicator, positivePart, hx]
  · have hx' : q x ≤ 0 := le_of_not_ge hx
    simp [positiveSupportIndicator, positivePart, hx, hx']

@[simp]
theorem finitePairing_one_left
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (fun _ : Ω => (1 : ℝ)) q = mean q := by
  simp [finitePairing]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def testMonomial
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) : Ω → ℝ :=
  fun x => ∏ i, q (s i) x

@[simp]
theorem testMonomial_apply
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) (x : Ω) :
    testMonomial q s x = ∏ i, q (s i) x :=
  rfl

@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

namespace WeightedSimplexSystem

def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight

end WeightedSimplexSystem

def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def simplexTailSum (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i

def simplexTailMoment (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i

def simplexCoordinatesOfAP (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (simplexTailMoment r N y - a - d - simplexTailSum r N y)
    (Fin.cases (a - simplexTailMoment r N y) y)

@[simp]
theorem simplexCoordinatesOfAP_zero (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 0 =
      simplexTailMoment r N y - a - d - simplexTailSum r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_one (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 1 =
      a - simplexTailMoment r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_succ_succ (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    simplexCoordinatesOfAP r N a d y i.succ.succ = y i :=
  rfl

theorem simplexCoordinateSum_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateSum (r + 2) N x =
      x 0 + x 1 +
        simplexTailSum r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateSum, simplexTailSum, Fin.sum_univ_succ,
    add_assoc]

theorem simplexCoordinateMoment_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateMoment (r + 2) N x =
      x 1 + simplexTailMoment r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateMoment, simplexTailMoment,
    Fin.sum_univ_succ]

@[simp]
theorem simplexCoordinateSum_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateSum (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = -d := by
  rw [simplexCoordinateSum_decompose]
  simp
  ring

@[simp]
theorem simplexCoordinateMoment_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateMoment (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = a := by
  rw [simplexCoordinateMoment_decompose]
  simp

def simplexAPEquiv (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((simplexCoordinateMoment (r + 2) N x,
      -simplexCoordinateSum (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := simplexCoordinatesOfAP r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [simplexCoordinatesOfAP_zero,
        simplexCoordinateMoment_decompose,
        simplexCoordinateSum_decompose]
      ring
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [simplexCoordinatesOfAP_one,
        simplexCoordinateMoment_decompose]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          simplexCoordinateMoment (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            a
        exact simplexCoordinateMoment_coordinatesOfAP r N a d tail
      · change
          -simplexCoordinateSum (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            d
        rw [simplexCoordinateSum_coordinatesOfAP]
        simp
    · funext i
      change simplexCoordinatesOfAP r N a d tail i.succ.succ = tail i
      exact simplexCoordinatesOfAP_succ_succ r N a d tail i

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph

noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    Finset (DeletedVector V j) := by
  classical
  exact Finset.univ.filter (H.edge j)

@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k)
    (x : DeletedVector V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]

noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }

@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]

def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j

end SimplexHypergraph

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)

@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl

@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

theorem isBoundedCutTest_const
    {G : Type*} {r : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsBoundedCutTest (fun _ : Fin r => fun _ : Fin (r - 1) → G => c) :=
  ⟨fun _ _ => hc0, fun _ _ => hc1⟩

@[simp]
theorem isBoundedCutTest_zero
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (0 : ℝ)) :=
  isBoundedCutTest_const (by positivity) (by norm_num)

@[simp]
theorem isBoundedCutTest_one
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) :=
  isBoundedCutTest_const (by positivity) le_rfl

noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutCorrelation_self
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f f u = 0 := by
  simp [cutCorrelation]

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def mulAddEquivOfIsUnit
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a) :
    R ≃+ R :=
  DistribMulAction.toAddEquiv R ha.unit

@[simp]
theorem mulAddEquivOfIsUnit_apply
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a)
    (x : R) :
    mulAddEquivOfIsUnit a ha x = a * x := by
  change (ha.unit : R) * x = a * x
  rw [IsUnit.unit_spec]

def coordinatewiseAddEquiv
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G) :
    (ι → G) ≃ (ι → G) where
  toFun x i := e i (x i)
  invFun x i := (e i).symm (x i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (e i).apply_symm_apply (x i)

@[simp]
theorem coordinatewiseAddEquiv_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    coordinatewiseAddEquiv e x i = e i (x i) :=
  rfl

@[simp]
theorem coordinatewiseAddEquiv_symm_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    (coordinatewiseAddEquiv e).symm x i =
      (e i).symm (x i) :=
  rfl

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (z - ∑ i, y i) y

@[simp]
theorem sumFiberTuple_zero {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    sumFiberTuple n z y 0 = z - ∑ i, y i :=
  rfl

@[simp]
theorem sumFiberTuple_succ {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) (i : Fin n) :
    sumFiberTuple n z y i.succ = y i :=
  rfl

@[simp]
theorem sum_sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    ∑ i, sumFiberTuple n z y i = z := by
  simp [sumFiberTuple, Fin.sum_univ_succ]

noncomputable def zeroFiberDelta
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) : ℝ := by
  classical
  exact if z = 0 then (Fintype.card G : ℝ) else 0

@[simp]
theorem zeroFiberDelta_zero
    {G : Type*} [Fintype G] [AddCommGroup G] :
    zeroFiberDelta (G := G) 0 = Fintype.card G := by
  classical
  simp [zeroFiberDelta]

@[simp]
theorem zeroFiberDelta_of_ne
    {G : Type*} [Fintype G] [AddCommGroup G]
    {z : G} (hz : z ≠ 0) :
    zeroFiberDelta z = 0 := by
  classical
  simp [zeroFiberDelta, hz]

noncomputable def fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (z : G) : ℝ := by
  cases r with
  | zero =>
      exact zeroFiberDelta z * w (fun i => Fin.elim0 i)
  | succ n =>
      exact mean fun y : Fin n → G => w (sumFiberTuple n z y)

@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl

@[simp]
theorem fiberConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    fiberConvolution (n + 1) w z =
      mean fun y : Fin n → G => w (sumFiberTuple n z y) :=
  rfl

def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]

@[simp]
theorem cutTestProduct_mul
    {G : Type*} {r : ℕ} (u v : CutTestFamily G r)
    (x : Fin r → G) :
    cutTestProduct (fun i y => u i y * v i y) x =
      cutTestProduct u x * cutTestProduct v x := by
  simp [cutTestProduct, Finset.prod_mul_distrib]

noncomputable def generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) (z : G) : ℝ :=
  fiberConvolution r (cutTestProduct u) z

@[simp]
theorem generalizedConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (u : CutTestFamily G 0) (z : G) :
    generalizedConvolution 0 u z = zeroFiberDelta z := by
  simp [generalizedConvolution, cutTestProduct]

@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl

theorem fiberConvolution_smul
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (c : ℝ) (w : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => c * w x) z =
      c * fiberConvolution r w z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero]
      ring
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ]
      exact mean_smul c (fun y : Fin n → G =>
        w (sumFiberTuple n z y))

@[simp]
theorem fiberConvolution_zero_weight
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (z : G) :
    fiberConvolution r (fun _ => (0 : ℝ)) z = 0 := by
  simpa using fiberConvolution_smul r 0 (fun _ => (1 : ℝ)) z

@[simp]
theorem fiberConvolution_const_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (c : ℝ) (z : G) :
    fiberConvolution (n + 1) (fun _ => c) z = c := by
  rw [fiberConvolution_succ]
  exact mean_const c

@[simp]
theorem generalizedConvolution_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by
  rw [generalizedConvolution_succ]
  calc
    mean (fun y : Fin n → G =>
        cutTestProduct
          (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ))
          (sumFiberTuple n z y)) =
        mean (fun _ : Fin n → G => (1 : ℝ)) := by
      apply congrArg mean
      funext y
      exact cutTestProduct_one (sumFiberTuple n z y)
    _ = 1 := mean_const 1

@[simp]
theorem generalizedConvolution_zero_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (0 : ℝ)) z = 0 := by
  rw [generalizedConvolution_succ]
  simp [cutTestProduct]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem apCoefficient_isUnit_of_coprime_factorial
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    IsUnit (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime]
  have hdiff :
      (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos :
      0 < Int.natAbs ((i : ℤ) - (j : ℤ)) :=
    Int.natAbs_pos.mpr hdiff
  have hle :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k - 1 := by
    have hi : (i : ℕ) ≤ k - 1 := by omega
    have hj : (j : ℕ) ≤ k - 1 := by omega
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have hdvd :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ∣
        Nat.factorial (k - 1) :=
    Nat.dvd_factorial hpos hle
  simpa using hN.coprime_dvd_right hdvd

noncomputable def apCoefficientAddEquiv
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    ZMod N ≃+ ZMod N :=
  mulAddEquivOfIsUnit
    ((((i : ℤ) - (j : ℤ) : ℤ) : ZMod N))
    (apCoefficient_isUnit_of_coprime_factorial hN i j hij)

@[simp]
theorem apCoefficientAddEquiv_apply
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) (x : ZMod N) :
    apCoefficientAddEquiv hN i j hij x =
      (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x := by
  simp [apCoefficientAddEquiv]

noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl

noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]

noncomputable def apFaceScalingEquiv
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) :
    ZMod N ≃+ ZMod N :=
  apCoefficientAddEquiv
    (by simpa using hN) (j.succAbove t) j
    (Fin.succAbove_ne j t)

@[simp]
theorem apFaceScalingEquiv_apply
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) (x : ZMod N) :
    apFaceScalingEquiv hN j t x =
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * x) := by
  simp [apFaceScalingEquiv]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0

abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩

def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CountExtraction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def cyclicAPMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cyclicAPProduct k N f a d

noncomputable def cyclicAPDiagonalMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cyclicAPProduct k N f a 0

noncomputable def cyclicAPOffDiagMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cyclicAPProduct k N f a d

@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

abbrev BooleanCutTest (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω

namespace BooleanCutTest

def eval (A : BooleanCutTest Ω) : Ω → ℝ :=
  finsetIndicator A

omit [Fintype Ω] in
@[simp]
theorem eval_of_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  finsetIndicator_of_mem hx

omit [Fintype Ω] in
@[simp]
theorem eval_of_not_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  finsetIndicator_of_not_mem hx

omit [Fintype Ω] in
theorem eval_sq (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_le_one (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

end BooleanCutTest

def IsPartitionMeasurable (P : FacePartition Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x

namespace IsPartitionMeasurable

theorem of_le {P Q : FacePartition Ω} {g : Ω → ℝ}
    (hPQ : P ≤ Q) (hg : IsPartitionMeasurable Q g) :
    IsPartitionMeasurable P g := by
  intro x y hy
  exact hg x y (FacePartition.part_subset_of_le hPQ x hy)

end IsPartitionMeasurable

theorem booleanCut_measurable_generatedBy (A : BooleanCutTest Ω) :
    IsPartitionMeasurable
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have hxy : x ∈ A ↔ y ∈ A := by
    have hsignature :=
      (FacePartition.mem_part_generatedBy_iff
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact hsignature A (by simp)
  by_cases hx : x ∈ A
  · have hyA : y ∈ A := hxy.mp hx
    simp [hx, hyA]
  · have hyA : y ∉ A := by
      intro hy
      exact hx (hxy.mpr hy)
    simp [hx, hyA]

structure FaceRegularityState (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : FacePartition Ω

namespace FaceRegularityState

noncomputable def structured (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  conditionalMean S.partition f

noncomputable def residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x

noncomputable def energy (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : ℝ :=
  partitionEnergy S.partition f

noncomputable def booleanCutCorrelation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x

def refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) : FaceRegularityState Ω where
  partition :=
    FacePartition.join S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω)))

@[simp]
theorem partition_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy ({A} : Finset (Finset Ω))) :=
  rfl

theorem refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition ≤ S.partition :=
  FacePartition.join_le_left _ _

theorem booleanCut_measurable_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    IsPartitionMeasurable (S.refineBy A).partition A.eval := by
  apply IsPartitionMeasurable.of_le
    (FacePartition.join_le_right S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))))
  exact booleanCut_measurable_generatedBy A

@[simp]
theorem conditionalMean_residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean S.partition (S.residual f) x = 0 := by
  change
    conditionalMean S.partition
      (fun y => f y - conditionalMean S.partition f y) x = 0
  rw [conditionalMean_sub]
  rw [conditionalMean_idem]
  ring

@[simp]
theorem mean_residual (S : FaceRegularityState Ω) (f : Ω → ℝ) :
    mean (S.residual f) = 0 := by
  change
    mean (fun x => f x - conditionalMean S.partition f x) = 0
  rw [mean_sub]
  rw [mean_conditionalMean]
  ring

theorem conditionalMean_residual_refineBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) (x : Ω) :
    conditionalMean (S.refineBy A).partition (S.residual f) x =
      (S.refineBy A).structured f x - S.structured f x := by
  change
    conditionalMean (S.refineBy A).partition
        (fun y => f y - conditionalMean S.partition f y) x =
      conditionalMean (S.refineBy A).partition f x -
        conditionalMean S.partition f x
  rw [conditionalMean_sub]
  rw [conditionalMean_reverse_tower_of_le
    (S.refineBy A).partition S.partition (S.refineBy_le A)]

theorem mean_mul_eq_mean_conditionalMean_mul
    (P : FacePartition Ω) (u v : Ω → ℝ)
    (hv : IsPartitionMeasurable P v) :
    mean (fun x => u x * v x) =
      mean (fun x => conditionalMean P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (conditionalMean P (fun x => u x * v x)) :=
      (mean_conditionalMean P _).symm
    _ = mean (fun x => conditionalMean P u x * v x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_right_of_constant_on_part
        P u v x (hv x)

theorem booleanCutCorrelation_eq_projection
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [booleanCutCorrelation]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          conditionalMean (S.refineBy A).partition (S.residual f) x *
            A.eval x) :=
      mean_mul_eq_mean_conditionalMean_mul
        (S.refineBy A).partition (S.residual f) A.eval
        (S.booleanCut_measurable_refineBy A)
    _ = mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.conditionalMean_residual_refineBy f A x]

omit [DecidableEq Ω] in

theorem mean_mul_sq_le_sq_mul_sq (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

theorem mean_booleanCut_sq_le_one [Nonempty Ω]
    (A : BooleanCutTest Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  rw [A.eval_sq x]
  exact A.eval_le_one x

theorem energy_refineBy_sub_eq_mean_sq
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).energy f - S.energy f =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      (S.refineBy A).partition S.partition (S.refineBy_le A) f

theorem booleanCutCorrelation_sq_le_energyIncrement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A ^ 2 ≤
      (S.refineBy A).energy f - S.energy f := by
  rw [S.booleanCutCorrelation_eq_projection f A]
  let d : Ω → ℝ :=
    fun x => (S.refineBy A).structured f x - S.structured f x
  have hcs :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    mean_mul_sq_le_sq_mul_sq d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hA := mean_booleanCut_sq_le_one A
  calc
    mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := hcs
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.refineBy A).energy f - S.energy f := by
      exact (S.energy_refineBy_sub_eq_mean_sq f A).symm

theorem energy_increment_of_booleanCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcorrelation : ε ≤ |S.booleanCutCorrelation f A|) :
    S.energy f + ε ^ 2 ≤ (S.refineBy A).energy f := by
  have hsquare :
      ε ^ 2 ≤ S.booleanCutCorrelation f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hcorrelation
  have hincrement :=
    S.booleanCutCorrelation_sq_le_energyIncrement f A
  linarith

def IsRegularAgainst (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    (ε : ℝ) : Prop :=
  ∀ A ∈ cuts, |S.booleanCutCorrelation f A| ≤ ε

theorem exists_booleanCut_of_not_regular
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬ S.IsRegularAgainst f cuts ε) :
    ∃ A ∈ cuts, ε < |S.booleanCutCorrelation f A| := by
  classical
  by_contra hnone
  apply h
  intro A hA
  by_contra hle
  apply hnone
  exact ⟨A, hA, lt_of_not_ge hle⟩

noncomputable def chosenIrregularCut
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsRegularAgainst f cuts ε then ∅
    else
      Classical.choose
        (S.exists_booleanCut_of_not_regular f cuts h)

noncomputable def regularityRun
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := regularityRun S f cuts ε n
      T.refineBy (T.chosenIrregularCut f cuts ε)

@[simp]
theorem regularityRun_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem regularityRun_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRun f cuts ε (n + 1) =
      (S.regularityRun f cuts ε n).refineBy
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε) :=
  rfl

noncomputable def regularityRunCuts
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.regularityRun f cuts ε i).chosenIrregularCut
      f cuts ε

@[simp]
theorem regularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRunCuts f cuts ε 0 = ∅ := by
  simp [regularityRunCuts]

@[simp]
theorem regularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
        (S.regularityRunCuts f cuts ε n) := by
  classical
  simp [regularityRunCuts, Finset.range_add_one]

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true

@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]

noncomputable def booleanFaceCutSupports
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ) :
    Finset (BooleanCutTest (Fin r → G)) := by
  classical
  exact Finset.univ.image booleanFaceCutSupport

namespace FaceRegularityState

noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x

def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def representingBooleanFaceCutAssignment
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ)
    (A : BooleanCutTest (Fin r → G)) :
    BooleanCutAssignment G r := by
  classical
  exact
    if hA : A ∈ booleanFaceCutSupports G r then
      Classical.choose
        (show ∃ b : BooleanCutAssignment G r,
            booleanFaceCutSupport b = A by
          obtain ⟨b, _hb, hsupport⟩ :=
            Finset.mem_image.mp hA
          exact ⟨b, hsupport⟩)
    else
      fun _ => false

abbrev GeneratorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :=
  F → Fin r

@[simp]
theorem card_generatorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :
    Fintype.card (GeneratorBranch F) = r ^ F.card := by
  simp [GeneratorBranch]

noncomputable def lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r) :
    BooleanCutTest (Fin (r - 1) → G) := by
  classical
  exact Finset.univ.filter fun z =>
    ∀ A : F,
      (y ∈ A.1 →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = true) ∧
      (y ∉ A.1 → w A = i →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = false)

@[simp]
theorem mem_lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r)
    (z : Fin (r - 1) → G) :
    z ∈ lowerGeneratorCell F y w i ↔
      ∀ A : F,
        (y ∈ A.1 →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = true) ∧
        (y ∉ A.1 → w A = i →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = false) := by
  simp [lowerGeneratorCell]

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPattern
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedFace (k r : ℕ) :=
  Fin r ↪o Fin k

instance orderedFaceDecidableEq
    (k r : ℕ) : DecidableEq (OrderedFace k r) :=
  Function.Injective.decidableEq
    (f := fun e : OrderedFace k r => (e : Fin r → Fin k))
    DFunLike.coe_injective

def orderedFaceTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)

abbrev OrderedFaceComplement
    {k r : ℕ} (e : OrderedFace k r) :=
  {v : Fin k // v ∉ Set.range e}

noncomputable def orderedFaceSumEquiv
    {k r : ℕ} (e : OrderedFace k r) :
    Fin r ⊕ OrderedFaceComplement e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (OrderedFaceComplement e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))

noncomputable def splitOrderedFaceEquiv
    {G : Type*} {k r : ℕ} (e : OrderedFace k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (OrderedFaceComplement e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (orderedFaceSumEquiv e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ OrderedFaceComplement e => G))

@[simp]
theorem splitOrderedFaceEquiv_fst
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).1 =
      orderedFaceTuple e x := by
  funext i
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceTuple]
  rfl

def orderedFaceComplementTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    OrderedFaceComplement e → G :=
  fun v => x v.1

@[simp]
theorem splitOrderedFaceEquiv_snd
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).2 =
      orderedFaceComplementTuple e x := by
  funext v
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceComplementTuple]

@[simp]
theorem orderedFaceTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = y := by
  rw [← splitOrderedFaceEquiv_fst]
  simp

@[simp]
theorem orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceComplementTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = z := by
  rw [← splitOrderedFaceEquiv_snd]
  simp

structure WeightedOrderedPattern
    (G : Type*) (k r : ℕ) where
  edgeWeight : OrderedFace k r → (Fin r → G) → ℝ

namespace WeightedOrderedPattern

noncomputable def patternWeight
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : OrderedFace k r,
    H.edgeWeight e (orderedFaceTuple e x)

noncomputable def patternCount
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : ℝ :=
  mean H.patternWeight

end WeightedOrderedPattern

structure OrderedPattern
    (G : Type*) (k r : ℕ) where
  edge : OrderedFace k r → (Fin r → G) → Prop

namespace OrderedPattern

def IsOccurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (orderedFaceTuple e x)

noncomputable def occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.IsOccurrence

@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

noncomputable def toWeighted
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    WeightedOrderedPattern G k r := by
  classical
  exact
    { edgeWeight := fun e y =>
        if H.edge e y then 1 else 0 }

abbrev DeletionFamily
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : OrderedFace k r) → Finset (Fin r → G)

def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (D : DeletionFamily (G := G) k r) : Prop :=
  ∀ x, x ∈ H.occurrenceFinset →
    ∃ e, orderedFaceTuple e x ∈ D e

noncomputable def faceDeletionDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k r)
    (e : OrderedFace k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)

def emptyDeletion
    {G : Type*} [DecidableEq G] (k r : ℕ) :
    DeletionFamily (G := G) k r :=
  fun _ => ∅

@[simp]
theorem faceDeletionDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (e : OrderedFace k r) :
    faceDeletionDensity
        (emptyDeletion (G := G) k r) e = 0 := by
  simp [faceDeletionDensity, emptyDeletion]

end OrderedPattern

def HasUniformOrderedPatternRemoval (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedCounting
namespace OAI

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

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :=
  (e : OrderedFace k r) →
    FaceRegularityState (Fin r → G)

noncomputable def regularizedOrderedPattern
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    WeightedOrderedPattern G k r where
  edgeWeight e :=
    (S e).structured (H.edgeWeight e)

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)

noncomputable def deleteEdges {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    SimplexHypergraph V := by
  classical
  exact
    { edge := fun j x => H.edge j x ∧ x ∉ deleted j }

@[simp]
theorem deleteEdges_edge {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) (x : DeletedVector V j) :
    (H.deleteEdges deleted).edge j x ↔
      H.edge j x ∧ x ∉ deleted j := by
  classical
  simp [deleteEdges]

@[simp]
theorem mem_deleteEdges_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (x : (i : Fin k) → V i) :
    x ∈ (H.deleteEdges deleted).simplexFinset ↔
      x ∈ H.simplexFinset ∧
        ∀ j, deleteCoordinate x j ∉ deleted j := by
  classical
  simp only [mem_simplexFinset, deleteEdges_edge, forall_and]

def emptyDeletion {k : ℕ} (V : Fin k → Type*) :
    DeletionFamily V :=
  fun _ => ∅

@[simp]
theorem mem_emptyDeletion {k : ℕ} {V : Fin k → Type*}
    (j : Fin k) (x : DeletedVector V j) :
    x ∉ emptyDeletion V j := by
  simp [emptyDeletion]

@[simp]
theorem deleteEdges_empty_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    (H.deleteEdges (emptyDeletion V)).simplexFinset =
      H.simplexFinset := by
  classical
  ext x
  simp

def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card

@[simp]
theorem deletionCount_empty {k : ℕ} (V : Fin k → Type*) :
    deletionCount (emptyDeletion V) = 0 := by
  simp [deletionCount, emptyDeletion]

def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)

@[simp]
theorem card_deletedVector_fin (k n : ℕ) (j : Fin k) :
    Fintype.card
        (DeletedVector (fun _ : Fin k => Fin n) j) =
      n ^ (k - 1) := by
  simp [DeletedVector, Fintype.card_pi]

@[simp]
theorem deletionCapacity_fin (k n : ℕ) :
    deletionCapacity (fun _ : Fin k => Fin n) =
      k * n ^ (k - 1) := by
  simp [deletionCapacity]

noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)

@[simp]
theorem colorDeletionDensity_fin {k n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin k => Fin n))
    (j : Fin k) :
    colorDeletionDensity deleted j =
      ((deleted j).card : ℝ) / (n ^ (k - 1) : ℕ) := by
  simp [colorDeletionDensity]

noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)

@[simp]
theorem normalizedDeletionCost_empty {k : ℕ}
    (V : Fin k → Type*) [∀ i, Fintype (V i)] :
    normalizedDeletionCost (emptyDeletion V) = 0 := by
  simp [normalizedDeletionCost]

end SimplexHypergraph

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def apSetHypergraph (k N : ℕ) (A : Finset (ZMod N)) :
    SimplexHypergraph (fun _ : Fin k => ZMod N) where
  edge j x := apSimplexForm k N j x ∈ A

@[simp]
theorem apSetHypergraph_edge
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).edge j x ↔
      apSimplexForm k N j x ∈ A :=
  Iff.rfl

@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

abbrev DiagonalAPParameter
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)

def diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) → ZMod N :=
  simplexCoordinatesOfAP r N p.1.1 0 p.2

@[simp]
theorem simplexCoordinateSum_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateSum (r + 2) N
      (diagonalAPSimplex r N A p) = 0 := by
  simp [diagonalAPSimplex]

@[simp]
theorem simplexCoordinateMoment_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateMoment (r + 2) N
      (diagonalAPSimplex r N A p) = p.1.1 := by
  simp [diagonalAPSimplex]

@[simp]
theorem apSimplexForm_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A)
    (j : Fin (r + 2)) :
    apSimplexForm (r + 2) N j
        (deleteCoordinate (diagonalAPSimplex r N A p) j) =
      p.1.1 := by
  rw [apSimplexForm_deleteCoordinate,
    simplexCoordinateMoment_diagonalAPSimplex,
    simplexCoordinateSum_diagonalAPSimplex]
  simp

theorem diagonalAPSimplex_mem_simplexFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    diagonalAPSimplex r N A p ∈
      (apSetHypergraph (r + 2) N A).simplexFinset := by
  let : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [SimplexHypergraph.mem_simplexFinset]
  intro j
  rw [apSetHypergraph_edge,
    apSimplexForm_diagonalAPSimplex]
  exact p.1.2

noncomputable def deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedVectorToFinTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

namespace SimplexHypergraph

noncomputable def deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (deleted j).image fun x =>
      (j, deletedVectorToFinTuple j x)

end SimplexHypergraph

noncomputable def diagonalCoverColor
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) :=
  Classical.choose
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

noncomputable def diagonalCoveredSlot
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := diagonalCoverColor r N A deleted hcover p
  (j, deletedVectorToFinTuple j
    (deleteCoordinate (diagonalAPSimplex r N A p) j))

@[simp]
theorem card_diagonalAPParameter
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    Fintype.card (DiagonalAPParameter r N A) =
      A.card * N ^ r := by
  simp [DiagonalAPParameter, ZMod.card]

@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]

def HasUniformCyclicPartiteSimplexRemoval (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            SimplexHypergraph (fun _ : Fin k => ZMod N),
          H.toWeighted.simplexCount < c →
            ∃ deleted :
                SimplexHypergraph.DeletionFamily
                  (fun _ : Fin k => ZMod N),
              H.IsSimplexCover deleted ∧
                SimplexHypergraph.normalizedDeletionCost
                    deleted ≤ ε

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)

@[simp]
theorem orderedFacetEquiv_apply
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp

@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl

@[simp]
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr

noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)

@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]

noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)

@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩

@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.StructuredCleaning
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace FaceRegularityState

noncomputable def lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ) :
    Finset Ω := by
  classical
  exact Finset.univ.filter fun x =>
    f x = 1 ∧ S.structured f x < τ

@[simp]
theorem mem_lowStructuredOneFinset
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ) (τ : ℝ)
    (x : Ω) :
    x ∈ S.lowStructuredOneFinset f τ ↔
      f x = 1 ∧ S.structured f x < τ := by
  simp [lowStructuredOneFinset]

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemovalAssembly
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1

namespace StrongOrderedComplexRegularityCertificate

end StrongOrderedComplexRegularityCertificate

namespace StrongOrderedComplexRegularityCertificate

end StrongOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

structure NatGrowthFunction where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  above_diagonal : ∀ n, n + 1 ≤ toFun n

namespace NatGrowthFunction

instance : CoeFun NatGrowthFunction (fun _ => ℕ → ℕ) :=
  ⟨NatGrowthFunction.toFun⟩

theorem monotone (F : NatGrowthFunction) :
    Monotone F :=
  F.monotone'

theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)

theorem one_le (F : NatGrowthFunction) (n : ℕ) :
    1 ≤ F n :=
  F.positive n

end NatGrowthFunction

noncomputable def growthRegularityStepTolerance
    (F : NatGrowthFunction) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)

noncomputable def growthRegularityStepBudget
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  orderedRemovalRegularityBudget
    k j (growthRegularityStepTolerance F M)

noncomputable def growthRegularityComplexity
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ
  | 0 => initialBound
  | n + 1 =>
      (2 ^ (j + 1)) ^
          growthRegularityStepBudget
            k j F
              (growthRegularityComplexity
                k j initialBound F n) *
        growthRegularityComplexity
          k j initialBound F n

noncomputable def growthRegularityTolerance
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℝ :=
  fun n =>
    growthRegularityStepTolerance F
      (growthRegularityComplexity
        k j initialBound F n)

noncomputable def growthRegularityBudget
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    ℕ → ℕ :=
  fun n =>
    growthRegularityStepBudget k j F
      (growthRegularityComplexity
        k j initialBound F n)

@[simp]
theorem growthRegularityComplexity_zero
    (k j initialBound : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
      k j initialBound F 0 = initialBound :=
  rfl

@[simp]
theorem growthRegularityComplexity_succ
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      (2 ^ (j + 1)) ^
          growthRegularityBudget
            k j initialBound F n *
        growthRegularityComplexity
          k j initialBound F n :=
  rfl

@[simp]
theorem growthRegularityTolerance_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityTolerance
        k j initialBound F n =
      1 /
        (F (growthRegularityComplexity
          k j initialBound F n) : ℝ) :=
  rfl

@[simp]
theorem growthRegularityBudget_eq
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityBudget
        k j initialBound F n =
      Nat.ceil
          ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
            (growthRegularityTolerance
              k j initialBound F n) ^ 2) +
        1 :=
  rfl

noncomputable def growthRegularityLength
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (OrderedFace k (j + 1)) : ℝ) / γ) +
    1

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedRemovalSchedule

end OrderedRemovalSchedule

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BinaryWordSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def binaryWordSupport {n : ℕ} (v : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i = 1)

def binaryWordSupportEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun := binaryWordSupport
  invFun S i := if i ∈ S then 1 else 0
  left_inv v := by
    funext i
    by_cases h : v i = 1
    · simp [binaryWordSupport, h]
    · simpa only [binaryWordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        if_neg h] using (binary_eq_zero_of_ne_one (v i) h).symm
  right_inv S := by
    ext i
    simp [binaryWordSupport]

theorem binaryWordSupport_card {n : ℕ} (v : Fin n → Fin 2) :
    (binaryWordSupport v).card = ∑ i, (v i).val := by
  rw [binaryWordSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = 1
  · simp [h]
  · rw [if_neg h, binary_eq_zero_of_ne_one (v i) h]
    rfl

theorem binaryWordSupport_zero (n : ℕ) :
    binaryWordSupport (fun _ : Fin n => 0) = ∅ := by
  ext i
  simp [binaryWordSupport]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelSupportContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def productKernelApply (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

noncomputable def anovaKernelMatrix (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (i : ι) (x : X i) (y : Y i) : ℝ :=
  if i ∈ S then centeredKernelMatrix (ν i) (K i) x y else (ν i).weight y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))

include hC hbound

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVASectionEnergy (T : Finset I) (D : Finset (Finset I))
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ (T ∪ U) f (productCoordinateMix T z x) ^ 2)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def disjointCoordinateLevel (T : Finset I) (d : ℕ) : Finset (Finset I) :=
  (Finset.univ.powersetCard d).filter (fun U => Disjoint T U)

noncomputable def productANOVASectionTensor (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) : (Fin d → Sigma X) → ℝ :=
  orderedFamilyTensor d base (fun U x =>
    if Disjoint T U then productANOVA μ (T ∪ U) f (productCoordinateMix T z x) else 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateLeafCount
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem trace_eq_of_agree (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i)
    (hagree : ∀ i ∈ (trace tree I base input).1, other i = input i) :
    trace tree I base other = trace tree I base input := by
  induction tree generalizing I base with
  | leaf => rfl
  | split i children ih =>
    have hi : i ∈ (trace (children (input i)) (insert i I) (Function.update base i (input i)) input).1 :=
      trace_contains _ _ _ _ (Finset.mem_insert_self _ _)
    have he : other i = input i := hagree i hi
    simp only [trace, he]
    exact ih (input i) (insert i I) (Function.update base i (input i)) hagree

def traceCylinder (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) : ProductCylinder Value :=
  ProductCylinder.ofAssignment (trace tree I base input).1 (trace tree I base input).2

theorem traceCylinder_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains input := by
  intro i
  exact (trace_agrees tree I base input (fun j hj => (hinput j hj).symm) i i.property).symm

theorem traceCylinder_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains other ↔
      (∀ i ∈ I, other i = base i) ∧ traceCylinder tree I base other = traceCylinder tree I base input := by
  have htrace := trace_agrees tree I base input (fun i hi => (hinput i hi).symm)
  constructor
  · intro h
    have hagree : ∀ i ∈ (trace tree I base input).1, other i = input i := by
      intro i hi
      exact (h ⟨i, hi⟩).trans (htrace i hi)
    have heq := trace_eq_of_agree tree I base input other hagree
    refine ⟨fun i hi => (hagree i (trace_contains tree I base input hi)).trans (hinput i hi), ?_⟩
    unfold traceCylinder
    rw [heq]
  · rintro ⟨hother, heq⟩
    rw [← heq]
    exact traceCylinder_contains tree I base other hother

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Value : ι → Type*}
  [∀ i, Fintype (Value i)]

noncomputable def leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) : Finset (ProductCylinder Value) :=
  (Finset.univ.filter (fun input : ∀ i, Value i => ∀ i ∈ I, input i = base i)).image
    (traceCylinder tree I base)

theorem mem_leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (c : ProductCylinder Value) :
    c ∈ leafCylinders tree I base ↔
      ∃ input, (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  simp only [leafCylinders, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem leafCylinders_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
    c.Contains input ↔ (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  obtain ⟨source, hs, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  exact traceCylinder_contains_iff tree I base source input hs

theorem leafCylinders_indicator_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree I base, productFiberIndicator c.1 (c.assignment base) input) =
      productFiberIndicator I base input := by
  have he (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
      productFiberIndicator c.1 (c.assignment base) input =
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then 1 else 0 := by
    simp only [productFiberIndicator, ← ProductCylinder.contains_iff,
      leafCylinders_contains_iff tree I base input c hc]
  calc
    _ = ∑ c ∈ leafCylinders tree I base,
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl he
    _ = _ := by
      by_cases hi : ∀ i ∈ I, input i = base i
      · have hc : traceCylinder tree I base input ∈ leafCylinders tree I base :=
          (mem_leafCylinders tree I base _).mpr ⟨input, hi, rfl⟩
        have hvalue : productFiberIndicator I base input = 1 := by
          unfold productFiberIndicator
          exact if_pos hi
        rw [hvalue, Finset.sum_eq_single (traceCylinder tree I base input)]
        · exact if_pos ⟨hi, rfl⟩
        · intro c _ hne
          exact if_neg (fun h => hne h.2.symm)
        · exact fun hn => False.elim (hn hc)
      · have hvalue : productFiberIndicator I base input = 0 := by
          unfold productFiberIndicator
          exact if_neg hi
        rw [hvalue]
        apply Finset.sum_eq_zero
        intro c _
        exact if_neg (fun h => hi h.1)

theorem leafCylinders_mass_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (w : (∀ i, Value i) → ℝ) :
    (∑ c ∈ leafCylinders tree I base, productFiberMass w c.1 (c.assignment base)) =
      productFiberMass w I base := by
  unfold productFiberMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, leafCylinders_indicator_sum]

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
  [∀ i, Fintype (Y i)]
  {Good : Finset ι → (∀ i, Y i) → Prop}
  {tree : CoordinateDecisionTree ι Y} {I : Finset ι} {base : ∀ i, Y i} {d : ℕ}

noncomputable def leafSourceAssignments (X : ι → Type*) [∀ i, Fintype (X i)]
    (tree : CoordinateDecisionTree ι Y) (I : Finset ι) (base : ∀ i, Y i) :
    Finset (Σ c : ProductCylinder Y, ∀ i : c.1, X i.val) :=
  (leafCylinders tree I base).sigma (fun _c => Finset.univ)

end Erdos3.CoordinateDecisionTree

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def normalizedCoordinateCutoff (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) : (D → ℝ) → ℝ :=
  Classical.choose (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I : Type*} [Fintype I]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexedAffineSource {I : Type*} {N : ℕ} (e : I ≃ Fin N)
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (a : I → ℝ) : I → ℝ :=
  (b + L (a ∘ e.symm)) ∘ e

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

noncomputable def affineCubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ δ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N)
    (cubeMinorProbabilityScale O N d c₀) η

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

noncomputable def affineBooleanCubeDeterminant
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (x : (B × Fin h) → Option α → ℝ) : ℝ :=
  booleanMinorDeterminant c sets block v sel (b + L (blockCubeFlatten B (Fin h) α x))

noncomputable def affineBooleanCubeGoodWeight
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ) :
    (BlockParameter B (Fin h) α → ℝ) → ℝ :=
  blockCubeWeight (scalarCubeGoodWeight α ψ r κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b))

noncomputable def affineBooleanCubeCutoff
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)
    (a : BlockParameter B (Fin h) α → ℝ) : ℝ :=
  goodDomainCutoff ψ κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b)
    (scalarCubeProductCutoff α r) ((blockCubeFlatten B (Fin h) α).symm a)

variable (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
  (v : Fin h) (sel : J → O → Option α)
  (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
  (b : BlockParameter B (Fin h) α → ℝ)
  (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

noncomputable def jointAffineBooleanGoodWeight : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

noncomputable def jointAffineBooleanCutoff : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

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

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanTranslationBudget
    (C : D → ℝ) (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ)
    (κ : D → ℝ) (K H : ℝ≥0) : ℝ≥0 :=
  (Fintype.card (Σ d, O d) : ℝ≥0) *
    (K * Real.toNNReal (jointBooleanWeightBudget (O := O) (α := α) h C A T r κ) +
      (Fintype.card (JointBlockParameter B h α) : ℝ≥0) * (K ^ 2 * H))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def canonicalAffineCubeMinorThreshold (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) (c₀ δ η : ℝ) : ℝ :=
  affineCubeMinorThreshold Unit O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ δ η

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineBooleanInverseBudget (h : D → ℕ) (C κ : D → ℝ) (δ : ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (δ⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
    (h d) (C d) 1 (κ d))

noncomputable def jointAffineBooleanErrorBudget (h : D → ℕ) (C κ : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (δ : ℝ) : ℝ :=
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  1 + 2 * (K : ℝ) * jointBooleanWeightBudget (O := O) (α := α) h C A T r κ +
    (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H : ℝ) + 1))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanTolerance
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointAffineSourceBoundaryRadius (h : D → ℕ) (E : ℝ)
    (d : D) (_ : B d × Fin (h d)) : ℝ :=
  scalarCubeProductBoundaryRadius (B d × Fin (h d)) α
    ((E / (12 * ((Fintype.card D : ℝ) + 1))) / 2)

noncomputable def jointAffineSourceMinorThreshold (h : D → ℕ) (c₀ : D → ℝ) (δ E : ℝ)
    (d : D) : ℝ :=
  canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ
    (E / (12 * ((Fintype.card D : ℝ) + 1)))

noncomputable def jointAffineSourceRadius (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  min 1 (E / (3 * (1 + (L : ℝ))))

noncomputable def jointAffineSourceTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  polynomialPerturbationScale K 1 Q (E / 3) (Fintype.card (Σ d, O d))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def coefficientCRTEquiv {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (J → ZMod (∏ l, q l)) ≃+ (∀ l, J → ZMod (q l)) where
  toFun x l j := ZMod.prodEquivPi q hq (x j) l
  invFun y j := (ZMod.prodEquivPi q hq).symm (fun l => y l j)
  left_inv x := by funext j; exact (ZMod.prodEquivPi q hq).symm_apply_apply (x j)
  right_inv y := by
    funext l j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l j)) l
  map_add' x y := by
    funext l j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x j) (y j)) l

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
open FiniteProbabilityWeights

noncomputable def smoothCoefficientResidueWeights (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M] :
    FiniteProbabilityWeights (ZMod M) :=
  ofPMF ((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

def smoothResiduePrimeBad {J : Type*} (P : Finset ℕ)
    (E : ∀ p : P, ∀ a : ℕ, (J → ZMod (p.val ^ a)) → Prop)
    (p a : ℕ) (x : J → ℤ) : Prop :=
  ∃ hp : p ∈ P, E ⟨p, hp⟩ a (fun j => (x j : ZMod (p ^ a)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BufferedCoordinateProjection
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]
variable (r : ℝ≥0) (hr : 0 < r) (f : (D → ℝ) → ℂ)

noncomputable def bufferedCoordinateProjection (z : D → ℝ) : ℂ :=
  (normalizedCoordinateCutoff D r hr z : ℂ) * f (coordinateZeroProjection P z)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteDescendingRankOrder
namespace OAI

section

namespace Erdos3

theorem exists_finite_descending_rank_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, ∀ i j, i ≤ j → rank (e j) ≤ rank (e i) := by
  classical
  let key : I → OrderDual ℕ ×ₗ Fin (Fintype.card I) :=
    fun i => toLex (rank i, Fintype.equivFin I i)
  have hkey : Function.Injective key := by
    intro i j hij
    apply (Fintype.equivFin I).injective
    exact congrArg (fun z => (ofLex z).2) hij
  let _ : LinearOrder I := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have hle : key (e i) ≤ key (e j) := e.monotone hij
  exact Prod.Lex.monotone_fst _ _ hle

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointAffinePolynomialSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z : Type*} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffinePolynomialTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Cp δ E : ℝ) : ℝ :=
  jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ E /
    (1 + polynomialC2BoxBudget
      (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentCombinatorics
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I R : Type*} [DecidableEq I] [CommSemiring R]

noncomputable def squarefreePermanent :
    (n : ℕ) → Finset I → (Fin n → I → R) → R
  | 0, S, _ => if S = ∅ then 1 else 0
  | n + 1, S, u => ∑ j ∈ S, u 0 j * squarefreePermanent n (S.erase j) (Fin.tail u)

noncomputable def squarefreeEmbeddingHeadEquiv (n : ℕ) (S : Finset I) :
    (Fin (n + 1) ↪ S) ≃ Σ j : S, Fin n ↪ (S.erase j.val) where
  toFun f := ⟨f 0, ⟨fun i => ⟨(f i.succ).val,
    Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero i (f.injective (Subtype.ext h)),
      (f i.succ).property⟩⟩,
    fun i j h => Fin.succ_injective _ (f.injective (Subtype.ext (congrArg (fun z : S.erase (f 0).val => z.val) h)))⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun i => ⟨(p.2 i).val, (Finset.mem_erase.mp (p.2 i).property).2⟩), by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact False.elim ((Finset.mem_erase.mp (p.2 j).property).1 (congrArg Subtype.val h).symm)
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact False.elim ((Finset.mem_erase.mp (p.2 i).property).1 (congrArg Subtype.val h))
      | succ j => exact congrArg Fin.succ (p.2.injective (Subtype.ext (congrArg (fun z : S => z.val) h)))⟩
  left_inv f := by
    ext i
    cases i using Fin.cases <;> rfl
  right_inv p := by
    cases p with
    | mk j f =>
      congr 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped Matrix NNReal BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X]
variable (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

noncomputable def canonicalSpatialKernelMap
    (p : (UnselectedColumn s → ℝ) × ((Unit ⊕ I) → ℝ)) : (Unit ⊕ I) → ℝ :=
  normalizedIntegerPivot (selectedSpatialPivot root D s)
      (anisotropicSpatialScale I (1 + W) 1) (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.2 +
    normalizedIntegerColumns (selectedSpatialFreeColumns root D s) (fun _ => 1)
      (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.1

variable [IsEmpty I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalZeroSpatialInputLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

noncomputable def canonicalZeroSpatialInputMap
    (u : Option Zsp × X → ℝ) (a : Σ _ : X, Unit ⊕ Empty) : ℝ :=
  canonicalSpatialKernelMap s root D (W := W) (L := L)
    ((fun j => u (some j.val, a.1)),
      (fun i => match i with | .inl _ => u (none, a.1) | .inr e => Empty.elim e)) a.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedSelectedCoefficientProbability
namespace OAI

section

namespace Erdos3
open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem supportedPMF_event_eq_map_true {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (bad : X → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => bad x.val) =
      ((p.map (fun x => decide (bad x))) true).toReal := by
  have h := ofSupportedPMF_map_event p T hT (fun x => decide (bad x)) (fun b : Bool => b = true)
  simpa [eventProbability, mean] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ)
  (hq : 0 < q)
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped NNReal

def slicedGridSiteLog {A : Type*} [Semiring A]
    (n d ta ti : ℕ) (D p E : A) : A :=
  positiveRetainedComplexityLog n d ta p p p E +
  uniformSpectrumCardLog n d ti p p p E + uniformRetainedFrequencyLog n d ti p p p E +
  uniformRetainedDenominatorLog n d ti p p p E +
  positiveSpectrumCardLog n d ta p p p 0 + uniformSpectrumSizeLog n d ti p p p +
  (D + 2) * p + E + 2 * D + 20

theorem slicedGridSiteLog_bounds (n d ta ti : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := slicedGridSiteLog n d ta ti D p E
    0 ≤ Q ∧ p ≤ Q ∧ E ≤ Q ∧
      positiveRetainedComplexityLog n d ta p p p E + 2 * D + 13 ≤ Q ∧
      uniformSpectrumCardLog n d ti p p p E ≤ Q ∧
      uniformRetainedFrequencyLog n d ti p p p E + 2 * D + 13 ≤ Q ∧
      uniformRetainedDenominatorLog n d ti p p p E ≤ Q ∧
      positiveSpectrumCardLog n d ta p p p 0 + 2 + E ≤ Q ∧
      uniformSpectrumSizeLog n d ti p p p + 2 + E ≤ Q ∧
      D * p ≤ Q ∧ 2 * D + (D + 2) * p + 1 ≤ Q := by
  have ha := (positiveRetainedComplexityLog_bounds n d ta hp hp hp hE).1
  obtain ⟨_, hc, hf, ht⟩ := uniformRetainedLogs_nonneg n d ti hp hp hp hE
  have hca := (positiveRetainedLogs_nonneg n d ta hp hp hp (le_refl (0 : ℝ))).2.1
  have hci := (uniformSpectrumLogs_nonneg n d ti hp hp hp).2.2
  have hDp := mul_nonneg hD hp
  dsimp only
  unfold slicedGridSiteLog
  constructor; · positivity
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor <;> nlinarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
variable (α : Type*) [Fintype α] (d T : ℕ)
local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ)
  (hq : 0 < q)
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ)
  (hq : 0 < q)
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ)
  (hq : 0 < q)
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (q : ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end


