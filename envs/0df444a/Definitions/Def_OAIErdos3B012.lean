-- Prove2me | Definitions.Def_OAIErdos3B012
-- name    : OAIErdos3B012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:58:15.52788+00:00
-- url     : https://prove2.me/theorems/7d4f9d7d-9902-4d4d-a348-30878e4ef3a1
-- title:
--   OpenAI Erdős-3 split, definitions bundle 13 of 88
-- statement:
--   Definitions bundle 13 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B011`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 13 available.
--
--   Modules: `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.abs_det_normalizedBasis`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.divideCoordinates`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.divideCoordinates_apply`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.divideCoordinates_mem_span_iff`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.divideCoordinates_symm_apply`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.mem_realBox_mul_iff`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.normalizedBasis`, `OAI.Erdos3.BohrLattice.MinkowskiDiagonalNormalization.normalizedBasis_apply`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.abs_apply_le_norm`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.abs_det_eq_abs_pivot_mul_abs_det_projectedTail`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.abs_det_zspan_basis_eq`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.abs_sub_roundedCoefficient_le_half`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.cube_has_successiveProductCertificate`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjection`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjectionLinear`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjectionLinear_apply`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjection_add_smul`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjection_rawTailLift`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.deleteProjection_self`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.exists_abs_apply_eq_norm`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.exists_shortest_nonzero_of_basis`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.intCastVec`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.intCastVec_add`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.intCastVec_smul`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.intCastVec_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.matrixBasis`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.matrixBasis_apply`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mem_realBox_const_iff_norm_le`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_nonneg`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_one`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_succ`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mul_tailShear_apply_succ`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mul_tailShear_apply_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mul_tailShear_minor`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mul_tailShear_pivot_succ`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.projectedTail`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.projectedTailBasis`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.projectedTailBasis_apply`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.projectedTail_det_ne_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.rawTailLift`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.realBox_has_minkowskiSecondCertificate`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.realBox_smul_one_eq_const`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.reducedLift_apply_le`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.roundedCoefficient`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear_apply_succ_succ`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear_apply_succ_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear_apply_zero_succ`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear_apply_zero_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.tailShear_det`, `OAI.Erdos3.FilteredLieTree`, `OAI.Erdos3.FilteredLieTree.eval`, `OAI.Erdos3.FilteredLieTree.eval_bracket`, `OAI.Erdos3.FilteredLieTree.eval_leaf`, `OAI.Erdos3.FilteredLieTree.eval_mem`, `OAI.Erdos3.FilteredLieTree.rank_le_degree`, `OAI.Erdos3.FilteredLieTree.rank_pos`, `OAI.Erdos3.FiniteCoefficientSlice`, `OAI.Erdos3.FiniteCoefficientSlice.radius`, `OAI.Erdos3.FiniteProbabilityWeights.coordinate_fiber_mass_pos`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.IsAdmissible`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.budget`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.budget_node_castSucc`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.budget_node_last`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.index`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.index_node_last`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.length`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.length_node_last`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.length_pos`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.tolerance`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.Realization.rec`, `OAI.Erdos3.FixedDensity.AdaptiveCoarseTargetSchedule.rec`, `OAI.Erdos3.FixedDensity.BoundaryBooleanCutAssignment`, `OAI.Erdos3.FixedDensity.ClosedOrderedAtomConfiguration.IsSourceFullMixedGood`, `OAI.Erdos3.FixedDensity.ClosedOrderedAtomConfiguration.casesOn`, `OAI.Erdos3.FixedDensity.ClosedOrderedAtomConfiguration.ofTuple`, `OAI.Erdos3.FixedDensity.CoarseTargetOrderedComplexRegularityCertificate`, `OAI.Erdos3.FixedDensity.CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine`, `OAI.Erdos3.FixedDensity.FaceRegularityState.FamilyIrregularWitness`, `OAI.Erdos3.FixedDensity.FaceRegularityState.IsFamilyRegularAgainst`, `OAI.Erdos3.FixedDensity.FaceRegularityState.chosenFamilyIrregularCut`, `OAI.Erdos3.FixedDensity.FaceRegularityState.chosenFamilyIrregularWitness`, `OAI.Erdos3.FixedDensity.FaceRegularityState.exists_index_booleanCut_of_not_familyRegular`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRun`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRunCuts`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRunCuts_succ`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRunCuts_zero`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRun_succ`, `OAI.Erdos3.FixedDensity.FaceRegularityState.familyRegularityRun_zero`, `OAI.Erdos3.FixedDensity.FixedUpperLayerCoarseFine.nonempty`, `OAI.Erdos3.FixedDensity.FixedUpperLayerCoarseFine.rec`, `OAI.Erdos3.FixedDensity.FixedUpperLayerRegularityCertificate`, `OAI.Erdos3.FixedDensity.FixedUpperLayerRegularityCertificate.nonempty`, `OAI.Erdos3.FixedDensity.GeneratedOrderedPatternRegularization.BranchSystem`, `OAI.Erdos3.FixedDensity.GeneratedOrderedPatternRegularization.CellIndex`, `OAI.Erdos3.FixedDensity.GeneratedOrderedPatternRegularization.TopAtomChoice`, `OAI.Erdos3.FixedDensity.GeneratedOrderedPatternRegularization.card_cellIndex`, `OAI.Erdos3.FixedDensity.GeneratedOrderedPatternRegularization.casesOn`, `OAI.Erdos3.FixedDensity.IsDownwardClosedPositiveFaces`, `OAI.Erdos3.FixedDensity.IsFullyMixedPreliminaryOrderedRegular`, `OAI.Erdos3.FixedDensity.IsFullyPreliminaryOrderedRegular`, `OAI.Erdos3.FixedDensity.IsPreliminaryOrderedBoundedRegular`, `OAI.Erdos3.FixedDensity.IsPreliminaryOrderedRegular`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.casesOn`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.coarseDiagonal`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.coarseUpperFaceAtomEnergyGap`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.coarseUpperLayerAtomEnergyGap`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.mem_orderedCoarseOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedCoarseFineComplex.orderedCoarseOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.OrderedFacePartitionRefines`, `OAI.Erdos3.FixedDensity.OrderedFacePartitionRefines.refl`, `OAI.Erdos3.FixedDensity.OrderedFacePartitionRefines.trans`, `OAI.Erdos3.FixedDensity.OrderedFacePartitionSystem`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.Refines`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.Refines.refl`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.appendTop`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.appendTop_dropTop_topLayer`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.appendTop_partition_castSucc`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.appendTop_partition_last`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.boundary`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.dropTop`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.dropTop_appendTop`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.layer`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.topLayer`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.topLayer_appendTop`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.topLayer_withTopLayer`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.withTopLayer`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.withTopLayer_partition_castSucc`, `OAI.Erdos3.FixedDensity.OrderedPartitionComplex.withTopLayer_partition_castSucc_general`, `OAI.Erdos3.FixedDensity.OrderedPattern.deletionCylinder`, `OAI.Erdos3.FixedDensity.OrderedPattern.edgeFinset`, `OAI.Erdos3.FixedDensity.OrderedPattern.liftLowerDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.lowStructuredDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_deletionCylinder`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_edgeFinset`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_liftLowerDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_lowStructuredDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.mem_unionDeletion`, `OAI.Erdos3.FixedDensity.OrderedPattern.unionDeletion`, `OAI.Erdos3.FixedDensity.OrderedPositiveSubface`, `OAI.Erdos3.FixedDensity.OrderedRegularityTolerance`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.boundary`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.boundary_lowerRank`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.equivSigma`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.instFintype`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.rank`, `OAI.Erdos3.FixedDensity.PositiveOrderedFace.rank_pos`, `OAI.Erdos3.FixedDensity.PreliminaryIrregularWitness`, `OAI.Erdos3.FixedDensity.ProperPositiveOrderedSubface`, `OAI.Erdos3.FixedDensity.SourceFullMixedGoodAtFace`, `OAI.Erdos3.FixedDensity.StrongOrderedComplexRegularityCertificate`, `OAI.Erdos3.FixedDensity.StrongOrderedComplexRegularityCertificate.toCoarseFine`, `OAI.Erdos3.FixedDensity.atomBadBaseSupport`, `OAI.Erdos3.FixedDensity.atomBoundaryDefect`, `OAI.Erdos3.FixedDensity.atomBoundaryDefectSq`, `OAI.Erdos3.FixedDensity.booleanAssignmentOfBoundary`, `OAI.Erdos3.FixedDensity.booleanAssignmentOfBoundary_equiv_apply`, `OAI.Erdos3.FixedDensity.booleanAssignmentOfBoundary_ofBoolean`, `OAI.Erdos3.FixedDensity.booleanBoundaryAssignmentEquiv`, `OAI.Erdos3.FixedDensity.boundaryBernoulliWeight`, `OAI.Erdos3.FixedDensity.boundaryBooleanAssignmentOfBoolean`, `OAI.Erdos3.FixedDensity.boundaryBooleanAssignmentOfBoolean_ofBoundary`, `OAI.Erdos3.FixedDensity.boundaryBooleanComponentCut`, `OAI.Erdos3.FixedDensity.boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts`, `OAI.Erdos3.FixedDensity.boundaryBooleanCutSupport`, `OAI.Erdos3.FixedDensity.boundaryComponentBit_eq_of_mem_refined_part`, `OAI.Erdos3.FixedDensity.card_orderedBoundaryComponentCuts_le`, `OAI.Erdos3.FixedDensity.chosenFixedUpperLayerCoarseFine`, `OAI.Erdos3.FixedDensity.chosenFixedUpperLayerRegularityCertificate`, `OAI.Erdos3.FixedDensity.chosenPreliminaryIrregularWitness`, `OAI.Erdos3.FixedDensity.coarseAtomOfFineAtom`, `OAI.Erdos3.FixedDensity.complexity_fixedUpperLayerRegularityTower_le`, `OAI.Erdos3.FixedDensity.complexity_preliminaryOrderedRegularityRun_le`, `OAI.Erdos3.FixedDensity.complexity_preliminaryOrderedRegularityStep_le`, `OAI.Erdos3.FixedDensity.complexity_refineOrderedFacePartitionsByBoundaryCut_le`, `OAI.Erdos3.FixedDensity.configurationCoarseDensity`, `OAI.Erdos3.FixedDensity.configurationFaceWeight`, `OAI.Erdos3.FixedDensity.downwardClosed_empty`, `OAI.Erdos3.FixedDensity.eraseBoundaryCoordinate`, `OAI.Erdos3.FixedDensity.eraseBoundaryFace`, `OAI.Erdos3.FixedDensity.eraseOrderedFace`, `OAI.Erdos3.FixedDensity.exists_adjacent_real_sub_le_div`, `OAI.Erdos3.FixedDensity.exists_boundaryCut_of_not_preliminaryRegular`, `OAI.Erdos3.FixedDensity.exists_preliminaryOrderedRegular_refinement_with_complexity_before`, `OAI.Erdos3.FixedDensity.exists_preliminaryOrderedRegularityRun_index_before`, `OAI.Erdos3.FixedDensity.extendedConfigurationCount`, `OAI.Erdos3.FixedDensity.extendedConfigurationCount_empty`, `OAI.Erdos3.FixedDensity.fineAtomsInCoarseAtom`, `OAI.Erdos3.FixedDensity.fixedUpperLayerComplexityFactor`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower_refines`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower_refines_initial`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower_regular`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower_succ`, `OAI.Erdos3.FixedDensity.fixedUpperLayerRegularityTower_zero`, `OAI.Erdos3.FixedDensity.fullConfigurationCount`, `OAI.Erdos3.FixedDensity.indiscreteOrderedPartitionComplex`, `OAI.Erdos3.FixedDensity.largeAverageBaseAtoms`, `OAI.Erdos3.FixedDensity.largeAverageBaseSupport`, `OAI.Erdos3.FixedDensity.largeDefectBaseAtoms`, `OAI.Erdos3.FixedDensity.largeDefectBaseSupport`, `OAI.Erdos3.FixedDensity.mem_boundaryBooleanComponentCut`, `OAI.Erdos3.FixedDensity.mem_boundaryBooleanCutSupport`, `OAI.Erdos3.FixedDensity.mem_fineAtomsInCoarseAtom`, `OAI.Erdos3.FixedDensity.mem_largeAverageBaseSupport`, `OAI.Erdos3.FixedDensity.mem_largeDefectBaseSupport`, `OAI.Erdos3.FixedDensity.mem_orderedBoundaryPartition_part_iff`, `OAI.Erdos3.FixedDensity.mem_orderedFacePullbackFinset`, `OAI.Erdos3.FixedDensity.mem_orderedOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.mem_ownAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.mem_partitionAtomUnion`, `OAI.Erdos3.FixedDensity.mem_partitionAtomUnion_iff_atomAt_mem`, `OAI.Erdos3.FixedDensity.mem_smallAverageBaseSupport`, `OAI.Erdos3.FixedDensity.mixedConfigurationBoundaryIndicator`, `OAI.Erdos3.FixedDensity.mixedConfigurationCoarseDensity`, `OAI.Erdos3.FixedDensity.mixedConfigurationDefect`, `OAI.Erdos3.FixedDensity.mixedConfigurationFineDensity`, `OAI.Erdos3.FixedDensity.mixedConfigurationUniform`, `OAI.Erdos3.FixedDensity.mixedExtendedConfigurationCount`, `OAI.Erdos3.FixedDensity.mixedExtendedConfigurationCount_empty`, `OAI.Erdos3.FixedDensity.orderedAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.orderedAtomBoundaryDefect`, `OAI.Erdos3.FixedDensity.orderedAtomEnergy`, `OAI.Erdos3.FixedDensity.orderedAtomEnergy_le_one`, `OAI.Erdos3.FixedDensity.orderedAtomEnergy_mono`, `OAI.Erdos3.FixedDensity.orderedAtomEnergy_nonneg`, `OAI.Erdos3.FixedDensity.orderedBoundaryAtomAt`, `OAI.Erdos3.FixedDensity.orderedBoundaryAtomAt_val`, `OAI.Erdos3.FixedDensity.orderedBoundaryComponentCuts`, `OAI.Erdos3.FixedDensity.orderedBoundaryPartition`, `OAI.Erdos3.FixedDensity.orderedBoundaryPartition_le_immediate`, `OAI.Erdos3.FixedDensity.orderedBoundaryPartition_mono`, `OAI.Erdos3.FixedDensity.orderedBoundaryPartition_refined_le_generatedSupport`, `OAI.Erdos3.FixedDensity.orderedBoundaryPartition_refined_le_refineBy`, `OAI.Erdos3.FixedDensity.orderedBoundaryStructured`, `OAI.Erdos3.FixedDensity.orderedFaceAtomAt`, `OAI.Erdos3.FixedDensity.orderedFaceAtomAt_val`, `OAI.Erdos3.FixedDensity.orderedFacePullbackFinset`, `OAI.Erdos3.FixedDensity.orderedFaceTuple_eraseBoundaryFace`, `OAI.Erdos3.FixedDensity.orderedFaceTuple_eraseOrderedFace`, `OAI.Erdos3.FixedDensity.orderedFaceTuple_orderedFullLowerAmbientFace`, `OAI.Erdos3.FixedDensity.orderedFullLowerAmbientFace`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryAtomAt`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryAtomAt_val`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryPartition`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryWeight`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryWeight_self`, `OAI.Erdos3.FixedDensity.orderedFullLowerBoundaryWeight_sq`, `OAI.Erdos3.FixedDensity.orderedFullLowerComplexRank`, `OAI.Erdos3.FixedDensity.orderedFullLowerComplexRank_val`, `OAI.Erdos3.FixedDensity.orderedFullLowerConstituentPartition`, `OAI.Erdos3.FixedDensity.orderedFullLowerPositivePartition`, `OAI.Erdos3.FixedDensity.orderedImmediateBoundaryPartition`, `OAI.Erdos3.FixedDensity.orderedLayerAtomEnergy`, `OAI.Erdos3.FixedDensity.orderedLayerAtomEnergy_increment_of_boundaryCut`, `OAI.Erdos3.FixedDensity.orderedLayerAtomEnergy_le_card`, `OAI.Erdos3.FixedDensity.orderedLayerAtomEnergy_mono`, `OAI.Erdos3.FixedDensity.orderedLayerAtomEnergy_nonneg`, `OAI.Erdos3.FixedDensity.orderedOwnAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.orderedPatternInitialComplex`, `OAI.Erdos3.FixedDensity.orderedPatternInitialComplex_topLayer`, `OAI.Erdos3.FixedDensity.orderedPatternTopPartition`, `OAI.Erdos3.FixedDensity.ownAtomBadBaseSupport`, `OAI.Erdos3.FixedDensity.partialConfigurationCount`, `OAI.Erdos3.FixedDensity.partialConfigurationCount_empty`, `OAI.Erdos3.FixedDensity.partialConfigurationWeight`, `OAI.Erdos3.FixedDensity.partialConfigurationWeight_empty`, `OAI.Erdos3.FixedDensity.partitionAtomAt`, `OAI.Erdos3.FixedDensity.partitionAtomAt_eq_iff_mem`, `OAI.Erdos3.FixedDensity.partitionAtomAt_val`, `OAI.Erdos3.FixedDensity.partitionAtomEnergy`, `OAI.Erdos3.FixedDensity.partitionAtomEnergy_le_one`, `OAI.Erdos3.FixedDensity.partitionAtomEnergy_mono`, `OAI.Erdos3.FixedDensity.partitionAtomEnergy_nonneg`, `OAI.Erdos3.FixedDensity.partitionAtomIndicator`, `OAI.Erdos3.FixedDensity.partitionAtomIndicator_of_mem`, `OAI.Erdos3.FixedDensity.partitionAtomIndicator_of_not_mem`, `OAI.Erdos3.FixedDensity.partitionAtomIndicator_sq`, `OAI.Erdos3.FixedDensity.partitionAtomUnion`, `OAI.Erdos3.FixedDensity.positiveFaceLowerLayer`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityRun`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityRun_refines`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityRun_succ`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityRun_zero`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityStep`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityStep_energy_increment`, `OAI.Erdos3.FixedDensity.preliminaryOrderedRegularityStep_refines`, `OAI.Erdos3.FixedDensity.properPositiveOrderedSubface_rank_lt_upper`, `OAI.Erdos3.FixedDensity.refineOrderedFacePartitionsByBoundaryCut`, `OAI.Erdos3.FixedDensity.refineOrderedFacePartitionsByBoundaryCut_le_component`, `OAI.Erdos3.FixedDensity.refineOrderedFacePartitionsByBoundaryCut_refines`, `OAI.Erdos3.FixedDensity.selectedOrderedComplexTolerance`, `OAI.Erdos3.FixedDensity.smallAverageBaseAtoms`, `OAI.Erdos3.FixedDensity.smallAverageBaseSupport`, `OAI.Erdos3.FixedDensity.sourceFullMixedBoundaryWeight`, `OAI.Erdos3.FixedDensity.sourceFullMixedBoundaryWeight_sq`, `OAI.Erdos3.FixedDensity.sourceFullMixedCoarseDensity`, `OAI.Erdos3.FixedDensity.sourceFullMixedDefect`, `OAI.Erdos3.FixedDensity.sourceFullMixedLocalizedDefectSq`, `OAI.Erdos3.FixedDensity.sum_partitionAtomIndicator`, `OAI.Erdos3.GoodScalarKernelTuple`, `OAI.Erdos3.NilpotentLieBCHGroup.DualGroup`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjointAddEquiv`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_add`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_cancel_inv`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_inv_cancel`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_neg`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_neg_spec`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_one`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_spec`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_sub`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_zero`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBCH_insertion_identity`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBaseHom`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBaseHom_constant`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBaseHom_eq_one_iff`, `OAI.Erdos3.NilpotentLieBCHGroup.dualBaseHom_tangent`, `OAI.Erdos3.NilpotentLieBCHGroup.dualConstantHom`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_factorization`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_spec`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_tangent_mul_constant`, `OAI.Erdos3.NilpotentLieBCHGroup.dualTangentElement`, `OAI.Erdos3.NilpotentLieBCHGroup.dualTangentElement_injective`, `OAI.Erdos3.NilpotentLieBCHGroup.dualTangentElement_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.dualTangentElement_neg`, `OAI.Erdos3.NilpotentLieBCHGroup.dualTangentElement_zero`, `OAI.Erdos3.NilpotentLieFiltration.layer_succ_le_rankLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_rankIdeal`, `OAI.Erdos3.NilpotentLieFiltration.rankGenerators`, `OAI.Erdos3.NilpotentLieFiltration.rankIdeal`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_degree_le`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_eq_layer_of_rank_le_one`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_eq_next_of_degree_lt_rank`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_le_layer`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_lex_antitone`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_one`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_rank_antitone`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_top_terminal`, `OAI.Erdos3.NilpotentLieFiltration.rankLayer_zero`, `OAI.Erdos3.NilpotentLieFiltration.rank_span_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.span_rankGenerators_le_rankLayer`, `OAI.Erdos3.NilpotentLieFiltration.tree_eval_mem_rankLayer`, `OAI.Erdos3.NormalizedScalarCubeSource`, `OAI.Erdos3.NormalizedScalarCubeSource.CoefficientDomain`, `OAI.Erdos3.NormalizedScalarCubeSource.baseLaw`, `OAI.Erdos3.NormalizedScalarCubeSource.baseLaw_coefficient_mean`, `OAI.Erdos3.NormalizedScalarCubeSource.coefficientDensity`, `OAI.Erdos3.NormalizedScalarCubeSource.coefficientDensity_mean_one`, `OAI.Erdos3.NormalizedScalarCubeSource.coefficientDensity_nonneg`, `OAI.Erdos3.NormalizedScalarCubeSource.coefficientWeights`, `OAI.Erdos3.NormalizedScalarCubeSource.majorArcLocalizationData`, `OAI.Erdos3.NormalizedScalarCubeSource.polynomialLocalizationData`, `OAI.Erdos3.NormalizedScalarCubeSource.source`, `OAI.Erdos3.NormalizedScalarCubeSource.weight_empty_coordinate`, `OAI.Erdos3.PatchKernel.buffered_lift_unique`, `OAI.Erdos3.PatchKernel.zeroWithLip`, `OAI.Erdos3.PolynomialPatch.LowestLayerModel`, `OAI.Erdos3.PolynomialPatch.LowestLayerModel.integerChange`, `OAI.Erdos3.PolynomialPatch.LowestLayerModel.normalizedOrigin`, `OAI.Erdos3.PolynomialPatch.LowestLayerModel.onAffineLine`, `OAI.Erdos3.PolynomialPatch.LowestLayerModel.reparam`, `OAI.Erdos3.PolynomialPatch.insertAffineLifts`, `OAI.Erdos3.PolynomialPatch.insertAffineLifts_lip`, `OAI.Erdos3.PolynomialPatch.insertLifts`, `OAI.Erdos3.PolynomialPatch.insertLifts_lip`, `OAI.Erdos3.PolynomialPatch.liftInterleaving`, `OAI.Erdos3.PolynomialPatch.lowestLayerModel`, `OAI.Erdos3.PolynomialPatch.nonempty_lowestLayerModel`, `OAI.Erdos3.PolynomialSlots.exists_lowest_affine_prefix`, `OAI.Erdos3.PolynomialSlots.lowest_prefix_slotAffine`, `OAI.Erdos3.PrincipalIntegerTuples`, `OAI.Erdos3.RepresentativeWindow.composeCRTPatch`, `OAI.Erdos3.RepresentativeWindow.composeCRTPatch_lip`, `OAI.Erdos3.ScalarCubeLocalizationData`, `OAI.Erdos3.ScalarCubeLocalizationData.baseLaw`, `OAI.Erdos3.ScalarCubeLocalizationData.cell`, `OAI.Erdos3.ScalarCubeLocalizationData.cellCount`, `OAI.Erdos3.ScalarCubeLocalizationData.cellLength`, `OAI.Erdos3.ScalarCubeLocalizationData.error`, `OAI.Erdos3.ScalarCubeLocalizationData.integerOffset`, `OAI.Erdos3.ScalarCubeLocalizationData.lengthLoss`, `OAI.Erdos3.ScalarCubeLocalizationData.point`, `OAI.Erdos3.ScalarCubeLocalizationData.source`, `OAI.Erdos3.ScalarCubePrimitiveBudget.casesOn`, `OAI.Erdos3.VectorPolynomial.PreparedSourceScalarData.rec`, `OAI.Erdos3.VectorPolynomial.PreparedSourceScalarData.scale`, `OAI.Erdos3.VectorPolynomial.exists_preparedRelativeEndpointPerturbationLog_budget`, `OAI.Erdos3.VectorPolynomial.preparedCenteredForecast_cramer_bounds`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointCoarseLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointComparisonLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointSigmaLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointSourceLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointTestLog`, `OAI.Erdos3.affineCubeTuple`, `OAI.Erdos3.affineKernelContinuousPoint`, `OAI.Erdos3.affineKernelDiscretePoint`, `OAI.Erdos3.affineLiftSubstitution`, `OAI.Erdos3.affineLiftSubstitution_degree`, `OAI.Erdos3.assigned_phase_cauchySchwarz`, `OAI.Erdos3.boxCodeModulus`, `OAI.Erdos3.boxCodeModulus_eq`, `OAI.Erdos3.boxCodeModulus_neZero`, `OAI.Erdos3.boxCodeModulus_pos`, `OAI.Erdos3.boxCode_density`, `OAI.Erdos3.boxCode_density_lower`, `OAI.Erdos3.boxCyclicCode`, `OAI.Erdos3.boxCyclicCode_reflectsPairSums`, `OAI.Erdos3.boxIntegerCode`, `OAI.Erdos3.boxIntegerCode_bounds`, `OAI.Erdos3.boxPhaseMoment_character`, `OAI.Erdos3.bufferedScalarScore`, `OAI.Erdos3.canonicalPrincipalExponent`, `OAI.Erdos3.canonicalPrincipalExponent_apply`, `OAI.Erdos3.canonicalPrincipalExponent_injective`, `OAI.Erdos3.canonicalPrincipalExponent_ne_zero`, `OAI.Erdos3.canonicalSlicedModulus`, `OAI.Erdos3.centeredFiniteProbabilityMeasure`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_ae_positive_weight`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_integral`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_integral_bounded`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_noise_event_le`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_probability`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_productive_family`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_real_event`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_real_event_le_of_support`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_real_event_of_support`, `OAI.Erdos3.centeredFiniteProbabilityMeasure_real_finset_fiber`, `OAI.Erdos3.centeredFinite_event_measurableSet`, `OAI.Erdos3.centeredFinite_mean_integrable`, `OAI.Erdos3.centeredFinite_mean_measurable`, `OAI.Erdos3.centeredFinite_weight_integrable`, `OAI.Erdos3.coefficientResidueSet`, `OAI.Erdos3.containedKernelCubeMap`, `OAI.Erdos3.containedProgressionCubeLaw`, `OAI.Erdos3.containedProgressionCubeMap`, `OAI.Erdos3.containedProgressionResidueLaw`, `OAI.Erdos3.containedProgressionTupleMap`, `OAI.Erdos3.containedSupportedProgressionLaw`, `OAI.Erdos3.coordinateScaleEquiv_basis_det`, `OAI.Erdos3.crtLiftPolynomial`, `OAI.Erdos3.crtLiftPolynomial_degree`, `OAI.Erdos3.det_one_sub_strictLower`, `OAI.Erdos3.discreteScalarMinorThreshold`, `OAI.Erdos3.earlierSlotMatrix`, `OAI.Erdos3.earlierSlotMatrix_mulVec`, `OAI.Erdos3.earlierSlotMatrix_strict`, `OAI.Erdos3.emptyScalarCubeResidueEquiv`, `OAI.Erdos3.enormousPerturbation_large`, `OAI.Erdos3.exists_biased_matrix_coordinate_slice`, `OAI.Erdos3.exists_preparedEndpointPerturbation_budget`, `OAI.Erdos3.exists_slicedDetection_uniform_budget`, `OAI.Erdos3.fixedPathSlicedPerturbationLog`, `OAI.Erdos3.fixedPathSlicedPerturbationLog_nonneg`, `OAI.Erdos3.fixedSpatialKernelBlock`, `OAI.Erdos3.fixedSpatialKernelBlockCoordinates`, `OAI.Erdos3.fixedSpatialKernelBlockEquiv`, `OAI.Erdos3.fixedSpatialKernelBlockEquiv_coe`, `OAI.Erdos3.fixedSpatialKernelBlockEquiv_jacobian`, `OAI.Erdos3.fixedSpatialKernelBlock_slice`, `OAI.Erdos3.fixedSpatialKernelBlock_slice_det`, `OAI.Erdos3.fixedSpatialKernelBlock_slice_det_ne_zero`, `OAI.Erdos3.fixedSpatialKernelDensity`, `OAI.Erdos3.fixedSpatialKernelMap`, `OAI.Erdos3.fixedSpatialKernelRest`, `OAI.Erdos3.fixedSpatialKernelSliceDensity`, `OAI.Erdos3.fixedSpatialKernelSliceFrame`, `OAI.Erdos3.fixedSpatialKernelSliceFrame_none`, `OAI.Erdos3.fixedSpatialKernelSliceFrame_some`, `OAI.Erdos3.goodKernelUniformCandidate`, `OAI.Erdos3.goodScalarKernelTuple_spatial_det_ne_zero`, `OAI.Erdos3.gram_det_injective_map_basis`, `OAI.Erdos3.gridJetFrequency`, `OAI.Erdos3.integerAxisTailPMF`, `OAI.Erdos3.integerAxisTailPMF_small`, `OAI.Erdos3.integerAxisTailPMF_support`, `OAI.Erdos3.integerAxisTail_width`, `OAI.Erdos3.integerMappedCubeTuple`, `OAI.Erdos3.integerMappedJetMatrix`, `OAI.Erdos3.integerPerturbation_scaled_support`, `OAI.Erdos3.integerPolynomialProfile_width_large`, `OAI.Erdos3.integerProgressionSupport_subset_iff_fin`, `OAI.Erdos3.integerProgressionSupport_subset_of_fin`, `OAI.Erdos3.integerScalarCube_iff_normalized`, `OAI.Erdos3.integerScalarCube_progression`, `OAI.Erdos3.integratedFiniteProbabilityWeights`, `OAI.Erdos3.integratedFiniteProbabilityWeights_weight`, `OAI.Erdos3.jointAffineCoefficientTolerance`, `OAI.Erdos3.kernelCoefficientDensity`, `OAI.Erdos3.kernelFamilyOutputLog`, `OAI.Erdos3.kernelGeometryLog`, `OAI.Erdos3.kernelInverseLog`, `OAI.Erdos3.kernelJetCoefficientScale`, `OAI.Erdos3.kernelJetCoefficientScale_pos`, `OAI.Erdos3.kernelPeriodCandidate`, `OAI.Erdos3.kernelPeriodCandidate_le`, `OAI.Erdos3.kernelPeriodCandidate_le_exp`, `OAI.Erdos3.kernelPeriodCandidate_neZero`, `OAI.Erdos3.kernelPeriodCandidate_pos`, `OAI.Erdos3.kernelRowOutputLog`, `OAI.Erdos3.maskedIntervalApprox`, `OAI.Erdos3.matrixCoordinateSplit`, `OAI.Erdos3.matrixCoordinateSplit_symm_update`, `OAI.Erdos3.monomialScale_canonicalPrincipal`, `OAI.Erdos3.monomialScale_le_uniform_pow`, `OAI.Erdos3.monomialScale_productBlockExponent`, `OAI.Erdos3.multiaffineIntervalPhase`, `OAI.Erdos3.multiaffine_phase_box_bias`, `OAI.Erdos3.multiaffine_phase_difference_mean`, `OAI.Erdos3.multivariateSublevelConstant_le_exp`, `OAI.Erdos3.nearestIntegerLift`, `OAI.Erdos3.nearestIntegerLift_close`, `OAI.Erdos3.norm_affine_fin_phase_mean`, `OAI.Erdos3.normalizedScalarCubeMinor`, `OAI.Erdos3.normalizedScalarCubePivot`, `OAI.Erdos3.normalizedScalarCubeSourceOfIntegerPMF`, `OAI.Erdos3.normalizedScalarKernelJet`, `OAI.Erdos3.paddedIntegerPoint`, `OAI.Erdos3.paddedResidueDensityCap`, `OAI.Erdos3.paddedResidueDensityFactor`, `OAI.Erdos3.paddedResidueOffset`, `OAI.Erdos3.paddedResidueStep`, `OAI.Erdos3.pmf_interval_toReal_mass`, `OAI.Erdos3.polynomialMatrixAction`, `OAI.Erdos3.polynomialMatrixAction_degree`, `OAI.Erdos3.polynomialMatrixAction_eval`, `OAI.Erdos3.polynomial_affine_origin`, `OAI.Erdos3.preparedEarlySpatialWidth`, `OAI.Erdos3.principalAxisInterpolation`, `OAI.Erdos3.principalAxisInterpolationCap`, `OAI.Erdos3.principalAxisInterpolationLip`, `OAI.Erdos3.principalAxisInterpolation_spec`, `OAI.Erdos3.principalFinTuplePoint`, `OAI.Erdos3.principalResidueLabel`, `OAI.Erdos3.principalResidueWeights`, `OAI.Erdos3.principalSpatialColumns`, `OAI.Erdos3.principalSpatialResidueColumns`, `OAI.Erdos3.principalTupleIntegers`, `OAI.Erdos3.principalTupleNormalized`, `OAI.Erdos3.principalTupleResidues`, `OAI.Erdos3.principalTupleWeights`, `OAI.Erdos3.productBlockExponent`, `OAI.Erdos3.productBlockExponent_monomial`, `OAI.Erdos3.real_matrix_complement_linearMap_specified_denominator_grid`, `OAI.Erdos3.real_matrix_complement_specified_denominator_grid`, `OAI.Erdos3.real_matrix_specified_denominator_grid`, `OAI.Erdos3.remainingMatrixColumns`, `OAI.Erdos3.residueCellCount`, `OAI.Erdos3.residueCellIntegerPoint`, `OAI.Erdos3.residueCellLength`, `OAI.Erdos3.residueCellPosition`, `OAI.Erdos3.scalarCubeGrid`, `OAI.Erdos3.scalarCubeMinorPolynomial`, `OAI.Erdos3.scalarCubeMinorTestPoint`, `OAI.Erdos3.scalarCubeResidueCutoffBudget`, `OAI.Erdos3.scalarCubeResidueGridEquiv`, `OAI.Erdos3.scalarCubeResidueWeights_empty_one_mean`, `OAI.Erdos3.scalarKernelAdjustedAccuracy`, `OAI.Erdos3.scalarKernelConditioningConstant`, `OAI.Erdos3.scalarKernelCutoff`, `OAI.Erdos3.scalarKernelCutoffLogBudget`, `OAI.Erdos3.scalarKernelFixedFree`, `OAI.Erdos3.scalarKernelFixedPivot`, `OAI.Erdos3.scalarKernelInputBudget`, `OAI.Erdos3.scalarKernelIntegerJet`, `OAI.Erdos3.scalarKernelLogarithmicBudget`, `OAI.Erdos3.scalarKernelLogarithmicBudget_eq`, `OAI.Erdos3.scalarKernelTailConstant`, `OAI.Erdos3.scalarKernelThreshold`, `OAI.Erdos3.scalarResidueGridOffset`, `OAI.Erdos3.scalarResidueGridPoint`, `OAI.Erdos3.scalarResidueGridPoint_injective`, `OAI.Erdos3.scalarResidueGridPoint_residue`, `OAI.Erdos3.scalarResidueGridPoint_surjective`, `OAI.Erdos3.scalarResidueGridScale`, `OAI.Erdos3.scalarResidueGridScale_pos`, `OAI.Erdos3.scalarResidueGrid_normalized`, `OAI.Erdos3.scalarTupleColumn`, `OAI.Erdos3.scalarTupleSpatialColumns`, `OAI.Erdos3.scaled_section_gram_sqrt`, `OAI.Erdos3.shiftedBoxSite`, `OAI.Erdos3.shiftedBoxSite_update`, `OAI.Erdos3.shifted_site_phase_cauchySchwarz`, `OAI.Erdos3.signedSplitCoordinates`, `OAI.Erdos3.slicedDetectionGainLog`, `OAI.Erdos3.slicedDetectionGainLog_nonneg`, `OAI.Erdos3.tensorDiagonalPolynomial`, `OAI.Erdos3.tensorDiagonalPolynomial_add`, `OAI.Erdos3.tensorDiagonalPolynomial_eq_sum_monomial`, `OAI.Erdos3.tensorDiagonalPolynomial_eval`, `OAI.Erdos3.tensorDiagonalPolynomial_map`, `OAI.Erdos3.tensorDiagonalPolynomial_mul`, `OAI.Erdos3.tensorDiagonalPolynomial_multilinear_eval`, `OAI.Erdos3.uniformSpectrumAbsoluteCap`, `OAI.Erdos3.univariateSublevelConstant_le_exp`, `OAI.Erdos3.weightedAffineModerateGridCoefficient`, `OAI.Erdos3.zeroScalarCubeIntervalEquiv`, `OAI.Erdos3.zeroScalarFinPoint`, `_private.Lattices.AllocatedSupportedSlicedResidue.0.OAI.Erdos3.finIntegerIntervalEquiv`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarCubeGridCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarCubeGrid {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N)
    (x : J → IntegerScalarCubeBox I L) : Fin N → ℤ :=
  fun i => (x (e.symm i).1 (e.symm i).2 : ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def scalarCubeMinorPolynomial {I J : Type*} [Fintype I] [DecidableEq I]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (s j, some i))).det

noncomputable def scalarCubeMinorTestPoint {I J : Type*} [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : Fin N → ℝ := fun k =>
  match (e.symm k).2 with
  | none => 0
  | some i => if (e.symm k).1 = s i then 1 else 0

noncomputable def normalizedScalarCubeMinor {I J : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (s : I → J) (x : J → IntegerScalarCubeBox I L) : ℝ :=
  (((scalarCubeDifferenceMatrix x).submatrix id s).det : ℝ) / (L : ℝ) ^ Fintype.card I

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiscreteMinorThreshold
namespace OAI

namespace Erdos3

noncomputable def discreteScalarMinorThreshold (I J : Type*) [Fintype I] [Fintype J]
    (N : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * Fintype.card I) 1
    ((integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I))
    ((Fintype.card I + 1 : ℝ) ^ N) η

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

def GoodScalarKernelTuple {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {L : ℕ} (s : I → J) (κ : ℝ) (B : ℕ) (x : J → IntegerScalarCubeBox I L) : Prop :=
  κ < |normalizedScalarCubeMinor s x| ∧
    HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B

noncomputable def scalarKernelConditioningConstant (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) : ℝ := (scalarCubeResidueDensityCap I (M * D)) ^ Fintype.card J

noncomputable def scalarKernelTailConstant (I J : Type*) [Fintype I] [Fintype J] : ℝ :=
  (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^ Fintype.card J

noncomputable def scalarKernelAdjustedAccuracy (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ := η / scalarKernelConditioningConstant I J M D

noncomputable def scalarKernelThreshold (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℝ :=
  discreteScalarMinorThreshold I J (Fintype.card (J × Option I))
    (scalarKernelAdjustedAccuracy I J M D η)

noncomputable def scalarKernelCutoff (I J : Type*) [Fintype I] [Fintype J]
    (M D : ℕ) (η : ℝ) : ℕ :=
  jointKernelCutoff (Fintype.card I + 1) (D * ((Fintype.card I + 1) * M))
    (coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))))
    (scalarKernelTailConstant I J) (scalarKernelAdjustedAccuracy I J M D η)
    (scalarKernelThreshold I J M D η)

noncomputable def normalizedScalarCubePivot {I J : Type*} {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) : Matrix I I ℝ :=
  fun i j => (x (s j) (some i) : ℤ) / (L : ℝ)

noncomputable def scalarKernelCutoffLogBudget (I J : Type*) [Fintype I] [Fintype J] (P : ℝ) : ℝ :=
  2 * ((4 + 3 * ((Fintype.card (J × Option I) * Fintype.card I : ℕ) : ℝ)) * (P + 2)) + 8

theorem univariateSublevelConstant_le_exp (q : ℕ) (hq : 0 < q) :
    univariateSublevelConstant q ≤ Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have hn : (q + 1 : ℝ) ≤ Real.exp (q + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (q + 1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hbase : 1 ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
    have hp : 1 ≤ (8 * (q + 1 : ℝ)) ^ q := one_le_pow₀ (by have := Nat.cast_nonneg q (α := ℝ); linarith)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hi : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hm : 8 * (q + 1 : ℝ) ≤ Real.exp (8 + (q + 1 : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul h8 hn (by positivity) (Real.exp_pos _).le
  calc
    _ ≤ (q + 1 : ℝ) * (8 * (q + 1 : ℝ)) ^ q := by
      simpa only [univariateSublevelConstant, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hbase hi
    _ ≤ Real.exp (q + 1 : ℝ) * Real.exp (8 + (q + 1 : ℝ)) ^ q := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem multivariateSublevelConstant_le_exp (N q : ℕ) (hq : 0 < q) :
    multivariateSublevelConstant N q ≤
      Real.exp (3 * (N : ℝ) + (q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hN : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hu0 := (univariateSublevelConstant_pos q).le
  have hu := univariateSublevelConstant_le_exp q hq
  unfold multivariateSublevelConstant
  calc
    _ ≤ (Real.exp 2) ^ N * Real.exp N *
        Real.exp ((q + 1 : ℝ) + q * (8 + (q + 1 : ℝ))) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

noncomputable def scalarKernelInputBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card (J × Option I) + R)^3

noncomputable def scalarKernelLogarithmicBudget (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : ℝ :=
  scalarKernelCutoffLogBudget I J (scalarKernelInputBudget I J R)

theorem scalarKernelLogarithmicBudget_eq (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) :
    scalarKernelLogarithmicBudget I J R =
      2 * ((4 + 3 * ((Fintype.card J : ℝ) * (Fintype.card I + 1) * Fintype.card I)) *
        (16 * (10 + (Fintype.card I : ℝ) + Fintype.card J + Fintype.card J * (Fintype.card I + 1) + R)^3 + 2)) + 8 := by
  simp only [scalarKernelLogarithmicBudget, scalarKernelCutoffLogBudget, scalarKernelInputBudget,
    Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePhaseDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_affine_fin_phase_mean (M : ℕ) (a b : ℝ) :
    ‖𝔼 t : Fin M, character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a : CircleFourier.Circle)‖ := by
  have he (t : Fin M) :
      character ((a*(t.val : ℝ)+b : ℝ) : CircleFourier.Circle) =
        character (b : CircleFourier.Circle) * character (t.val • (a : CircleFourier.Circle)) := by
    have hr : a*(t.val : ℝ)+b = b+t.val • a := by simp only [nsmul_eq_mul]; ring
    rw [hr, AddCircle.coe_add, AddCircle.coe_nsmul, character_add]
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, norm_character, one_mul]
  rfl

noncomputable def multiaffineIntervalPhase {n : ℕ} {N : Fin n → ℕ} {M : ℕ}
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x : ∀ i, Fin (N i)) (t : Fin M) : ℂ :=
  character ((multiaffineExpansion (fun S => a S*(w+(t.val : ℝ))+b S)
    (fun i => u i+((x i).val : ℝ)) : ℝ) : CircleFourier.Circle)

theorem multiaffine_phase_difference_mean {n : ℕ} (N : Fin n → ℕ) (M : ℕ)
    (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    (x y : ∀ i, Fin (N i)) :
    ‖𝔼 t : Fin M, iteratedBoxDifference n (multiaffineIntervalPhase a b u w) x y t‖ =
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  unfold multiaffineIntervalPhase
  simp_rw [iteratedBoxDifference_character,
    multiaffineExpansion_box_difference n
      (fun S (t : Fin M) => a S*(w+(t.val : ℝ))+b S)
      (fun i (j : Fin (N i)) => u i+(j.val : ℝ)), add_sub_add_left_eq_sub]
  let D := ∏ i, (((x i).val : ℝ)-((y i).val : ℝ))
  change ‖𝔼 t : Fin M,
    character (((a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D : ℝ) : CircleFourier.Circle)‖ =
      ‖geometricCharacterMean M (a Finset.univ*D : CircleFourier.Circle)‖
  have he (t : Fin M) : (a Finset.univ*(w+(t.val : ℝ))+b Finset.univ)*D =
      (a Finset.univ*D)*(t.val : ℝ)+(a Finset.univ*w+b Finset.univ)*D := by ring
  simp_rw [he]
  exact norm_affine_fin_phase_mean M _ _

theorem multiaffine_phase_box_bias {n : ℕ} (N : Fin n → ℕ) (hN : ∀ i, 0 < N i)
    (M : ℕ) (hM : 0 < M) (a b : Finset (Fin n) → ℝ) (u : Fin n → ℝ) (w : ℝ)
    {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i), 𝔼 t : Fin M, multiaffineIntervalPhase a b u w x t‖) :
    ζ^(2^n) ≤ 𝔼 y : (∀ i, Fin (N i)), 𝔼 x : (∀ i, Fin (N i)),
      ‖geometricCharacterMean M
        ((a Finset.univ * ∏ i, (((x i).val : ℝ)-((y i).val : ℝ)) : ℝ) : CircleFourier.Circle)‖ := by
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  let : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have h := (pow_le_pow_left₀ hζ hbias (2^n)).trans
    (iterated_box_cauchy_schwarz n (multiaffineIntervalPhase a b u w))
  simp_rw [multiaffine_phase_difference_mean] at h
  rwa [Finset.expect_comm] at h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalBlockExponent
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def productBlockExponent {K : Type*} {h : ℕ} (principal : Fin h → K) : K →₀ ℕ :=
  ∑ v, Finsupp.single (principal v) 1

theorem productBlockExponent_monomial {K : Type*} {h : ℕ}
    (principal : Fin h → K) (c : ℝ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

noncomputable def canonicalPrincipalExponent {D G : Type*} {B : D → Type*} (h : D → ℕ)
    (d : D) (b : B d) : SamplerTupleIndex G B h →₀ ℕ :=
  productBlockExponent (fun v => .inr ⟨d, b, v⟩)

theorem canonicalPrincipalExponent_apply {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [DecidableEq (B d)] (b b' : B d) (v : Fin (h d)) :
    canonicalPrincipalExponent (G := G) h d b (.inr ⟨d, b', v⟩) = if b = b' then 1 else 0 := by
  classical
  by_cases hb : b = b' <;>
    simp [canonicalPrincipalExponent, productBlockExponent, Finsupp.single_apply, hb]

theorem canonicalPrincipalExponent_ne_zero {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) (b : B d) :
    canonicalPrincipalExponent (G := G) h d b ≠ 0 := by
  classical
  intro he
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b, ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply] at hv

theorem canonicalPrincipalExponent_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (canonicalPrincipalExponent (G := G) (B := B) h d) := by
  classical
  intro b b' he
  by_contra hne
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b', ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply, hne] at hv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrincipalMonomialScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialScale_productBlockExponent {K : Type*} {h : ℕ}
    (principal : Fin h → K) (T : K → ℝ) :
    monomialScale T (productBlockExponent principal) = ∏ v, T (principal v) := by
  have he := congrArg (MvPolynomial.eval T) (productBlockExponent_monomial principal (1 : ℝ))
  simpa only [MvPolynomial.eval_monomial, one_mul, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Finsupp.prod, monomialScale] using he

theorem monomialScale_canonicalPrincipal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (T : SamplerTupleIndex G B h → ℝ) (d : D) (b : B d) :
    monomialScale T (canonicalPrincipalExponent h d b) = ∏ v, T (.inr ⟨d, b, v⟩) :=
  monomialScale_productBlockExponent _ T

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixCoordinateSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def matrixCoordinateSplit {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) :
    (H → ∀ k, X k) ≃ (∀ i, X (j i)) × (∀ i, ∀ k : {k // k ≠ j i}, X k) where
  toFun v := (fun i => v i (j i), fun i k => v i k)
  invFun p i := (Equiv.piSplitAt (j i) X).symm (p.1 i, p.2 i)
  left_inv v := by
    funext i
    exact (Equiv.piSplitAt (j i) X).symm_apply_apply (v i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))

theorem matrixCoordinateSplit_symm_update {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) (x x₀ : ∀ i, X (j i))
    (r : ∀ i, ∀ k : {k // k ≠ j i}, X k) :
    (matrixCoordinateSplit j X).symm (x, r) =
      fun i => Function.update ((matrixCoordinateSplit j X).symm (x₀, r) i) (j i) (x i) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [matrixCoordinateSplit, Equiv.piSplitAt]
  · simp [matrixCoordinateSplit, Equiv.piSplitAt, hk]

theorem exists_biased_matrix_coordinate_slice {H I : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I]
    (X : I → Type*) [∀ k, Fintype (X k)] [∀ k, Nonempty (X k)]
    (j : H → I) (F : (H → ∀ k, X k) → ℂ) {δ : ℝ}
    (hδ : δ ≤ ‖𝔼 v, F v‖) :
    ∃ b : H → ∀ k, X k, δ ≤ ‖𝔼 x : ∀ i, X (j i),
      F (fun i => Function.update (b i) (j i) (x i))‖ := by
  let e := matrixCoordinateSplit j X
  have he := Fintype.expect_equiv e F (fun p => F (e.symm p)) (fun v => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm] at hδ
  obtain ⟨r, hr⟩ := exists_biased_finite_slice (fun r x => F (e.symm (x, r))) hδ
  let x₀ : ∀ i, X (j i) := fun i => Classical.choice inferInstance
  refine ⟨e.symm (x₀, r), ?_⟩
  have hmean : (𝔼 x : ∀ i, X (j i), F (e.symm (x, r))) =
      𝔼 x : ∀ i, X (j i), F (fun i => Function.update (e.symm (x₀, r) i) (j i) (x i)) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg F (matrixCoordinateSplit_symm_update j X x x₀ r)
  exact hr.trans_eq (congrArg norm hmean)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SitePhaseCauchySchwarz
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem boxPhaseMoment_character {X : Type*} [Fintype X] (h : ℕ)
    (P : (Fin h → X) → ℝ) :
    boxPhaseMoment h (fun x => character (P x : CircleFourier.Circle)) =
      𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle) := by
  unfold boxPhaseMoment
  simp_rw [iteratedBoxDifference_character]

theorem assigned_phase_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (P : (Fin h → X) → ℝ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) * ∏ s, U s x‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  have hc := assigned_site_cauchySchwarz hh
    (fun x => character (P x : CircleFourier.Circle)) assignment U hU hmiss
  rw [boxPhaseMoment_character] at hc
  exact hc.trans (Complex.re_le_norm _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ShiftedBoxSites
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

noncomputable def shiftedBoxSite {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) (x : Fin h → X) : V :=
  base + ∑ i, coefficient i • shift (x i)

theorem shiftedBoxSite_update {h : ℕ} {X V : Type*} [AddCommGroup V]
    (base : V) (coefficient : Fin h → ℤ) (shift : X → V) {i : Fin h}
    (hi : coefficient i = 0) (x : Fin h → X) (a : X) :
    shiftedBoxSite base coefficient shift (Function.update x i a) =
      shiftedBoxSite base coefficient shift x := by
  unfold shiftedBoxSite
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, zero_smul]
  · simp only [Function.update_of_ne hj]

theorem shifted_site_phase_cauchySchwarz {h : ℕ} {S X V : Type*}
    [Fintype S] [Fintype X] [Nonempty X] [AddCommGroup V] (hh : 0 < h)
    (base : S → V) (coefficient : S → Fin h → ℤ) (shift : X → V)
    (hzero : ∀ s, ∃ i, coefficient s i = 0) (P : (Fin h → X) → ℝ)
    (test : S → V → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character (P x : CircleFourier.Circle) *
      ∏ s, test s (shiftedBoxSite (base s) (coefficient s) shift x)‖ ^ (2 ^ h) ≤
      ‖𝔼 u, 𝔼 v, character
        ((additiveBoxDifference h (fun x (_ : Unit) => P x) u v () : ℝ) : CircleFourier.Circle)‖ := by
  let assignment : S → Fin h := fun s => (hzero s).choose
  apply assigned_phase_cauchySchwarz hh P assignment
    (fun s x => test s (shiftedBoxSite (base s) (coefficient s) shift x))
    (fun s x => htest s _)
  intro s x a
  exact congrArg (test s)
    (shiftedBoxSite_update (base s) (coefficient s) shift (hzero s).choose_spec x a)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
namespace OAI

namespace Erdos3

theorem goodScalarKernelTuple_spatial_det_ne_zero {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L B : ℕ} {κ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hκ : 0 < κ) (hx : GoodScalarKernelTuple s κ B x) :
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
  rw [selectedSpatialPivot, rootDifferenceMatrix_det]
  intro hz
  have h := hx.1
  rw [normalizedScalarCubeMinor, hz, Int.cast_zero, zero_div, abs_zero] at h
  exact (not_lt_of_ge hκ.le) h

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem monomialScale_le_uniform_pow {K : Type*} (T : K → ℝ)
    (hT : ∀ k, 0 ≤ T k) {L : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (e : K →₀ ℕ) {h : ℕ} (he : e.sum (fun _ n => n) ≤ h) :
    monomialScale T e ≤ L ^ h := by
  classical
  change (∏ k ∈ e.support, T k ^ e k) ≤ _
  calc
    _ ≤ ∏ k ∈ e.support, L ^ e k :=
      Finset.prod_le_prod (fun k _ => pow_nonneg (hT k) _)
        (fun k _ => pow_le_pow_left₀ (hT k) (hTL k) _)
    _ = L ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := pow_le_pow_right₀ hL he

end Erdos3

namespace Erdos3

open scoped Matrix

def remainingMatrixColumns {I J R : Type*} (A : Matrix I J R) (s : I ↪ J) :
    Matrix I (UnselectedColumn s) R := A.submatrix id Subtype.val

end Erdos3

namespace Erdos3

noncomputable def normalizedScalarKernelJet {I J O : Type*}
    [DecidableEq I] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) : Matrix O (BoundedIntegerExponent J h) ℝ :=
  boundedDegreeRealJetMatrix (fun j => (x j none : ℝ) / L)
    (fun i j => (x j (some i) : ℝ) / L) h rows

noncomputable def scalarKernelIntegerJet {I J O : Type*} [DecidableEq I] [Fintype J]
    {L : ℕ} (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I) :
    Matrix O (BoundedIntegerExponent J h) ℤ :=
  boundedDegreeIntegerJetMatrix (fun j => (x j none : ℤ)) (scalarCubeDifferenceMatrix x) h rows

noncomputable def kernelJetCoefficientScale (J : Type*) (h : ℕ) (L H : ℝ)
    (e : BoundedIntegerExponent J h) : ℝ := H / monomialScale (fun _ => L) e.val

theorem kernelJetCoefficientScale_pos (J : Type*) (h : ℕ) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (e : BoundedIntegerExponent J h) :
    0 < kernelJetCoefficientScale J h L H e :=
  div_pos hH (monomialScale_pos _ (fun _ => hL) e.val)

noncomputable def scalarKernelFixedPivot {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    (O → ℝ) ≃L[ℝ] (O → ℝ) :=
  normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L 1 (s i))
    (fun _ => 1) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) zero_lt_one (s i))
    (fun _ => zero_lt_one)

noncomputable def scalarKernelFixedFree {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree) :
    (UnselectedColumn s → ℝ) →L[ℝ] (O → ℝ) :=
  matrixSupCLM (remainingMatrixColumns (normalizedScalarKernelJet x degree rows) s)

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DiagonalTensorPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def tensorDiagonalPolynomial {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) : MvPolynomial I R :=
  ∑ j : Fin h → I, MvPolynomial.C (θ j) * ∏ i, MvPolynomial.X (j i)

theorem tensorDiagonalPolynomial_eval {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) (w : I → R) :
    MvPolynomial.eval w (tensorDiagonalPolynomial θ) = ∑ j, θ j * ∏ i, w (j i) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_add {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ ψ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => θ j + ψ j) =
      tensorDiagonalPolynomial θ + tensorDiagonalPolynomial ψ := by
  simp [tensorDiagonalPolynomial, add_mul, Finset.sum_add_distrib]

theorem tensorDiagonalPolynomial_mul {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (c : R) (θ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => c * θ j) = MvPolynomial.C c * tensorDiagonalPolynomial θ := by
  simp [tensorDiagonalPolynomial, Finset.mul_sum, mul_assoc]

theorem tensorDiagonalPolynomial_map {I R S : Type*} [Fintype I]
    [CommSemiring R] [CommSemiring S] {h : ℕ} (f : R →+* S) (θ : (Fin h → I) → R) :
    MvPolynomial.map f (tensorDiagonalPolynomial θ) = tensorDiagonalPolynomial (fun j => f (θ j)) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_eq_sum_monomial {I : Type*} [Fintype I]
    {h : ℕ} (θ : (Fin h → I) → ℝ) :
    tensorDiagonalPolynomial θ = ∑ j, MvPolynomial.monomial (productBlockExponent j) (θ j) := by
  simp only [tensorDiagonalPolynomial, productBlockExponent_monomial]

theorem tensorDiagonalPolynomial_multilinear_eval {I R : Type*} [Fintype I]
    [DecidableEq I] [CommRing R] {h : ℕ}
    (F : MultilinearMap R (fun _ : Fin h => I → R) R) (w : I → R) :
    MvPolynomial.eval w
      (tensorDiagonalPolynomial (fun j => F (fun i => Pi.single (j i) (1 : R)))) = F (fun _ => w) := by
  rw [tensorDiagonalPolynomial_eval]
  exact (multilinear_diagonal_expansion F w).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DualBCHDifferential
namespace OAI

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev DualGroup (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (DualLieAlgebra L) s (dualLie_lowerCentralSeries_eq_bot hnil)

noncomputable def dualConstantHom : NilpotentLieBCHGroup L s hnil →* DualGroup hnil :=
  map dualConstantLie

noncomputable def dualBaseHom : DualGroup hnil →* NilpotentLieBCHGroup L s hnil :=
  map dualBaseLie

noncomputable def dualTangentElement (x : L) : DualGroup hnil := ⟨dualInfinitesimal x⟩

@[simp] theorem dualBaseHom_constant (g : NilpotentLieBCHGroup L s hnil) :
    dualBaseHom (dualConstantHom g) = g := by
  apply ext
  exact dualBaseLinear_constant g.coord

@[simp] theorem dualBaseHom_tangent (x : L) :
    dualBaseHom (dualTangentElement (hnil := hnil) x) = 1 := by
  apply ext
  exact dualBaseLinear_infinitesimal x

theorem dualTangentElement_injective : Function.Injective (dualTangentElement (hnil := hnil)) := by
  intro x y h
  exact dualInfinitesimal_injective (congrArg coord h)

@[simp] theorem dualTangentElement_zero : dualTangentElement (hnil := hnil) (0 : L) = 1 := by
  apply ext
  exact map_zero dualInfinitesimal

theorem dualTangentElement_mul (x y : L) :
    dualTangentElement (hnil := hnil) x * dualTangentElement y = dualTangentElement (x + y) := by
  apply ext
  change lieBCH s (dualInfinitesimal x) (dualInfinitesimal y) = dualInfinitesimal (x + y)
  rw [lieBCH_eq_add_of_lie_eq_zero (dualLie_lowerCentralSeries_eq_bot hnil) (dualInfinitesimal_lie x y),
    map_add]

theorem dualTangentElement_neg (x : L) :
    dualTangentElement (hnil := hnil) (-x) = (dualTangentElement x)⁻¹ := by
  apply ext
  exact map_neg dualInfinitesimal x

theorem dualBaseHom_eq_one_iff (g : DualGroup hnil) :
    dualBaseHom g = 1 ↔ g = dualTangentElement (dualTangentLinear g.coord) := by
  constructor
  · intro hg
    have hb : dualBaseLinear g.coord = 0 := congrArg coord hg
    apply ext
    change g.coord = dualInfinitesimal (dualTangentLinear g.coord)
    conv_lhs => rw [dualLie_decomposition g.coord, hb, map_zero, zero_add]
  · intro hg
    rw [hg, dualBaseHom_tangent]

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def dualAdjoint (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  dualTangentLinear
    (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord

theorem dualAdjoint_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹ =
      dualTangentElement (dualAdjoint g x) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, dualBaseHom_tangent, mul_one, mul_inv_cancel]

theorem dualAdjoint_neg_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement (-x) * (dualConstantHom g)⁻¹ =
      dualTangentElement (-dualAdjoint g x) := by
  calc
    _ = (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹)⁻¹ := by
      rw [dualTangentElement_neg]
      group
    _ = _ := by rw [dualAdjoint_spec, dualTangentElement_neg]

noncomputable def dualLogDerivative (z : DualGroup hnil) : L :=
  dualTangentLinear (z * (dualConstantHom (dualBaseHom z))⁻¹).coord

theorem dualLogDerivative_spec (z : DualGroup hnil) :
    z * (dualConstantHom (dualBaseHom z))⁻¹ = dualTangentElement (dualLogDerivative z) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, mul_inv_cancel]

theorem dualLogDerivative_factorization (z : DualGroup hnil) :
    z = dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z) := by
  calc
    _ = (z * (dualConstantHom (dualBaseHom z))⁻¹) * dualConstantHom (dualBaseHom z) := by group
    _ = _ := by rw [dualLogDerivative_spec]

theorem dualLogDerivative_tangent_mul_constant (x : L) (g : NilpotentLieBCHGroup L s hnil) :
    dualLogDerivative (dualTangentElement x * dualConstantHom g) = x := by
  simp only [dualLogDerivative, map_mul, dualBaseHom_tangent, dualBaseHom_constant, one_mul,
    mul_inv_cancel_right]
  exact dualTangentLinear_infinitesimal x

theorem dualLogDerivative_mul (z w : DualGroup hnil) :
    dualLogDerivative (z * w) = dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w) := by
  have h : z * w =
      dualTangentElement (dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w)) *
        dualConstantHom (dualBaseHom z * dualBaseHom w) := by
    calc
      _ = (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
          (dualTangentElement (dualLogDerivative w) * dualConstantHom (dualBaseHom w)) :=
        congrArg₂ (· * ·) (dualLogDerivative_factorization z) (dualLogDerivative_factorization w)
      _ = dualTangentElement (dualLogDerivative z) *
          (dualConstantHom (dualBaseHom z) * dualTangentElement (dualLogDerivative w) *
            (dualConstantHom (dualBaseHom z))⁻¹) *
          (dualConstantHom (dualBaseHom z) * dualConstantHom (dualBaseHom w)) := by group
      _ = _ := by rw [dualAdjoint_spec, dualTangentElement_mul, map_mul]
  rw [h, dualLogDerivative_tangent_mul_constant]

theorem dualBCH_insertion_identity (z : DualGroup hnil) (e m : L) :
    dualTangentElement (-e) * z * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹ =
      dualTangentElement (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  calc
    _ = dualTangentElement (-e) *
        (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
        dualTangentElement (-m) * (dualConstantHom (dualBaseHom z))⁻¹ :=
      congrArg (fun a => dualTangentElement (-e) * a * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹) (dualLogDerivative_factorization z)
    _ = dualTangentElement (-e) * dualTangentElement (dualLogDerivative z) *
        (dualConstantHom (dualBaseHom z) * dualTangentElement (-m) *
          (dualConstantHom (dualBaseHom z))⁻¹) := by group
    _ = dualTangentElement (-e + dualLogDerivative z + -dualAdjoint (dualBaseHom z) m) := by
      rw [dualAdjoint_neg_spec, dualTangentElement_mul, dualTangentElement_mul]
    _ = _ := by congr 1; abel

end Erdos3.NilpotentLieBCHGroup

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualAdjointAction
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualAdjoint_zero (g : NilpotentLieBCHGroup L s hnil) :
    dualAdjoint g 0 = 0 := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualTangentElement_zero, mul_one, mul_inv_cancel]

theorem dualAdjoint_add (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x + y) = dualAdjoint g x + dualAdjoint g y := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualTangentElement_mul, ← dualTangentElement_mul,
    ← dualAdjoint_spec, ← dualAdjoint_spec]
  group

@[simp] theorem dualAdjoint_neg (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (-x) = -dualAdjoint g x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualAdjoint_neg_spec]

theorem dualAdjoint_sub (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x - y) = dualAdjoint g x - dualAdjoint g y := by
  simp only [sub_eq_add_neg, dualAdjoint_add, dualAdjoint_neg]

@[simp] theorem dualAdjoint_one (x : L) :
    dualAdjoint (1 : NilpotentLieBCHGroup L s hnil) x = x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, map_one, one_mul, inv_one, mul_one]

theorem dualAdjoint_mul (g h : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint (g * h) x = dualAdjoint g (dualAdjoint h x) := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualAdjoint_spec, ← dualAdjoint_spec, map_mul]
  group

@[simp] theorem dualAdjoint_inv_cancel (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g⁻¹ (dualAdjoint g x) = x := by
  rw [← dualAdjoint_mul, inv_mul_cancel, dualAdjoint_one]

@[simp] theorem dualAdjoint_cancel_inv (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (dualAdjoint g⁻¹ x) = x := by
  rw [← dualAdjoint_mul, mul_inv_cancel, dualAdjoint_one]

noncomputable def dualAdjointAddEquiv (g : NilpotentLieBCHGroup L s hnil) : L ≃+ L where
  toFun := dualAdjoint g
  invFun := dualAdjoint g⁻¹
  left_inv := dualAdjoint_inv_cancel g
  right_inv := dualAdjoint_cancel_inv g
  map_add' := dualAdjoint_add g

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FilteredLieTree
namespace OAI

section

namespace Erdos3

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

inductive FilteredLieTree (F : NilpotentLieFiltration L s) : ℕ → ℕ → Type u where
  | leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) : FilteredLieTree F d 1
  | bracket {d e r t : ℕ} (a : FilteredLieTree F d r) (b : FilteredLieTree F e t) :
      FilteredLieTree F (d + e) (r + t)

namespace FilteredLieTree

variable {F : NilpotentLieFiltration L s}

def eval : {d r : ℕ} → FilteredLieTree F d r → L
  | _, _, .leaf _ x _ => x
  | _, _, .bracket a b => ⁅eval a, eval b⁆

@[simp] theorem eval_leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) :
    eval (leaf hd x hx) = x := rfl

@[simp] theorem eval_bracket {d e r t : ℕ} (a : FilteredLieTree F d r)
    (b : FilteredLieTree F e t) : eval (bracket a b) = ⁅eval a, eval b⁆ := rfl

theorem rank_pos {d r : ℕ} (a : FilteredLieTree F d r) : 0 < r := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem rank_le_degree {d r : ℕ} (a : FilteredLieTree F d r) : r ≤ d := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem eval_mem {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ F.layer d := by
  induction a with
  | leaf hd x hx => exact hx
  | bracket a b ha hb => exact F.lie_mem ha hb

end FilteredLieTree

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankLayers
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def rankGenerators (d r : ℕ) : Set L :=
  {x | ∃ k, r ≤ k ∧ ∃ a : FilteredLieTree F d k, a.eval = x}

def rankLayer (d r : ℕ) : Submodule ℚ L :=
  F.layer (d + 1) ⊔ Submodule.span ℚ (F.rankGenerators d r)

theorem layer_succ_le_rankLayer (d r : ℕ) : F.layer (d + 1) ≤ F.rankLayer d r := le_sup_left

theorem span_rankGenerators_le_rankLayer (d r : ℕ) :
    Submodule.span ℚ (F.rankGenerators d r) ≤ F.rankLayer d r := le_sup_right

theorem tree_eval_mem_rankLayer {d r k : ℕ} (a : FilteredLieTree F d k) (hr : r ≤ k) :
    a.eval ∈ F.rankLayer d r :=
  F.span_rankGenerators_le_rankLayer d r (Submodule.subset_span ⟨k, hr, a, rfl⟩)

theorem rankLayer_le_layer (d r : ℕ) : F.rankLayer d r ≤ F.layer d := by
  apply sup_le (F.antitone (by omega))
  apply Submodule.span_le.mpr
  rintro x ⟨k, _, a, rfl⟩
  exact a.eval_mem

theorem rankLayer_rank_antitone (d : ℕ) : Antitone (F.rankLayer d) := by
  intro r t hrt
  apply sup_le_sup_left
  apply Submodule.span_mono
  rintro x ⟨k, htk, a, hx⟩
  exact ⟨k, hrt.trans htk, a, hx⟩

theorem rankLayer_degree_le {d e : ℕ} (hde : d < e) (r t : ℕ) :
    F.rankLayer e t ≤ F.rankLayer d r :=
  (F.rankLayer_le_layer e t).trans
    ((F.antitone (show d + 1 ≤ e by omega)).trans (F.layer_succ_le_rankLayer d r))

theorem rankLayer_lex_antitone {d e r t : ℕ} (h : d < e ∨ d = e ∧ r ≤ t) :
    F.rankLayer e t ≤ F.rankLayer d r := by
  rcases h with h | ⟨rfl, h⟩
  · exact F.rankLayer_degree_le h r t
  · exact F.rankLayer_rank_antitone d h

theorem rankLayer_eq_layer_of_rank_le_one (d : ℕ) {r : ℕ} (hr : r ≤ 1) :
    F.rankLayer d r = F.layer d := by
  apply le_antisymm (F.rankLayer_le_layer d r)
  intro x hx
  by_cases hd : d = 0
  · subst d
    exact F.layer_succ_le_rankLayer 0 r (by simp only [zero_add, F.one_eq_top, Submodule.mem_top])
  · exact F.tree_eval_mem_rankLayer (.leaf (by omega) x hx) hr

theorem rankLayer_zero (d : ℕ) : F.rankLayer d 0 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d (by omega)

theorem rankLayer_one (d : ℕ) : F.rankLayer d 1 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d le_rfl

theorem rankLayer_eq_next_of_degree_lt_rank {d r : ℕ} (hdr : d < r) :
    F.rankLayer d r = F.layer (d + 1) := by
  have hgen : F.rankGenerators d r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨k, hrk, a, _⟩
    have := a.rank_le_degree
    omega
  simp only [rankLayer, hgen, Submodule.span_empty, sup_bot_eq]

theorem rankLayer_top_terminal (r : ℕ) (hr : s < r) : F.rankLayer s r = ⊥ := by
  rw [F.rankLayer_eq_next_of_degree_lt_rank hr, F.terminal]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DegreeRankLieBrackets
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem rank_span_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ Submodule.span ℚ (F.rankGenerators d r))
    (hy : y ∈ Submodule.span ℚ (F.rankGenerators e t)) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, hi, a, rfl⟩ := hx
    obtain ⟨j, hj, b, rfl⟩ := hy
    exact F.tree_eval_mem_rankLayer (a.bracket b) (Nat.add_le_add hi hj)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem rankLayer_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ F.rankLayer d r) (hy : y ∈ F.rankLayer e t) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  have hb' : b ∈ F.layer d := F.rankLayer_le_layer d r (F.span_rankGenerators_le_rankLayer d r hb)
  have hz' : z ∈ F.layer e := F.rankLayer_le_layer e t (F.span_rankGenerators_le_rankLayer e t hz)
  have hc' : c ∈ F.layer e := F.antitone (by omega) hc
  have hleft {u v : L} (hu : u ∈ F.layer (d + 1)) (hv : v ∈ F.layer e) :
      ⁅u, v⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem hu hv
  have hright : ⁅b, c⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc] using F.lie_mem hb' hc
  simp only [add_lie, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hleft ha hc') hright)
    (Submodule.add_mem _ (hleft ha hz') (F.rank_span_lie_mem hb hz))

def rankIdeal (d r : ℕ) : LieIdeal ℚ L :=
  { F.rankLayer d r with
    lie_mem := by
      intro x y hy
      apply F.layer_succ_le_rankLayer
      have hx : x ∈ F.layer 1 := by simp only [F.one_eq_top, Submodule.mem_top]
      simpa only [Nat.add_comm 1 d] using F.lie_mem hx (F.rankLayer_le_layer d r hy) }

@[simp] theorem mem_rankIdeal (d r : ℕ) (x : L) :
    x ∈ F.rankIdeal d r ↔ x ∈ F.rankLayer d r := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PerturbationCoefficientLaw
namespace OAI

section

namespace Erdos3

theorem integerPerturbation_scaled_support {K ε S : ℝ} (hK : 0 < K) (hε : 0 < ε) (hS : 0 < S)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / S) * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K 0 (ε / S) hK (div_pos hε hS) hlarge).support) :
    |(k : ℝ) / K| * S < 3 * ε / 4 := by
  have hb := normalizedIntegerPMF_support K 0 (ε / S) hK (div_pos hε hS) hlarge hk
  simp only [sub_zero] at hb
  have he := mul_lt_mul_of_pos_right hb hS
  have hs : 3 * (ε / S) / 4 * S = 3 * ε / 4 := by field_simp
  rwa [hs] at he

theorem enormousPerturbation_large {V : Type*} (T : V → ℝ) (hT : ∀ i, 0 < T i)
    {K L ε : ℝ} {s : ℕ} (hL : 1 ≤ L) (hε : 0 < ε) (hTL : ∀ i, T i ≤ L)
    (hK : L ^ (s + 1) ≤ K) (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hS := monomialScale_pos T hT e
  have hSL : L * monomialScale T e ≤ K := by
    calc
      _ ≤ L * L ^ s := mul_le_mul_of_nonneg_left
        (monomialScale_le_uniform_pow T (fun i => (hT i).le) hL hTL e he) hL0
      _ = L ^ (s + 1) := by rw [pow_succ]; ring
      _ ≤ K := hK
  have hb := mul_le_mul_of_nonneg_left hSL hε.le
  have hstep : ε * L ≤ (ε / monomialScale T e) * K := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hS).mpr
    nlinarith
  exact hεL.trans hstep

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisTailLaw
namespace OAI

section

namespace Erdos3

theorem integerAxisTail_width {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : L ^ (s + 1) < K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  apply enormousPerturbation_large T hT (by exact_mod_cast hL) hε hTL
  · exact_mod_cast ha.le
  · exact hεL
  · exact he

noncomputable def integerAxisTailPMF {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) : PMF ℤ :=
  if ha : L ^ (s + 1) < K then
    normalizedIntegerPMF K 0 (ε / monomialScale T e) (by exact_mod_cast hK)
      (div_pos hε (monomialScale_pos T hT e)) (integerAxisTail_width T hT hL hTL hε hεL e he ha)
  else PMF.pure 0

theorem integerAxisTailPMF_small {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : K ≤ L ^ (s + 1)) :
    integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he = PMF.pure 0 := by
  simp [integerAxisTailPMF, Nat.not_lt.mpr ha]

theorem integerAxisTailPMF_support {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) {k : ℤ}
    (hk : k ∈ (integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL e he).support) :
    |(k : ℝ) / K| * monomialScale T e < 3 * ε / 4 := by
  by_cases ha : L ^ (s + 1) < K
  · simp only [integerAxisTailPMF, ha, ↓reduceDIte] at hk
    exact integerPerturbation_scaled_support (by exact_mod_cast hK) hε
      (monomialScale_pos T hT e) (integerAxisTail_width T hT hL hTL hε hεL e he ha) hk
  · rw [integerAxisTailPMF_small T hT hK hL hTL hε hεL e he (Nat.le_of_not_gt ha)] at hk
    have hk0 : k = 0 := by simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    simp only [Int.cast_zero, zero_div, abs_zero, zero_mul]
    positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

noncomputable def integerMappedCubeTuple {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x : X → ℤ) : Finset α → K → ℤ :=
  integerAffineCube (fun k => Sum.elim z x (input k none))
    (fun i k => Sum.elim z x (input k (some i)))

noncomputable def integerMappedJetMatrix {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x : X → ℤ) : Matrix I N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerMappedCubeTuple input z x) rows

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

abbrev PrincipalIntegerTuples {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*)
    (L : PrincipalTupleIndex B h → ℕ) := ∀ j, IntegerScalarCubeBox α (L j)

def principalTupleIntegers {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℤ :=
  fun a => (y ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2 : ℤ)

noncomputable def principalTupleNormalized {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (L : PrincipalTupleIndex B h → ℕ) (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℝ :=
  fun a => (principalTupleIntegers y a : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩

def principalTupleResidues {D α : Type*} {B : D → Type*} {h : D → ℕ} {m : ℕ}
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : JointBlockParameter B h α → ZMod m :=
  fun a => r ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2

noncomputable def principalResidueWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) m (hL j)
    (fun _ => m) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def principalTupleWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights α (L j) (hL j))

def principalResidueLabel {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (y : PrincipalIntegerTuples B h α L) :
    PrincipalTupleIndex B h → Option α → ZMod m := fun j i => ((y j i : ℤ) : ZMod m)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def paddedIntegerPoint {I : Type*} (L P : ℕ) (x : I → Fin P) : I → ℤ :=
  fun i => (x i).val - L

end Erdos3

end

section

namespace Erdos3

noncomputable def residueCellLength (δ : ℝ) (L M : ℕ) : ℕ := ⌊δ * L / M⌋₊

def residueCellCount (L N : ℕ) : ℕ := 2 * L / N + 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def scalarResidueGridPoint {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (k : Option I → ℤ) : Option I → ℤ := fun i => (r i).val + (m i : ℤ)*k i

noncomputable def scalarResidueGridOffset {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => -((r i).val : ℝ) / m i

noncomputable def scalarResidueGridScale {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (L : ℝ) / m i

theorem scalarResidueGridScale_pos {I : Type*} {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (hm : ∀ i, 0 < m i) (i : Option I) : 0 < scalarResidueGridScale L m i := by
  unfold scalarResidueGridScale
  exact div_pos (by exact_mod_cast hL) (by exact_mod_cast hm i)

theorem scalarResidueGrid_normalized {I : Type*} [Fintype I] {L : ℕ} (hL : 0 < L)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) (k : Option I → ℤ) :
    rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k =
      fun i => (scalarResidueGridPoint m r k i : ℝ) / L := by
  funext i
  have hmi : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
  simp only [rectangularLatticePoint, scalarResidueGridOffset, scalarResidueGridScale,
    scalarResidueGridPoint, Int.cast_add, Int.cast_natCast, Int.cast_mul]
  field_simp
  ring

theorem integerScalarCube_iff_normalized {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (z : Option I → ℤ) :
    IntegerScalarCube L z ↔ (fun i => (z i : ℝ) / L) ∈ halfOpenScalarCubeDomain I := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have he (t : Finset I) : scalarCubeValue (fun i => (z i : ℝ) / L) t = (integerScalarCubeValue z t : ℝ) / L := by
    simp only [scalarCubeValue_formula, integerScalarCubeValue, Int.cast_add, Int.cast_sum, add_div, Finset.sum_div]
  constructor
  · intro hz t
    rw [he]
    constructor
    · exact div_nonneg (by exact_mod_cast (hz t).1) hLp.le
    · exact (div_lt_one hLp).mpr (by exact_mod_cast (hz t).2)
  · intro hz t
    have ht := hz t
    rw [he] at ht
    constructor
    · have hh : (0 : ℝ) ≤ (integerScalarCubeValue z t : ℝ) := by
        simpa only [zero_mul] using (le_div_iff₀ hLp).mp ht.1
      exact_mod_cast hh
    · exact_mod_cast (div_lt_one hLp).mp ht.2

theorem scalarResidueGridPoint_residue {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (k : Option I → ℤ) (i : Option I) :
    (scalarResidueGridPoint m r k i : ZMod (m i)) = r i := by
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp [scalarResidueGridPoint]

theorem scalarResidueGridPoint_injective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) : Function.Injective (scalarResidueGridPoint m r) := by
  intro k l h
  funext i
  have hh := congrFun h i
  have hmi : (m i : ℤ) ≠ 0 := by exact_mod_cast (hm i).ne'
  exact mul_left_cancel₀ hmi (add_left_cancel hh)

theorem scalarResidueGridPoint_surjective {I : Type*} (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (z : Option I → ℤ)
    (hz : ∀ i, (z i : ZMod (m i)) = r i) : ∃ k, scalarResidueGridPoint m r k = z := by
  have hi (i : Option I) : ∃ k : ℤ, z i = (r i).val + (m i : ℤ)*k := by
    let : NeZero (m i) := ⟨(hm i).ne'⟩
    have he : (((r i).val : ℤ) : ZMod (m i)) = (z i : ZMod (m i)) := by simpa using (hz i).symm
    obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (z i) (m i)).mp he
    exact ⟨k, by linarith⟩
  choose k hk using hi
  exact ⟨k, funext (fun i => (hk i).symm)⟩

noncomputable def scalarCubeResidueGridEquiv (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) :
    ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) ≃
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let F : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) →
      ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := fun k => by
    have hk := (mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm) k.val).mp k.property
    rw [scalarResidueGrid_normalized hL m r hm] at hk
    have hc := (integerScalarCube_iff_normalized hL _).mpr hk
    let z : IntegerScalarCubeBox I L := fun i => ⟨scalarResidueGridPoint m r k.val i,
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hc i).1.le, (integerScalarCube_coordinates hc i).2⟩⟩
    exact ⟨z, Finset.mem_inter.mpr ⟨(mem_integerScalarCubeSet L z).mpr hc,
      (mem_scalarCubeResidueSet L m r z).mpr (scalarResidueGridPoint_residue m r hm k.val)⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro k l h
    apply Subtype.ext
    apply scalarResidueGridPoint_injective m r hm
    exact funext (fun i => congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h)
  · intro z
    obtain ⟨k,hk⟩ := scalarResidueGridPoint_surjective m r hm (fun i => (z.val i : ℤ))
      ((mem_scalarCubeResidueSet L m r z.val).mp (Finset.mem_inter.mp z.property).2)
    have hc := (mem_integerScalarCubeSet L z.val).mp (Finset.mem_inter.mp z.property).1
    have hmem : k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) := by
      rw [mem_scalarCubeGridSet _ _ (scalarResidueGridScale_pos hL m hm), scalarResidueGrid_normalized hL m r hm, hk]
      exact (integerScalarCube_iff_normalized hL _).mp hc
    refine ⟨⟨k,hmem⟩, ?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun hk i

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

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

noncomputable def paddedResidueOffset {I : Type*} (L : ℕ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) : Option I → ℝ :=
  fun i => ((r i).val - (m i : ℝ) * L) / L

noncomputable def paddedResidueStep {I : Type*} (L : ℕ) (m : Option I → ℕ) : Option I → ℝ :=
  fun i => (m i : ℝ) / L

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarCubeResidueCutoffBudget (I : Type*) [Fintype I] [DecidableEq I]
    (A r : ℝ≥0) (L M : ℕ) : ℝ :=
  scalarCubeBoundaryConstant I * r +
    (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
      scalarCubeCutoffLipschitzConstant I A r) * ((M : ℝ) / L)

end Erdos3

end

section

namespace Erdos3

noncomputable def paddedResidueDensityFactor (I : Type*) [Fintype I] (L P : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : ℝ :=
  (P : ℝ) ^ (Fintype.card I + 1) /
    ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card

noncomputable def paddedResidueDensityCap (I : Type*) [Fintype I] (M : ℕ) : ℝ :=
  2 ^ (Fintype.card I + 1) * scalarCubeResidueDensityCap I M

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

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def residueCellPosition {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℝ :=
  fun i => progressionCellCorner (fun _ => N) (paddedResidueOffset L m res)
    (paddedResidueStep L m) k i + paddedResidueStep L m i * (t i).val

end Erdos3

end

section

namespace Erdos3

def residueCellIntegerPoint {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℤ :=
  scalarResidueGridPoint m res (fun i => (N : ℤ) * (k i).val + (t i).val - L)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
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

open MeasureTheory
open scoped BigOperators NNReal

structure ScalarCubeLocalizationData (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  gridSmall : scalarCubeGridBoundaryConstant I * ((modulusBound : ℝ) / length) <
    volume.real (scalarCubeDomain I)
  transitionBound : ℝ≥0
  transition_lipschitz : LipschitzWith transitionBound Real.smoothTransition
  radius : ℝ≥0
  radius_pos : 0 < radius
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1
  mesh : ℝ
  mesh_pos : 0 < mesh
  mesh_le_one : mesh ≤ 1
  meshLarge : 2 * (modulusBound : ℝ) ≤ mesh * length
  margin : ((Fintype.card I : ℝ) + 1) * mesh < radius

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  scalarCubeResidueWeights I d.length d.modulusBound d.length_pos d.modulus d.residue
    d.modulus_pos d.modulus_le d.size

noncomputable def point (z : IntegerScalarCubeBox I d.length) : Option I → ℝ :=
  fun i => (z i : ℝ) / d.length

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  d.baseLaw.reweight (fun z => d.weight (d.point z)) (fun z => (d.weight_range (d.point z)).1) d.normalized

noncomputable def cellLength : ℕ := residueCellLength d.mesh d.length d.modulusBound

noncomputable def cellCount : ℕ := residueCellCount d.length d.cellLength

noncomputable def cell (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) : Option I → ℝ :=
  residueCellPosition d.length d.cellLength d.cellCount d.modulus d.residue k t

noncomputable def error (η : ℝ) : ℝ :=
  d.weightBound * scalarCubeResidueCutoffBudget I d.transitionBound d.radius d.length d.modulusBound +
    paddedResidueDensityCap I d.modulusBound *
      (((d.weightLipschitz : ℝ) + d.weightBound * scalarCubeCutoffLipschitzConstant I d.transitionBound d.radius) *
        d.mesh + d.weightBound * η)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure NormalizedScalarCubeSource (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  scalarCubeResidueWeights I s.length s.modulusBound s.length_pos s.modulus s.residue
    s.modulus_pos s.modulus_le s.size

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  s.baseLaw.reweight (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def integerOffset (k : Option I → Fin d.cellCount) : Option I → ℝ :=
  fun i => (d.residue i).val + (d.modulus i : ℝ) * ((d.cellLength : ℝ) * (k i).val - d.length)

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def lengthLoss : ℝ := 2 * d.modulusBound / d.mesh

end ScalarCubeLocalizationData

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
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientResidueSet (L m : ℕ) (r : ZMod m) : Finset ℤ :=
  (Finset.Ico 0 (L : ℤ)).filter (fun z => (z : ZMod m) = r)

noncomputable def emptyScalarCubeResidueEquiv (L : ℕ) (m : Option Empty → ℕ)
    (r : ∀ i, ZMod (m i)) :
    ↥((integerScalarCubeSet Empty L) ∩ scalarCubeResidueSet Empty L m r) ≃
      ↥(coefficientResidueSet L (m none) (r none)) where
  toFun x := by
    have hx := Finset.mem_inter.mp x.property
    have h0 := ((mem_integerScalarCubeSet L x.val).mp hx.1) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr h0,
      (mem_scalarCubeResidueSet L m r x.val).mp hx.2 none⟩⟩
  invFun z := by
    have hz := Finset.mem_filter.mp z.property
    have hb := Finset.mem_Ico.mp hz.1
    let x : IntegerScalarCubeBox Empty L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hb.2⟩⟩
    refine ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply (mem_integerScalarCubeSet L x).mpr
      intro t
      have ht : t = ∅ := Subsingleton.elim _ _
      simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hb
    · apply (mem_scalarCubeResidueSet L m r x).mpr
      intro i
      cases i with
      | none => exact hz.2
      | some a => exact a.elim
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv z := by apply Subtype.ext; rfl

namespace NormalizedScalarCubeSource

abbrev CoefficientDomain (s : NormalizedScalarCubeSource Empty) :=
  ↥(coefficientResidueSet s.length (s.modulus none) (s.residue none))

theorem baseLaw_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.baseLaw.mean (fun x => f (x none : ℤ)) = 𝔼 z : s.CoefficientDomain, f z := by
  unfold baseLaw
  rw [scalarCubeResidueWeights_mean]
  exact Fintype.expect_equiv (emptyScalarCubeResidueEquiv s.length s.modulus s.residue) _ _ (fun _ => rfl)

theorem weight_empty_coordinate (s : NormalizedScalarCubeSource Empty)
    (x : IntegerScalarCubeBox Empty s.length) :
    s.weight (fun i => (x i : ℝ) / s.length) = s.weight (fun _ => (x none : ℝ) / s.length) := by
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

noncomputable def coefficientDensity (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) : ℝ :=
  s.weight (fun _ => (z.val : ℝ) / s.length)

theorem coefficientDensity_nonneg (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) :
    0 ≤ s.coefficientDensity z := (s.weight_range _).1

theorem coefficientDensity_mean_one (s : NormalizedScalarCubeSource Empty) :
    (𝔼 z : s.CoefficientDomain, s.coefficientDensity z) = 1 := by
  have he := s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length))
  have hn : s.baseLaw.mean (fun x => s.weight (fun _ => (x none : ℝ) / s.length)) = 1 := by
    have h := s.normalized
    simpa only [s.weight_empty_coordinate, baseLaw] using h
  exact he.symm.trans hn

noncomputable def coefficientWeights (s : NormalizedScalarCubeSource Empty) :
    FiniteProbabilityWeights s.CoefficientDomain :=
  FiniteProbabilityWeights.ofDensity s.coefficientDensity s.coefficientDensity_nonneg s.coefficientDensity_mean_one

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

structure FiniteCoefficientSlice where
  length : ℕ
  offset : ℤ
  stride : ℤ
  modulus : ℕ
  residue : ZMod modulus

namespace FiniteCoefficientSlice

def radius (s : FiniteCoefficientSlice) : ℕ := s.offset.natAbs + s.stride.natAbs * s.length

end FiniteCoefficientSlice

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubePrimitiveBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure ScalarCubePrimitiveBudget {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (U : ℝ) : Prop where
  one_le : 1 ≤ U
  dimension_le : (Fintype.card I : ℝ) + 1 ≤ U
  modulus_le : (s.modulusBound : ℝ) ≤ U
  weight_le : (s.weightBound : ℝ) ≤ U
  weightLipschitz_le : (s.weightLipschitz : ℝ) ≤ U
  boundary_le : scalarCubeBoundaryConstant I ≤ U
  grid_le : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ U
  derivative_le : scalarCubeCutoffDerivativeNumerator I A ≤ U
  density_le : paddedResidueDensityCap I s.modulusBound ≤ U

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialScalarCubeLength
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ s.length)

noncomputable def polynomialLocalizationData : ScalarCubeLocalizationData I := by
  have hU0 : 0 < U := by linarith [h.one_le]
  have hδ := localizationMesh_pos h.one_le hε
  have hbase : U ^ 2 ≤ (s.length : ℝ) :=
    (localizationLengthBudget_ge_square h.one_le hε hε1 hW).trans hlen
  have hgrid : 2 * scalarCubeGridBoundaryConstant I * s.modulusBound /
      volume.real (scalarCubeDomain I) ≤ s.length := by
    calc
      _ = (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * s.modulusBound := by ring
      _ ≤ U * U := mul_le_mul h.grid_le h.modulus_le (Nat.cast_nonneg _) hU0.le
      _ ≤ _ := by nlinarith
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  exact {
    length := s.length, modulusBound := s.modulusBound, length_pos := s.length_pos
    modulus := s.modulus, residue := s.residue, modulus_pos := s.modulus_pos
    modulus_le := s.modulus_le, size := s.size
    gridSmall := scalarCubeGrid_small_error_of_length I s.length_pos hgrid
    transitionBound := A, transition_lipschitz := hA
    radius := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
    radius_pos := localizationRadius_pos h.one_le hε
    weight := s.weight, weightBound := s.weightBound, weightLipschitz := s.weightLipschitz
    weightBound_pos := s.weightBound_pos, weight_range := s.weight_range
    weight_lipschitz := s.weight_lipschitz, normalized := s.normalized
    mesh := localizationMesh U ε, mesh_pos := hδ
    mesh_le_one := localizationMesh_le_one h.one_le hε hε1
    meshLarge := by
      have hw := le_mul_of_one_le_right hU0.le hW
      nlinarith [h.modulus_le]
    margin := (mul_le_mul_of_nonneg_right h.dimension_le hδ.le).trans_lt
      (localizationMesh_margin h.one_le hε hε1) }

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NormalizedScalarCubeSource

end NormalizedScalarCubeSource

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {n : ℕ} {U ζ : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : localizedMajorArcLengthBudget n U ζ ≤ s.length)

noncomputable def majorArcLocalizationData : ScalarCubeLocalizationData I :=
  s.polynomialLocalizationData A hA h (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen

end NormalizedScalarCubeSource
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def gridJetFrequency {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : Finset I) : ℝ :=
  if h : S ∈ J then ((k ⟨S, h⟩).val : ℝ) / M else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def weightedAffineModerateGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  c.source.complexMean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((shift + (z none : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

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
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformSpectrumAbsoluteCap (n j t : ℕ) (U V W : ℝ) : ℝ :=
  uniformSpectrumSizeConstant n j t U V W + 1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem pmf_interval_toReal_mass (L : ℕ) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ)) :
    (∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal) = 1 := by
  have hm : (∑ k ∈ Finset.Ico 0 (L : ℤ), p k) = 1 := by
    rw [← p.tsum_coe]
    apply (tsum_eq_sum (s := Finset.Ico 0 (L : ℤ)) _).symm
    intro k hk
    by_contra hn
    exact hk (hs k hn)
  rw [← ENNReal.toReal_sum (fun k _ => p.apply_ne_top k), hm, ENNReal.toReal_one]

theorem scalarCubeResidueWeights_empty_one_mean (L : ℕ) (hL : 0 < L) (f : ℤ → ℝ) :
    (scalarCubeResidueWeights Empty L 1 hL (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => le_rfl) (by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL)).mean
      (fun x => f (x none : ℤ)) =
        (∑ k ∈ Finset.Ico 0 (L : ℤ), f k) / (L : ℝ) := by
  rw [scalarCubeResidueWeights_mean]
  calc
    _ = 𝔼 k : coefficientResidueSet L 1 0, f k :=
      Fintype.expect_equiv (emptyScalarCubeResidueEquiv L (fun _ => 1) (fun _ => 0))
        _ _ (fun _ => rfl)
    _ = _ := by
      have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
        ext k
        simp only [coefficientResidueSet, Finset.mem_filter]
        exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
      rw [hr, Fintype.expect_eq_sum_div_card]
      simp [Finset.sum_attach]

noncomputable def normalizedScalarCubeSourceOfIntegerPMF
    (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
    (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal) :
    NormalizedScalarCubeSource Empty where
  length := L
  modulusBound := 1
  length_pos := hL
  modulus := fun _ => 1
  residue := fun _ => 0
  modulus_pos := fun _ => by norm_num
  modulus_le := fun _ => le_rfl
  size := by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL
  weight := w
  weightBound := B
  weightLipschitz := T
  weightBound_pos := hB
  weight_range := hw
  weight_lipschitz := hLip
  normalized := by
    have he (x : IntegerScalarCubeBox Empty L) :
        w (fun i => (x i : ℝ) / L) = w (fun _ => (x none : ℝ) / L) := by
      congr 1
      funext i
      cases i with
      | none => rfl
      | some e => exact e.elim
    simp only [he]
    refine (scalarCubeResidueWeights_empty_one_mean L hL
      (fun k => w (fun _ => (k : ℝ) / L))).trans ?_
    simp_rw [hgrid]
    rw [← Finset.mul_sum, pmf_interval_toReal_mass L p hs, mul_one]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hL))

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

end IntegerSourceLaw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

noncomputable def signedSplitCoordinates (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F) :
    E ≃ₗ[R] (J → R) × (I → R) :=
  (splitSurjectionEquiv q s hs).symm.trans
    ((bK.equivFun.prodCongr bI.equivFun).trans
      ((LinearEquiv.prodComm R (I → R) (J → R)).trans
        ((LinearEquiv.neg R : (J → R) ≃ₗ[R] (J → R)).prodCongr
          (LinearEquiv.refl R (I → R)))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def zeroScalarCubeIntervalEquiv (α : Type*) [Fintype α]
    [DecidableEq α] [IsEmpty α] (L : ℕ) :
    ↥(integerScalarCubeSet α L) ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := by
    have h0 := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_Ico.mpr h0⟩
  invFun z := by
    have hz := Finset.mem_Ico.mp z.property
    let x : IntegerScalarCubeBox α L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hz.2⟩⟩
    refine ⟨x, (mem_integerScalarCubeSet L x).mpr ?_⟩
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hz
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact isEmptyElim a
  right_inv z := by apply Subtype.ext; rfl

variable {D α : Type*} [Fintype D] [DecidableEq D]
variable [Fintype α] [DecidableEq α] [IsEmpty α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBox
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

noncomputable def minkowskiSecondConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n * (n - 1) / 2)

@[simp] theorem minkowskiSecondConstant_zero : minkowskiSecondConstant 0 = 1 := by
  simp [minkowskiSecondConstant]

@[simp] theorem minkowskiSecondConstant_one : minkowskiSecondConstant 1 = 1 := by
  simp [minkowskiSecondConstant]

theorem minkowskiSecondConstant_nonneg (n : ℕ) :
    0 ≤ minkowskiSecondConstant n := by
  exact pow_nonneg (by norm_num) _

theorem exists_shortest_nonzero_of_basis {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ,
      v ∈ Submodule.span ℤ (Set.range b) ∧ v ≠ 0 ∧
        ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  classical
  let e : Fin (n + 1) := 0
  have hbe_mem : b e ∈ Submodule.span ℤ (Set.range b) :=
    Submodule.subset_span ⟨e, rfl⟩
  have hbe_ne : b e ≠ 0 := b.ne_zero e
  let S : Set (Fin (n + 1) → ℝ) :=
    Metric.closedBall 0 ‖b e‖ ∩ Submodule.span ℤ (Set.range b)
  have hSfin : S.Finite := by
    exact ZSpan.setFinite_inter b Metric.isBounded_closedBall
  let T : Set (Fin (n + 1) → ℝ) := {x ∈ S | x ≠ 0}
  have hTfin : T.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hbeS : b e ∈ S := by
    refine ⟨?_, hbe_mem⟩
    simp
  have hTne : T.Nonempty := ⟨b e, hbeS, hbe_ne⟩
  obtain ⟨v, hvT, hvmin⟩ := Set.exists_min_image T norm hTfin hTne
  refine ⟨v, hvT.1.2, hvT.2, ?_⟩
  intro x hxL hx0
  by_cases hxle : ‖x‖ ≤ ‖b e‖
  · exact hvmin x ⟨⟨by simpa [Metric.mem_closedBall] using hxle, hxL⟩, hx0⟩
  · have hvle : ‖v‖ ≤ ‖b e‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvT.1.1
    exact hvle.trans (le_of_not_ge hxle)

theorem abs_det_zspan_basis_eq {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    |(Matrix.of (((↑) : span ℤ (Set.range b) → (Fin n → ℝ)) ∘ B)).det| =
      |(Matrix.of b).det| := by
  let L : Submodule ℤ (Fin n → ℝ) := span ℤ (Set.range b)
  have hB := ZLattice.covolume_eq_det L B
  have hb := ZLattice.covolume_eq_det L
    (Erdos3.BohrLattice.PrimitiveExtension.zspanBasis b)
  calc
    |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B)).det| =
        ZLattice.covolume L := hB.symm
    _ = |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘
        Erdos3.BohrLattice.PrimitiveExtension.zspanBasis b)).det| := hb
    _ = |(Matrix.of b).det| := by
      congr 2
      ext i j
      simp [L]

def intCastVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (z i : ℝ)

@[simp] theorem intCastVec_zero {n : ℕ} :
    intCastVec (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_add {n : ℕ} (z w : Fin n → ℤ) :
    intCastVec (z + w) = intCastVec z + intCastVec w := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_smul {n : ℕ} (a : ℤ) (z : Fin n → ℤ) :
    intCastVec (a • z) = (a : ℝ) • intCastVec z := by
  funext i
  simp [intCastVec]

theorem mem_realBox_const_iff_norm_le {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    x ∈ realBox (fun _ ↦ s) ↔ ‖x‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  constructor
  · intro hx i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.1
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.2

noncomputable def roundedCoefficient (a : ℝ) : ℤ := round a

theorem abs_sub_roundedCoefficient_le_half (a : ℝ) :
    |a - (roundedCoefficient a : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [roundedCoefficient] using abs_sub_round a

noncomputable def deleteProjection {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ x (h.succAbove i) - (x h / v h) * v (h.succAbove i)

noncomputable def deleteProjectionLinear {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := deleteProjection h v
  map_add' x y := by
    funext i
    simp only [deleteProjection, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp [deleteProjection]
    ring

@[simp] theorem deleteProjectionLinear_apply {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) :
    deleteProjectionLinear h v x = deleteProjection h v x := rfl

theorem deleteProjection_add_smul {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (a : ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v (x + a • v) = deleteProjection h v x := by
  funext i
  simp only [deleteProjection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem deleteProjection_self {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v v = 0 := by
  funext i
  simp [deleteProjection, hvh]

theorem abs_apply_le_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp (le_refl ‖x‖) i
  simpa only [Real.norm_eq_abs] using hi

theorem reducedLift_apply_le {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (t a : ℝ)
    (hh : |v h| = ‖v‖) (hvh : v h ≠ 0)
    (ha : |x h / v h + a| ≤ (1 : ℝ) / 2)
    (hx : ‖deleteProjection h v x‖ ≤ t) :
    ‖x + a • v‖ ≤ t + ‖v‖ / 2 := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hx
  rw [pi_norm_le_iff_of_nonneg (add_nonneg ht (by positivity))]
  rw [h.forall_iff_succAbove]
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have heq : x h + a * v h = (x h / v h + a) * v h := by
      field_simp
    rw [heq, abs_mul, hh]
    calc
      |x h / v h + a| * ‖v‖ ≤ ((1 : ℝ) / 2) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg v)
      _ ≤ t + ‖v‖ / 2 := by linarith
  · intro j
    have hproj : |deleteProjection h v x j| ≤ t := by
      simpa only [Real.norm_eq_abs] using
        (abs_apply_le_norm (deleteProjection h v x) j).trans hx
    have hv : |v (h.succAbove j)| ≤ ‖v‖ :=
      abs_apply_le_norm v (h.succAbove j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hdecomp : x (h.succAbove j) + a * v (h.succAbove j) =
        deleteProjection h v x j +
          (x h / v h + a) * v (h.succAbove j) := by
      rw [deleteProjection]
      ring
    rw [hdecomp]
    calc
      |deleteProjection h v x j + (x h / v h + a) * v (h.succAbove j)| ≤
          |deleteProjection h v x j| +
            |x h / v h + a| * |v (h.succAbove j)| := by
            simpa only [abs_mul] using
              abs_add_le (deleteProjection h v x j)
                ((x h / v h + a) * v (h.succAbove j))
      _ ≤ t + ((1 : ℝ) / 2) * ‖v‖ := by
        exact add_le_add hproj
          (mul_le_mul ha hv (abs_nonneg _) (by norm_num))
      _ = t + ‖v‖ / 2 := by ring

noncomputable def tailShear {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦
    if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -(B h j / B h 0)
    else if i = j then 1 else 0

@[simp] theorem tailShear_apply_zero_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    tailShear h B 0 0 = 1 := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) :
    tailShear h B i.succ 0 = 0 := by simp [tailShear]

@[simp] theorem tailShear_apply_zero_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin n) :
    tailShear h B 0 j.succ = -(B h j.succ / B h 0) := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin n) :
    tailShear h B i.succ j.succ = if i = j then 1 else 0 := by
  simp [tailShear]

theorem tailShear_det {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (tailShear h B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [tailShear]
    · simp [tailShear, hi]
  · intro i j hji
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    have hij : i ≠ j := ne_of_gt hji
    simp [tailShear, hi0, hij]

noncomputable def projectedTail {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ B (h.succAbove i) j.succ -
    (B h j.succ / B h 0) * B (h.succAbove i) 0

theorem mul_tailShear_apply_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (B * tailShear h B) i 0 = B i 0 := by
  simp [Matrix.mul_apply, tailShear]

theorem mul_tailShear_apply_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (j : Fin n) :
    (B * tailShear h B) i j.succ =
      B i j.succ - (B h j.succ / B h 0) * B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShear]
  ring

theorem mul_tailShear_pivot_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (j : Fin n) :
    (B * tailShear h B) h j.succ = 0 := by
  rw [mul_tailShear_apply_succ]
  field_simp
  ring

theorem mul_tailShear_minor {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (B * tailShear h B).submatrix h.succAbove Fin.succ = projectedTail h B := by
  ext i j
  simp [projectedTail, mul_tailShear_apply_succ]

theorem abs_det_eq_abs_pivot_mul_abs_det_projectedTail {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B h 0 ≠ 0) :
    |B.det| = |B h 0| * |(projectedTail h B).det| := by
  have hdetC : (B * tailShear h B).det = B.det := by
    simp [Matrix.det_mul, tailShear_det]
  have hminor :
      (B * tailShear h B).submatrix h.succAbove (Fin.succAbove 0) =
        projectedTail h B := by
    simpa using mul_tailShear_minor h B
  have hLaplace := Matrix.det_succ_row (B * tailShear h B) h
  rw [Fin.sum_univ_succ] at hLaplace
  rw [mul_tailShear_apply_zero] at hLaplace
  simp_rw [mul_tailShear_pivot_succ h B hB] at hLaplace
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hLaplace
  rw [hdetC] at hLaplace
  rw [hminor] at hLaplace
  rw [hLaplace, abs_mul, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MinkowskiSecondBoxBasis
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module

theorem projectedTail_det_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    (projectedTail h B).det ≠ 0 := by
  intro hq
  have habs := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h B hB
  rw [hq, abs_zero, mul_zero] at habs
  exact hdet (abs_eq_zero.mp habs)

noncomputable def projectedTailBasis {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (projectedTail h B).col
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (projectedTail_det_ne_zero h B hdet hB))
    (by simp)

@[simp] theorem projectedTailBasis_apply {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) (j : Fin n) :
    projectedTailBasis h B hdet hB j = (projectedTail h B).col j := by
  simp [projectedTailBasis]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

def rawTailLift {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVec z))

theorem deleteProjection_rawTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (rawTailLift B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  funext i
  simp only [deleteProjection, rawTailLift, Matrix.mulVec, dotProduct,
    projectedTail]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
    zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def matrixBasis {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] theorem matrixBasis_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasis D hD j = fun i ↦ D i j := by
  ext i
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

theorem minkowskiSecondConstant_succ (n : ℕ) :
    minkowskiSecondConstant (n + 1) =
      (2 : ℝ) ^ n * minkowskiSecondConstant n := by
  unfold minkowskiSecondConstant
  have he : (n + 1) * ((n + 1) - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right]
    simp [Nat.choose_succ_succ]
  rw [he, pow_add]

theorem exists_abs_apply_eq_norm {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∃ h, |x h| = ‖x‖ := by
  classical
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    Finset.univ_nonempty
  refine ⟨h, le_antisymm (abs_apply_le_norm x h) ?_⟩
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg (x h))]
  intro i
  simpa only [Real.norm_eq_abs] using hh i (Finset.mem_univ i)

theorem realBox_smul_one_eq_const {n : ℕ} (s : ℝ) :
    realBox (s • (fun _ : Fin n ↦ (1 : ℝ))) = realBox (fun _ ↦ s) := by
  congr 1
  funext i
  simp

theorem cube_has_successiveProductCertificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      Nonempty (SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|)) := by
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
        product_le := ?_ }⟩
      simp [minkowskiSecondConstant]
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
      obtain ⟨cq⟩ := ih qB
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
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }⟩
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

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledSectionGram
namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_injective_map_basis
    {ι V E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : V →ₗ[ℝ] E) (hf : Function.Injective f) (b₀ b₁ : Basis ι ℝ V) :
    (Matrix.gram ℝ (fun i => f (b₁ i))).det =
      (b₀.det b₁) ^ 2 * (Matrix.gram ℝ (fun i => f (b₀ i))).det := by
  let e := LinearEquiv.ofInjective f hf
  have h := gram_det_basis_change (b₀.map e) (fun i => e (b₁ i))
  have hd : (b₀.map e).det (fun i => e (b₁ i)) = b₀.det b₁ := by
    rw [Basis.det_map]
    apply congrArg b₀.det
    funext i
    exact e.symm_apply_apply (b₁ i)
  have h₀ : Matrix.gram ℝ (b₀.map e) = Matrix.gram ℝ (fun i => f (b₀ i)) := by
    ext i j
    simp only [Matrix.gram_apply, Basis.map_apply]
    rfl
  have h₁ : Matrix.gram ℝ (fun i => e (b₁ i)) = Matrix.gram ℝ (fun i => f (b₁ i)) := by
    ext i j
    rfl
  rw [hd, h₀, h₁] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open Module

theorem coordinateScaleEquiv_basis_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℝ) (hT : ∀ i, T i ≠ 0) :
    (Pi.basisFun ℝ ι).det ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = ∏ i, T i := by
  rw [Pi.basisFun_det_apply]
  have he : Matrix.of ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = Matrix.diagonal T := by
    ext i j
    by_cases hij : i = j <;>
      simp [Basis.map_apply, coordinateScaleEquiv_apply, Pi.basisFun_apply, hij]
  rw [he, Matrix.det_diagonal]

theorem scaled_section_gram_sqrt {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (hL : Function.Injective L)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    Real.sqrt (Matrix.gram ℝ (fun i => L (coordinateScaleEquiv T (fun j => (hT j).ne')
      (Pi.basisFun ℝ ι i)))).det =
      (∏ i, T i) * Real.sqrt (Matrix.gram ℝ (fun i => L (Pi.basisFun ℝ ι i))).det := by
  have h := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι)
    ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T (fun j => (hT j).ne')))
  rw [coordinateScaleEquiv_basis_det] at h
  have he := congrArg Real.sqrt h
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Finset.prod_nonneg (fun i _ => (hT i).le))] at he
  simpa only [Basis.map_apply] using he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MinkowskiSecondInduction
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiDiagonalNormalization

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Submodule Module

noncomputable section

def divideCoordinates {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i / r i
  invFun x i := x i * r i
  left_inv x := by
    funext i
    exact div_mul_cancel₀ (x i) (hr i).ne'
  right_inv x := by
    funext i
    exact mul_div_cancel_right₀ (x i) (hr i).ne'
  map_add' x y := by
    funext i
    exact add_div (x i) (y i) (r i)
  map_smul' a x := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]

@[simp] theorem divideCoordinates_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    divideCoordinates r hr x i = x i / r i := rfl

@[simp] theorem divideCoordinates_symm_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    (divideCoordinates r hr).symm x i = x i * r i := rfl

def normalizedBasis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  b.map (divideCoordinates r hr)

@[simp] theorem normalizedBasis_apply {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (j i : Fin n) :
    normalizedBasis b r hr j i = b j i / r i := by
  simp [normalizedBasis]

theorem mem_realBox_mul_iff {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (s : ℝ) (_hs : 0 ≤ s) (x : Fin n → ℝ) :
    x ∈ realBox (fun i ↦ s * r i) ↔
      divideCoordinates r hr x ∈ realBox (fun _ ↦ s) := by
  constructor
  · intro hx
    constructor
    · intro i
      apply (le_div_iff₀ (hr i)).2
      simpa [mul_comm] using hx.1 i
    · intro i
      apply (div_le_iff₀ (hr i)).2
      simpa [mul_comm] using hx.2 i
  · intro hx
    constructor
    · intro i
      have hi := (le_div_iff₀ (hr i)).1 (hx.1 i)
      simpa [mul_comm] using hi
    · intro i
      have hi := (div_le_iff₀ (hr i)).1 (hx.2 i)
      simpa [mul_comm] using hi

theorem abs_det_normalizedBasis {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    |(Matrix.of (normalizedBasis b r hr)).det| =
      |(Matrix.of b).det| * (∏ i, r i)⁻¹ := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ (r i)⁻¹)
  have hmatrix : Matrix.of (normalizedBasis b r hr) = Matrix.of b * D := by
    ext j i
    change b j i / r i = ∑ k, b j k * D k i
    rw [Finset.sum_eq_single i]
    · simp [D, div_eq_mul_inv]
    · intro k _ hki
      simp [D, hki]
    · simp
  have hdetD : D.det = (∏ i, r i)⁻¹ := by
    simp [D, Finset.prod_inv_distrib]
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  rw [hmatrix, Matrix.det_mul, hdetD, abs_mul, abs_inv, abs_of_pos hprod]

theorem divideCoordinates_mem_span_iff {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) :
    divideCoordinates r hr x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔
      x ∈ Submodule.span ℤ (Set.range b) := by
  let e : (Fin n → ℝ) ≃ₗ[ℤ] (Fin n → ℝ) :=
    (divideCoordinates r hr).restrictScalars ℤ
  have hrange : Set.range (normalizedBasis b r hr) = e '' Set.range b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      simp [e, normalizedBasis]
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [e, normalizedBasis]
  change e x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔ _
  rw [hrange]
  exact Submodule.apply_mem_span_image_iff_mem_span e.injective

end

end Erdos3.BohrLattice.MinkowskiDiagonalNormalization

end

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate _root_.Set Module Submodule

noncomputable section

theorem realBox_has_minkowskiSecondCertificate {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (BoxCertificate.SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range b)).toAddSubgroup r
      (minkowskiSecondConstant n * |(Matrix.of b).det| *
        (∏ i, r i)⁻¹)) := by
  classical
  open Erdos3.BohrLattice.MinkowskiDiagonalNormalization in
    let b' := normalizedBasis b r hr
    let e := divideCoordinates r hr
    obtain ⟨C⟩ := cube_has_successiveProductCertificate b'
    let point : Fin n → Fin n → ℝ := fun i ↦ e.symm (C.point i)
    refine ⟨{
      scale := C.scale
      point := point
      scale_nonneg := C.scale_nonneg
      point_mem := ?_
      independent := ?_
      mem_scaledBox := ?_
      product_le := ?_ }⟩
    · intro i
      change point i ∈ Submodule.span ℤ (Set.range b)
      apply (divideCoordinates_mem_span_iff b r hr (point i)).mp
      simpa [point, e, b'] using C.point_mem i
    · apply LinearIndependent.of_comp e.toLinearMap
      convert C.independent using 1
      funext i
      simp [point, e]
    · intro i
      change point i ∈ realBox (fun j ↦ C.scale i * r j)
      apply (mem_realBox_mul_iff r hr (C.scale i) (C.scale_nonneg i) (point i)).mpr
      have hi : C.point i ∈ realBox (fun _ ↦ C.scale i) := by
        rw [← realBox_smul_one_eq_const]
        exact C.mem_scaledBox i
      simpa [point, e] using hi
    · simpa [b', abs_det_normalizedBasis, mul_assoc] using C.product_le

end

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalAxisInterpolation (h K L : ℕ) (γ : ℝ) : ℝ → ℝ :=
  if L^h < K then principalIntegerInterpolation K ((L : ℝ)^h) γ
  else integerMassTent K (inactivePrincipalCoefficient K (inactiveDenominator γ))

noncomputable def principalAxisInterpolationCap (h L : ℕ) (γ : ℝ) : ℝ :=
  max (4 * (L : ℝ)^h / γ) ((L : ℝ)^h)

noncomputable def principalAxisInterpolationLip (h L : ℕ) (γ : ℝ) : ℝ :=
  max (8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2)
    (2 * ((L : ℝ)^h)^2)

theorem principalAxisInterpolation_spec (h K L : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K) :
    IsIntegerMassInterpolation K (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap)
      (principalAxisInterpolationCap h L γ) (principalAxisInterpolationLip h L γ)
      (principalAxisInterpolation h K L γ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases ha : L^h < K
  · simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    exact (principalIntegerInterpolation_spec K ((L : ℝ)^h) γ hKr
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))).mono
      (le_max_left _ _) (le_max_left _ _)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^h := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte,
      inactivePrincipalPMF]
    apply (integerMassTent_spec K hKr (inactivePrincipalCoefficient K (inactiveDenominator γ))).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def kernelCoefficientDensity {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (C : Matrix I N ℤ) (T : N → ℝ) (c w : J ⊕ N → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity
    (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
    (splitFreeColumns
      (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
      (matrixSupCLM (normalizedIntegerColumns C T P)))
    (splitFreeProfile
      (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
      (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialAffineLaw
namespace OAI

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
variable (hgap : L^h < K → (principalSamplingGapRatio γ*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ ε*L)
variable (ha : L^h < K) (henormous : L^(s+1) < K)
variable (hconst : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K)
variable (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
variable (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (L : ℝ)^h)

local notation "centers" => coefficientProfileCenter P γ
local notation "widths" => coefficientProfileWidth P j₀ ρ γ ε
local notation "scales" => fun j => (K : ℝ)/monomialScale T (e j)

include hh hL hT hTL he hγ hε hgap hεL ha henormous hconst he₀ hprincipal in
omit [Fintype J] in
theorem integerPolynomialProfile_width_large (j : J) :
    8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)) := by
  classical
  by_cases hj : j = j₀
  · subst j
    simpa only [coefficientProfileWidth, ↓reduceIte, he₀, monomialScale_zero, div_one] using hconst
  · by_cases hp : j ∈ P
    · simpa only [coefficientProfileWidth, hj, hp, ↓reduceIte, hprincipal j hp] using
        integerAxisPrincipal_width hh hL hγ (hgap ha)
    · simp only [coefficientProfileWidth, hj, hp, ↓reduceIte]
      calc
        _ ≤ (ε/monomialScale T (e j))*(K : ℝ) :=
          integerAxisTail_width T hT hL hTL hε hεL (e j) (he j) henormous
        _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I]

def affineCubeTuple (lower width : J → ℝ) (x : J → Option I → ℝ) : J → Option I → ℝ :=
  fun j i => (if i = none then lower j else 0) + width j * x j i

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

noncomputable def affineKernelContinuousPoint (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (x : G → Option Empty → ℝ) : G → ℝ :=
  fun g => (lower g + step * ((H g - 1 : ℕ) : ℝ) * x g none) / S

noncomputable def affineKernelDiscretePoint (lower : G → ℝ) (step S : ℝ) {H : G → ℕ}
    (z : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → ℝ :=
  fun g => (lower g + step * (z g none : ℝ)) / S

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCube_progression {I : Type*} [Fintype I] [DecidableEq I]
    {L H step : ℕ} (c : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : Option I → ℤ) (hz : IntegerScalarCube H z) :
    IntegerScalarCube L (fun i => (if i = none then c else 0) + (step : ℤ) * z i) := by
  intro t
  have ht : c + (step : ℤ) * integerScalarCubeValue z t ∈
      integerProgressionSupport c (step : ℤ) H := by
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨integerScalarCubeValue z t, Finset.mem_Ico.mpr (hz t), ?_⟩
    change (step : ℤ) * integerScalarCubeValue z t = _
    ring
  have he : integerScalarCubeValue
      (fun i => (if i = none then c else 0) + (step : ℤ) * z i) t =
      c + (step : ℤ) * integerScalarCubeValue z t := by
    simp only [integerScalarCubeValue, ite_true, Option.some_ne_none, ite_false,
      zero_add, Finset.mul_sum, mul_add]
    ring
  rw [he]
  exact Finset.mem_Ico.mp (hsubset ht)

noncomputable def containedProgressionCubeMap (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) : IntegerScalarCubeBox I L :=
  if hz : IntegerScalarCube H (fun i => (z i : ℤ)) then
    fun i => ⟨(if i = none then c else 0) + (step : ℤ) * (z i : ℤ),
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates
        (integerScalarCube_progression c hsubset _ hz) i).1.le,
        (integerScalarCube_coordinates (integerScalarCube_progression c hsubset _ hz) i).2⟩⟩
  else fun _ => ⟨0, Finset.mem_Ico.mpr (by constructor <;> omega)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointProductiveMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

noncomputable def centeredFiniteProbabilityMeasure : Measure (C × Ω) :=
  realDensityMeasure (μ.prod Measure.count) (centeredFiniteWeightDensity law)

include hweight

theorem centeredFiniteProbabilityMeasure_probability [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) :=
  realDensityMeasure_probability _ _ (centeredFiniteWeightDensity_integrable law hweight μ)
    (centeredFiniteWeightDensity_nonneg law) (centeredFiniteWeightDensity_integral law hweight μ)

theorem centeredFiniteProbabilityMeasure_ae_positive_weight :
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, 0 < (law z.1).weight z.2 := by
  exact realDensityMeasure_ae_of_support (μ.prod Measure.count) (centeredFiniteWeightDensity law)
    (centeredFiniteWeightDensity_measurable law hweight) _ (fun z hz =>
      lt_of_le_of_ne (centeredFiniteWeightDensity_nonneg law z) (Ne.symm hz))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_weight_integrable [IsFiniteMeasure μ] (x : Ω) :
    Integrable (fun c => (law c).weight x) μ :=
  Integrable.of_bound (hweight x).aestronglyMeasurable 1 (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

omit μ [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_measurable (f : C → Ω → ℝ)
    (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => (law c).mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hweight x).mul (hf x))

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mean_integrable (f : C → Ω → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => (law c).mean (f c)) μ := by
  apply integrable_finsetSum
  intro x _
  exact (hf x).bdd_mul (hweight x).aestronglyMeasurable (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

theorem centeredFiniteProbabilityMeasure_integral [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Integrable f (centeredFiniteProbabilityMeasure μ law)) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  have hi := (integrable_withDensity_iff_integrable_smul'
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal
    (ae_of_all (μ.prod Measure.count) (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simp only [ENNReal.toReal_ofReal (centeredFiniteWeightDensity_nonneg law _), smul_eq_mul] at hi
  rw [centeredFiniteProbabilityMeasure, realDensityMeasure_integral _ _
    (centeredFiniteWeightDensity_measurable law hweight) (centeredFiniteWeightDensity_nonneg law),
    integral_prod _ hi]
  simp only [integral_count, centeredFiniteWeightDensity, FiniteProbabilityWeights.mean]

theorem centeredFiniteProbabilityMeasure_integral_bounded [IsProbabilityMeasure μ]
    (f : C × Ω → ℝ) (hf : Measurable f) {M : ℝ} (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ z, f z ∂centeredFiniteProbabilityMeasure μ law) =
      ∫ c, (law c).mean (fun x => f (c, x)) ∂μ := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  exact centeredFiniteProbabilityMeasure_integral μ law hweight f
    (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hbound))

theorem centeredFiniteProbabilityMeasure_real_event [IsProbabilityMeasure μ]
    (event : Set (C × Ω)) (hevent : MeasurableSet event) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c, x) ∈ event then 1 else 0) ∂μ := by
  rw [← integral_indicator_one (μ := centeredFiniteProbabilityMeasure μ law) hevent]
  have hmeas : Measurable (event.indicator (1 : C × Ω → ℝ)) :=
    measurable_const.indicator hevent
  have hbound (z : C × Ω) : ‖event.indicator (1 : C × Ω → ℝ) z‖ ≤ 1 := by
    by_cases hz : z ∈ event <;> simp [hz]
  rw [centeredFiniteProbabilityMeasure_integral_bounded μ law hweight _ hmeas hbound]
  rfl

theorem centeredFiniteProbabilityMeasure_real_finset_fiber [IsProbabilityMeasure μ]
    (F : Finset Ω) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F} =
      ∫ c, (law c).mass F ∂μ := by
  have hevent : MeasurableSet {z : C × Ω | z.2 ∈ F} :=
    (Finset.measurableSet F).preimage measurable_snd
  have h := centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent
  refine h.trans (integral_congr_ae (ae_of_all μ (fun c => ?_)))
  calc
    _ = (law c).mean (fun x => if x ∈ F then 1 else 0) := by
      apply congrArg (law c).mean
      funext x
      by_cases hx : x ∈ F <;> simp [hx]
    _ = _ := (law c).mean_indicator F

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

noncomputable def integratedFiniteProbabilityWeights : FiniteProbabilityWeights Ω where
  weight x := ∫ c, (law c).weight x ∂μ
  nonneg x := integral_nonneg (fun c => (law c).nonneg x)
  total := by
    rw [← integral_finsetSum _ (fun x _ => centeredFinite_weight_integrable μ law hweight x)]
    simp only [(law _).total, integral_const, probReal_univ, smul_eq_mul, one_mul]

@[simp] theorem integratedFiniteProbabilityWeights_weight (x : Ω) :
    (integratedFiniteProbabilityWeights μ law hweight).weight x =
      ∫ c, (law c).weight x ∂μ := rfl

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

theorem centeredFiniteProbabilityMeasure_productive_family
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (productive : Finset Ω) (Qgood : C × Ω → Prop)
    (hgood : ∀ c z, 0 < (law c).weight z → Qgood (c,z))
    {τ : ℝ} (hmass : τ ≤ ∫ c, (law c).mass productive ∂μ) :
    IsProbabilityMeasure (centeredFiniteProbabilityMeasure μ law) ∧
      MeasurableSet {z : C × Ω | z.2 ∈ productive} ∧
      τ ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Qgood z := by
  refine ⟨centeredFiniteProbabilityMeasure_probability μ law hweight,
    (Finset.measurableSet productive).preimage measurable_snd, ?_, ?_⟩
  · rw [centeredFiniteProbabilityMeasure_real_finset_fiber μ law hweight]
    exact hmass
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight] with z hz
    exact hgood z.1 z.2 hz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
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

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

noncomputable def containedProgressionTupleMap (v : PrincipalIntegerTuples B h α H) :
    PrincipalIntegerTuples B h α L :=
  fun j => containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (v j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

noncomputable def containedProgressionCubeLaw :
    FiniteProbabilityWeights (∀ k, IntegerScalarCubeBox α (L k)) :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).fiberLaw
    (fun y k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

noncomputable def nearestIntegerLift {m : ℕ} (x : Fin m → ℝ) : Fin m → ℤ :=
  fun i => round (x i)

theorem nearestIntegerLift_close {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    |x i - (nearestIntegerLift x i : ℝ)| ≤ 1 / 2 := abs_sub_round (x i)

namespace PatchKernel

theorem buffered_lift_unique {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (β γ : Fin m → ℤ) (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hγ : Ψ.value (fun i => x i - (γ i : ℝ)) ≠ 0) : γ = β := by
  apply (constantSlots x).integer_unique (b := γ) (c := β) (by norm_num : (1 : ℝ) / 4 + 1 / 2 < 1)
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using Ψ.support _ hγ i
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using hβ i

end PatchKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedIntervalApproximation
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def maskedIntervalApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) : ℂ :=
  ∑ a : S → ZMod m, ∑ k : S → Fin (intervalSiteCount B r),
    (M a * F (fun i => intervalSiteCenter B r (k i))) *
      ((∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i) : ℝ) : ℂ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

def scalarTupleColumn {I : Type*} (c : ℤ) (x : Option I → ℤ) : (Unit ⊕ I) → ℤ :=
  Sum.elim (fun _ => c + x none) (fun i => x (some i))

def scalarTupleSpatialColumns {I N : Type*} (T : N → ℕ) (c : N → ℤ)
    (x : ∀ j, IntegerScalarCubeBox I (T j)) : Matrix (Unit ⊕ I) N ℤ :=
  tupleColumnMatrix (fun j x => scalarTupleColumn (c j) (fun i => (x i : ℤ))) x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

def principalSpatialColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) : Matrix (Unit ⊕ α) N ℤ :=
  scalarTupleSpatialColumns (fun n => L (index n)) c (fun n => y (index n))

def principalSpatialResidueColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : Matrix (Unit ⊕ α) N (ZMod m) :=
  fun i n => Sum.elim (fun _ => (c n : ZMod m)+r (index n) none)
    (fun j => r (index n) (some j)) i

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

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

end Erdos3

end

section

namespace Erdos3

def kernelPeriodCandidate {B : ℕ} (degree : ℕ) (a : Fin B) : ℕ :=
  (a.val + 1) ^ degree

theorem kernelPeriodCandidate_pos {B : ℕ} (degree : ℕ) (a : Fin B) :
    0 < kernelPeriodCandidate degree a :=
  pow_pos (Nat.succ_pos _) _

instance kernelPeriodCandidate_neZero {B : ℕ} (degree : ℕ) (a : Fin B) :
    NeZero (kernelPeriodCandidate degree a) :=
  ⟨(kernelPeriodCandidate_pos degree a).ne'⟩

theorem kernelPeriodCandidate_le {B : ℕ} (degree : ℕ) (a : Fin B) :
    kernelPeriodCandidate degree a ≤ B ^ degree :=
  Nat.pow_le_pow_left (Nat.succ_le_of_lt a.isLt) _

theorem kernelPeriodCandidate_le_exp {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) (degree : ℕ) (a : Fin B) :
    (kernelPeriodCandidate degree a : ℝ) ≤ Real.exp (degree * p) := by
  calc
    _ ≤ (B : ℝ) ^ degree := by exact_mod_cast kernelPeriodCandidate_le degree a
    _ ≤ (Real.exp p) ^ degree := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := (Real.exp_nat_mul p degree).symm

end Erdos3

end

section

namespace Erdos3

noncomputable def goodKernelUniformCandidate {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (_height : ℕ) : Fin B :=
  ⟨Classical.choose hx.2 - 1, by
    have h := Classical.choose_spec hx.2
    omega⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def kernelInverseLog (q n j d : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ) + (j : ℝ)^2 + (j - 1 : ℕ) * ((q : ℝ) * (d + 1)) +
    j * (d * n + d * ((q : ℝ)^2 + q + p + 2))

def kernelGeometryLog (q n j k d : ℕ) (p : ℝ) : ℝ :=
  p + j + k + (q : ℝ) * (d + 1) + kernelInverseLog q n j d p

noncomputable def kernelRowOutputLog (q n j k u d : ℕ) (p : ℝ) : ℝ :=
  let P := kernelGeometryLog q n j k d p
  (j : ℝ)^2 + (j + 1) * P + affineProfileLogBound k p + k * (P + 1) +
    jetOutputRadiusLog q u d P + 1

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
variable [∀ j, DecidableEq (R j)]
variable (p : ∀ j, FiniteProbabilityWeights (X j))
variable (F : ∀ j, X j → R j) (r : ∀ j, R j)
variable (hcell : 0 < (pi p).mass
  (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)))

include hcell in
theorem coordinate_fiber_mass_pos (j : J) :
    0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j)) := by
  have hp : 0 < ∏ k, (p k).mass (Finset.univ.filter (fun x => F k x = r k)) := by
    simpa only [pi_fiber_mass] using hcell
  have hn := Finset.prod_ne_zero_iff.mp hp.ne' j (Finset.mem_univ j)
  exact lt_of_le_of_ne ((p j).mass_nonneg _) hn.symm

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

noncomputable def containedSupportedProgressionLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  (weights).fiberLaw tupleMap

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def liftInterleaving (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    SlotInterleaving D E :=
  SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono

noncomputable def insertLifts (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    PolynomialPatch σ s (D + E) :=
  let I := A.liftInterleaving B
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.insertLifts B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem insertLifts_lip (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E) :
    (A.insertLifts B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtLiftPolynomial : MvPolynomial (J ⊕ Fin 1) ℝ :=
  (∑ j, (crtIntegerCoefficient N hN j : ℝ) • X (Sum.inl j)) -
    ((∏ j, N j : ℕ) : ℝ) • X (Sum.inr 0)

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_degree :
    crtLiftPolynomial N hN ∈
      weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1 := by
  apply (weightedSupportLE _ _).sub_mem
  · apply Submodule.sum_mem
    intro j _
    apply (weightedSupportLE _ _).smul_mem
    exact weightedSupportLE_X _ (Sum.inl j)
  · exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ (Sum.inr 0))

namespace RepresentativeWindow

variable (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) {d : ℕ}

noncomputable def composeCRTPatch (P : PolynomialPatch Unit s d) : PolynomialPatch J s (1 + d) :=
  (w.crtPatch N hN s hs).insertLifts
    (P.weightedParameters.reparam
      (q := Sum.elim (fun _ : J => 1) (w.crtPatch N hN s hs).weight)
      (fun _ : Unit => crtLiftPolynomial N hN)
      (by
        intro _
        change crtLiftPolynomial N hN ∈
          weightedSupportLE (Sum.elim (fun _ : J => 1) (fun _ : Fin 1 => 1)) 1
        exact crtLiftPolynomial_degree N hN))

omit [NeZero (∏ j, N j)] in
@[simp] theorem composeCRTPatch_lip (P : PolynomialPatch Unit s d) :
    (w.composeCRTPatch N hN s hs P).kernel.lip = w.lip + P.kernel.lip := rfl

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLiftInsertion
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ ρ : Type*} {D E s : ℕ}

noncomputable def affineLiftSubstitution (c : ρ → ℝ) (M : ρ → Fin D → ℝ) :
    σ ⊕ ρ → MvPolynomial (σ ⊕ Fin D) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun a => C (c a) + ∑ j, M a j • X (Sum.inr j))

theorem affineLiftSubstitution_degree {p : ρ → ℕ} {w : Fin D → ℕ}
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → w j ≤ p a) (a : σ ⊕ ρ) :
    affineLiftSubstitution c M a ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w)
      (Sum.elim (fun _ : σ => 1) p a) := by
  classical
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr a =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro j _
    by_cases hj : M a j = 0
    · simp only [hj, zero_smul]
      exact (weightedSupportLE _ _).zero_mem
    · exact weightedSupportLE_mono (hM a j hj)
        ((weightedSupportLE _ _).smul_mem (M a j)
          (weightedSupportLE_X (Sum.elim (fun _ : σ => 1) w) (Sum.inr j)))

namespace PolynomialPatch

noncomputable def insertAffineLifts {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) : PolynomialPatch σ s (D + E) :=
  A.insertLifts (B.reparam (affineLiftSubstitution c M) (affineLiftSubstitution_degree c M hM))

@[simp] theorem insertAffineLifts_lip {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) :
    (A.insertAffineLifts B c M hM).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BufferedScalarScoreBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def bufferedScalarScore {Ω : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (u : Ω) : ℝ :=
  (f u - lam) * χ.value (fun i => x u i - (nearestIntegerLift (x u) i : ℝ)) *
    T u (nearestIntegerLift (x u))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

noncomputable def slicedDetectionGainLog (s C count : ℕ) (p q a : ℝ) : ℝ :=
  (5 * p + 20) * count + p + 2 + a + 1 + (2 ^ (s + 1) : ℕ) * (q + C) ^ C

theorem slicedDetectionGainLog_nonneg (s C count : ℕ) {p q a : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ slicedDetectionGainLog s C count p q a := by
  unfold slicedDetectionGainLog
  positivity

theorem exists_slicedDetection_uniform_budget (s C : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p q a : ℝ} {count : ℕ} (G : Type*) [Fintype G],
      0 ≤ D → 0 ≤ p → 0 ≤ q → 0 ≤ a →
      (count : ℝ) ≤ D → (Fintype.card G : ℝ) ≤ D →
      slicedDetectionGainLog s C count p q a ≤ (D + p + q + a + A) ^ A ∧
      scalarKernelLogarithmicBudget (Fin (s + 1)) G
        (slicedDetectionGainLog s C count p q a + p + 4) ≤ (D + p + q + a + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let g : Polynomial ℕ := (5 * X + 20) * X + X + 2 + X + 1 +
    Polynomial.C (2 ^ (s + 1)) * (X + Polynomial.C C) ^ C
  let dim : Polynomial ℕ := Polynomial.C (s + 1)
  let k : Polynomial ℕ := 2 * ((4 + 3 * (X * (dim + 1) * dim)) *
    (16 * (10 + dim + X + X * (dim + 1) + (g + X + 4)) ^ 3 + 2)) + 8
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget (g + k)
  refine ⟨A, hA, ?_⟩
  intro D p q a count G _ hD hp hq ha hcount hG
  let R := D + p + q + a
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hDR : D ≤ R := by dsimp only [R]; linarith
  have hpR : p ≤ R := by dsimp only [R]; linarith
  have hqR : q ≤ R := by dsimp only [R]; linarith
  have haR : a ≤ R := by dsimp only [R]; linarith
  have hcR := hcount.trans hDR
  have hGR := hG.trans hDR
  let gainR := (5 * R + 20) * R + R + 2 + R + 1 + (2 ^ (s + 1) : ℕ) * (R + C) ^ C
  let kernelR := 2 * ((4 + 3 * (R * ((s + 1 : ℕ) + 1) * (s + 1 : ℕ))) *
    (16 * (10 + (s + 1 : ℕ) + R + R * ((s + 1 : ℕ) + 1) + (gainR + R + 4)) ^ 3 + 2)) + 8
  have hgainR : slicedDetectionGainLog s C count p q a ≤ gainR := by
    dsimp only [slicedDetectionGainLog, gainR]
    gcongr
  have hgain0 : 0 ≤ gainR := by dsimp only [gainR]; positivity
  have hk0 : 0 ≤ kernelR := by dsimp only [kernelR]; positivity
  have hgainActual := slicedDetectionGainLog_nonneg s C count hp hq ha
  have hkernelR : scalarKernelLogarithmicBudget (Fin (s + 1)) G
      (slicedDetectionGainLog s C count p q a + p + 4) ≤ kernelR := by
    rw [scalarKernelLogarithmicBudget_eq]
    simp only [Fintype.card_fin]
    dsimp only [kernelR]
    push_cast
    gcongr
  have hbound : gainR + kernelR ≤ (R + A) ^ A := by
    simpa [X, g, k, dim, gainR, kernelR, Polynomial.eval₂_pow] using hb R hR
  exact ⟨hgainR.trans ((le_add_of_nonneg_right hk0).trans hbound),
    hkernelR.trans ((le_add_of_nonneg_left hgain0).trans hbound)⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelComparisonScales
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def kernelFamilyOutputLog {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ) (p : ℝ) : ℝ :=
  1 + ∑ q, kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
    (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

noncomputable def containedProgressionResidueLaw :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) := (weights).fiberLaw tupleMap

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical NNReal

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t)

variable [Fintype D] [DecidableEq D] [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)

local notation "law" => FiniteProbabilityWeights.toPMF (principalResidueWeights B h L hL q hq r hsize)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)
variable (c : B a → NormalizedScalarCubeSource Empty) (rows : Finset (Finset α))
variable (offset : B a → ℤ) (shift : rows → ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerProgressionSupport_subset_iff_fin (L H step : ℕ) (start : ℤ) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) ↔
      ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
        start + (step : ℤ) * t.val < L := by
  constructor
  · intro hs t
    apply Finset.mem_Ico.mp
    apply hs
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨(t.val : ℤ), Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩, ?_⟩
    change (step : ℤ) * t.val = _
    ring
  · intro hi z hz
    rw [integerProgressionSupport, mem_translateSupport] at hz
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
    have hv' := Finset.mem_Ico.mp hv
    let t : Fin H := ⟨v.toNat, by omega⟩
    have ht : (t.val : ℤ) = v := Int.toNat_of_nonneg hv'.1
    have hi' := hi t
    rw [ht] at hi'
    change (step : ℤ) * v = _ at he
    apply Finset.mem_Ico.mpr
    constructor <;> omega

theorem integerProgressionSupport_subset_of_fin (L H step : ℕ) (start : ℤ)
    (hinside : ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
      start + (step : ℤ) * t.val < L) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) :=
  (integerProgressionSupport_subset_iff_fin L H step start).mpr hinside

def finIntegerIntervalEquiv (L : ℕ) :
    Fin L ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun t := ⟨t.val, Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩⟩
  invFun z := ⟨z.val.toNat, by have hz := Finset.mem_Ico.mp z.property; omega⟩
  left_inv t := by apply Fin.ext; simp
  right_inv z := by
    apply Subtype.ext
    change (z.val.toNat : ℤ) = z.val
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp z.property).1

def zeroScalarFinPoint (L : ℕ) (t : Fin L) : IntegerScalarCubeBox Empty L :=
  fun _ => ⟨t.val, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast t.isLt⟩⟩

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

def principalFinTuplePoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty H :=
  fun j => zeroScalarFinPoint (H j) (t j)

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hH : ∀ j, 0 < H j) (P : D → Prop)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : ℕ) (hM : 0 < M)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*}
  [Fintype α]
  [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*}
  [DecidableEq α]
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α) (q : ℕ)

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*}
  [Fintype α]
  [DecidableEq α]
variable (q : ℕ)
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def fixedPathSlicedPerturbationLog (D P Pslice E : ℝ) (m : ℕ) : ℝ :=
  fixedPathPerturbationLog D (P + Pslice) E m

theorem fixedPathSlicedPerturbationLog_nonneg {D P Pslice E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathSlicedPerturbationLog D P Pslice E m :=
  fixedPathPerturbationLog_nonneg hD (add_nonneg hP hPslice) hE m

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedEndpointPerturbationPolynomial
namespace OAI

section

namespace Erdos3

theorem exists_preparedEndpointPerturbation_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
      fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
          (2 * sourceLog + Ecompare + 18) m ∈ Set.Icc 0 ((t + C) ^ C) ∧
        2 * sourceLog + Ecompare + 18 ∈ Set.Icc 0 ((t + C) ^ C) := by
  let Lpoly : Polynomial ℕ := 2 + Polynomial.X ^ 2 + 2 * Polynomial.X
  let Epoly : Polynomial ℕ := 2 * Lpoly + Polynomial.X + 18
  let Qpoly : Polynomial ℕ := 4 * Polynomial.X + 3 * Lpoly + Polynomial.C m + 25
  let Tpoly : Polynomial ℕ :=
    48 * ((3 * Qpoly + 4) * Polynomial.C m + 5 * Qpoly + 10) +
      2 * Qpoly + 2 * Polynomial.C m + 47
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Tpoly + Epoly)
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hprimitive htest hcompare hcost
  let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
  let L := 2 + t ^ 2 + 2 * t
  let E := 2 * L + t + 18
  let Q := 4 * t + 3 * L + m + 25
  let T := 48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47
  have hsource : 0 ≤ sourceLog := by
    dsimp only [sourceLog]
    exact add_nonneg (add_nonneg (by positivity) hprimitive.1) (le_max_left _ _)
  have hsourceL : sourceLog ≤ L := by
    have hsquare := pow_le_pow_left₀ hD.1 hD.2 2
    dsimp only [sourceLog, L]
    rw [max_eq_right htest.1]
    linarith only [hsquare, hprimitive.2, htest.2]
  have hE : 0 ≤ E := by dsimp only [E, L]; positivity
  have hT : 0 ≤ T := by dsimp only [T, Q, L]; positivity
  have hcoarse : 0 ≤ 2 * sourceLog + Ecompare + 18 := by
    linarith only [hsource, hcompare.1]
  have hcoarseE : 2 * sourceLog + Ecompare + 18 ≤ E := by
    dsimp only [E]
    linarith only [hsourceL, hcompare.2]
  have hQ : D + ((D + sourceLog + 4) + (cost + 1)) +
      (2 * sourceLog + Ecompare + 18) + m + 2 ≤ Q := by
    dsimp only [Q]
    linarith only [hsourceL, hD.2, hcost.2, hcompare.2]
  have hQm := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) m)
  have hperturb : fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
      (2 * sourceLog + Ecompare + 18) m ≤ T := by
    dsimp only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, T]
    nlinarith only [hQ, hQm]
  have htotal : T + E ≤ (t + C) ^ C := by
    simpa [Tpoly, Epoly, Qpoly, Lpoly, T, Q, E, L] using hbound t ht
  exact ⟨⟨fixedPathSlicedPerturbationLog_nonneg hD.1
      (by linarith only [hD.1, hsource]) (by linarith only [hcost.1]) hcoarse m,
      hperturb.trans ((le_add_of_nonneg_right hE).trans htotal)⟩,
    ⟨hcoarse, hcoarseE.trans ((le_add_of_nonneg_left hT).trans htotal)⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedRelativeEndpointComparisonBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedRelativeEndpointTestLog (localBudget earlyNative : ℝ) : ℝ :=
  max localBudget (3 * earlyNative + 3)

def preparedRelativeEndpointComparisonLog
    (localBudget earlyNative earlyMass u p cost : ℝ) : ℝ :=
  max (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20) + 2 + cost + cost + 8

def preparedRelativeEndpointSourceLog (D primitiveCap Ptest : ℝ) : ℝ :=
  2 + D ^ 2 + primitiveCap + max 0 Ptest

def preparedRelativeEndpointCoarseLog (D primitiveCap Ptest Ecompare : ℝ) : ℝ :=
  2 * preparedRelativeEndpointSourceLog D primitiveCap Ptest + Ecompare + 18

noncomputable def preparedRelativeEndpointSigmaLog
    (D primitiveCap Ptest Ecompare cost : ℝ) (m : ℕ) : ℝ :=
  fixedPathSlicedPerturbationLog D
    (D + preparedRelativeEndpointSourceLog D primitiveCap Ptest + 4) (cost + 1)
    (preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare) m

theorem exists_preparedRelativeEndpointPerturbationLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈
        Set.Icc 0 ((t + C) ^ C) ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈
        Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedEndpointPerturbation_budget m
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hcap htest hcompare hcost
  exact hbound ht hD hcap htest hcompare hcost

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCyclicEncoding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boxCodeModulus {n : ℕ} (T : Fin n → ℕ) : ℕ := ∏ i, 4 * T i

def boxIntegerCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ :=
  integerRadixHom (fun i => 4 * T i)

def boxCyclicCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ZMod (boxCodeModulus T) :=
  (Int.castAddHom (ZMod (boxCodeModulus T))).comp (boxIntegerCode T)

theorem boxCodeModulus_pos {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    0 < boxCodeModulus T :=
  Finset.prod_pos (fun i _ => Nat.mul_pos (by norm_num) (NeZero.pos (T i)))

instance boxCodeModulus_neZero {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    NeZero (boxCodeModulus T) := ⟨(boxCodeModulus_pos T).ne'⟩

theorem boxCodeModulus_eq {n : ℕ} (T : Fin n → ℕ) :
    boxCodeModulus T = 4 ^ n * ∏ i, T i := by
  simp [boxCodeModulus, Finset.prod_mul_distrib]

theorem boxIntegerCode_bounds {n : ℕ} (T : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : x ∈ integerBox T) :
    0 ≤ boxIntegerCode T x ∧ boxIntegerCode T x < (boxCodeModulus T : ℤ) := by
  apply integerRadixValue_bounds
  intro i
  have h := (mem_integerBox T x).mp hx i
  constructor
  · exact h.1
  · push_cast
    omega

theorem boxCyclicCode_reflectsPairSums {n : ℕ} (T : Fin n → ℕ) :
    ReflectsPairSums (boxCyclicCode T) (integerBox T : Set (Fin n → ℤ)) := by
  intro a ha b hb c hc d hd he
  have hab : ∀ i, 0 ≤ (a + b) i ∧ (a + b) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T a).mp ha i
    have h2 := (mem_integerBox T b).mp hb i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have hcd : ∀ i, 0 ≤ (c + d) i ∧ (c + d) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T c).mp hc i
    have h2 := (mem_integerBox T d).mp hd i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have he' : ((boxIntegerCode T (a + b) : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T (c + d) : ℤ) : ZMod (boxCodeModulus T)) := by
    change ((boxIntegerCode T a : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T b : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T c : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T d : ℤ) : ZMod (boxCodeModulus T)) at he
    simpa only [map_add, Int.cast_add] using he
  have hh := int_eq_of_zmod_eq_of_bounds
    (integerRadixValue_bounds (fun i => 4 * T i) (a + b) hab)
    (integerRadixValue_bounds (fun i => 4 * T i) (c + d) hcd) he'
  exact integerRadixValue_injective_on_digits (fun i => 4 * T i) (a + b) (c + d) hab hcd hh

theorem boxCode_density {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) = ((4 : ℝ) ^ n)⁻¹ := by
  have hprod : ((∏ i, T i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (T i)))
  rw [card_integerBox, boxCodeModulus_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hprod]

theorem boxCode_density_lower {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    Real.exp (-(4 * (n : ℝ))) ≤ ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpow : (4 : ℝ) ^ n ≤ Real.exp (4 * (n : ℝ)) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 n
    rw [← Real.exp_nat_mul] at h
    simpa only [mul_comm] using h
  rw [boxCode_density, ← one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mpr
  calc
    _ ≤ Real.exp (-(4 * (n : ℝ))) * Real.exp (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

noncomputable def canonicalSlicedModulus (x : G → IntegerScalarCubeBox α L) : ℕ :=
  if hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x then
    residueRefinedPeriod (kernelPeriodCandidate (height + 1)
      (goodKernelUniformCandidate selection x hx height)) stride
  else 1

end Erdos3

end

section

namespace Erdos3

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteNoiseEventBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFiniteProbabilityMeasure_noise_event_le
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (bad : Ω → Prop) {ε : ℝ}
    (hbound : ∀ c, (law c).mean (fun x => if bad x then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | bad z.2} ≤ ε := by
  have hevent : MeasurableSet {z : C × Ω | bad z.2} :=
    (Set.toFinite {x : Ω | bad x}).measurableSet.preimage measurable_snd
  rw [centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent]
  have hi := centeredFinite_mean_integrable μ law hweight
    (fun _ x => if bad x then (1 : ℝ) else 0) (fun _ => integrable_const _)
  calc
    _ ≤ ∫ _ : C, ε ∂μ := integral_mono hi (integrable_const ε) hbound
    _ = ε := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedEarlySpatialWidth
namespace OAI

section

namespace Erdos3

theorem preparedEarlySpatialWidth (d : ℕ) {gainLog : ℝ} (hg : 0 ≤ gainLog) :
    let Pτ := gainLog + (d : ℝ) + 8
    let τ := Real.exp (-Pτ)
    0 ≤ Pτ ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧ (d : ℝ) * τ ≤ 1 / 2 ∧
      τ⁻¹ = Real.exp Pτ ∧
      (∀ Pmaster : ℝ, Pτ ≤ Pmaster → τ⁻¹ ≤ Real.exp Pmaster) ∧
      (∀ Pprod gain : ℝ, gainLog + 8 ≤ Pprod → Real.exp (-gainLog) ≤ gain →
        Real.exp (-Pprod) ≤ gain / 16 ∧
          12 * positiveProjectionAccuracy Pprod + 2 * (d : ℝ) * τ ≤ gain / 8) := by
  dsimp only
  have hnonneg : 0 ≤ gainLog + (d : ℝ) + 8 := by positivity
  have hexp : Real.exp (-gainLog) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg)
  have hprecision := preparedModularProductivity_precision d hg
    (Pprod := gainLog + 8) (Pphysical := gainLog + (d : ℝ) + 8)
    (gain := Real.exp (-gainLog)) le_rfl le_rfl le_rfl
  have hτhalf : Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, ← one_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hτdim : (d : ℝ) * Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    have ha : 0 ≤ positiveProjectionAccuracy (gainLog + 8) := Real.exp_nonneg _
    linarith only [hprecision.2, hexp, ha]
  have hinv : (Real.exp (-(gainLog + (d : ℝ) + 8)))⁻¹ =
      Real.exp (gainLog + (d : ℝ) + 8) := by rw [Real.exp_neg, inv_inv]
  refine ⟨hnonneg, Real.exp_pos _, hτhalf, hτdim, hinv, ?_, ?_⟩
  · intro Pmaster hmaster
    rw [hinv]
    exact Real.exp_le_exp.mpr hmaster
  · intro Pprod gain hprod hgain
    exact preparedModularProductivity_precision d hg hprod le_rfl hgain

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {D : ℕ} {R : Type*} [CommRing R]

noncomputable def earlierSlotMatrix (m : (i : Fin D) → Fin i.val → R) :
    Matrix (Fin D) (Fin D) R := fun i j =>
  ∑ k : Fin i.val, if earlierSlot i k = j then m i k else 0

theorem earlierSlotMatrix_strict (m : (i : Fin D) → Fin i.val → R)
    (i j : Fin D) (hij : i ≤ j) : earlierSlotMatrix m i j = 0 := by
  classical
  have hne (k : Fin i.val) : earlierSlot i k ≠ j := by
    intro heq
    have hval := congrArg Fin.val heq
    have hi := k.isLt
    change k.val = j.val at hval
    change i.val ≤ j.val at hij
    omega
  simp [earlierSlotMatrix, hne]

theorem earlierSlotMatrix_mulVec (m : (i : Fin D) → Fin i.val → R)
    (x : Fin D → R) (i : Fin D) :
    (earlierSlotMatrix m).mulVec x i = ∑ k : Fin i.val, m i k * x (earlierSlot i k) := by
  classical
  simp only [earlierSlotMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul]
  simp

theorem det_one_sub_strictLower (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0) : (1 - M).det = 1 := by
  have htri : (1 - M).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [Matrix.sub_apply, hM i j hij.le, Matrix.one_apply_ne hij.ne]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  apply Finset.prod_eq_one
  intro i _
  simp [Matrix.sub_apply, hM i i le_rfl]

variable {σ : Type*}

noncomputable def polynomialMatrixAction (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) : Fin D → MvPolynomial σ R :=
  fun i => ∑ j, M i j • C₀ j

theorem polynomialMatrixAction_degree (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∀ i, polynomialMatrixAction M C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h := by
  intro i
  exact (weightedSupportLE _ _).sum_mem
    (fun j _ => (weightedSupportLE _ _).smul_mem _ (hC j))

theorem polynomialMatrixAction_eval (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) (t : σ → R) :
    (fun i => aeval t (polynomialMatrixAction M C₀ i)) =
      M.mulVec (fun i => aeval t (C₀ i)) := by
  ext i
  simp [polynomialMatrixAction, Matrix.mulVec, dotProduct]

theorem polynomial_affine_origin (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0)
    (C₀ : Fin D → MvPolynomial σ R) {h : ℕ}
    (hC : ∀ i, C₀ i ∈ weightedSupportLE (fun _ : σ => 1) h) :
    ∃ P : Fin D → MvPolynomial σ R,
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → R, (1 - M).mulVec (fun i => aeval t (P i)) =
        (fun i => aeval t (C₀ i)) := by
  refine ⟨polynomialMatrixAction (1 - M)⁻¹ C₀,
    polynomialMatrixAction_degree _ C₀ hC, ?_⟩
  intro t
  rw [polynomialMatrixAction_eval, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (by rw [det_one_sub_strictLower M hM]; exact isUnit_one),
    Matrix.one_mulVec]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin (D + E) → ℕ}

theorem lowest_prefix_slotAffine (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) (i : Fin D) :
    SlotAffine h (A.center (i.castAdd E)) := by
  apply slotAffine_of_weightedSupport hh
  have hweight : patchVariableWeight w (i.castAdd E) =
      lowestSlotWeight (σ := σ) (τ := Fin i.val) h := by
    funext v
    cases v with
    | inl a => rfl
    | inr j =>
      exact hw ⟨j.val, lt_trans j.isLt i.isLt⟩
  rw [← hweight, ← hw i]
  exact A.degree (i.castAdd E)

theorem exists_lowest_affine_prefix (A : PolynomialSlots σ (D + E) w)
    {h : ℕ} (hh : 0 < h) (hw : ∀ i : Fin D, w (i.castAdd E) = h) :
    ∃ (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
      (P : Fin D → MvPolynomial σ ℝ),
      (∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) h) ∧
      ∀ t : σ → ℝ, (A.slots t).takePrefix =
        TriangularSlots.affineBlock M hM (fun i => aeval t (P i)) := by
  classical
  have hrows := A.lowest_prefix_slotAffine hh hw
  choose C₀ m hC hrow using hrows
  let M := earlierSlotMatrix m
  have hM : ∀ i j, i ≤ j → M i j = 0 := earlierSlotMatrix_strict m
  have hcenter (t : σ → ℝ) (x : Fin D → ℝ) (i : Fin D) :
      (A.slots t).takePrefix.center x i = aeval t (C₀ i) + M.mulVec x i := by
    change aeval (Sum.elim t (fun j =>
      Fin.append x 0 (earlierSlot (i.castAdd E) j))) (A.center (i.castAdd E)) = _
    have hargs : (fun j : Fin i.val => Fin.append x 0 (earlierSlot (i.castAdd E) j)) =
        (fun j => x (earlierSlot i j)) := by
      funext j
      change Fin.append x 0 ((earlierSlot i j).castAdd E) = _
      exact Fin.append_left _ _ _
    calc
      _ = aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center (i.castAdd E)) :=
        congrArg (fun f : Fin i.val → ℝ => aeval (Sum.elim t f) (A.center (i.castAdd E))) hargs
      _ = aeval t (C₀ i) + ∑ j, m i j * x (earlierSlot i j) := hrow i t _
      _ = _ := congrArg (fun z => aeval t (C₀ i) + z) (earlierSlotMatrix_mulVec m x i).symm
  obtain ⟨P, hP, hsolve⟩ := polynomial_affine_origin M hM C₀ hC
  refine ⟨M, hM, P, hP, ?_⟩
  intro t
  apply TriangularSlots.ext
  intro x i
  rw [hcenter]
  change aeval t (C₀ i) + M.mulVec x i =
    aeval t (P i) + M.mulVec (x - fun j => aeval t (P j)) i
  rw [Matrix.mulVec_sub]
  have hs := hsolve t
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hs
  have hi := congrFun hs i
  simp only [Pi.sub_apply] at hi ⊢
  linarith

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

structure LowestLayerModel (A : PolynomialPatch σ s (D + E)) (h : ℕ) where
  matrix : Matrix (Fin D) (Fin D) ℝ
  strict : ∀ i j, i ≤ j → matrix i j = 0
  origin : Fin D → MvPolynomial σ ℝ
  degree : ∀ i, origin i ∈ weightedSupportLE (fun _ : σ => 1) h
  weights : ∀ i : Fin D, A.weight (i.castAdd E) = h
  form_eq : ∀ t : σ → ℝ, (A.form.slots t).takePrefix =
    TriangularSlots.affineBlock matrix strict (fun i => aeval t (origin i))

theorem nonempty_lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    Nonempty (A.LowestLayerModel h) := by
  obtain ⟨M, hM, P, hP, heq⟩ := A.form.exists_lowest_affine_prefix hh hw
  exact ⟨⟨M, hM, P, hP, hw, heq⟩⟩

noncomputable def lowestLayerModel (A : PolynomialPatch σ s (D + E))
    (hh : 0 < h) (hw : ∀ i : Fin D, A.weight (i.castAdd E) = h) :
    A.LowestLayerModel h := Classical.choice (A.nonempty_lowestLayerModel hh hw)

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch.LowestLayerModel

variable {σ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}
    (L : A.LowestLayerModel h)

noncomputable def integerChange : Matrix (Fin D) (Fin D) ℤ :=
  triangularReductionMatrix (1 - L.matrix)

noncomputable def normalizedOrigin : Fin D → MvPolynomial σ ℝ :=
  polynomialMatrixAction (L.integerChange⁻¹.map (Int.castRingHom ℝ)) L.origin

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open _root_.MvPolynomial

variable {σ τ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}

noncomputable def reparam (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).LowestLayerModel h where
  matrix := L.matrix
  strict := L.strict
  origin i := aeval f (L.origin i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (fun _ : τ => 1) f hf (L.degree i)
  weights := L.weights
  form_eq t := by
    change ((A.form.reparam f hf).slots t).takePrefix = _
    rw [PolynomialSlots.reparam_slots, L.form_eq]
    simp only [MvPolynomial.comp_aeval_apply]

noncomputable def onAffineLine (L : A.LowestLayerModel h) (a q : σ → ℝ) :
    (A.onAffineLine a q).LowestLayerModel h :=
  L.reparam (PolynomialPatch.affineLineParameters a q) (PolynomialPatch.affineLineParameters_degree a q)

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

def PatchKernel.zeroWithLip (d : ℕ) (L : ℝ≥0) : PatchKernel d where
  value _ := 0
  nonneg _ := le_rfl
  le_one _ := zero_le_one
  support _ h := (h rfl).elim
  lip := L
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_self]
    exact mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))

namespace PolynomialPatch.LowestLayerModel

variable {s D E h : ℕ} {A : PolynomialPatch Unit s (D + E)}

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel

open VectorPolynomial _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {X : Type} {s D E m : ℕ} {A : PolynomialPatch X s (D + E)}

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedSlicedCoefficientSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z K₀ : Type*} [Fintype Z] [DecidableEq Z]
  [fintypeD : Fintype D] [decidableEqD : DecidableEq D] [Fintype α]
  [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [fintypeO : ∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)]
  [nonemptyO : ∀ d, Nonempty (O d)]

noncomputable def jointAffineCoefficientTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Csum Wsum δ E : ℝ) : ℝ :=
  jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α) h c₀ C A T
    (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
      booleanJetMassBudget (Fintype.card α) degree Wsum) δ E

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {Ω D α Z K₀ : Type*} [MeasurableSpace Ω] [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRegularizedCells
namespace OAI

section

namespace Erdos3.FixedDensity

structure GeneratedOrderedPatternRegularization
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (H : WeightedOrderedPattern G k r)
    (ε : ℝ) where
  state : OrderedRegularitySystem G k r
  generators :
    (e : OrderedFace k r) →
      Finset (BooleanCutTest (Fin r → G))
  budgetLength : OrderedFace k r → ℕ
  stepIndex : OrderedFace k r → ℕ
  budget_large :
    ∀ e, 1 < (budgetLength e : ℝ) * ε ^ 2
  step_lt_budget :
    ∀ e, stepIndex e < budgetLength e
  partition_eq_generated :
    ∀ e, (state e).partition =
      FacePartition.generatedBy (generators e)
  generators_supported :
    ∀ e, generators e ⊆ booleanFaceCutSupports G r
  generator_card_le :
    ∀ e, (generators e).card ≤ stepIndex e
  regular :
    ∀ e, (state e).IsFaceCutRegular
      (H.edgeWeight e) ε
  count_close :
    |H.patternCount -
        (regularizedOrderedPattern H state).patternCount| ≤
      (Fintype.card (OrderedFace k r) : ℝ) * ε
  complexity_le :
    ∀ e, FacePartition.complexity (state e).partition ≤
      2 ^ stepIndex e

namespace GeneratedOrderedPatternRegularization

abbrev BranchSystem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    GeneratorBranch (R.generators e)

abbrev TopAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  (e : OrderedFace k r) →
    (R.state e).partition.parts

end GeneratedOrderedPatternRegularization

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
namespace OAI

section

namespace Erdos3.FixedDensity

def eraseOrderedFace
    {k r : ℕ} (e : OrderedFace k r) (i : Fin r) :
    OrderedFace k (r - 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      exact (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseOrderedFace
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (i : Fin r)
    (x : Fin k → G) :
    orderedFaceTuple (eraseOrderedFace e i) x =
      eraseCoordinate i (orderedFaceTuple e x) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      rfl

namespace OrderedPattern

noncomputable def deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    eraseCoordinate i y ∈ D (eraseOrderedFace e i)

@[simp]
theorem mem_deletionCylinder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (i : Fin r)
    (y : Fin r → G) :
    y ∈ deletionCylinder D e i ↔
      eraseCoordinate i y ∈
        D (eraseOrderedFace e i) := by
  simp [deletionCylinder]

noncomputable def liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1)) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun i =>
      deletionCylinder D e i

@[simp]
theorem mem_liftLowerDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ liftLowerDeletion D e ↔
      ∃ i : Fin r,
        eraseCoordinate i y ∈
          D (eraseOrderedFace e i) := by
  classical
  simp [liftLowerDeletion]

noncomputable def unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r) :
    DeletionFamily (G := G) k r := by
  classical
  exact fun e =>
    Finset.univ.biUnion fun t => D t e

@[simp]
theorem mem_unionDeletion
    {ι G : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : ι → DeletionFamily (G := G) k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ unionDeletion D e ↔
      ∃ t : ι, y ∈ D t e := by
  classical
  simp [unionDeletion]

noncomputable def lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) :
    DeletionFamily (G := G) k r :=
  fun e =>
    (S e).lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ

@[simp]
theorem mem_lowStructuredDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (τ : ℝ) (e : OrderedFace k r)
    (y : Fin r → G) :
    y ∈ lowStructuredDeletion H S τ e ↔
      H.toWeighted.edgeWeight e y = 1 ∧
        (S e).structured
          (H.toWeighted.edgeWeight e) y < τ := by
  exact
    (S e).mem_lowStructuredOneFinset
      (H.toWeighted.edgeWeight e) τ y

end OrderedPattern

namespace GeneratedOrderedPatternRegularization

abbrev CellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :=
  R.TopAtomChoice × R.BranchSystem

@[simp]
theorem card_cellIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H ε) :
    Fintype.card R.CellIndex =
      Fintype.card R.TopAtomChoice *
        Fintype.card R.BranchSystem := by
  simp [CellIndex]

end GeneratedOrderedPatternRegularization

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseBoundaryFace
    {G : Type*} {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    orderedFaceTuple (eraseBoundaryFace e i) x =
      eraseBoundaryCoordinate i (orderedFaceTuple e x) :=
  rfl

abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines

def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩

@[simp]
theorem orderedBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryAtomAt P e x).1 =
      (orderedBoundaryPartition P e).part x :=
  rfl

noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f

structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex

def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩

def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : OrderedPartitionComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  orderedBoundaryPartition (C.layer j (Nat.le_of_lt hj)) e

def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl

end OrderedPartitionComplex

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedAtomEnergy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

def IsFamilyRegularAgainst
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) : Prop :=
  ∀ i, S.IsRegularAgainst (f i) cuts ε

theorem exists_index_booleanCut_of_not_familyRegular
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι, ∃ A ∈ cuts,
      ε < |S.booleanCutCorrelation (f i) A| := by
  classical
  unfold IsFamilyRegularAgainst at h
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨A, hA, hcorr⟩ :=
    S.exists_booleanCut_of_not_regular (f i) cuts hi
  exact ⟨i, A, hA, hcorr⟩

structure FamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) where
  index : ι
  cut : BooleanCutTest Ω
  mem_cuts : cut ∈ cuts
  correlation :
    ε < |S.booleanCutCorrelation (f index) cut|

noncomputable def chosenFamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.FamilyIrregularWitness f cuts ε := by
  classical
  let hex :=
    S.exists_index_booleanCut_of_not_familyRegular f cuts h
  let i : ι := Classical.choose hex
  let hi := Classical.choose_spec hex
  let A : BooleanCutTest Ω := Classical.choose hi
  have hA :=
    (Classical.choose_spec hi).1
  have hcorr :=
    (Classical.choose_spec hi).2
  exact ⟨i, A, hA, hcorr⟩

noncomputable def chosenFamilyIrregularCut
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsFamilyRegularAgainst f cuts ε then ∅
    else (S.chosenFamilyIrregularWitness f cuts ε h).cut

noncomputable def familyRegularityRun
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := familyRegularityRun S f cuts ε n
      T.refineBy (T.chosenFamilyIrregularCut f cuts ε)

@[simp]
theorem familyRegularityRun_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem familyRegularityRun_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRun f cuts ε (n + 1) =
      (S.familyRegularityRun f cuts ε n).refineBy
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε) :=
  rfl

noncomputable def familyRegularityRunCuts
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.familyRegularityRun f cuts ε i).chosenFamilyIrregularCut
      f cuts ε

@[simp]
theorem familyRegularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRunCuts f cuts ε 0 = ∅ := by
  simp [familyRegularityRunCuts]

@[simp]
theorem familyRegularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε)
        (S.familyRegularityRunCuts f cuts ε n) := by
  classical
  simp [familyRegularityRunCuts, Finset.range_add_one]

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) :
    Ω → ℝ :=
  finsetIndicator a.1

@[simp]
theorem partitionAtomIndicator_of_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    partitionAtomIndicator Q a x = 1 :=
  finsetIndicator_of_mem hx

@[simp]
theorem partitionAtomIndicator_of_not_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    partitionAtomIndicator Q a x = 0 :=
  finsetIndicator_of_not_mem hx

theorem partitionAtomIndicator_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ^ 2 =
      partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem sum_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts, partitionAtomIndicator Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact partitionAtomIndicator_of_mem Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb hba
    apply partitionAtomIndicator_of_not_mem
    intro hxb
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 hxb
        (Q.mem_part (Finset.mem_univ x))
    exact hba heq
  · intro hax
    exact (hax (Finset.mem_univ ax)).elim

noncomputable def partitionAtomEnergy
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) : ℝ :=
  ∑ a : Q.parts,
    Erdos3.FixedDensity.partitionEnergy P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) :
    0 ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  exact Finset.sum_nonneg fun a _ =>
    Erdos3.FixedDensity.partitionEnergy_nonneg P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : FacePartition Ω) :
    partitionAtomEnergy P Q ≤ 1 := by
  unfold partitionAtomEnergy
  calc
    (∑ a : Q.parts,
        Erdos3.FixedDensity.partitionEnergy P
          (partitionAtomIndicator Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            partitionAtomIndicator Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact partitionEnergy_le_mean_sq P
        (partitionAtomIndicator Q a)
    _ =
        ∑ a : Q.parts,
          mean (partitionAtomIndicator Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact partitionAtomIndicator_sq Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, partitionAtomIndicator Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => partitionAtomIndicator Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact sum_partitionAtomIndicator Q x
    _ = 1 := mean_const 1

theorem partitionAtomEnergy_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy R Q ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  apply Finset.sum_le_sum
  intro a _
  exact partitionEnergy_mono P R hPR
    (partitionAtomIndicator Q a)

noncomputable def orderedAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) : ℝ :=
  partitionAtomEnergy (orderedBoundaryPartition lower e) upper

theorem orderedAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    0 ≤ orderedAtomEnergy lower e upper :=
  partitionAtomEnergy_nonneg _ _

theorem orderedAtomEnergy_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy lower e upper ≤ 1 :=
  partitionAtomEnergy_le_one _ _

theorem orderedAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy coarse e upper ≤
      orderedAtomEnergy fine e upper := by
  exact partitionAtomEnergy_mono
    (orderedBoundaryPartition_mono hfc e) upper

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BoundaryBernoulli
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev BoundaryBooleanCutAssignment
    (G : Type*) (j : ℕ) :=
  (i : Fin (j + 1)) → (Fin j → G) → Bool

noncomputable def boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    BooleanCutTest (Fin j → G) := by
  classical
  exact Finset.univ.filter fun z => b i z = true

@[simp]
theorem mem_boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    z ∈ boundaryBooleanComponentCut b i ↔
      b i z = true := by
  simp [boundaryBooleanComponentCut]

noncomputable def boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutTest (Fin (j + 1) → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b i (eraseBoundaryCoordinate i x) = true

@[simp]
theorem mem_boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    x ∈ boundaryBooleanCutSupport b ↔
      ∀ i, b i (eraseBoundaryCoordinate i x) = true := by
  simp [boundaryBooleanCutSupport]

noncomputable def orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    Finset (BooleanCutTest (Fin j → G)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)).image
      (fun i => boundaryBooleanComponentCut b i)

theorem boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    boundaryBooleanComponentCut b i ∈
      orderedBoundaryComponentCuts e b
        (eraseBoundaryFace e i) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp

noncomputable def refineOrderedFacePartitionsByBoundaryCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionSystem G k j :=
  fun g =>
    FacePartition.join (P g)
      (FacePartition.generatedBy
        (orderedBoundaryComponentCuts e b g))

theorem refineOrderedFacePartitionsByBoundaryCut_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionRefines
      (refineOrderedFacePartitionsByBoundaryCut P e b) P := by
  intro g
  exact FacePartition.join_le_left _ _

theorem refineOrderedFacePartitionsByBoundaryCut_le_component
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i) ≤
      FacePartition.generatedBy
        ({boundaryBooleanComponentCut b i} :
          Finset (Finset (Fin j → G))) := by
  apply le_trans (FacePartition.join_le_right _ _)
  apply FacePartition.generatedBy_antitone
  intro A hA
  have hAeq : A = boundaryBooleanComponentCut b i := by
    simpa using hA
  subst A
  exact
    boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
      e b i

theorem boundaryComponentBit_eq_of_mem_refined_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1))
    (x y : Fin j → G)
    (hy :
      y ∈
        (refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i)).part x) :
    b i x = b i y := by
  have hpart :
      y ∈
        (FacePartition.generatedBy
          ({boundaryBooleanComponentCut b i} :
            Finset (Finset (Fin j → G)))).part x :=
    FacePartition.part_subset_of_le
      (refineOrderedFacePartitionsByBoundaryCut_le_component
        P e b i) x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({boundaryBooleanComponentCut b i} :
        Finset (Finset (Fin j → G))) x y).1 hpart
      (boundaryBooleanComponentCut b i) (by simp)
  cases hbx : b i x <;> cases hby : b i y <;>
    simp [mem_boundaryBooleanComponentCut, hbx, hby] at hsignature ⊢

theorem orderedBoundaryPartition_refined_le_generatedSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      FacePartition.generatedBy
        ({boundaryBooleanCutSupport b} :
          Finset (Finset (Fin (j + 1) → G))) := by
  rw [FacePartition.le_iff_part_subset]
  intro x y hy
  rw [FacePartition.mem_part_generatedBy_iff]
  intro A hA
  have hAeq : A = boundaryBooleanCutSupport b := by
    simpa using hA
  subst A
  rw [mem_boundaryBooleanCutSupport,
    mem_boundaryBooleanCutSupport]
  have hboundary :=
    (mem_orderedBoundaryPartition_part_iff
      (refineOrderedFacePartitionsByBoundaryCut P e b)
      e x y).1 hy
  constructor
  · intro hx i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit ▸ hx i
  · intro hy' i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit.symm ▸ hy' i

theorem orderedBoundaryPartition_refined_le_refineBy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
      orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      ((⟨orderedBoundaryPartition P e⟩ :
          FaceRegularityState (Fin (j + 1) → G)).refineBy
        (boundaryBooleanCutSupport b)).partition := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact orderedBoundaryPartition_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines P e b) e
  · exact orderedBoundaryPartition_refined_le_generatedSupport
      P e b

noncomputable def orderedLayerAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) : ℝ :=
  ∑ e : OrderedFace k (j + 1),
    orderedAtomEnergy lower e (upper e)

theorem orderedLayerAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    0 ≤ orderedLayerAtomEnergy lower upper := by
  unfold orderedLayerAtomEnergy
  exact Finset.sum_nonneg fun e _ =>
    orderedAtomEnergy_nonneg lower e (upper e)

theorem orderedLayerAtomEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy lower upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
  unfold orderedLayerAtomEnergy
  calc
    (∑ e : OrderedFace k (j + 1),
        orderedAtomEnergy lower e (upper e)) ≤
        ∑ _e : OrderedFace k (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact orderedAtomEnergy_le_one lower e (upper e)
    _ = (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
      simp

theorem orderedLayerAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy coarse upper ≤
      orderedLayerAtomEnergy fine upper := by
  unfold orderedLayerAtomEnergy
  apply Finset.sum_le_sum
  intro e _
  exact orderedAtomEnergy_mono hfc e (upper e)

theorem orderedLayerAtomEnergy_increment_of_boundaryCut
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (e : OrderedFace k (j + 1))
    (a : (upper e).parts)
    (b : BoundaryBooleanCutAssignment G j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorrelation :
      ε ≤
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
            (partitionAtomIndicator (upper e) a)
            (boundaryBooleanCutSupport b)|) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (refineOrderedFacePartitionsByBoundaryCut lower e b)
        upper := by
  classical
  let fine :=
    refineOrderedFacePartitionsByBoundaryCut lower e b
  let S : FaceRegularityState (Fin (j + 1) → G) :=
    ⟨orderedBoundaryPartition lower e⟩
  have hincrement :
      S.energy (partitionAtomIndicator (upper e) a) + ε ^ 2 ≤
        (S.refineBy (boundaryBooleanCutSupport b)).energy
          (partitionAtomIndicator (upper e) a) :=
    S.energy_increment_of_booleanCut
      (partitionAtomIndicator (upper e) a)
      (boundaryBooleanCutSupport b) hε hcorrelation
  have hrefined :
      orderedBoundaryPartition fine e ≤
        (S.refineBy (boundaryBooleanCutSupport b)).partition := by
    exact orderedBoundaryPartition_refined_le_refineBy
      lower e b
  have hatom :
      orderedAtomEnergy lower e (upper e) + ε ^ 2 ≤
        orderedAtomEnergy fine e (upper e) := by
    unfold orderedAtomEnergy partitionAtomEnergy
    let U : Finset (upper e).parts := Finset.univ
    have haU : a ∈ U := by simp [U]
    have hother :
        ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c) ≤
          ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) := by
      apply Finset.sum_le_sum
      intro c _
      exact partitionEnergy_mono
        (orderedBoundaryPartition fine e)
        (orderedBoundaryPartition lower e)
        (orderedBoundaryPartition_mono
          (refineOrderedFacePartitionsByBoundaryCut_refines
            lower e b) e)
        (partitionAtomIndicator (upper e) c)
    have hchosen :
        partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
            ε ^ 2 ≤
          partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) := by
      exact le_trans hincrement
        (partitionEnergy_mono
          (orderedBoundaryPartition fine e)
          (S.refineBy (boundaryBooleanCutSupport b)).partition
          hrefined
          (partitionAtomIndicator (upper e) a))
    change
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
          ε ^ 2 ≤
        ∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition fine e)
            (partitionAtomIndicator (upper e) c)
    calc
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
            ε ^ 2 =
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c)) +
            (partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
              ε ^ 2) := by
        rw [← Finset.sum_erase_add U _ haU]
        ring
      _ ≤
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c)) +
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) :=
        add_le_add hother hchosen
      _ =
          ∑ c ∈ U,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) :=
        Finset.sum_erase_add U _ haU
  unfold orderedLayerAtomEnergy
  let E : Finset (OrderedFace k (j + 1)) := Finset.univ
  have heE : e ∈ E := by simp [E]
  have hotherFaces :
      ∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d) ≤
        ∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d) := by
    apply Finset.sum_le_sum
    intro d _
    exact orderedAtomEnergy_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines
        lower e b)
      d (upper d)
  change
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
        ε ^ 2 ≤
      ∑ d ∈ E, orderedAtomEnergy fine d (upper d)
  calc
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
          ε ^ 2 =
        (∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d)) +
        (orderedAtomEnergy lower e (upper e) + ε ^ 2) := by
      rw [← Finset.sum_erase_add E _ heE]
      ring
    _ ≤
        (∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d)) +
        orderedAtomEnergy fine e (upper e) :=
      add_le_add hotherFaces hatom
    _ =
        ∑ d ∈ E, orderedAtomEnergy fine d (upper d) :=
      Finset.sum_erase_add E _ heE

def IsPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts)
      (b : BoundaryBooleanCutAssignment G j),
    |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower e⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper e) a)
        (boundaryBooleanCutSupport b)| ≤ ε

theorem exists_boundaryCut_of_not_preliminaryRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ}
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    ∃ (e : OrderedFace k (j + 1))
        (a : (upper e).parts)
        (b : BoundaryBooleanCutAssignment G j),
      ε <
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
          (partitionAtomIndicator (upper e) a)
          (boundaryBooleanCutSupport b)| := by
  unfold IsPreliminaryOrderedRegular at h
  obtain ⟨e, he⟩ := not_forall.mp h
  obtain ⟨a, ha⟩ := not_forall.mp he
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨e, a, b, lt_of_not_ge hb⟩

structure PreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) where
  face : OrderedFace k (j + 1)
  atom : (upper face).parts
  cut : BoundaryBooleanCutAssignment G j
  correlation :
    ε <
      |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower face⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper face) atom)
        (boundaryBooleanCutSupport cut)|

noncomputable def chosenPreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    PreliminaryIrregularWitness lower upper ε := by
  classical
  let hex :=
    exists_boundaryCut_of_not_preliminaryRegular
      lower upper h
  let e := Classical.choose hex
  let he := Classical.choose_spec hex
  let a := Classical.choose he
  let ha := Classical.choose_spec he
  let b := Classical.choose ha
  have hcorr := Classical.choose_spec ha
  exact ⟨e, a, b, hcorr⟩

noncomputable def preliminaryOrderedRegularityStep
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionSystem G k j := by
  classical
  exact
    if h : IsPreliminaryOrderedRegular lower upper ε then
      lower
    else
      let W :=
        chosenPreliminaryIrregularWitness lower upper ε h
      refineOrderedFacePartitionsByBoundaryCut
        lower W.face W.cut

theorem preliminaryOrderedRegularityStep_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityStep lower upper ε)
      lower := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simpa [preliminaryOrderedRegularityStep, h] using
      OrderedFacePartitionRefines.refl lower
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact refineOrderedFacePartitionsByBoundaryCut_refines
      lower W.face W.cut

theorem preliminaryOrderedRegularityStep_energy_increment
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (preliminaryOrderedRegularityStep lower upper ε)
        upper := by
  classical
  simp only [preliminaryOrderedRegularityStep, dif_neg h]
  let W :=
    chosenPreliminaryIrregularWitness lower upper ε h
  exact orderedLayerAtomEnergy_increment_of_boundaryCut
    lower upper W.face W.atom W.cut hε
    (le_of_lt W.correlation)

noncomputable def preliminaryOrderedRegularityRun
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => lower
  | n + 1 =>
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε

@[simp]
theorem preliminaryOrderedRegularityRun_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    preliminaryOrderedRegularityRun lower upper ε 0 =
      lower :=
  rfl

@[simp]
theorem preliminaryOrderedRegularityRun_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    preliminaryOrderedRegularityRun lower upper ε (n + 1) =
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε :=
  rfl

theorem preliminaryOrderedRegularityRun_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityRun lower upper ε n)
      lower := by
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl lower
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (preliminaryOrderedRegularityStep_refines
          (preliminaryOrderedRegularityRun lower upper ε n)
          upper ε)
        ih

theorem exists_preliminaryOrderedRegularityRun_index_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      IsPreliminaryOrderedRegular
        (preliminaryOrderedRegularityRun
          lower upper ε n)
        upper ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬IsPreliminaryOrderedRegular
          (preliminaryOrderedRegularityRun
            lower upper ε n)
          upper ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper +
            ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1))
            upper := by
    intro n hn
    rw [preliminaryOrderedRegularityRun_succ]
    exact preliminaryOrderedRegularityStep_energy_increment
      (preliminaryOrderedRegularityRun
        lower upper ε n)
      upper hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε i)
              upper +
              ε ^ 2 ≤
            orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε (i + 1))
              upper) →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε 0)
            upper +
            (n : ℝ) * ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε 0)
                upper +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              (orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε 0)
                  upper +
                (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤
              orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε n)
                  upper +
                ε ^ 2 := by
            linarith
          _ ≤
              orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε (n + 1))
                upper :=
            hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤
        orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε 0)
          upper :=
    orderedLayerAtomEnergy_nonneg _ _
  have hupper :
      orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε m)
          upper ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) :=
    orderedLayerAtomEnergy_le_card _ _
  linarith

theorem card_orderedBoundaryComponentCuts_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    (orderedBoundaryComponentCuts e b g).card ≤
      j + 1 := by
  classical
  let I : Finset (Fin (j + 1)) :=
    (Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)
  calc
    (orderedBoundaryComponentCuts e b g).card ≤
        I.card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (j + 1))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = j + 1 := by simp

theorem complexity_refineOrderedFacePartitionsByBoundaryCut_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (P g) := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy
            (orderedBoundaryComponentCuts e b g)) ≤
        2 ^ (j + 1) := by
    exact le_trans
      (FacePartition.complexity_generatedBy_le
        (orderedBoundaryComponentCuts e b g))
      (Nat.pow_le_pow_right (by decide)
        (card_orderedBoundaryComponentCuts_le e b g))
  calc
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
        FacePartition.complexity (P g) *
          FacePartition.complexity
            (FacePartition.generatedBy
              (orderedBoundaryComponentCuts e b g)) :=
      FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity (P g) *
          2 ^ (j + 1) :=
      Nat.mul_le_mul_left _ hgenerated
    _ =
        2 ^ (j + 1) *
          FacePartition.complexity (P g) :=
      Nat.mul_comm _ _

theorem complexity_preliminaryOrderedRegularityStep_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityStep
          lower upper ε g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (lower g) := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simp only [preliminaryOrderedRegularityStep, dif_pos h]
    exact Nat.le_mul_of_pos_left _
      (by positivity : 0 < 2 ^ (j + 1))
  · simp only [preliminaryOrderedRegularityStep, dif_neg h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact
      complexity_refineOrderedFacePartitionsByBoundaryCut_le
        lower W.face W.cut g

theorem complexity_preliminaryOrderedRegularityRun_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityRun
          lower upper ε n g) ≤
      (2 ^ (j + 1)) ^ n *
        FacePartition.complexity (lower g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1) g) ≤
            2 ^ (j + 1) *
              FacePartition.complexity
                (preliminaryOrderedRegularityRun
                  lower upper ε n g) := by
          rw [preliminaryOrderedRegularityRun_succ]
          exact complexity_preliminaryOrderedRegularityStep_le
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper ε g
        _ ≤
            2 ^ (j + 1) *
              ((2 ^ (j + 1)) ^ n *
                FacePartition.complexity (lower g)) :=
          Nat.mul_le_mul_left _ ih
        _ =
            (2 ^ (j + 1)) ^ (n + 1) *
              FacePartition.complexity (lower g) := by
          rw [pow_succ]
          ring

theorem exists_preliminaryOrderedRegular_refinement_with_complexity_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ fine : OrderedFacePartitionSystem G k j,
        n < m ∧
        OrderedFacePartitionRefines fine lower ∧
        IsPreliminaryOrderedRegular fine upper ε ∧
        ∀ g,
          FacePartition.complexity (fine g) ≤
            (2 ^ (j + 1)) ^ n *
              FacePartition.complexity (lower g) := by
  obtain ⟨n, hn, hregular⟩ :=
    exists_preliminaryOrderedRegularityRun_index_before
      lower upper hε hlong
  exact
    ⟨n,
      preliminaryOrderedRegularityRun lower upper ε n,
      hn,
      preliminaryOrderedRegularityRun_refines
        lower upper ε n,
      hregular,
      complexity_preliminaryOrderedRegularityRun_le
        lower upper ε n⟩

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary

@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b

def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

namespace FaceRegularityState

end FaceRegularityState

def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedGoodAtoms
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩

@[simp]
theorem partitionAtomAt_val
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    (partitionAtomAt P x).1 = P.part x :=
  rfl

@[simp]
theorem partitionAtomAt_eq_iff_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) (a : P.parts) :
    partitionAtomAt P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx

def partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1

@[simp]
theorem mem_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      ∃ a ∈ s, x ∈ a.1 := by
  simp [partitionAtomUnion]

theorem mem_partitionAtomUnion_iff_atomAt_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      partitionAtomAt P x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    have hcanonical :
        partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hxa
    simpa [hcanonical] using ha
  · intro hx
    exact
      (mem_partitionAtomUnion P s x).2
        ⟨partitionAtomAt P x, hx,
          P.mem_part (Finset.mem_univ x)⟩

noncomputable def smallAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    conditionalMean P f (P.representative b) < α

noncomputable def smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (smallAverageBaseAtoms P f α)

@[simp]
theorem mem_smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ)
    (x : Ω) :
    x ∈ smallAverageBaseSupport P f α ↔
      conditionalMean P f x < α := by
  rw [smallAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [smallAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

noncomputable def largeAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < conditionalMean P f (P.representative b)

noncomputable def largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (largeAverageBaseAtoms P f β)

@[simp]
theorem mem_largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ)
    (x : Ω) :
    x ∈ largeAverageBaseSupport P f β ↔
      β < conditionalMean P f x := by
  rw [largeAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [largeAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

noncomputable def atomBoundaryDefect
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  conditionalMean fine (partitionAtomIndicator upper a) x -
    conditionalMean coarse (partitionAtomIndicator upper a) x

noncomputable def atomBoundaryDefectSq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  atomBoundaryDefect fine coarse upper a x ^ 2

noncomputable def largeDefectBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset coarse.parts :=
  largeAverageBaseAtoms coarse
    (atomBoundaryDefectSq fine coarse upper a) β

noncomputable def largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion coarse
    (largeDefectBaseAtoms fine coarse upper a β)

@[simp]
theorem mem_largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) (x : Ω) :
    x ∈ largeDefectBaseSupport fine coarse upper a β ↔
      β <
        conditionalMean coarse
          (atomBoundaryDefectSq fine coarse upper a) x := by
  exact
    mem_largeAverageBaseSupport coarse
      (atomBoundaryDefectSq fine coarse upper a) β x

noncomputable def atomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (α β : ℝ) :
    Finset Ω :=
  smallAverageBaseSupport coarse
      (partitionAtomIndicator upper a) α ∪
    largeDefectBaseSupport fine coarse upper a β

def orderedFaceAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (P e).parts :=
  partitionAtomAt (P e) x

@[simp]
theorem orderedFaceAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (orderedFaceAtomAt P e x).1 = (P e).part x :=
  rfl

noncomputable def orderedAtomBoundaryDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  atomBoundaryDefect
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a x

noncomputable def orderedAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  atomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a α β

structure ClosedOrderedAtomConfiguration
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : OrderedPartitionComplex G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        (C.partition j e).parts
  mem_atom :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      orderedFaceTuple e witness ∈ (atom j e).1

namespace ClosedOrderedAtomConfiguration

def ofTuple
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : OrderedPartitionComplex G k r)
    (x : Fin k → G) :
    ClosedOrderedAtomConfiguration G k r C where
  witness := x
  atom j e :=
    partitionAtomAt (C.partition j e)
      (orderedFaceTuple e x)
  mem_atom j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (orderedFaceTuple e x))

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedPartitionComplex

def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j

@[simp]
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]

@[simp]
theorem dropTop_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).dropTop = C := by
  cases C with
  | mk partition =>
      simp [dropTop, appendTop]

@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

@[simp]
theorem withTopLayer_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1))
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (withTopLayer C top).partition j.castSucc =
      C.partition j.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]

@[simp]
theorem withTopLayer_partition_castSucc_general
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (i : Fin r) :
    (withTopLayer C top).partition i.castSucc =
      C.partition i.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]

end OrderedPartitionComplex

structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

namespace OrderedCoarseFineComplex

end OrderedCoarseFineComplex

abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

def IsFullyPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def OrderedPattern.edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) : Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter (H.edge e)

@[simp]
theorem OrderedPattern.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [OrderedPattern.edgeFinset]

noncomputable def orderedPatternTopPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedFacePartitionSystem G k r := by
  classical
  exact fun e =>
    FacePartition.generatedBy ({H.edgeFinset e} :
      Finset (Finset (Fin r → G)))

def indiscreteOrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) : OrderedPartitionComplex G k r where
  partition _ _ := FacePartition.indiscrete

noncomputable def orderedPatternInitialComplex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedPartitionComplex G k r :=
  (indiscreteOrderedPartitionComplex G k r).withTopLayer
    (orderedPatternTopPartition H)

@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseAtomBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def coarseAtomOfFineAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (b : fineUpper.parts) :
    coarseUpper.parts :=
  partitionAtomAt coarseUpper
    (fineUpper.representative b)

noncomputable def fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) :
    Finset fineUpper.parts := by
  classical
  exact
    (Finset.univ : Finset fineUpper.parts).filter fun b =>
      coarseAtomOfFineAtom fineUpper coarseUpper b = a

@[simp]
theorem mem_fineAtomsInCoarseAtom
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fineUpper coarseUpper : FacePartition Ω)
    (a : coarseUpper.parts) (b : fineUpper.parts) :
    b ∈ fineAtomsInCoarseAtom fineUpper coarseUpper a ↔
      coarseAtomOfFineAtom fineUpper coarseUpper b = a := by
  classical
  simp [fineAtomsInCoarseAtom]

namespace OrderedCoarseFineComplex

noncomputable def coarseUpperFaceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.coarse.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.coarse.partition j.succ e)

noncomputable def coarseUpperLayerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.coarse.partition j.succ)

end OrderedCoarseFineComplex

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace FaceRegularityState

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) : Finset Ω := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ atomBadBaseSupport fine coarse upper a α β

@[simp]
theorem mem_ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) (x : Ω) :
    x ∈ ownAtomBadBaseSupport fine coarse upper α β ↔
      x ∈ atomBadBaseSupport fine coarse upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [ownAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ atomBadBaseSupport
          fine coarse upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical :
        partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [ownAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine
      ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_inter.mpr
    exact
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

noncomputable def orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  ownAtomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper α β

@[simp]
theorem mem_orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) (x : Fin (j + 1) → G) :
    x ∈ orderedOwnAtomBadBaseSupport
        fine coarse e upper α β ↔
      x ∈ orderedAtomBadBaseSupport
        fine coarse e upper
          (partitionAtomAt upper x) α β := by
  exact
    mem_ownAtomBadBaseSupport
      (orderedBoundaryPartition fine e)
      (orderedBoundaryPartition coarse e)
      upper α β x

abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)

noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) :
    Finset (Fin (j.1 + 1) → G) :=
  orderedOwnAtomBadBaseSupport
    (P.fine.partition j.castSucc)
    (P.coarse.partition j.castSucc)
    e
    (P.coarse.partition j.succ e)
    α β

@[simp]
theorem mem_orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) (x : Fin (j.1 + 1) → G) :
    x ∈ P.orderedCoarseOwnAtomBadBaseSupport j e α β ↔
      x ∈ orderedAtomBadBaseSupport
        (P.fine.partition j.castSucc)
        (P.coarse.partition j.castSucc)
        e
        (P.coarse.partition j.succ e)
        (partitionAtomAt
          (P.coarse.partition j.succ e) x)
        α β := by
  exact
    mem_orderedOwnAtomBadBaseSupport
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.castSucc)
      e (P.coarse.partition j.succ e) α β x

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

end ClosedOrderedAtomConfiguration

namespace OrderedCoarseFineComplex

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.StrongOrderedComplexRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure FixedUpperLayerRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ) where
  steps : ℕ
  fine : OrderedFacePartitionSystem G k j
  steps_lt : steps < budget
  refines : OrderedFacePartitionRefines fine lower
  regular : IsPreliminaryOrderedRegular fine upper ε
  complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        (2 ^ (j + 1)) ^ steps *
          FacePartition.complexity (lower e)

theorem FixedUpperLayerRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {budget : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    Nonempty
      (FixedUpperLayerRegularityCertificate
        G k j lower upper ε budget) := by
  obtain ⟨steps, fine, hsteps, hrefines,
      hregular, hcomplexity⟩ :=
    exists_preliminaryOrderedRegular_refinement_with_complexity_before
      lower upper hε hlong
  exact ⟨{
    steps := steps
    fine := fine
    steps_lt := hsteps
    refines := hrefines
    regular := hregular
    complexity := hcomplexity }⟩

noncomputable def chosenFixedUpperLayerRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    FixedUpperLayerRegularityCertificate
      G k j lower upper ε budget :=
  Classical.choice
    (FixedUpperLayerRegularityCertificate.nonempty
      lower upper hε hlong)

noncomputable def fixedUpperLayerRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => initial
  | n + 1 =>
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine

@[simp]
theorem fixedUpperLayerRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong 0 = initial :=
  rfl

@[simp]
theorem fixedUpperLayerRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1) =
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine :=
  rfl

theorem fixedUpperLayerRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    OrderedFacePartitionRefines
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).refines

theorem fixedUpperLayerRegularityTower_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      OrderedFacePartitionRefines
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl initial
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong n)
        ih

theorem fixedUpperLayerRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    IsPreliminaryOrderedRegular
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      upper (ε n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).regular

def fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (budget n) *
        fixedUpperLayerComplexityFactor j budget n

theorem complexity_fixedUpperLayerRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : OrderedFace k j),
      FacePartition.complexity
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n e) ≤
        fixedUpperLayerComplexityFactor j budget n *
          FacePartition.complexity (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      intro e
      let certificate :=
        chosenFixedUpperLayerRegularityCertificate
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n)
          upper (ε n) (budget n)
          (hε n) (hlong n)
      have hstep := certificate.complexity e
      have hexponent :
          (2 ^ (j + 1)) ^ certificate.steps ≤
            (2 ^ (j + 1)) ^ (budget n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt certificate.steps_lt)
      rw [fixedUpperLayerRegularityTower_succ]
      calc
        FacePartition.complexity (certificate.fine e) ≤
            (2 ^ (j + 1)) ^ certificate.steps *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          hstep
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          Nat.mul_le_mul_right _ hexponent
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              (fixedUpperLayerComplexityFactor
                  j budget n *
                FacePartition.complexity (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            fixedUpperLayerComplexityFactor
                j budget (n + 1) *
              FacePartition.complexity (initial e) := by
          simp [fixedUpperLayerComplexityFactor,
            Nat.mul_assoc]

structure FixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (ε index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ)
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

theorem exists_adjacent_real_sub_le_div
    (E : ℕ → ℝ) {length : ℕ}
    (hlength : 0 < length)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [htel]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

theorem FixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (hlength : 0 < length) :
    Nonempty
      (FixedUpperLayerCoarseFine
        G k j initial upper ε budget length) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_le_div
      (fun n => orderedLayerAtomEnergy
        (tower n) upper)
      hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact fixedUpperLayerRegularityTower_refines
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_refines_initial
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_regular
      initial upper ε budget hε hlong i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong i)
        upper)
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong i
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong (i + 1)

noncomputable def chosenFixedUpperLayerCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (hlength : 0 < length) :
    FixedUpperLayerCoarseFine
      G k j initial upper ε budget length :=
  Classical.choice
    (FixedUpperLayerCoarseFine.nonempty
      initial upper ε budget hε hlong hlength)

def selectedOrderedComplexTolerance
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    OrderedRegularityTolerance r :=
  fun j => ε j (index j)

structure StrongOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (selectedOrderedComplexTolerance ε index)
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
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace StrongOrderedComplexRegularityCertificate

def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end StrongOrderedComplexRegularityCertificate

namespace StrongOrderedComplexRegularityCertificate

end StrongOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure CoarseTargetOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  mixedRegular :
    ∀ j : Fin r,
      IsPreliminaryOrderedRegular
        (fine.partition j.castSucc)
        (coarse.partition j.succ)
        (ε j (index j))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace CoarseTargetOrderedComplexRegularityCertificate

def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

end CoarseTargetOrderedComplexRegularityCertificate

namespace OrderedCoarseFineComplex

end OrderedCoarseFineComplex

namespace CoarseTargetOrderedComplexRegularityCertificate

end CoarseTargetOrderedComplexRegularityCertificate

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.AdaptiveCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

inductive AdaptiveCoarseTargetSchedule (k : ℕ) : ℕ → Type
  | nil : AdaptiveCoarseTargetSchedule k 0
  | node {r : ℕ}
      (tolerance : ℕ → ℝ)
      (budget : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → AdaptiveCoarseTargetSchedule k r) :
      AdaptiveCoarseTargetSchedule k (r + 1)

namespace AdaptiveCoarseTargetSchedule

def IsAdmissible {k r : ℕ} :
    AdaptiveCoarseTargetSchedule k r → Prop
  | .nil => True
  | .node tolerance budget length next =>
      (∀ n, 0 ≤ tolerance n) ∧
      (∀ n,
        (Fintype.card (OrderedFace k r) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible

inductive Landing {k : ℕ} :
    {r : ℕ} → AdaptiveCoarseTargetSchedule k r → Type
  | nil : Landing (.nil : AdaptiveCoarseTargetSchedule k 0)
  | node {r : ℕ}
      {tolerance : ℕ → ℝ}
      {budget : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → AdaptiveCoarseTargetSchedule k r}
      (index : Fin length)
      (lower : Landing (next index)) :
      Landing (.node tolerance budget length next)

namespace Landing

def tolerance {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (tolerance := tolerance) _ lower =>
      fun j => Fin.lastCases tolerance lower.tolerance j

def budget {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (budget := budget) _ lower =>
      fun j => Fin.lastCases budget lower.budget j

def length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j

def index {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node chosen lower =>
      fun j => Fin.lastCases chosen.1 lower.index j

@[simp]
theorem tolerance_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance (Fin.last r) =
      tolerance := by
  simp [Landing.tolerance]

@[simp]
theorem tolerance_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j.castSucc =
      lower.tolerance j := by
  simp [Landing.tolerance]

@[simp]
theorem budget_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget (Fin.last r) =
      budget := by
  simp [Landing.budget]

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

@[simp]
theorem length_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length (Fin.last r) =
      length := by
  simp [Landing.length]

@[simp]
theorem length_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j.castSucc =
      lower.length j := by
  simp [Landing.length]

@[simp]
theorem index_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index (Fin.last r) =
      chosen.1 := by
  simp [Landing.index]

@[simp]
theorem index_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index j.castSucc =
      lower.index j := by
  simp [Landing.index]

theorem length_pos {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j, 0 < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨_htolerance, _hbudget, hlength, hnext⟩
      intro j
      cases j using Fin.lastCases with
      | last =>
          simpa using hlength
      | cast j =>
          simpa using ih (hnext chosen) j

end Landing

structure Realization
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r) where
  landing : S.Landing
  certificate :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial
        landing.tolerance landing.budget landing.length
  index_eq : certificate.index = landing.index

end AdaptiveCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedConfigurationCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure PositiveOrderedFace (k r : ℕ) where
  lowerRank : Fin r
  face : OrderedFace k (lowerRank.1 + 1)
deriving DecidableEq

namespace PositiveOrderedFace

def equivSigma (k r : ℕ) :
    PositiveOrderedFace k r ≃
      Σ j : Fin r, OrderedFace k (j.1 + 1) where
  toFun e := ⟨e.lowerRank, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance instFintype (k r : ℕ) :
    Fintype (PositiveOrderedFace k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, OrderedFace k (j.1 + 1))
    (equivSigma k r).symm

def rank {k r : ℕ} (e : PositiveOrderedFace k r) : ℕ :=
  e.lowerRank.1 + 1

@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]

noncomputable def boundary
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨e.lowerRank.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.lowerRank.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.lowerRank.1 := by
    simp only [j]
    omega
  exact hj ▸ eraseBoundaryFace e.face i

@[simp]
theorem boundary_lowerRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).lowerRank.1 =
      e.lowerRank.1 - 1 := by
  rfl

end PositiveOrderedFace

def IsDownwardClosedPositiveFaces
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r)) : Prop :=
  ∀ (e : PositiveOrderedFace k r), e ∈ s →
    ∀ (hpos : 0 < e.lowerRank.1)
      (i : Fin (e.lowerRank.1 + 1)),
      e.boundary hpos i ∈ s

theorem downwardClosed_empty
    {k r : ℕ} :
    IsDownwardClosedPositiveFaces
      (∅ : Finset (PositiveOrderedFace k r)) := by
  intro e he
  simp at he

def configurationFaceWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (C.partition e.lowerRank.succ e.face)
    (A.atom e.lowerRank.succ e.face) y

noncomputable def partialConfigurationWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    configurationFaceWeight A e
      (orderedFaceTuple e.face x)

noncomputable def partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  mean (partialConfigurationWeight A s)

noncomputable def fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) : ℝ :=
  partialConfigurationCount A Finset.univ

@[simp]
theorem partialConfigurationWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    partialConfigurationWeight A ∅ x = 1 := by
  simp [partialConfigurationWeight]

@[simp]
theorem partialConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    partialConfigurationCount A ∅ = 1 := by
  change mean (fun _x : Fin k → G => (1 : ℝ)) = 1
  exact mean_const 1

def positiveFaceLowerLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    OrderedFacePartitionSystem G k e.lowerRank.1 :=
  C.partition e.lowerRank.castSucc

noncomputable def configurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

noncomputable def extendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, configurationCoarseDensity P A e

@[simp]
theorem extendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine) :
    extendedConfigurationCount P A ∅ = 1 := by
  rw [extendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ConfigurationWeightedDefect
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def OrderedCoarseFineComplex.coarseDiagonal
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    OrderedCoarseFineComplex G k r where
  coarse := P.coarse
  fine := P.coarse
  refines := OrderedPartitionComplex.Refines.refl P.coarse

noncomputable def mixedConfigurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

noncomputable def mixedConfigurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

noncomputable def mixedConfigurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationFineDensity P A e y -
    mixedConfigurationCoarseDensity P A e

noncomputable def mixedConfigurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    mixedConfigurationFineDensity P A e y

noncomputable def mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y

def IsFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (τ : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      (τ j)

noncomputable def mixedExtendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, mixedConfigurationCoarseDensity P A e

@[simp]
theorem mixedExtendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    mixedExtendedConfigurationCount P A ∅ = 1 := by
  rw [mixedExtendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedFullBoundary
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩

@[simp]
theorem orderedFullLowerComplexRank_val
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (orderedFullLowerComplexRank e d).1 =
      d.lowerRank.1 + 1 :=
  rfl

abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face

@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl

noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)

noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)

noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x

@[simp]
theorem orderedFullLowerBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryAtomAt C e x).1 =
      (orderedFullLowerBoundaryPartition C e).part x :=
  rfl

noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y

@[simp]
theorem orderedFullLowerBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ^ 2 =
      orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_sq _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_self
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x x = 1 := by
  apply partitionAtomIndicator_of_mem
  exact
    (orderedFullLowerBoundaryPartition C e).mem_part
      (Finset.mem_univ x)

noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y

@[simp]
theorem sourceFullMixedBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ^ 2 =
      sourceFullMixedBoundaryWeight P A e y :=
  orderedFullLowerBoundaryWeight_sq _ _ _ _

def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredFiniteEventSupport
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

theorem centeredFinite_event_measurableSet (event : Set (C × Ω))
    (hevent : ∀ x, MeasurableSet {c | (c,x) ∈ event}) : MeasurableSet event := by
  have hm : Measurable (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left
      (fun x => measurable_const.ite (hevent x) measurable_const)
  have he : event = (fun z : C × Ω => if z ∈ event then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext z
    by_cases hz : z ∈ event <;> simp [hz]
  rw [he]
  exact hm (measurableSet_singleton 1)

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test)) :
    (centeredFiniteProbabilityMeasure μ law).real event =
      ∫ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ∂μ := by
  have hae : event =ᵐ[centeredFiniteProbabilityMeasure μ law] test :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  rw [measureReal_def, measure_congr hae, ← measureReal_def,
    centeredFiniteProbabilityMeasure_real_event μ law hweight test htest]
  apply integral_congr_ae
  apply ae_of_all
  intro c
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (law c).weight x = 0
  · simp only [hx, zero_mul]
  · have hpos := lt_of_le_of_ne ((law c).nonneg x) (Ne.symm hx)
    simp only [heq c x hpos]

include hweight in

theorem centeredFiniteProbabilityMeasure_real_event_le_of_support [IsProbabilityMeasure μ]
    (event test : Set (C × Ω)) (htest : MeasurableSet test)
    (heq : ∀ c x, 0 < (law c).weight x → ((c,x) ∈ event ↔ (c,x) ∈ test))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x => if (c,x) ∈ event then 1 else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real event ≤ ε := by
  rw [centeredFiniteProbabilityMeasure_real_event_of_support μ law hweight event test htest heq]
  calc
    _ ≤ ∫ _ : C, ε ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all μ (fun c => (law c).mean_nonneg (fun _ => by split_ifs <;> norm_num))
      · exact integrable_const ε
      · exact ae_of_all μ hbound
    _ = ε := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

noncomputable def fixedSpatialKernelMap (W L : ℝ) (z : Option G × X → ℝ)
    (t : G → ℝ) : (Σ _ : X, Unit ⊕ Empty) → ℝ :=
  fun a => z (none, a.1) + (L / (1 + W)) * ∑ g, z (some g, a.1) * t g

variable [DecidableEq G]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

noncomputable def fixedSpatialKernelBlock (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (second : Bool) : Matrix X X ℝ :=
  fun x i => (L / (1 + W)) * z (some (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)), x)

noncomputable def fixedSpatialKernelRest (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (t : T → ℝ) : X → ℝ :=
  fun x => (L / (1 + W)) * ∑ j, z (some (e.symm (Sum.inr (Sum.inr j))), x) * t j

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

def fixedSpatialKernelBlockCoordinates (e : G ≃ X ⊕ (X ⊕ T))
    (t : G → ℝ) : (T → ℝ) × ((X → ℝ) × (X → ℝ)) :=
  (fun j => t (e.symm (.inr (.inr j))),
    (fun i => t (e.symm (.inl i)), fun i => t (e.symm (.inr (.inl i)))))

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

noncomputable def fixedSpatialKernelSliceFrame (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) : Option G × X → ℝ :=
  fun a => match a.1 with
    | none => z (none, a.2) + (L / (1 + W)) * ∑ g, z (some g, a.2) * lower g
    | some g => width g * z (some g, a.2)

@[simp] theorem fixedSpatialKernelSliceFrame_none (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (none, x) =
      z (none, x) + (L / (1 + W)) * ∑ g, z (some g, x) * lower g := rfl

@[simp] theorem fixedSpatialKernelSliceFrame_some (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (g : G) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (some g, x) =
      width g * z (some g, x) := rfl

variable {T : Type*} [Fintype X]

omit [Fintype X] in
theorem fixedSpatialKernelBlock_slice (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    fixedSpatialKernelBlock e W L (fixedSpatialKernelSliceFrame W L z lower width) second =
      fun x i => fixedSpatialKernelBlock e W L z second x i *
        width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  funext x i
  simp only [fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
  ring

theorem fixedSpatialKernelBlock_slice_det (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det =
      (fixedSpatialKernelBlock e W L z second).det *
        ∏ i, width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  have hmatrix : fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second =
      fixedSpatialKernelBlock e W L z second * Matrix.diagonal
        (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))) := by
    ext x i
    simp only [Matrix.mul_diagonal, fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]

theorem fixedSpatialKernelBlock_slice_det_ne_zero
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool)
    (hdet : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hwidth : ∀ g, width g ≠ 0) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0 := by
  rw [fixedSpatialKernelBlock_slice_det]
  exact mul_ne_zero hdet (Finset.prod_ne_zero_iff.mpr (fun _ _ => hwidth _))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

noncomputable def containedKernelCubeMap (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → IntegerScalarCubeBox Empty S :=
  fun g => containedProgressionCubeMap Empty S (H g) (step g) (c g) hS (hsubset g) (x g)

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

noncomputable def fixedSpatialKernelBlockEquiv (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  Classical.choose (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_coe (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap =
      matrixSupCLM (fixedSpatialKernelBlock e W L z b) :=
  Classical.choose_spec (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_jacobian (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    inverseJacobian (fixedSpatialKernelBlockEquiv e W L z b h) =
      |(fixedSpatialKernelBlock e W L z b).det|⁻¹ := by
  rw [inverseJacobian_eq]
  congr 2
  change LinearMap.det (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap.toLinearMap = _
  rw [fixedSpatialKernelBlockEquiv_coe]
  exact LinearMap.det_toLin' _

variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

noncomputable def fixedSpatialKernelDensity : (X → ℝ) → ℝ :=
  fixedSpatialBlockDensity (unitBoxMeasure T) (fun x => z (none,x))
    (fixedSpatialKernelRest e W L z)
    (fixedSpatialKernelBlockEquiv e W L z false h0)
    (fixedSpatialKernelBlockEquiv e W L z true h1)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable {T : Type*} [Fintype T] [DecidableEq X]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)
local notation "frame" => fixedSpatialKernelSliceFrame W L z lower width
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width false h0 hw
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width true h1 hw

noncomputable def fixedSpatialKernelSliceDensity : (X → ℝ) → ℝ :=
  fixedSpatialKernelDensity e W L frame h0slice h1slice

local notation "density" => fixedSpatialKernelSliceDensity e W L z lower width h0 h1 hw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastCramer
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {G X T : Type*} [Fintype X] [DecidableEq X]

theorem preparedCenteredForecast_cramer_bounds
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    {P B H κ0 κ1 : ℝ} (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hH : H ∈ Set.Icc (0 : ℝ) 1) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp B) (hi1 : κ1⁻¹ ≤ Real.exp B)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|) :
    ∃ h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0,
    ∃ h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0,
      inverseJacobian (fixedSpatialKernelBlockEquiv e W L z true h1) ≤
        Real.exp (B + P ^ 2 + P) ∧
      ‖(fixedSpatialKernelBlockEquiv e W L z false h0).symm.toContinuousLinearMap‖ ≤
        Real.exp (B + P ^ 2 + P) := by
  have h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0 :=
    abs_pos.mp (hκ0.trans_le hdet0)
  have h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0 :=
    abs_pos.mp (hκ1.trans_le hdet1)
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [fixedSpatialKernelBlockEquiv_jacobian]
    exact ((inv_anti₀ hκ1 hdet1).trans hi1).trans
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg P]))
  · have hnorm := (matrixSupCLM_inverse_norm_le (fixedSpatialKernelBlock e W L z false)
      hH.1 hentry hκ0 hdet0).2
    rw [← fixedSpatialKernelBlockEquiv_coe e W L z false h0,
      ContinuousLinearMap.inverse_equiv] at hnorm
    have hfac := factorial_le_exp_square (Fintype.card X) hP hX
    have hpow : H ^ (Fintype.card X - 1) ≤ 1 := pow_le_one₀ hH.1 hH.2
    have hXexp : (Fintype.card X : ℝ) ≤ Real.exp P :=
      hX.trans (by linarith [Real.add_one_le_exp P])
    have hinner : ((Fintype.card X).factorial : ℝ) * H ^ (Fintype.card X - 1) / κ0 ≤
        Real.exp (P ^ 2) * Real.exp B := by
      rw [div_eq_mul_inv]
      apply mul_le_mul _ hi0 (inv_nonneg.mpr hκ0.le) (Real.exp_nonneg _)
      exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans
        (by simpa only [mul_one] using hfac)
    calc
      _ ≤ Fintype.card X * ((Fintype.card X).factorial * H ^ (Fintype.card X - 1) / κ0) :=
        hnorm
      _ ≤ Real.exp P * (Real.exp (P ^ 2) * Real.exp B) :=
        mul_le_mul hXexp hinner
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH.1 _)) hκ0.le)
          (Real.exp_nonneg _)
      _ = Real.exp (B + P ^ 2 + P) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedUniformShortSourceRankBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedSourceScalarData where
  D : ℝ
  pRadius : ℝ
  Ptail : ℝ
  Prho : ℝ
  Pk : ℝ
  target : ℝ
  F : ℝ
  Tmod : ℝ
  Ppert : ℝ
  Epert : ℝ
  Bstruct : ℝ
  Pmin : ℝ
  Elog : ℝ
  Vlog : ℝ
  master : ℝ
  Pphysical : ℝ
  lateTarget : ℝ
  Eforecast : ℝ
  gainLog : ℝ

namespace PreparedSourceScalarData

noncomputable def scale (v : PreparedSourceScalarData) (m : ℕ) : ℝ :=
  v.pRadius + v.Ptail + fixedPathPerturbationLog v.D (v.D + v.Ppert + 4) v.Epert m

end PreparedSourceScalarData

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealMatrixSpecifiedGrid
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem real_matrix_specified_denominator_grid (M : Matrix ι κ ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : κ → ℝ) (hx : x ∈ realDenominatorGrid l) :
    M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  classical
  choose A hA using hM
  obtain ⟨z, hz⟩ := hx
  refine ⟨A *ᵥ z, funext fun i => ?_⟩
  change (((A *ᵥ z) i : ℤ) : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [← hA i j, hj]
  ring

theorem real_matrix_complement_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    x - M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := real_matrix_specified_denominator_grid M D l hM x ⟨z, hz⟩
  refine ⟨fun i => (D : ℤ) * z i - w i, funext fun i => ?_⟩
  have hzi : (z i : ℝ) = (l : ℝ) * x i := congrFun hz i
  have hwi : (w i : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i := congrFun hw i
  change (((D : ℤ) * z i - w i : ℤ) : ℝ) =
    ((D * l : ℕ) : ℝ) * (x i - (M *ᵥ x) i)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, hzi, hwi]
  ring

theorem real_matrix_complement_linearMap_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) - M.mulVecLin) x ∈ realDenominatorGrid (D * l) := by
  exact real_matrix_complement_specified_denominator_grid M D l hM x hx

end Erdos3

end

end OAI

end


