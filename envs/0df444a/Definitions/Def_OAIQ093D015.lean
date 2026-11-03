-- Prove2me | Definitions.Def_OAIQ093D015
-- name    : OAIQ093D015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:10:17.349509+00:00
-- url     : https://prove2.me/theorems/ac75fb7c-6635-4180-ad76-b6b88bac6b91
-- title:
--   Definitions bundle OAIQ093D015 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 297 declarations of OpenAI's Lean: 154 definitions, 20 instances and 123 theorems. The definitions and types are `OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction`, `OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.commutingDerivationAction`, `OAI.PolycyclicRecognition.SupportDatum.segmentSupportTime`, `OAI.PolycyclicRecognition.SupportDatum.templateSupportConstant`, `OAI.PolycyclicRecognition.boundedResolutionTopHomologyEquiv`, `OAI.PolycyclicRecognition.bundleWordEndpoint`, `OAI.PolycyclicRecognition.cartanRealShadowEquiv`, `OAI.PolycyclicRecognition.cartanSupportVisitPath`, `OAI.PolycyclicRecognition.compactSemidirectLCModel`, `OAI.PolycyclicRecognition.completedIdentity`, `OAI.PolycyclicRecognition.complexAdjointMatrixHom`, `OAI.PolycyclicRecognition.complexificationConjSemilinear`, `OAI.PolycyclicRecognition.coordinateMatrixReadout`, `OAI.PolycyclicRecognition.correctedHom`, `OAI.PolycyclicRecognition.derivationCombination`, `OAI.PolycyclicRecognition.directedDerivedSeries`, `OAI.PolycyclicRecognition.extensionInvariantMean`, `OAI.PolycyclicRecognition.fgDerivedSubgroup`, `OAI.PolycyclicRecognition.finiteIndexCoarseEquivalence`, `OAI.PolycyclicRecognition.finiteInvariantMean`, `OAI.PolycyclicRecognition.finsuppCohomologyIso`, `OAI.PolycyclicRecognition.flatAlternatingProduct`, `OAI.PolycyclicRecognition.horseshoeAugmentation`, `OAI.PolycyclicRecognition.horseshoeCover`, `OAI.PolycyclicRecognition.horseshoeFst`, `OAI.PolycyclicRecognition.horseshoeInl`, `OAI.PolycyclicRecognition.horseshoeInr`, `OAI.PolycyclicRecognition.horseshoeKernel`, `OAI.PolycyclicRecognition.horseshoeKernelInl`, `OAI.PolycyclicRecognition.horseshoeKernelSnd`, `OAI.PolycyclicRecognition.horseshoeLeftTower`, `OAI.PolycyclicRecognition.horseshoeMiddleTower`, `OAI.PolycyclicRecognition.horseshoeRightTower`, `OAI.PolycyclicRecognition.horseshoeSnd`, `OAI.PolycyclicRecognition.horseshoeStage`, `OAI.PolycyclicRecognition.horseshoeSyzygySequence`, `OAI.PolycyclicRecognition.horseshoeTowerInl`, `OAI.PolycyclicRecognition.horseshoeTowerSnd`, `OAI.PolycyclicRecognition.imageInvariantMean`, `OAI.PolycyclicRecognition.inducedCohomologyDifferenceCokernelIso` and 114 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates`, `PolycyclicRecognition_Algebra_BundleWordCoordinates`, `PolycyclicRecognition_Algebra_CommutingDerivationAction`, `PolycyclicRecognition_Algebra_ComplexMatrixExtension`, `PolycyclicRecognition_Algebra_CountableSumPrefixes`, `PolycyclicRecognition_Algebra_CouplingTransfer`, `PolycyclicRecognition_Algebra_DirectedDerivedSeries`, `PolycyclicRecognition_Algebra_FiniteIndexTraceRetract`, `PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries`, `PolycyclicRecognition_Algebra_NormalInductionTensor`, `PolycyclicRecognition_Algebra_NormalizedIdentityConnecting`, `PolycyclicRecognition_Algebra_PolynomialCoordinateAction`, `PolycyclicRecognition_Algebra_PolynomialGroupDifference`, `PolycyclicRecognition_Algebra_PolynomialGroupLaws`, `PolycyclicRecognition_Algebra_PolynomialIdealCongruence`, `PolycyclicRecognition_Algebra_PolynomialLowerCentralProjection`, `PolycyclicRecognition_Algebra_PolynomialModelDifference`, `PolycyclicRecognition_Algebra_PolynomialModelWords`, `PolycyclicRecognition_Algebra_PolynomialParameterExtension`, `PolycyclicRecognition_Algebra_PolynomialSubalgebraFiltration`, `PolycyclicRecognition_Algebra_PolynomialSubalgebraGroup`, `PolycyclicRecognition_Algebra_PolynomialSubalgebraNilpotence`, `PolycyclicRecognition_Algebra_RationalScalarTwist`, `PolycyclicRecognition_Algebra_RegularEvaluationKernel`, `PolycyclicRecognition_Algebra_SequentialModuleTail`, `PolycyclicRecognition_Algebra_SmallCoefficientFiniteIndex`, `PolycyclicRecognition_Algebra_SmallCoefficientRationalRetract`, `PolycyclicRecognition_Algebra_SmallCoefficientTensorAlgebra`, `PolycyclicRecognition_Algebra_SolvableFaithfulRepresentation`, `PolycyclicRecognition_Algebra_TemplateSymmetries`, `PolycyclicRecognition_Algebra_TruncatedEnvelopingDerivation`, `PolycyclicRecognition_Algebra_UpperCentralLayerMap`, `PolycyclicRecognition_Analysis_AmenableCorrection`, `PolycyclicRecognition_Analysis_CoarseEquivalence`, `PolycyclicRecognition_Analysis_CompactExtensionModels`, `PolycyclicRecognition_Analysis_CompactGeneratingBalls`, `PolycyclicRecognition_Analysis_CompactWordCost`, `PolycyclicRecognition_Analysis_ExtensionInvariantMean`, `PolycyclicRecognition_Analysis_HorseshoeCover`, `PolycyclicRecognition_Analysis_LinearSupportSymmetries`, `PolycyclicRecognition_Analysis_MeanSubgroup`, `PolycyclicRecognition_Analysis_PairErgodic`, `PolycyclicRecognition_Analysis_PairMeanControl`, `PolycyclicRecognition_Analysis_SampledSuccessfulVolume`, `PolycyclicRecognition_Analysis_SegmentSupportTimes`, `PolycyclicRecognition_Analysis_StationaryCentered`, `PolycyclicRecognition_Analysis_StationarySlope`, `PolycyclicRecognition_Analysis_SupportSymmetries`, `PolycyclicRecognition_Analysis_SupportTemplates`, `PolycyclicRecognition_Analysis_TemplateOffsetCones`, `PolycyclicRecognition_Analysis_WordBallLeftShift`, `PolycyclicRecognition_Analysis_WordChartLeftShift`, `PolycyclicRecognition_Analysis_WordChartScaleTransition`, `PolycyclicRecognition_Finiteness_BoundedResolutionTopHomology`, `PolycyclicRecognition_Finiteness_CompleteCohomologyConnecting`, `PolycyclicRecognition_Finiteness_CompleteVanishingExactFunctor`, `PolycyclicRecognition_Finiteness_CompletedCohomologyProjective`, `PolycyclicRecognition_Finiteness_CompletedIdentity`, `PolycyclicRecognition_Finiteness_CountableSumVanishing`, `PolycyclicRecognition_Finiteness_FiniteGroupSyzygyScalar`, `PolycyclicRecognition_Finiteness_FinsuppCohomology`, `PolycyclicRecognition_Finiteness_HorseshoeProjectiveTowers`, `PolycyclicRecognition_Finiteness_HorseshoeSyzygySequence`, `PolycyclicRecognition_Finiteness_InducedCohomologyDifference`, `PolycyclicRecognition_Finiteness_IntegerExtensionDuality`, `PolycyclicRecognition_Finiteness_IntegerInducedCochains`, `PolycyclicRecognition_Finiteness_NormalQuotientCompleteVanishing`, `PolycyclicRecognition_Finiteness_NormalizedProjectiveTower`, `PolycyclicRecognition_Finiteness_NormalizedSyzygyIteration`, `PolycyclicRecognition_Finiteness_RegularDualCohomology`, `PolycyclicRecognition_Finiteness_RegularProjectiveEvaluation`, `PolycyclicRecognition_Finiteness_ResolutionCoefficientSequence`, `PolycyclicRecognition_Finiteness_ShiftedCohomologyDimensionShift`, `PolycyclicRecognition_Finiteness_ShiftedCompletedCohomology`, `PolycyclicRecognition_Finiteness_TensorProjectiveTower`, `PolycyclicRecognition_Finiteness_TopHomologyNaturality`, `PolycyclicRecognition_Geometry_AnalyticDerivationAction`, `PolycyclicRecognition_Geometry_CartanRealShadow`, `PolycyclicRecognition_Geometry_CartanRealShadowSolvable`, `PolycyclicRecognition_Geometry_CartanScaleTransition`, `PolycyclicRecognition_Geometry_CartanVisitPath`, `PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism`, `PolycyclicRecognition_Geometry_ExponentialBasisGeneration`, `PolycyclicRecognition_Geometry_IntrinsicAdjointHeight`, `PolycyclicRecognition_Geometry_InvariantGraphLieModel`, `PolycyclicRecognition_Geometry_PresentationRotation`, `PolycyclicRecognition_Geometry_RealPhaseDerivative`, `PolycyclicRecognition_Geometry_RealPhaseExponential`, `PolycyclicRecognition_Geometry_RealShadowSplit`, `PolycyclicRecognition_Geometry_SemidirectPolynomialMaps`, `PolycyclicRecognition_Geometry_SemidirectPolynomialRepresentation`, `PolycyclicRecognition_Geometry_ShadowExponentialCoordinates`, `PolycyclicRecognition_Geometry_TangentRotationRepresentation`, `PolycyclicRecognition_Geometry_TriangularExponentialKernel`, `PolycyclicRecognition_Geometry_TruncatedSemidirectRepresentation`, `PolycyclicRecognition_Geometry_UnipotentLieFlow`, `PolycyclicRecognition_Geometry_UnipotentLieLogarithm`, `PolycyclicRecognition_Geometry_UnitsLieAlgebra`, `PolycyclicRecognition_Geometry_WeightedChainMetric`, `PolycyclicRecognition_Geometry_WeightedMetricChains`, `PolycyclicRecognition_Lattices_LatticeWordExtension`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D007`, `OAIQ093D008`, `OAIQ093D009`, `OAIQ093D010` and `OAIQ093D011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D017` and `OAIQ093D018`; the statements `OAI_PolycyclicRecognition_CartanWordModel_cartan_cell_affine_distance_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_generator_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_independent_raw_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_cartan_linked_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_cartan_neighbor_profiles_common_affine_of_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_increment_mem_template_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_exists_basepoint_geometry_of_factor_bounds`, `OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_target_tuples`, `OAI.PolycyclicRecognition.CartanWordModel.exists_metric_basepoint_sampling_geometry`, `OAI_PolycyclicRecognition_CartanWordModel_exists_original_neighbor_root_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_published_adjacent_scale_labels`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_small_metric_log_chart_shift`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_identical_neighbor_profiles`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_neighbor_common_affinity`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_allowed_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_bounded_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos` and `OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_cartan_cell_affine_distance_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_generator_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_independent_raw_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_cartan_linked_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_cartan_neighbor_profiles_common_affine_of_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_eventually_root_neighbor_labels_eq`, `OAI_PolycyclicRecognition_CartanWordModel_exists_basepoint_geometry_of_factor_bounds`, `OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_measurable_box_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_template_profile_paths`, `OAI.PolycyclicRecognition.CartanWordModel.exists_concentrated_profile_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths`, `OAI_PolycyclicRecognition_CartanWordModel_exists_interval_recurrence_cells_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_exists_linked_probe_paths_with_pivot`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI_PolycyclicRecognition_CartanWordModel_exists_original_neighbor_root_frames`, `OAI_PolycyclicRecognition_CartanWordModel_exists_published_adjacent_scale_labels`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_segment_sampled_visit_bound`, `OAI_PolycyclicRecognition_CartanWordModel_exists_source_target_comparison_schemes`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_neighbor_common_affinity`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_affine_mean_approximation`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_allowed_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_bounded_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_good_affine_templates_support_le`, `OAI_PolycyclicRecognition_CartanWordModel_nonempty_boxProbeChains`, `OAI.PolycyclicRecognition.CartanWordModel.original_neighbor_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.select_linked_profiles_of_published_inputs`, `OAI.PolycyclicRecognition.affine_of_horizontal_labels`, `OAI_PolycyclicRecognition_affine_profile_of_segment_inequalities`, `OAI.PolycyclicRecognition.cartan_cocycle_approximation`, `OAI_PolycyclicRecognition_cartan_cocycle_compact_words`, `OAI.PolycyclicRecognition.cartan_cocycle_polynomial_boxes`, `OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors`, `OAI.PolycyclicRecognition.exists_cartan_n_log_metric_bound` and `OAI_PolycyclicRecognition_exists_compact_allowed_cartan_profiles`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008
import Definitions.Def_OAIQ093D009
import Definitions.Def_OAIQ093D010
import Definitions.Def_OAIQ093D011

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

/-- Exact coordinate transport of the fixed binary polynomial. -/
theorem basis_dynkinProduct (b : Module.Basis (Fin n) ℝ L)
    {c : ℕ} (a : DynkinCoefficients c 2) (x y : L) :
    dynkinProduct a (basisBracket b) (b.equivFun x) (b.equivFun y) =
      b.equivFun (finiteDynkinPolynomial a ![x, y]) := by
  simp only [dynkinProduct, bilinearDynkinPolynomial, finiteDynkinPolynomial,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have hX : (![b.equivFun x, b.equivFun y] : Fin 2 → (Fin n → ℝ)) =
      fun i => b.equivFun (![x, y] i) := by
    funext i
    fin_cases i <;> rfl
  rw [hX]
  exact evalBilinearWord_basisBracket b ![x, y] (rightNestedWord d.val w)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support exponents of compact templates

The support exponent is the finite maximum of word-basis exponents, with
each letter allowed its own supporting point. Balance gives translation
invariance, and segments recover the support norm.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- A fixed Lipschitz constant for the full template support. -/
def templateSupportConstant : ℝ :=
  ∑ b, ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and smooth coordinates for the alternating product

These coordinates keep the two embedding maps among the coefficient
parameters. The input chart can be any fixed continuous linear equivalence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

def flatAlternatingProduct {m n h c : ℕ} (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (p : AlternatingLawData n) (x : Fin m → ℝ) : Fin n → ℝ :=
  alternatingCoordinateProduct a p.1 p.2.1 p.2.2 (e x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleWordCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed source bundles in joint independent coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

def bundleWordEndpoint {I : Type*} {n m h c M N : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (input : (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ))
    (output : (Fin N → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ))
    (p : WordLawData I n) (t : Fin M → ℝ) : Fin N → ℝ :=
  output.symm (fun j => differenceAmplitudeWordEndpoint a letters p (input t j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticDerivationAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth real actions on polynomial exponential groups

Any derivation gives an action; nilpotence of the derivation is unnecessary.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

namespace PolynomialExponentialCoordinates
variable [P : PolynomialExponentialCoordinates L]

def analyticDerivationAction (D : LieDerivation ℝ L L) : Multiplicative ℝ →* MulAut L where
  toFun t := groupAutomorphism (P := P) (analyticDerivationFlow D t.toAdd)
  map_one' := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationFlow_zero D x
  map_mul' s t := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationFlow_add D s.toAdd t.toAdd x

@[simp] theorem analyticDerivationAction_apply (D : LieDerivation ℝ L L)
    (t : Multiplicative ℝ) (x : L) :
    analyticDerivationAction (P := P) D t x = analyticDerivationFlow D t.toAdd x := rfl

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanSubgroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting invariant means to subgroups

The finite-index height kernel in the recognition argument inherits amenability
from the ambient group. The construction below works for an arbitrary subgroup:
choose representatives for right cosets, construct an equivariant map to the subgroup,
and extend each bounded function by composition with this map.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u

variable {G : Type u} [Group G]

/-- Equivariance makes extension commute with pullback by subgroup translations. -/
theorem subgroupFunctionExtension_leftPull (K : Subgroup G) (k : K) (f : BoundedReal K) :
    subgroupFunctionExtension K (leftPull k f) =
      leftPull (k : G) (subgroupFunctionExtension K f) := by
  apply lp.ext
  funext g
  change f (k * subgroupCoordinate K g) = f (subgroupCoordinate K ((k : G) * g))
  rw [subgroupCoordinate_mul]

/-- Every subgroup of a group with an invariant mean has an invariant mean. -/
def subgroupInvariantMean (M : InvariantMean G) (K : Subgroup G) : InvariantMean K where
  toLinearMap := M.toLinearMap.comp (subgroupFunctionExtension K)
  positive f hf := M.positive _ (fun g => hf (subgroupCoordinate K g))
  normalized := by
    change M.toLinearMap (subgroupFunctionExtension K 1) = 1
    rw [subgroupFunctionExtension_one]
    exact M.normalized
  left_invariant k f := by
    change M.toLinearMap (subgroupFunctionExtension K (leftPull k f)) =
      M.toLinearMap (subgroupFunctionExtension K f)
    rw [subgroupFunctionExtension_leftPull]
    exact M.left_invariant (k : G) (subgroupFunctionExtension K f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarseEquivalence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse equivalences of discrete groups

Finite subsets are the bounded sets in a word metric on a finitely generated
group. Controlling all finite sets of differences is the metric-free form of
being bornologous. For finitely generated groups, a coarse equivalence in this
sense is a quasi-isometry. It also matches the coarse-equivalence formulation
of Li's finiteness and duality theorems.
-/

namespace PolycyclicRecognition

open scoped Pointwise

variable {G H J : Type*} [Group G] [Group H] [Group J]

theorem groupBornologous_subgroupCoordinate (K : Subgroup G) [K.FiniteIndex] :
    GroupBornologous (subgroupCoordinate K) := by
  intro S hS
  let R := Set.range (rightCosetRepresentative K)
  have hR : R.Finite := finite_rightCosetRepresentatives K
  let T := R * S * R⁻¹
  have hT : T.Finite := (hR.mul hS).mul hR.inv
  refine ⟨K.subtype ⁻¹' T, hT.preimage (fun _ _ _ _ h => Subtype.val_injective h), ?_⟩
  intro x y hxy
  change ((subgroupCoordinate K x : G))⁻¹ * (subgroupCoordinate K y : G) ∈ T
  have heq : ((subgroupCoordinate K x : G))⁻¹ * (subgroupCoordinate K y : G) =
      rightCosetRepresentative K x * (x⁻¹ * y) * (rightCosetRepresentative K y)⁻¹ := by
    simp [subgroupCoordinate, mul_assoc]
  rw [heq]
  refine ⟨_, ⟨_, ⟨x, rfl⟩, _, hxy, rfl⟩, _, ?_, rfl⟩
  simpa only [Set.mem_inv, inv_inv] using
    (show rightCosetRepresentative K y ∈ R from ⟨y, rfl⟩)

/-- Finite-index subgroups are coarsely equivalent to their ambient groups.
The coordinate map uses a finite right-coset transversal. -/
noncomputable def finiteIndexCoarseEquivalence (K : Subgroup G) [K.FiniteIndex] :
    GroupCoarseEquivalence K G where
  toFun := K.subtype
  invFun := subgroupCoordinate K
  bornologous_toFun := groupBornologous_hom K.subtype
  bornologous_invFun := groupBornologous_subgroupCoordinate K
  left_error := by
    let R := Set.range (rightCosetRepresentative K)
    have hR : R.Finite := finite_rightCosetRepresentatives K
    apply (hR.inv.preimage (fun _ _ _ _ h => Subtype.val_injective h)).subset
    rintro _ ⟨x, rfl⟩
    change (x : G)⁻¹ * ((x : G) * (rightCosetRepresentative K x)⁻¹) ∈ R⁻¹
    simpa only [inv_mul_cancel_left, Set.mem_inv, inv_inv] using
      (show rightCosetRepresentative K x ∈ R from ⟨x, rfl⟩)
  right_error := by
    apply (finite_rightCosetRepresentatives K).inv.subset
    rintro _ ⟨y, rfl⟩
    change y⁻¹ * (y * (rightCosetRepresentative K y)⁻¹) ∈ _
    simpa only [inv_mul_cancel_left, Set.mem_inv, inv_inv] using
      (show rightCosetRepresentative K y ∈ Set.range (rightCosetRepresentative K)
        from ⟨y, rfl⟩)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FinsuppCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct sums in cohomology computed from finite group-ring resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] (G : Type) [Group G] (α : Type)

def finsuppCohomologyIso (P : ProjectiveResolution (Rep.trivial k G k))
    (hP : ∀ i, Module.Finite k[G] (P.complex.X i).ρ.asModule) (A : Rep k G) (i : ℕ) :
    groupCohomology (Rep.finsupp α A) i ≅
      (moduleFinsuppFunctor k α).obj (groupCohomology A i) :=
  groupCohomologyIso (Rep.finsupp α A) i P ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (finsuppCochainsIso k G α P hP A).symm ≪≫
      ((P.complex.linearYonedaObj k A).sc i).mapHomologyIso (moduleFinsuppFunctor k α) ≪≫
        (moduleFinsuppFunctor k α).mapIso (groupCohomologyIso A i P).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerInducedCochains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer coordinates on the induced resolution and its cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

def integerInducedCohomologyIso (i : ℕ) :
    ((normalInducedResolution ℤ q.ker P).complex.linearYonedaObj ℤ
      (Rep.leftRegular ℤ G)).homology i ≅
        (moduleFinsuppFunctor ℤ ℤ).obj
          ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (integerInducedCochainsIso q t ht P hP) ≪≫
    bilateralCohomologyIso ℤ _ i

theorem integerInducedCohomologyIso_translation (i : ℕ) :
    HomologicalComplex.homologyMap
        (repCochainPrecomp ℤ (inducedTranslation ℤ q.ker t P) (Rep.leftRegular ℤ G)) i ≫
        (integerInducedCohomologyIso q t ht P hP i).hom =
      (integerInducedCohomologyIso q t ht P hP i).hom ≫
        (bilateralFunctorTranslation ℤ (Multiplicative.ofAdd 1)).app
          ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) ≫
            (moduleFinsuppFunctor ℤ ℤ).map (conjugationCohomologyIso ℤ q.ker t P i).hom := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (integerInducedCochainsIso_translation q t ht P hP)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change _ ≫ ((HomologicalComplex.homologyMap _ i) ≫
      (bilateralCohomologyIso ℤ _ i).hom) = _
  rw [← Category.assoc, h, Category.assoc, bilateralCohomologyIso_twist]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InducedCohomologyDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity and cokernel of translation minus identity on induced cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] Finsupp.module

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))
  (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

theorem integerInducedCohomologyIso_difference (i : ℕ) :
    inducedCohomologyDifference q t P i ≫
        (integerInducedCohomologyIso q t ht P hP i).hom =
      (integerInducedCohomologyIso q t ht P hP i).hom ≫
        ModuleCat.ofHom (twistedBilateralDifference ℤ _
          (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv) := by
  have h := integerInducedCohomologyIso_translation q t ht P hP i
  rw [inducedCohomologyDifference, inducedTranslationDifference,
    repCochainPrecomp_sub, repCochainPrecomp_id, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id, Preadditive.sub_comp, Category.id_comp, h]
  change _ = (integerInducedCohomologyIso q t ht P hP i).hom ≫
    ((bilateralFunctorTranslation ℤ (Multiplicative.ofAdd 1)).app
      ((P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i) ≫
      (moduleFinsuppFunctor ℤ ℤ).map (conjugationCohomologyIso ℤ q.ker t P i).hom - 𝟙 _)
  rw [Preadditive.comp_sub, Category.comp_id]

include ht hP in
theorem inducedCohomologyDifference_injective (i : ℕ) :
    Function.Injective (inducedCohomologyDifference q t P i).hom := by
  intro x y hxy
  apply (integerInducedCohomologyIso q t ht P hP i).toLinearEquiv.injective
  apply twistedBilateralDifference_injective ℤ _
    (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv
  have h := integerInducedCohomologyIso_difference q t ht P hP i
  have hx := congrArg (fun f => f.hom x) h
  have hy := congrArg (fun f => f.hom y) h
  exact hx.symm.trans ((congrArg (integerInducedCohomologyIso q t ht P hP i).hom.hom hxy).trans hy)

def inducedCohomologyDifferenceCokernelIso (i : ℕ) :
    cokernel (inducedCohomologyDifference q t P i) ≅
      (P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ q.ker)).homology i :=
  cokernel.mapIso _ _
    (integerInducedCohomologyIso q t ht P hP i)
    (integerInducedCohomologyIso q t ht P hP i)
    (integerInducedCohomologyIso_difference q t ht P hP i) ≪≫
      twistedBilateralCokernelIso ℤ _ (conjugationCohomologyIso ℤ q.ker t P i).toLinearEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegerExtensionDuality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cohomological dimension shift for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

section Cyclic
variable [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]

variable (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))

variable (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

attribute [local instance] OAI.PolycyclicRecognition.instCommGroupQuotientSubgroupKerMultiplicativeInt_solutions
include ht hP in
omit [Infinite (G ⧸ q.ker)] in
theorem integerExtensionMap_homology_mono (i : ℕ) :
    Mono (HomologicalComplex.homologyMap
      (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i) := by
  rw [integerExtensionMap_homology]
  exact (ModuleCat.mono_iff_injective _).mpr
    (inducedCohomologyDifference_injective q t ht P hP i)

def integerExtensionCohomologyIso (i : ℕ) :
    groupCohomology (Rep.leftRegular ℤ G) (i + 1) ≅
      groupCohomology (Rep.leftRegular ℤ q.ker) i := by
  let := integerExtensionMap_homology_mono q t ht P hP (i + 1)
  refine groupCohomologyIso (Rep.leftRegular ℤ G) (i + 1) (integerExtensionResolution q t ht P) ≪≫
    (cofiberCochainCokernelIso (integerExtensionMap q t P) (Rep.leftRegular ℤ G) i).symm ≪≫
      ?_ ≪≫ inducedCohomologyDifferenceCokernelIso q t ht P hP i ≪≫
        (groupCohomologyIso (Rep.leftRegular ℤ q.ker) i P).symm
  exact cokernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
    (by
      exact (Category.comp_id (HomologicalComplex.homologyMap
        (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i)).trans
          ((integerExtensionMap_homology q t P i).trans
            (Category.id_comp (inducedCohomologyDifference q t P i)).symm))

end Cyclic

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexifiedLieAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complexification of a real semisimple Lie automorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

def complexificationConjSemilinear : (ℂ ⊗[ℝ] L) →ₗ⋆[ℂ] (ℂ ⊗[ℝ] L) where
  toFun := complexificationConjugation L
  map_add' := map_add (complexificationConjugation L)
  map_smul' := complexificationConjugation_smul L

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentLieLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm of a unipotent Lie automorphism is a derivation

Integer iterates preserve the bracket. Polynomiality extends that identity to
the real flow; its derivative at zero is the derivation identity.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.unipotentLogRationalModule
def unipotentLieLogarithm (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1)) :
    LieDerivation ℝ L L := by
  let D := nilpotentLog (A.toLinearMap - 1)
  have hD : IsNilpotent D := nilpotentLog_nilpotent _ hA
  have hExp : IsNilpotent.exp D = A.toLinearMap := by
    rw [exp_nilpotentLog _ hA]
    abel
  refine { D with leibniz' := ?_ }
  intro x y
  have hxy := hasDerivAt_nilpotentLinearFlow_zero D hD ⁅x, y⁆
  have hx := hasDerivAt_nilpotentLinearFlow_zero D hD x
  have hy := hasDerivAt_nilpotentLinearFlow_zero D hD y
  have hb := (normedLieBracket (L := L)).hasDerivAt_of_bilinear (fun _ => hx) (fun _ => hy)
  have heq : (fun t : ℝ => nilpotentLinearFlow D t ⁅x, y⁆) =
      (fun t : ℝ => ⁅nilpotentLinearFlow D t x, nilpotentLinearFlow D t y⁆) :=
    funext (fun t => nilpotentLinearFlow_preserves_lie A D hD hExp t x y)
  rw [heq] at hxy
  have hd := hxy.unique hb
  change D ⁅x, y⁆ = ⁅nilpotentLinearFlow D 0 x, D y⁆ + ⁅D x, nilpotentLinearFlow D 0 y⁆ at hd
  simp only [nilpotentLinearFlow, zero_smul, IsNilpotent.exp_zero, Module.End.one_apply] at hd
  rw [hd, sub_eq_add_neg, lie_skew (D x) y]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnipotentLieFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A real Lie-automorphism flow through a given unipotent automorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.unipotentFlowRationalModule
theorem unipotentLieLogarithm_toLinearMap (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    (unipotentLieLogarithm A hA).toLinearMap = nilpotentLog (A.toLinearMap - 1) := rfl

theorem unipotentLieLogarithm_nilpotent (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    IsNilpotent (unipotentLieLogarithm A hA).toLinearMap := by
  rw [unipotentLieLogarithm_toLinearMap]
  exact nilpotentLog_nilpotent _ hA

def unipotentLieFlow (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1))
    (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  nilpotentDerivationFlow (unipotentLieLogarithm A hA)
    (unipotentLieLogarithm_nilpotent A hA) t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingDerivationAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth vector actions from commuting derivations -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L I : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [Fintype I]

def derivationCombination (D : I → LieDerivation ℝ L L) (v : I → ℝ) :
    LieDerivation ℝ L L := ∑ i, v i • D i

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_zero (D : I → LieDerivation ℝ L L) :
    derivationCombination D 0 = 0 := by simp [derivationCombination]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_add (D : I → LieDerivation ℝ L L) (s t : I → ℝ) :
    derivationCombination D (s + t) = derivationCombination D s + derivationCombination D t := by
  simp only [derivationCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_commute (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) (s t : I → ℝ) :
    Commute (derivationCombination D s).toLinearMap (derivationCombination D t).toLinearMap := by
  let f := (LieDerivation.toLinearMapLieHom ℝ L).toLinearMap
  change Commute (f (∑ i, s i • D i)) (f (∑ i, t i • D i))
  simp only [map_sum, map_smul]
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((hD i j).smul_left (s i)).smul_right (t j)

theorem analyticDerivationCombination_add (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) (s t : I → ℝ) (x : L) :
    analyticDerivationExp (derivationCombination D (s + t)) x =
      analyticDerivationExp (derivationCombination D s)
        (analyticDerivationExp (derivationCombination D t) x) := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : Commute (E (derivationCombination D s).toLinearMap)
      (E (derivationCombination D t).toLinearMap) :=
    (derivationCombination_commute D hD s t).map E.toRingHom
  simp only [analyticDerivationExp_apply, derivationCombination_add]
  change NormedSpace.exp (E ((derivationCombination D s).toLinearMap +
      (derivationCombination D t).toLinearMap)) x = _
  rw [map_add, NormedSpace.exp_add_of_commute hc]
  rfl

namespace PolynomialExponentialCoordinates
variable [P : PolynomialExponentialCoordinates L]

def commutingDerivationAction (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) :
    Multiplicative (I → ℝ) →* MulAut L where
  toFun t := groupAutomorphism (P := P) (analyticDerivationExp (derivationCombination D t.toAdd))
  map_one' := by
    apply DFunLike.ext
    intro x
    change analyticDerivationExp (derivationCombination D 0) x = x
    rw [derivationCombination_zero, analyticDerivationExp_apply]
    change NormedSpace.exp (0 : L →L[ℝ] L) x = x
    rw [NormedSpace.exp_zero]
    rfl
  map_mul' s t := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationCombination_add D hD s.toAdd t.toAdd x

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBasisGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generation by exponential basis directions

The product of the basis one-parameter subgroups has invertible derivative
at the identity. A subgroup containing those curves is open, hence is the
whole connected group. No global exponential-chart assumption is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G] in
theorem exponentialProduct_mem_subgroup
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} {n : ℕ}
    (S : Subgroup G) (v : Fin n → E)
    (hv : ∀ i (t : ℝ), Exp (t • v i) ∈ S) (x : Fin n → ℝ) :
    exponentialProduct Exp v x ∈ S := by
  rw [exponentialProduct_eq_list_prod]
  apply S.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact hv i (x i)

theorem subgroup_eq_top_of_exponential_basis [PreconnectedSpace G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (S : Subgroup G)
    (hb : ∀ i (t : ℝ), Exp (t • b i) ∈ S) : S = ⊤ := by
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp b) 0 d.toContinuousLinearMap := by
    apply (hExp.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hmap := (locally_injective_open_of_mfderiv_equiv d
    (hExp.contMDiff_exponentialProduct b).contMDiffAt hd).2
  have hS : (S : Set G) ∈ 𝓝 (1 : G) := by
    rw [← hExp.exponentialProduct_zero b, ← hmap]
    change ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), exponentialProduct Exp b x ∈ S
    exact Eventually.of_forall (exponentialProduct_mem_subgroup S b hb)
  have hopen := S.isOpen_of_mem_nhds hS
  have hclosed := S.isClosed_of_isOpen hopen
  have hall : (S : Set G) = univ :=
    (show IsClopen (S : Set G) from ⟨hclosed, hopen⟩).eq_univ ⟨1, S.one_mem⟩
  exact SetLike.coe_injective hall

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic adjoint height on a connected triangular Lie group

The actual adjoint action is positive upper triangular because this holds
on exponential basis curves, which generate the connected group. Its
logarithmic diagonal is therefore a continuous character without a global
exponential chart or a faithful group representation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

variable [IsTopologicalGroup G] [PreconnectedSpace G]

theorem adjointMatrixHom_positive_triangular {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) : (adjointMatrixHom T.basis g).IsUpperTriangular ∧
      ∀ i, 0 < adjointMatrixHom T.basis g i i := by
  let ρ := (adjointMatrixHom T.basis).toHomUnits
  let S := (positiveTriangular n).comap ρ
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    change (adjointMatrixHom T.basis (Exp (t • Module.finBasis ℝ E i))).IsUpperTriangular ∧
      ∀ j, 0 < adjointMatrixHom T.basis (Exp (t • Module.finBasis ℝ E i)) j j
    have he := adjointMatrixHom_exp_intrinsic T.basis hExp (t • Module.finBasis ℝ E i)
    constructor
    · exact he.symm ▸ matrix_exp_upperTriangular _ (T.upper _)
    · intro j
      have hp : 0 < NormedSpace.exp
          (LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ _
            (t • Module.finBasis ℝ E i))) j j := by
        exact (matrix_exp_diagonal _ (T.upper _) j).symm ▸ Real.exp_pos _
      exact he.symm ▸ hp
  have hg : g ∈ S := by rw [hS]; trivial
  exact hg

/-- The character is constructed from the actual adjoint action. -/
def intrinsicAdjointCharacterHom {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) :
    G →* Multiplicative (Fin n → ℝ) :=
  matrixLogDiagonalHom (adjointMatrixHom T.basis)
    (fun g => (adjointMatrixHom_positive_triangular T hExp g).1)
    (fun g => (adjointMatrixHom_positive_triangular T hExp g).2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexMatrixExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex matrix coordinates for the intrinsic adjoint representation -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m n : ℕ}

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

def complexAdjointMatrixHom
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    G →* Matrix (Fin n) (Fin n) ℂ :=
  (complexMatrixExtension b c).toMonoidHom.comp (adjointMatrixHom b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequentialModuleTail
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the first stage of a sequential integral module colimit -/
noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2300] Module.DirectLimit.module
variable (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[ℤ] M j)
  [DirectedSystem M (fun i j h => f i j h)]

def sequentialModuleTailEquiv : ModuleTailLimit M f ≃ₗ[ℤ] Module.DirectLimit M f :=
  LinearEquiv.ofLinearMap (moduleTailToOriginal M f) (moduleOriginalToTail M f)
    (moduleTail_original_inverse M f) (moduleOriginal_tail_inverse M f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyIteration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedCohomologyForward_directed _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.completedCohomologyMap_of _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_d _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyMap_class _root_.OAI.PolycyclicRecognition.shiftedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.shiftedCompletedCohomologyMap_of _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving one normalized syzygy across an iterated syzygy -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedSyzygyIterationIso (A : Rep.{0} ℤ G) (n : ℕ) :
    (iteratedNormalizedSyzygy n).obj (normalizedSyzygy A) ≅
      (iteratedNormalizedSyzygy (n + 1)).obj A :=
  eqToIso (congrArg (fun F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G => F.obj A)
    (normalizedSyzygy_iterate_comm n))

@[simp]
theorem normalizedSyzygyIterationIso_succ (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedSyzygyIterationIso A (n + 1) =
      normalizedSyzygyFunctor.mapIso (normalizedSyzygyIterationIso A n) := by
  exact (eqToIso_map normalizedSyzygyFunctor
    (congrArg (fun F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G => F.obj A)
      (normalizedSyzygy_iterate_comm n))).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomologyProjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete cohomology vanishes on projective coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

instance normalizedSyzygy_projective (A : Rep.{0} ℤ G) [Projective A] :
    Projective (normalizedSyzygy A) := by
  apply (projective_iff_hasProjectiveDimensionLE_zero _).mpr
  exact (normalizedSyzygySequence_shortExact A).hasProjectiveDimensionLT_X₁ 1
    (inferInstance : HasProjectiveDimensionLT (normalizedFreeRepresentation A) 1)
    (hasProjectiveDimensionLT_of_ge A 1 2 (by omega))

instance iteratedNormalizedSyzygy_projective (A : Rep.{0} ℤ G) [Projective A] (n : ℕ) :
    Projective ((iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact inferInstanceAs (Projective A)
  | succ n ih =>
    let := ih
    change Projective (normalizedSyzygy ((iteratedNormalizedSyzygy n).obj A))
    infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ResolutionCoefficientSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short exact coefficient sequences in a projective-resolution Hom complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem resolutionCoefficientSequence_shortExact
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (resolutionCoefficientSequence P S).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine {
    exact := ?_
    mono_f := ?_
    epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro v hv
    change P.complex.X i ⟶ S.X₂ at v
    change v ≫ S.g = 0 at hv
    exact ⟨hS.exact.lift v hv, hS.exact.lift_f v hv⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro v w hvw
    change P.complex.X i ⟶ S.X₁ at v w
    change v ≫ S.f = w ≫ S.f at hvw
    exact (cancel_mono S.f).mp hvw
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro v
    change P.complex.X i ⟶ S.X₃ at v
    exact ⟨Projective.factorThru v S.g, Projective.factorThru_comp v S.g⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedIdentityConnecting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The connecting maps carry the normalized identity cocycle forward -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable (G : Type) [Group G]

def normalizedIdentityConnecting (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))).homology n ⟶
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy (n + 1)).obj (trivialIntegral G))).homology (n + 1) :=
  (resolutionCoefficientSequence_shortExact (normalizedProjectiveResolution (trivialIntegral G))
    (normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))).δ
      n (n + 1) rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete identity detects finite integral cohomological dimension

The class of the augmentation is transported into ordinary cohomology. Its
successive connecting images are the syzygy identity classes. Vanishing of
its image in complete cohomology therefore forces a projective syzygy.
No vanishing from FP-infinity is assumed or asserted.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

def completedIdentity : CompletedCohomology (trivialIntegral G) :=
  Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
    (normalizedGroupIdentityClass G 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteGroupSyzygyScalar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Descending a stable scalar through an integral split syzygy sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

instance normalizedSyzygy_integral_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : Module.Projective ℤ (normalizedSyzygy A) := by
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ)
  let S := normalizedSyzygySequence A
  have hS := (normalizedSyzygySequence_shortExact A).map_of_exact F
  let : Projective ((S.map F).X₃) := by
    change Projective (ModuleCat.of ℤ A)
    infer_instance
  let : Projective ((S.map F).X₂) := by
    change Projective (ModuleCat.of ℤ (normalizedFreeRepresentation A))
    infer_instance
  let sp := hS.splittingOfProjective
  have : Projective ((S.map F).X₁) :=
    (show Retract ((S.map F).X₁) ((S.map F).X₂) from
      ⟨(S.map F).f, sp.r, sp.f_r⟩).projective
  exact ModuleCat.projective_of_module_projective ((S.map F).X₁)

instance iteratedNormalizedSyzygy_integral_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] (n : ℕ) :
    Module.Projective ℤ ((iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact inferInstanceAs (Module.Projective ℤ A)
  | succ n ih =>
    let := ih
    change Module.Projective ℤ (normalizedSyzygy ((iteratedNormalizedSyzygy n).obj A))
    infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCompletedCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.iteratedNormalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonnegative degree shifts of complete cohomology

The hierarchy argument uses positive connecting degrees. The n-th stage is
H^(n+p)(G, Omega^n A), with the actual coefficient connecting maps.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCohomologyStageMap_comp (p : ℕ) {A B C : Rep.{0} ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    shiftedCohomologyStageMap p (f ≫ g) n =
      (shiftedCohomologyStageMap p g n).comp (shiftedCohomologyStageMap p f n) := by
  unfold shiftedCohomologyStageMap
  rw [CategoryTheory.Functor.map_comp, groupCohomology.map_id_comp]
  rfl

instance shiftedCohomologyForward_directed (p : ℕ) (A : Rep.{0} ℤ G) :
    DirectedSystem (shiftedCohomologyStage p A)
      (fun i j h => shiftedCohomologyForward p A i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

def shiftedCompletedCohomologyFunctor (p : ℕ) : Rep.{0} ℤ G ⥤ ModuleCat ℤ where
  obj A := ModuleCat.of ℤ (ShiftedCompletedCohomology p A)
  map f := ModuleCat.ofHom (shiftedCompletedCohomologyMap p f)
  map_id A := by
    apply ModuleCat.hom_ext
    change shiftedCompletedCohomologyMap p (𝟙 A) = LinearMap.id
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [shiftedCompletedCohomologyMap_of]
    rw [shiftedCohomologyStageMap_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change shiftedCompletedCohomologyMap p (f ≫ g) =
      (shiftedCompletedCohomologyMap p g).comp (shiftedCompletedCohomologyMap p f)
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    simp only [LinearMap.comp_apply, shiftedCompletedCohomologyMap_of]
    rw [shiftedCohomologyStageMap_comp]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCohomologyDimensionShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension shifting in the completed coefficient theory -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable {G : Type} [Group G]

def shiftedSyzygyStageIso (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj (normalizedSyzygy A)) (n + (p + 1)) ≅
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1 + p) :=
  (groupCohomology.functor ℤ G (n + (p + 1))).mapIso (normalizedSyzygyIterationIso A n) ≪≫
    eqToIso (congrArg (fun d => groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) d)
      (show n + (p + 1) = n + 1 + p by omega))

theorem shiftedSyzygyStageIso_connecting (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
        (shiftedSyzygyStageIso p A (n + 1)).hom =
      (shiftedSyzygyStageIso p A n).hom ≫ shiftedSyzygyConnecting p A (n + 1) := by
  let e := normalizedSyzygyIterationIso A n
  let Y := (iteratedNormalizedSyzygy (n + 1)).obj A
  have hn := groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj (normalizedSyzygy A)))
    (normalizedSyzygySequence_shortExact Y)
    (normalizedSyzygySequenceMap e.hom)
    (n + (p + 1)) (n + 1 + (p + 1)) (by omega)
  change shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
      (groupCohomology.functor ℤ G (n + 1 + (p + 1))).map
        (normalizedSyzygyFunctor.map e.hom) =
    (groupCohomology.functor ℤ G (n + (p + 1))).map e.hom ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact Y)
        (n + (p + 1)) (n + 1 + (p + 1)) (by omega) at hn
  have ht := cohomologyConnecting_reindex (normalizedSyzygySequence Y)
    (normalizedSyzygySequence_shortExact Y)
    (n + (p + 1)) (n + 1 + (p + 1)) (n + 1 + p) (n + 1 + 1 + p)
    (by omega) (by omega) (by omega) (by omega)
  simp only [shiftedSyzygyStageIso, normalizedSyzygyIterationIso_succ]
  change shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
      ((groupCohomology.functor ℤ G (n + 1 + (p + 1))).map
        (normalizedSyzygyFunctor.map e.hom) ≫ _) = _
  erw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc]


theorem shiftedCohomologyForward_succ (p : ℕ) (A : Rep.{0} ℤ G)
    (i j : ℕ) (h : i ≤ j) (x : shiftedCohomologyStage p A i) :
    shiftedCohomologyForward p A i (j + 1) (Nat.le_succ_of_le h) x =
      (shiftedSyzygyConnecting p A j).hom (shiftedCohomologyForward p A i j h x) := by
  exact Nat.leRecOn_succ (C := shiftedCohomologyStage p A) h x

theorem shiftedSyzygyStageIso_forward (p : ℕ) (A : Rep.{0} ℤ G)
    (i j : ℕ) (h : i ≤ j)
    (x : shiftedCohomologyStage (p + 1) (normalizedSyzygy A) i) :
    (shiftedSyzygyStageIso p A j).hom
        (shiftedCohomologyForward (p + 1) (normalizedSyzygy A) i j h x) =
      shiftedCohomologyForward p A (i + 1) (j + 1) (Nat.add_le_add_right h 1)
        ((shiftedSyzygyStageIso p A i).hom x) := by
  induction h with
  | refl =>
    simp only [shiftedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    rw [shiftedCohomologyForward_succ (p + 1) (normalizedSyzygy A) i j h,
      shiftedCohomologyForward_succ p A (i + 1) (j + 1) (Nat.add_le_add_right h 1)]
    have he := ConcreteCategory.congr_hom (shiftedSyzygyStageIso_connecting p A j)
      (shiftedCohomologyForward (p + 1) (normalizedSyzygy A) i j h x)
    change (shiftedSyzygyStageIso p A (j + 1)).hom
      ((shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) j).hom _) =
        (shiftedSyzygyConnecting p A (j + 1)).hom
          ((shiftedSyzygyStageIso p A j).hom _) at he
    rw [he, ih]

def shiftedSyzygyTailEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃ₗ[ℤ]
      ModuleTailLimit (shiftedCohomologyStage p A) (shiftedCohomologyForward p A) :=
  Module.DirectLimit.congr (f := shiftedCohomologyForward (p + 1) (normalizedSyzygy A))
    (f' := moduleTailMap (shiftedCohomologyStage p A) (shiftedCohomologyForward p A))
    (fun n => (shiftedSyzygyStageIso p A n).toLinearEquiv) (by
      intro i j h
      apply LinearMap.ext
      exact shiftedSyzygyStageIso_forward p A i j h)

def shiftedSyzygyEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃ₗ[ℤ]
      ShiftedCompletedCohomology p A :=
  (shiftedSyzygyTailEquiv p A).trans
    (sequentialModuleTailEquiv (shiftedCohomologyStage p A) (shiftedCohomologyForward p A))

def shiftedSyzygyAddEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃+
      ShiftedCompletedCohomology p A :=
  (shiftedSyzygyEquiv p A).toAddEquiv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CountableSumPrefixes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable coefficient sum as a sequential union of finite prefixes -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
attribute [local instance 2300] Submodule.module
variable {G : Type} [Group G]

def sumPrefixSubmodule (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    Submodule ℤ (integralRepresentationSum A) where
  carrier := {x | ∀ i, n ≤ i → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    change x i + y i = 0
    rw [hx i hi, hy i hi, zero_add]
  smul_mem' := by
    intro r x hx i hi
    have h := congrArg (fun y : integralRepresentationSum A => y i)
      (int_smul_eq_zsmul (integralRepresentationSum A).hV2 r x)
    exact h.trans (by rw [DFinsupp.zsmul_apply, hx i hi, zsmul_zero])

theorem sumPrefixSubmodule_invariant (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (g : G) :
    sumPrefixSubmodule A n ≤ (sumPrefixSubmodule A n).comap ((integralRepresentationSum A).ρ g) := by
  intro x hx i hi
  change (A i).ρ g (x i) = 0
  rw [hx i hi, map_zero]

abbrev sumPrefixRepresentation (A : ℕ → Rep.{0} ℤ G) (n : ℕ) : Rep.{0} ℤ G :=
  Rep.subrepresentation (integralRepresentationSum A) (sumPrefixSubmodule A n)
    (sumPrefixSubmodule_invariant A n)

def sumPrefixInclusion (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ⟶ integralRepresentationSum A :=
  Rep.subtype _ _ _

def sumPrefixMap (A : ℕ → Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    sumPrefixRepresentation A i ⟶ sumPrefixRepresentation A j :=
  Rep.ofHom ⟨Submodule.inclusion (by
    intro x hx k hk
    exact hx k (h.trans hk)), fun _ => rfl⟩

def sumPrefixDiagram (A : ℕ → Rep.{0} ℤ G) : SequentialRepresentationDiagram G where
  obj := sumPrefixRepresentation A
  map := sumPrefixMap A
  map_id _i := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  map_comp _i _j _k _hij _hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl

def sumPrefixColimit (A : ℕ → Rep.{0} ℤ G) :
    (sumPrefixDiagram A).ColimitCocone (integralRepresentationSum A) where
  ι := sumPrefixInclusion A
  comm _i _j _h := by
    change sumPrefixMap A _i _j _h ≫ sumPrefixInclusion A _j = sumPrefixInclusion A _i
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  surj x := by
    classical
    let n := x.support.sup id + 1
    have hx : x ∈ sumPrefixSubmodule A n := by
      intro i hi
      by_contra hn
      have hm : i ∈ x.support := DFinsupp.mem_support_iff.mpr hn
      have hb : i ≤ x.support.sup id := Finset.le_sup (f := id) hm
      dsimp only [n] at hi
      omega
    exact ⟨n, ⟨x, hx⟩, rfl⟩
  zero_exact i x hx := by
    refine ⟨i, le_rfl, ?_⟩
    apply Subtype.ext
    change x.val = 0
    change x.val = 0 at hx
    exact hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationarySlope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging the stationary height cocycle

The normalized pair space carries a measure-preserving action. Its height
evaluation is a cocycle for inverse pullback. We construct that action on the
actual space `L²`, and show that integration gives an additive slope. No
reduced-cohomology assertion is assumed in this construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X]
  [NormedAddCommGroup W]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

instance stationaryL2Isometric : IsIsometricSMul G (Lp W 2 μ) where
  isometry_smul g := by
    change Isometry (stationaryPullback (W := W) μ g)
    exact Lp.isometry_compMeasurePreserving (measurePreserving_smul g⁻¹ μ)

variable [NormedSpace ℝ W] [CompleteSpace W]

instance stationaryL2SMulComm : SMulCommClass G ℝ (Lp W 2 μ) where
  smul_comm g r v := (Lp.compMeasurePreservingₗ ℝ
    (fun x : X => g⁻¹ • x) (measurePreserving_smul g⁻¹ μ)).map_smul r v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryCentered
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The zero-mean Hilbert representation and stationary sublinearity

The closed kernel of integration is invariant under inverse pullback.
Ergodicity removes its invariant vectors. This constructs the representation
to which the published reduced-cohomology input is applied; the conclusion
is the manuscript's averaged sublinear estimate for a fixed measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

attribute [local instance] zeroMeanL2Action

instance zeroMeanL2Isometric : IsIsometricSMul G (ZeroMeanL2 (W := W) μ) where
  isometry_smul g := by
    intro v w
    exact (Lp.isometry_compMeasurePreserving (measurePreserving_smul g⁻¹ μ)) v.val w.val

instance zeroMeanL2SMulComm : SMulCommClass G ℝ (ZeroMeanL2 (W := W) μ) where
  smul_comm g r v := Subtype.ext (smul_comm g r (v : Lp W 2 μ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CouplingTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer functions in the two coupling charts

The transfer is lifted by adding target height. Its domain defect is the
original stationary cocycle defect. In inverse coordinates, differences
inside a fiber are the same defects, and fiber averaging gives the exact
inverse transfer identity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [NormedAddCommGroup W]

/-- The stationary domain defect, with the proposed mean height subtracted. -/
def pairTransferDefect (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (t : G) (p : NormalizedPair G Λ) : W :=
  pairHeight π t p + φ (normalizedTranslate t p) - φ p - (l t).toAdd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derived-series bound passes from finitely generated subgroups -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

def fgDerivedSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H : Subgroup G, H.FG ∧ g ∈ ambientDerivedSeries H n}
  one_mem' := ⟨⊥, Subgroup.FG.bot, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    exact ⟨H ⊔ K, hH.sup hK, Subgroup.mul_mem _
      (ambientDerivedSeries_mono le_sup_left n hx)
      (ambientDerivedSeries_mono le_sup_right n hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DirectedDerivedSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directed unions with uniformly bounded derived series -/
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

def directedDerivedSeries (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H ∈ C, g ∈ ambientDerivedSeries H n}
  one_mem' := by
    obtain ⟨H, hH⟩ := hne
    exact ⟨H, hH, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.mul_mem _
      (ambientDerivedSeries_mono hHL n hx) (ambientDerivedSeries_mono hKL n hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteIndexTraceRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative trace-one coefficients are retracts of induced restrictions

The averaging is over a finite coset space, so the subgroup itself may be
infinite. The trace element is invariant under that subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G R : Type} [Group G] [Ring R] [MulSemiringAction G R]
variable (N : Subgroup G)

variable (e : R) (he : ∀ n : N, (n : G) • e = e)

include he in
theorem relativeTraceTerm_mul (n : N) (g : G) :
    relativeTraceTerm N e ((n : G) * g) = relativeTraceTerm N e g := by
  ext b
  change IndV.mk _ _ ((n : G) * g) (e * (((n : G) * g) • b)) =
    IndV.mk _ _ g (e * (g • b))
  rw [mul_smul]
  have h : e * ((n : G) • (g • b)) = (n : G) • (e * (g • b)) := by
    rw [smul_mul', he]
  rw [h]
  exact induced_mk_mul_left N (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) n g _

def relativeTraceCosetTerm (c : subgroupRightCosets N) : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  Quotient.lift (relativeTraceTerm N e) (by
    intro g h hgh
    let n : N := ⟨h * g⁻¹, (QuotientGroup.rightRel_apply).mp hgh⟩
    have hn : (n : G) * g = h := by simp [n, mul_assoc]
    rw [← hn]
    exact (relativeTraceTerm_mul N e he n g).symm) c

@[simp]
theorem relativeTraceCosetTerm_mk (g : G) :
    relativeTraceCosetTerm N e he (subgroupRightCoset N g) = relativeTraceTerm N e g := rfl

include he in
theorem relativeTraceCosetTerm_action (g : G) (c : subgroupRightCosets N) (b : R) :
    relativeTraceCosetTerm N e he c (g • b) =
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))).ρ g
        (relativeTraceCosetTerm N e he (subgroupRightCosetMulEquiv N g c) b) := by
  induction c using Quotient.inductionOn with
  | _ x =>
    change IndV.mk _ _ x (e * (x • (g • b))) =
      (Representation.ind _ _) g (IndV.mk _ _ (x * g) (e * ((x * g) • b)))
    rw [ind_mk, mul_inv_cancel_right, mul_smul]

variable [Fintype (subgroupRightCosets N)]

def relativeTraceSectionLinear : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  ∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c

def relativeTraceSection : relativeTraceRepresentation (G := G) (R := R) ⟶
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  Rep.ofHom ⟨relativeTraceSectionLinear N e he, fun g => by
    ext b
    simp only [relativeTraceSectionLinear]
    erw [LinearMap.comp_apply]
    change (∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c) (g • b) =
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))).ρ g
        ((∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c) b)
    erw [LinearMap.sum_apply, LinearMap.sum_apply]
    rw [map_sum]
    apply Fintype.sum_equiv (subgroupRightCosetMulEquiv N g)
    intro c
    exact relativeTraceCosetTerm_action N e he g c b⟩

def relativeTraceCounit :
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) ⟶
      relativeTraceRepresentation (G := G) (R := R) :=
  (Rep.indResHomEquiv N.subtype _ _).symm (𝟙 _)

omit [Fintype (subgroupRightCosets N)] in
@[simp]
theorem relativeTraceCounit_mk (g : G) (b : R) :
    (relativeTraceCounit N (R := R)).hom (IndV.mk _ _ g b) = g⁻¹ • b := by
  simp [relativeTraceCounit, Rep.indResHomEquiv, IndV.mk]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalInductionTensor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Induced restriction as the quotient regular representation tensored with a coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory Representation MonoidalCategory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

theorem normalTensorTerm_eq (g h : G)
    (hgh : QuotientGroup.mk' N g = QuotientGroup.mk' N h) :
    normalTensorTerm N A g = normalTensorTerm N A h := by
  let n : N := ⟨h⁻¹ * g, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (h⁻¹ * g) = 1
    rw [map_mul, map_inv, hgh, inv_mul_cancel]⟩
  have hn : h⁻¹ = (n : G) * g⁻¹ := by simp [n, mul_assoc]
  ext a
  change IndV.mk _ _ g⁻¹ (A.ρ g⁻¹ a) = IndV.mk _ _ h⁻¹ (A.ρ h⁻¹ a)
  rw [hn, map_mul, Module.End.mul_apply]
  exact (induced_mk_mul_left N (Rep.res N.subtype A) n g⁻¹ (A.ρ g⁻¹ a)).symm

@[simp]
theorem normalTensorQuotientTerm_mk (g : G) :
    normalTensorQuotientTerm N A (QuotientGroup.mk' N g) = normalTensorTerm N A g :=
  normalTensorTerm_eq N A _ _ (normalQuotientRepresentative_mk N _)

def normalInductionTensorInvLinear :
    quotientRegularTensor N A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ (normalTensorQuotientTerm N A)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp]
theorem normalInductionTensorInvLinear_single (g : G) (a : A) :
    normalInductionTensorInvLinear N A
      (MonoidAlgebra.single (QuotientGroup.mk' N g) 1 ⊗ₜ[ℤ] a) =
        IndV.mk _ _ g⁻¹ (A.ρ g⁻¹ a) := by
  have h : normalInductionTensorInvLinear N A
      (MonoidAlgebra.single (QuotientGroup.mk' N g) (1 : ℤ) ⊗ₜ[ℤ] a) =
      normalTensorQuotientTerm N A (QuotientGroup.mk' N g) a := by
    simp [normalInductionTensorInvLinear]
  rw [h, normalTensorQuotientTerm_mk]
  rfl

theorem normalInductionTensor_left_inv :
    (normalInductionTensorInvLinear N A).comp (normalInductionTensorLinear N A) =
      LinearMap.id := by
  apply IndV.hom_ext
  intro g
  ext a
  change normalInductionTensorInvLinear N A
    (normalInductionTensorLinear N A (IndV.mk _ _ g a)) = IndV.mk _ _ g a
  rw [normalInductionTensorLinear_mk, normalInductionTensorInvLinear_single]
  simp [← Module.End.mul_apply, ← map_mul]

theorem normalInductionTensor_right_inv :
    (normalInductionTensorLinear N A).comp (normalInductionTensorInvLinear N A) =
      LinearMap.id := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  ext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
  change normalInductionTensorLinear N A (normalInductionTensorInvLinear N A
    (MonoidAlgebra.single (QuotientGroup.mk' N g) (1 : ℤ) ⊗ₜ[ℤ] a)) = _
  rw [normalInductionTensorInvLinear_single, normalInductionTensorLinear_mk]
  simp [← Module.End.mul_apply, ← map_mul]

def normalInductionTensorEquiv :
    Rep.ind N.subtype (Rep.res N.subtype A) ≃ₗ[ℤ] quotientRegularTensor N A :=
  LinearEquiv.ofLinearMap (normalInductionTensorLinear N A) (normalInductionTensorInvLinear N A)
    (normalInductionTensor_right_inv N A) (normalInductionTensor_left_inv N A)

/-- This is an isomorphism of the actual ambient group representations. -/
def normalInductionTensorIso :
    Rep.ind N.subtype (Rep.res N.subtype A) ≅ quotientRegularTensor N A :=
  by
    let f := normalInductionTensorHom N A
    let : Mono f := (Rep.mono_iff_injective f).mpr (normalInductionTensorEquiv N A).injective
    let : Epi f := (Rep.epi_iff_surjective f).mpr (normalInductionTensorEquiv N A).surjective
    let : IsIso f := isIso_of_mono_of_epi f
    exact asIso f

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinate-orbit representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {G Q I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G]
  {m : ℕ} (q : Q → G → ℝ)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

def coordinateMatrixReadout : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Q → ℝ) where
  toFun A i := (B (A.mulVec (B.symm ⟨q i, coordinate_mem_orbitSpan q i⟩)) : G → ℝ) 1
  map_add' A C := by
    funext i
    simp only [Matrix.add_mulVec, map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' a A := by
    funext i
    simp only [RingHom.id_apply, Matrix.smul_mulVec, map_smul, Submodule.coe_smul, Pi.smul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite-difference estimate for the polynomial nilpotent group law -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_mul_difference (k : ℕ) (a b c d : L)
    (hac : a - c ∈ lowerCentralSeries ℝ L L k)
    (hbd : b - d ∈ lowerCentralSeries ℝ L L k) :
    ((a * b) - (c * d)) - ((a - c) + (b - d)) ∈
      (lowerCentralSeries ℝ L L (k + 1)).toSubmodule := by
  have h := finiteDynkinPolynomial_sub_linear_mem_succ P.coefficients ![a, b] ![c, d] k (by
    intro i
    fin_cases i
    · exact hac
    · exact hbd)
  have he : ![a, b] - ![c, d] = ![a - c, b - d] := by
    ext i
    fin_cases i <;> rfl
  rw [he, binaryDynkinLinearPart P.coefficients
    (PolynomialExponentialCoordinates.axis_normalized), ← P.mul_eq, ← P.mul_eq] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSubalgebraGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial nilpotent group laws on Lie subalgebras

The finite BCH formula closes every Lie subalgebra under the group law. Lie
homomorphisms from such a subalgebra preserve that same finite formula.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialSubalgebraSubgroup (K : LieSubalgebra ℝ L) : Subgroup L where
  carrier := K
  one_mem' := by rw [P.one_eq_zero]; exact K.zero_mem
  inv_mem' := by
    intro x hx
    rw [P.inv_eq_neg]
    exact K.neg_mem hx
  mul_mem' := by
    intro x y hx hy
    let a : K := ⟨x, hx⟩
    let b : K := ⟨y, hy⟩
    let z : K := finiteDynkinPolynomial P.coefficients ![a, b]
    have hz : (z : L) = x * y := by
      have hh := finiteDynkinPolynomial_map K.incl P.coefficients ![a, b]
      change (z : L) = _ at hh
      rw [P.mul_eq]
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact z.property

@[instance_reducible] def polynomialSubalgebraGroup (K : LieSubalgebra ℝ L) : Group K :=
  inferInstanceAs (Group (polynomialSubalgebraSubgroup K))

attribute [local instance] polynomialSubalgebraGroup

theorem polynomialSubalgebra_mul_eq (K : LieSubalgebra ℝ L) (x y : K) :
    x * y = finiteDynkinPolynomial P.coefficients ![x, y] := by
  apply Subtype.ext
  change (x : L) * (y : L) = _
  rw [P.mul_eq]
  have h := finiteDynkinPolynomial_map K.incl P.coefficients ![x, y]
  have he : (fun i : Fin 2 => K.incl (![x, y] i)) = ![(x : L), (y : L)] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h.symm

def polynomialSubalgebraHom (K : LieSubalgebra ℝ L) (f : K →ₗ⁅ℝ⁆ L) : K →* L where
  toFun := f
  map_one' := by
    have hzero : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [hzero, map_zero, P.one_eq_zero]
  map_mul' x y := by
    rw [polynomialSubalgebra_mul_eq, P.mul_eq]
    have h := finiteDynkinPolynomial_map f P.coefficients ![x, y]
    have he : (fun i : Fin 2 => f (![x, y] i)) = ![f x, f y] := by
      funext i
      fin_cases i <;> rfl
    rwa [he] at h

def polynomialSubalgebraMap (K J : LieSubalgebra ℝ L) (f : K →ₗ⁅ℝ⁆ L)
    (hf : ∀ x, f x ∈ J) : K →* J where
  toFun x := ⟨f x, hf x⟩
  map_one' := Subtype.ext ((polynomialSubalgebraHom K f).map_one)
  map_mul' x y := Subtype.ext ((polynomialSubalgebraHom K f).map_mul x y)

def polynomialSubalgebraEquiv (K J : LieSubalgebra ℝ L) (T : L ≃ₗ⁅ℝ⁆ L)
    (hT : ∀ x ∈ K, T x ∈ J) (hTi : ∀ x ∈ J, T.symm x ∈ K) : K ≃* J where
  toFun x := ⟨T x, hT x x.property⟩
  invFun x := ⟨T.symm x, hTi x x.property⟩
  left_inv x := Subtype.ext (T.symm_apply_apply x)
  right_inv x := Subtype.ext (T.apply_symm_apply x)
  map_mul' x y := Subtype.ext
    ((PolynomialExponentialCoordinates.groupAutomorphism (P := P) T).map_mul x y)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSubalgebraFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic lower-central estimates on polynomial Lie subgroups

The restricted BCH law has the same normalized linear term. Its higher
terms raise the intrinsic lower central series of the subalgebra.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialSubalgebra_axis_normalized (K : LieSubalgebra ℝ L) (i : Fin 2) (v : K) :
    finiteDynkinPolynomial P.coefficients (Pi.single i v) = v := by
  classical
  apply Subtype.ext
  have hh := finiteDynkinPolynomial_map K.incl P.coefficients (Pi.single i v)
  have he : (fun j : Fin 2 => K.incl ((Pi.single i v : Fin 2 → K) j)) =
      Pi.single i (v : L) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he, PolynomialExponentialCoordinates.axis_normalized] at hh
  exact hh

theorem polynomialSubalgebra_mul_difference (K : LieSubalgebra ℝ L)
    (k : ℕ) (a b c d : K)
    (hac : a - c ∈ lowerCentralSeries ℝ K K k)
    (hbd : b - d ∈ lowerCentralSeries ℝ K K k) :
    ((a * b) - (c * d)) - ((a - c) + (b - d)) ∈
      (lowerCentralSeries ℝ K K (k + 1)).toSubmodule := by
  have h := finiteDynkinPolynomial_sub_linear_mem_succ P.coefficients ![a, b] ![c, d] k (by
    intro i
    fin_cases i
    · exact hac
    · exact hbd)
  have he : ![a, b] - ![c, d] = ![a - c, b - d] := by
    ext i
    fin_cases i <;> rfl
  rw [he, binaryDynkinLinearPart P.coefficients (polynomialSubalgebra_axis_normalized K),
    ← polynomialSubalgebra_mul_eq, ← polynomialSubalgebra_mul_eq] at h
  exact h

theorem polynomialSubalgebra_inner_difference (K : LieSubalgebra ℝ L)
    (v : K) (k : ℕ) (x : K) (hx : x ∈ lowerCentralSeries ℝ K K k) :
    v * x * v⁻¹ - x ∈ lowerCentralSeries ℝ K K (k + 1) := by
  let F : ℕ → Submodule ℝ K := fun k => (lowerCentralSeries ℝ K K k).toSubmodule
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  have hv0 : v * (0 : K) = v := by rw [← hone, mul_one]
  have h1 : (v * x - v) - x ∈ F (k + 1) := by
    simpa only [sub_self, sub_zero, zero_add, hv0] using
      polynomialSubalgebra_mul_difference K k v x v 0 (by simp) (by simpa using hx)
  have hd : v * x - v ∈ F k := by
    have hh := (F k).add_mem ((antitone_lowerCentralSeries ℝ K K (Nat.le_succ k)) h1) hx
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have h2 : (v * x * v⁻¹ - 0) - (v * x - v) ∈ F (k + 1) := by
    simpa only [sub_self, add_zero, mul_inv_cancel, hone] using
      polynomialSubalgebra_mul_difference K k (v * x) v⁻¹ v v⁻¹ hd (by simp)
  have hh := (F (k + 1)).add_mem h2 h1
  change v * x * v⁻¹ - x ∈ F (k + 1)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialIdealCongruence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Congruence of the polynomial group law modulo a Lie ideal -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]

theorem finiteDynkinPolynomial_sub_mem_of_sub_mem {c n : ℕ}
    (coeff : DynkinCoefficients c n) (J : LieIdeal ℝ V) (X Y : Fin n → V)
    (hXY : ∀ i, X i - Y i ∈ J) :
    finiteDynkinPolynomial coeff X - finiteDynkinPolynomial coeff Y ∈ J := by
  simp only [finiteDynkinPolynomial, ← Finset.sum_sub_distrib, ← smul_sub]
  apply J.sum_mem
  intro d _
  apply J.sum_mem
  intro w _
  exact J.smul_mem _ (evalBracketWord_sub_mem X Y J hXY (rightNestedWord d.val w))

variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
attribute [local instance] polynomialSubalgebraGroup

theorem polynomialSubalgebra_mul_congr (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K)
    (a b c d : K) (hac : a - c ∈ J) (hbd : b - d ∈ J) : a * b - c * d ∈ J := by
  rw [polynomialSubalgebra_mul_eq, polynomialSubalgebra_mul_eq]
  apply finiteDynkinPolynomial_sub_mem_of_sub_mem P.coefficients J
  intro i
  fin_cases i
  · exact hac
  · exact hbd

theorem polynomialSubalgebra_mul_inv_mem_of_sub_mem (K : LieSubalgebra ℝ L)
    (J : LieIdeal ℝ K) (a b : K) (hab : a - b ∈ J) : a * b⁻¹ ∈ J := by
  have h := polynomialSubalgebra_mul_congr K J a b⁻¹ b b⁻¹ hab (by simp)
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  simpa only [mul_inv_cancel, hone, sub_zero] using h

theorem polynomialSubalgebra_conjugate_mem (K : LieSubalgebra ℝ L)
    (J : LieIdeal ℝ K) (x : K) (hx : x ∈ J) (v : K) : v * x * v⁻¹ ∈ J := by
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  have hv0 : v * (0 : K) = v := by rw [← hone, mul_one]
  have hh : v * x - v ∈ J := by
    have hh := polynomialSubalgebra_mul_congr K J v x v 0 (by simp) (by simpa using hx)
    rwa [hv0] at hh
  exact polynomialSubalgebra_mul_inv_mem_of_sub_mem K J (v * x) v hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSubalgebraNilpotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Group nilpotence of the concrete BCH subgroups

The intrinsic Lie lower central series is a sequence of actual subgroups.
The finite-difference formula puts every group commutator one step deeper.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialLieIdealSubgroup (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K) : Subgroup K where
  carrier := J
  one_mem' := by
    have h : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [h]
    exact J.zero_mem
  inv_mem' := by
    intro x hx
    have h : x⁻¹ = -x := Subtype.ext (P.inv_eq_neg x)
    rw [h]
    exact J.neg_mem hx
  mul_mem' := by
    intro x y hx hy
    let a : J := ⟨x, hx⟩
    let b : J := ⟨y, hy⟩
    let z : J := finiteDynkinPolynomial P.coefficients ![a, b]
    have hz : (z : K) = x * y := by
      have hh := finiteDynkinPolynomial_map J.toLieSubalgebra.incl P.coefficients ![a, b]
      change (z : K) = _ at hh
      rw [polynomialSubalgebra_mul_eq]
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact z.property

instance polynomialLieIdealSubgroup_normal (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K) :
    (polynomialLieIdealSubgroup K J).Normal where
  conj_mem x hx v := polynomialSubalgebra_conjugate_mem K J x hx v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLowerCentralProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive coordinates on the polynomial group's lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialLowerCentralProjection (K : LieSubalgebra ℝ L) (k : ℕ) :
    polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k) →*
      Multiplicative (InvariantLinearLayer (lowerCentralSeries ℝ K K k).toSubmodule
        (lowerCentralSeries ℝ K K (k + 1)).toSubmodule) where
  toFun x := Multiplicative.ofAdd (Submodule.Quotient.mk
    (⟨x.val, x.property⟩ : (lowerCentralSeries ℝ K K k).toSubmodule))
  map_one' := by
    apply Multiplicative.ext
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (1 : K) ∈ lowerCentralSeries ℝ K K (k + 1)
    have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [hone]
    exact LieSubmodule.zero_mem _
  map_mul' x y := by
    apply Multiplicative.ext
    change (Submodule.Quotient.mk ⟨(x : K) * y, _⟩ :
      InvariantLinearLayer (lowerCentralSeries ℝ K K k).toSubmodule
        (lowerCentralSeries ℝ K K (k + 1)).toSubmodule) =
      Submodule.Quotient.mk ⟨(x : K), x.property⟩ + Submodule.Quotient.mk ⟨(y : K), y.property⟩
    rw [← Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).mpr
    change (x : K) * y - ((x : K) + y) ∈ (lowerCentralSeries ℝ K K (k + 1)).toSubmodule
    have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    have hx0 : (x : K) * 0 = x := by rw [← hone, mul_one]
    have hh := polynomialSubalgebra_mul_difference K k (x : K) y x 0 (by simp)
      (by rw [sub_zero]; exact y.property)
    rw [hx0] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelDifference
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group differences in exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d e : ℕ} {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ L}

theorem IsPolynomialInBasis.mul {f g : V → L}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g) :
    IsPolynomialInBasis b c (fun x => f x * g x) := by
  have hp := IsCoordinatePolynomial.pair hf hg
  have h := (coordinatePolynomial_dynkinProduct P.coefficients (basisBracket c)).comp hp
  change IsCoordinatePolynomial (fun x => c.equivFun (f (b.equivFun.symm x) *
    g (b.equivFun.symm x)))
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    basis_dynkinProduct, ← P.mul_eq] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialModelWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered real powers in a polynomial Lie model -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {d : ℕ}

def modelLineHom (v : L) : Multiplicative ℝ →* L where
  toFun t := t.toAdd • v
  map_one' := by change (0 : ℝ) • v = 1; rw [zero_smul, P.one_eq_zero]
  map_mul' s t := (PolynomialExponentialCoordinates.smul_mul v s.toAdd t.toAdd).symm

theorem model_zpow (v : L) (n : ℤ) : v ^ n = (n : ℝ) • v := by
  have h : modelLineHom v (Multiplicative.ofAdd 1) = v := one_smul ℝ v
  calc
    v ^ n = (modelLineHom v (Multiplicative.ofAdd 1)) ^ n := congrArg (fun x : L => x ^ n) h.symm
    _ = modelLineHom v ((Multiplicative.ofAdd 1) ^ n) := (map_zpow _ _ _).symm
    _ = (n : ℝ) • v := by
      change (n • (1 : ℝ)) • v = (n : ℝ) • v
      rw [zsmul_eq_mul, mul_one]

omit [FiniteDimensional ℝ L] P in
theorem IsPolynomialInBasis.coordinate_smul (b : Basis (Fin d) ℝ L)
    (i : Fin d) (v : L) : IsPolynomialInBasis b b (fun x => b.equivFun x i • v) := by
  simpa only [IsPolynomialInBasis, LinearEquiv.apply_symm_apply, map_smul] using
    (IsCoordinatePolynomial.coordinate_smul i (b.equivFun v))

theorem IsPolynomialInBasis.list_prod (b : Basis (Fin d) ℝ L) (fs : List (L → L))
    (hfs : ∀ f ∈ fs, IsPolynomialInBasis b b f) :
    IsPolynomialInBasis b b (fun x => (fs.map (fun f => f x)).prod) := by
  induction fs with
  | nil =>
    simpa only [IsPolynomialInBasis, List.map_nil, List.prod_nil, P.one_eq_zero, map_zero] using
      (IsCoordinatePolynomial.const (I := Fin d) (0 : Fin d → ℝ))
  | cons f fs ih =>
    exact (hfs f (List.mem_cons_self ..)).mul
      (ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)))

def orderedRealWord (b : Basis (Fin d) ℝ L) (X : Fin d → L) (x : L) : L :=
  (List.ofFn (fun i => b.equivFun x i • X i)).prod

theorem orderedRealWord_polynomial (b : Basis (Fin d) ℝ L) (X : Fin d → L) :
    IsPolynomialInBasis b b (orderedRealWord b X) := by
  have h := IsPolynomialInBasis.list_prod b
    (List.ofFn (fun i : Fin d => fun x : L => b.equivFun x i • X i)) (by
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact IsPolynomialInBasis.coordinate_smul b i (X i))
  change IsPolynomialInBasis b b (fun x => (List.ofFn (fun i => b.equivFun x i • X i)).prod)
  simpa only [List.map_ofFn, Function.comp_def] using h

theorem orderedRealWord_integer (b : Basis (Fin d) ℝ L) (X : Fin d → L)
    (z : Fin d → ℤ) :
    orderedRealWord b X (b.equivFun.symm (fun i => (z i : ℝ))) = orderedWord X z := by
  simp only [orderedRealWord, LinearEquiv.apply_symm_apply, orderedWord, model_zpow]

theorem orderedWord_map {H K : Type*} [Group H] [Group K]
    (f : H →* K) (X : Fin d → H) (z : Fin d → ℤ) :
    orderedWord (fun i => f (X i)) z = f (orderedWord X z) := by
  simp only [orderedWord, map_list_prod, List.map_ofFn, Function.comp_def, map_zpow]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialParameterExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending lattice identities through a polynomial coordinate parameter

The parameter need not be linear. This permits ordered exponential coordinates
whose integral grid parametrizes a nilpotent lattice.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {d : ℕ} (b : Basis (Fin d) ℝ L)

theorem polynomial_mul_of_parameter_grid {f p : L → L}
    (hf : IsPolynomialInBasis b b f) (hp : IsPolynomialInBasis b b p)
    (hps : Function.Surjective p)
    (hm : ∀ z w : Fin d → ℤ,
      f (p (b.equivFun.symm (fun i => (z i : ℝ))) * p (b.equivFun.symm (fun i => (w i : ℝ)))) =
      f (p (b.equivFun.symm (fun i => (z i : ℝ)))) * f (p (b.equivFun.symm (fun i => (w i : ℝ))))) :
    ∀ x y, f (x * y) = f x * f y := by
  have hmul := coordinatePolynomial_dynkinProduct P.coefficients (basisBracket b)
  have hmul_eq (u v : Fin d → ℝ) :
      dynkinProduct P.coefficients (basisBracket b) u v =
        b.equivFun (b.equivFun.symm u * b.equivFun.symm v) := by
    simpa only [LinearEquiv.apply_symm_apply, ← P.mul_eq] using
      (basis_dynkinProduct b P.coefficients (b.equivFun.symm u) (b.equivFun.symm v))
  have hpl := IsCoordinatePolynomial.comp hp
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin d → Fin d ⊕ Fin d))
  have hpr := IsCoordinatePolynomial.comp hp
    (IsCoordinatePolynomial.reindex (Sum.inr : Fin d → Fin d ⊕ Fin d))
  have hl := IsCoordinatePolynomial.comp hf (hmul.comp (hpl.pair hpr))
  have hr := hmul.comp ((IsCoordinatePolynomial.comp hf hpl).pair
    (IsCoordinatePolynomial.comp hf hpr))
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, hmul_eq,
    LinearEquiv.symm_apply_apply] at hl hr
  have heq := IsCoordinatePolynomial.ext_integer_grid hl hr (by
    intro z
    exact congrArg b.equivFun (hm (z ∘ Sum.inl) (z ∘ Sum.inr)))
  intro x y
  obtain ⟨u, rfl⟩ := hps x
  obtain ⟨v, rfl⟩ := hps y
  apply b.equivFun.injective
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    LinearEquiv.symm_apply_apply] using congrFun heq (Sum.elim (b.equivFun u) (b.equivFun v))

omit P [FiniteDimensional ℝ L] in
theorem polynomial_leftInverse_of_parameter_grid {f g p : L → L}
    (hf : IsPolynomialInBasis b b f) (hg : IsPolynomialInBasis b b g)
    (hp : IsPolynomialInBasis b b p) (hps : Function.Surjective p)
    (h : ∀ z : Fin d → ℤ,
      g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
        p (b.equivFun.symm (fun i => (z i : ℝ)))) : Function.LeftInverse g f := by
  have he : (g ∘ f) ∘ p = p := ((hg.comp hf).comp hp).ext_integer_grid hp h
  intro x
  obtain ⟨y, rfl⟩ := hps x
  exact congrFun he y

def polynomialGroupEquivFromParameter {f g p : L → L}
    (hf : IsPolynomialInBasis b b f) (hg : IsPolynomialInBasis b b g)
    (hp : IsPolynomialInBasis b b p) (hps : Function.Surjective p)
    (hm : ∀ z w : Fin d → ℤ,
      f (p (b.equivFun.symm (fun i => (z i : ℝ))) * p (b.equivFun.symm (fun i => (w i : ℝ)))) =
      f (p (b.equivFun.symm (fun i => (z i : ℝ)))) * f (p (b.equivFun.symm (fun i => (w i : ℝ)))))
    (hl : ∀ z : Fin d → ℤ,
      g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (hr : ∀ z : Fin d → ℤ,
      f (g (p (b.equivFun.symm (fun i => (z i : ℝ))))) = p (b.equivFun.symm (fun i => (z i : ℝ)))) :
    L ≃* L where
  toFun := f
  invFun := g
  left_inv := polynomial_leftInverse_of_parameter_grid b hf hg hp hps hl
  right_inv := polynomial_leftInverse_of_parameter_grid b hg hf hp hps hr
  map_mul' := polynomial_mul_of_parameter_grid b hf hp hps hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalScalarTwist
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational scalar twists of an ambient coefficient representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

variable (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

def normalHomologyAddAction (d : ℕ) : G →* AddMonoid.End
    (groupHomology (Rep.res N.subtype A) d) where
  toFun g := (normalHomologyMap ℤ N A d g).hom.toAddMonoidHom
  map_one' := by rw [normalHomologyMap_one]; rfl
  map_mul' g h := by rw [normalHomologyMap_mul]; rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RegularProjectiveEvaluation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular-dual evaluation for finite projective modules

Naturality passes the finite free evaluation isomorphism to its projective
retracts. This is the termwise comparison for top-degree duality.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem regularCoinvariantEvaluation_bijective (P A : Rep ℤ G)
    [Projective P] (hP : IntegralRepresentationFinite G P) :
    Function.Bijective (regularCoinvariantEvaluation P A) := by
  classical
  obtain ⟨ι, hι, q, hq⟩ := finiteIntegralFreeCover_exists P hP
  let := hι
  let := hq
  let s := Projective.factorThru (𝟙 P) q
  have hs : s ≫ q = 𝟙 P := Projective.factorThru_comp (𝟙 P) q
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hfree : Function.Bijective (regularCoinvariantEvaluation (Rep.free ℤ G ι) A) := by
    rw [← regularFreeEvaluationEquiv_eq]
    exact (regularFreeEvaluationEquiv ι A).bijective
  constructor
  · intro x y hxy
    have he : regularCoinvariantEvaluation (Rep.free ℤ G ι) A (F.map s x) =
        regularCoinvariantEvaluation (Rep.free ℤ G ι) A (F.map s y) := by
      rw [regularCoinvariantEvaluation_naturality, regularCoinvariantEvaluation_naturality,
        hxy]
    have he' := congrArg (fun z => F.map q z) (hfree.1 he)
    simpa only [← ModuleCat.comp_apply, ← F.map_comp, hs, F.map_id,
      ModuleCat.id_apply] using he'
  · intro y
    obtain ⟨x, hx⟩ := hfree.2 (regularDualMap s ≫ y)
    refine ⟨F.map q x, ?_⟩
    rw [regularCoinvariantEvaluation_naturality, hx, ← Category.assoc,
      ← regularDualMap_comp, hs, regularDualMap_id, Category.id_comp]

def regularProjectiveEvaluationEquiv (P A : Rep ℤ G) [Projective P]
    (hP : IntegralRepresentationFinite G P) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj P ≃ₗ[ℤ] (regularDual P ⟶ A) :=
  LinearEquiv.ofBijective (regularCoinvariantEvaluation P A)
    (regularCoinvariantEvaluation_bijective P A hP)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularEvaluationKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The kernel comparison induced by regular evaluation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularEvaluationKernelAddEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃+
      LinearMap.ker (Linear.leftComp ℤ A (regularDualMap f)) where
  toFun x := ⟨regularCoinvariantEvaluation P A x, by
    change regularDualMap f ≫ regularCoinvariantEvaluation P A x.val = 0
    rw [← regularCoinvariantEvaluation_naturality, x.property, map_zero]⟩
  invFun y := ⟨(regularProjectiveEvaluationEquiv P A hP).symm y, by
    apply (regularCoinvariantEvaluation_bijective Q A hQ).1
    rw [map_zero, regularCoinvariantEvaluation_naturality]
    change regularDualMap f ≫ regularProjectiveEvaluationEquiv P A hP
      ((regularProjectiveEvaluationEquiv P A hP).symm y.val) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (regularProjectiveEvaluationEquiv P A hP).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (regularProjectiveEvaluationEquiv P A hP).apply_symm_apply y.val
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _

def regularEvaluationKernelEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃ₗ[ℤ]
      LinearMap.ker (Linear.leftComp ℤ A (regularDualMap f)) where
  __ := regularEvaluationKernelAddEquiv f A hP hQ
  map_smul' r x := map_intCast_smul (regularEvaluationKernelAddEquiv f A hP hQ) ℤ ℤ r x

def regularKernelCokernelEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃ₗ[ℤ]
      (cokernel (regularDualMap f) ⟶ A) :=
  (regularEvaluationKernelEquiv f A hP hQ).trans
    (cokernelHomModuleEquiv (regularDualMap f) A).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedProjectiveTower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparison with the normalized complete-cohomology construction -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedProjectiveTowerMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    IntegralProjectiveTower.Map (normalizedProjectiveTower A) (normalizedProjectiveTower B) where
  app n := (iteratedNormalizedSyzygy n).map f
  cover n := normalizedFreeMap ((iteratedNormalizedSyzygy n).map f)
  comm_left _n := normalizedSyzygyMap_ι _
  comm_right _n := normalizedFreeAugmentation_natural _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TensorProjectiveTower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projective tower tensored with the coefficient algebra

For a coefficient projective over the integers, tensoring the normalized
integral tower gives an actual projective tower, based at that coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

variable (A : Rep.{0} ℤ G) [Module.Projective ℤ A]

def tensorNormalizedProjectiveTower : IntegralProjectiveTower G where
  obj n := A ⊗ (normalizedProjectiveTower (trivialIntegral G)).obj n
  projectiveObj n := A ⊗ (normalizedProjectiveTower (trivialIntegral G)).projectiveObj n
  projective n := representation_tensor_projective A _
  ι n := (tensorLeft A).map ((normalizedProjectiveTower (trivialIntegral G)).ι n)
  π n := (tensorLeft A).map ((normalizedProjectiveTower (trivialIntegral G)).π n)
  zero n := by
    rw [← CategoryTheory.Functor.map_comp, (normalizedProjectiveTower (trivialIntegral G)).zero,
      CategoryTheory.Functor.map_zero]
  shortExact n := representation_tensorLeft_map_shortExact A
    ((normalizedProjectiveTower (trivialIntegral G)).sequence n)
    ((normalizedProjectiveTower (trivialIntegral G)).shortExact n)

def tensorNormalizedTowerBaseIso : (tensorNormalizedProjectiveTower A).obj 0 ≅ A :=
  ρ_ A

def tensorNormalizedTowerCompletion (p : ℕ) :
    (tensorNormalizedProjectiveTower A).Cohomology p ≃ₗ[ℤ]
      ShiftedCompletedCohomology p A :=
  (tensorNormalizedProjectiveTower A).completeCohomologyEquiv A
    (tensorNormalizedTowerBaseIso A) p

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientFiniteIndex
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_apply _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small coefficient ring over finite-index subgroups

Relative coset indicators provide an actual trace-one element. Restriction to
an integer-finite-dimensional subgroup therefore bounds the dimension of the
ring over the larger subgroup, without requiring normality.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G] (J : Subgroup G) (hJ : J.FG)
variable (N : Subgroup J) (hN : N.FG)

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientRelativeTransversal : SmallCoefficientRing G :=
  ⟨fun x => if smallCoefficientFeature G (Sum.inr ⟨⟨J, hJ⟩, ⟨N, hN⟩⟩, 1) x then 1 else 0,
    booleanStepRing_coordinate _ _⟩

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientRelativeTransversal_apply (x : G) :
    (smallCoefficientRelativeTransversal G J hJ N hN).val x =
      if subgroupRightPart J x ∈ N then 1 else 0 := by
  simp [smallCoefficientRelativeTransversal, smallCoefficientFeature]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientRationalRetract
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational constants split off the rationalized bounded coefficient ring -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory ThompsonNonamenability
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

abbrev smallCoefficientRationalTensor : Rep ℤ G :=
  Rep.trivial ℤ G ℚ ⊗ smallCoefficientRepresentation G

theorem smallCoefficientRationalTensor_action (g : G)
    (x : smallCoefficientRationalTensor (G := G)) :
    (smallCoefficientRationalTensor (G := G)).ρ g x = smallCoefficientRationalAction g x := by
  induction x using OAI.tensorInductionOn with
  | tmul q b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def smallCoefficientRationalConstants :
    Rep.trivial ℤ G ℚ ⟶ smallCoefficientRationalTensor (G := G) :=
  Rep.ofHom ⟨(TensorProduct.mk ℤ ℚ (SmallCoefficientRing G)).flip 1, fun g => by
    ext q
    change q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G) = q ⊗ₜ[ℤ] (g • (1 : SmallCoefficientRing G))
    rw [smul_one]⟩

def smallCoefficientRationalRetract (M : InvariantMean G) :
    Retract (Rep.trivial ℤ G ℚ) (smallCoefficientRationalTensor (G := G)) := by
  let hmexists := exists_smallCoefficient_rational_mean M
  let m := Classical.choose hmexists
  have hm := (Classical.choose_spec hmexists).1
  have hinv := (Classical.choose_spec hmexists).2
  let r : smallCoefficientRationalTensor (G := G) ⟶ Rep.trivial ℤ G ℚ :=
    Rep.ofHom ⟨m.restrictScalars ℤ, fun g => by
      apply LinearMap.ext
      intro x
      change m ((smallCoefficientRationalTensor (G := G)).ρ g x) = m x
      rw [smallCoefficientRationalTensor_action, hinv]⟩
  refine ⟨smallCoefficientRationalConstants, r, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext q
  change m (q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) = q
  have he : q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G) =
      q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul, hm, smul_eq_mul, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientTensorAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_apply _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRelativeTransversal_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit and multiplication on the small coefficient tensor functor -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

set_option synthInstance.maxHeartbeats 400000 in
abbrev smallCoefficientTensor (A : Rep.{0} ℤ G) : Rep ℤ G :=
  smallCoefficientRepresentation G ⊗ A

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientTensorUnit (A : Rep.{0} ℤ G) : A ⟶ smallCoefficientTensor A :=
  Rep.ofHom ⟨TensorProduct.mk ℤ (SmallCoefficientRing G) A 1, fun g => by
      apply LinearMap.ext
      intro x
      change (1 : SmallCoefficientRing G) ⊗ₜ[ℤ] A.ρ g x =
        (g • (1 : SmallCoefficientRing G)) ⊗ₜ[ℤ] A.ρ g x
      rw [smul_one]⟩

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientTensorUnit_apply (A : Rep.{0} ℤ G) (x : A) :
    (smallCoefficientTensorUnit A).hom x = (1 : SmallCoefficientRing G) ⊗ₜ[ℤ] x := rfl

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientMultiplication :
    smallCoefficientRepresentation G ⊗ smallCoefficientRepresentation G ⟶
      smallCoefficientRepresentation G :=
  Rep.ofHom ⟨LinearMap.mul' ℤ (SmallCoefficientRing G), fun g => by
    apply TensorProduct.ext'
    intro x y
    change (g • x) * (g • y) = g • (x * y)
    exact (smul_mul' g x y).symm⟩

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientTensorMultiply (A : Rep.{0} ℤ G) :
    smallCoefficientTensor (smallCoefficientTensor A) ⟶ smallCoefficientTensor A :=
  (α_ (smallCoefficientRepresentation G) (smallCoefficientRepresentation G) A).inv ≫
    (smallCoefficientMultiplication ⊗ₘ 𝟙 A)

set_option synthInstance.maxHeartbeats 400000 in
@[simp]
theorem smallCoefficientTensorMultiply_apply (A : Rep.{0} ℤ G)
    (b c : SmallCoefficientRing G) (x : A) :
    (smallCoefficientTensorMultiply A).hom (b ⊗ₜ[ℤ] (c ⊗ₜ[ℤ] x)) =
      (b * c) ⊗ₜ[ℤ] x := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedEnvelopingDerivation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivations on the finite truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "Q" => TruncatedEnvelopingAlgebra R L

def truncatedEnvelopingDerivation (c : ℕ) (D : LieDerivation R L L) : Q c →ₗ[R] Q c where
  toFun := Quotient.map' (envelopingDerivation D) (by
    intro x y hxy
    apply ((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mpr
    rw [← map_sub]
    exact envelopingDerivation_preserves_truncation D c
      (((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mp hxy))
  map_add' x y := Quotient.inductionOn₂ x y fun a b => by
    change truncatedEnvelopingProjection c (envelopingDerivation D (a + b)) =
      truncatedEnvelopingProjection c (envelopingDerivation D a) +
      truncatedEnvelopingProjection c (envelopingDerivation D b)
    rw [map_add, map_add]
  map_smul' r x := Quotient.inductionOn x fun a => by
    change truncatedEnvelopingProjection c (envelopingDerivation D (r • a)) =
      r • truncatedEnvelopingProjection c (envelopingDerivation D a)
    rw [map_smul, map_smul]

@[simp]
theorem truncatedEnvelopingDerivation_projection (c : ℕ) (D : LieDerivation R L L) (u : U) :
    truncatedEnvelopingDerivation c D (truncatedEnvelopingProjection c u) =
      truncatedEnvelopingProjection c (envelopingDerivation D u) := rfl

@[simp]
theorem truncatedEnvelopingDerivation_generator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    truncatedEnvelopingDerivation c D (truncatedEnvelopingGenerator c x) =
      truncatedEnvelopingGenerator c (D x) := by
  change truncatedEnvelopingProjection c
    (envelopingDerivation D (UniversalEnvelopingAlgebra.ι R x)) = _
  rw [envelopingDerivation_generator]
  rfl

theorem truncatedEnvelopingDerivation_mul (c : ℕ) (D : LieDerivation R L L) (x y : Q c) :
    truncatedEnvelopingDerivation c D (x * y) =
      x * truncatedEnvelopingDerivation c D y + truncatedEnvelopingDerivation c D x * y := by
  obtain ⟨a, rfl⟩ := truncatedEnvelopingProjection_surjective c x
  obtain ⟨b, rfl⟩ := truncatedEnvelopingProjection_surjective c y
  rw [← map_mul, truncatedEnvelopingDerivation_projection, envelopingDerivation_mul,
    map_add, map_mul, map_mul, truncatedEnvelopingDerivation_projection,
    truncatedEnvelopingDerivation_projection]

def truncatedEnvelopingDerivationRepresentation (c : ℕ) :
    LieDerivation R L L →ₗ⁅R⁆ Module.End R (Q c) where
  toFun := truncatedEnvelopingDerivation c
  map_add' D E := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [LinearMap.add_apply, truncatedEnvelopingDerivation_projection,
      envelopingDerivation_add, map_add]
  map_smul' r D := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [LinearMap.smul_apply, truncatedEnvelopingDerivation_projection,
      envelopingDerivation_smul, map_smul, RingHom.id_apply]
  map_lie' {D E} := by
    ext x
    obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective c x
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      truncatedEnvelopingDerivation_projection, envelopingDerivation_lie, map_sub]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TruncatedSemidirectRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Representing a semidirect extension on the truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Q" => TruncatedEnvelopingAlgebra R L

def truncatedLeftRepresentation (c : ℕ) : L →ₗ⁅R⁆ Module.End R (Q c) :=
  (Algebra.lmul R (Q c)).toLieHom.comp (truncatedEnvelopingGenerator c)

@[simp]
theorem truncatedLeftRepresentation_apply (c : ℕ) (x : L) (u : Q c) :
    truncatedLeftRepresentation (R := R) c x u = truncatedEnvelopingGenerator c x * u := rfl

theorem truncated_derivation_left_commutator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    ⁅truncatedEnvelopingDerivation c D, truncatedLeftRepresentation (R := R) c x⁆ =
      truncatedLeftRepresentation (R := R) c (D x) := by
  ext u
  change truncatedEnvelopingDerivation c D (truncatedEnvelopingGenerator c x * u) -
    truncatedEnvelopingGenerator c x * truncatedEnvelopingDerivation c D u = _
  rw [truncatedEnvelopingDerivation_mul, truncatedEnvelopingDerivation_generator]
  simp

theorem truncated_left_derivation_commutator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    ⁅truncatedLeftRepresentation (R := R) c x, truncatedEnvelopingDerivation c D⁆ =
      -truncatedLeftRepresentation (R := R) c (D x) := by
  rw [← lie_skew, truncated_derivation_left_commutator]

variable {H : Type*} [LieRing H] [LieAlgebra R H]

def truncatedSemidirectRepresentation (c : ℕ) (ψ : H →ₗ⁅R⁆ LieDerivation R L L) :
    (L ⋊⁅ψ⁆ H) →ₗ⁅R⁆ Module.End R (Q c) where
  toFun p := truncatedLeftRepresentation (R := R) c p.left +
    truncatedEnvelopingDerivationRepresentation c (ψ p.right)
  map_add' p q := by
    change truncatedLeftRepresentation (R := R) c (p.left + q.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ (p.right + q.right)) = _
    simp only [map_add]
    abel
  map_smul' r p := by
    change truncatedLeftRepresentation (R := R) c (r • p.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ (r • p.right)) = _
    simp only [map_smul, RingHom.id_apply, smul_add]
  map_lie' {p q} := by
    change truncatedLeftRepresentation (R := R) c
      (⁅p.left, q.left⁆ + ψ p.right q.left - ψ q.right p.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ ⁅p.right, q.right⁆) =
      ⁅truncatedLeftRepresentation (R := R) c p.left + truncatedEnvelopingDerivation c (ψ p.right),
        truncatedLeftRepresentation (R := R) c q.left + truncatedEnvelopingDerivation c (ψ q.right)⁆
    simp only [map_add, map_sub, LieHom.map_lie, lie_add, add_lie,
      truncated_left_derivation_commutator, truncated_derivation_left_commutator]
    change _ + ⁅truncatedEnvelopingDerivation c (ψ p.right),
      truncatedEnvelopingDerivation c (ψ q.right)⁆ = _
    abel

@[simp]
theorem truncatedEnvelopingDerivation_one (c : ℕ) (D : LieDerivation R L L) :
    truncatedEnvelopingDerivation c D 1 = 0 := by
  change truncatedEnvelopingProjection c (envelopingDerivation D (1 :
    UniversalEnvelopingAlgebra R L)) = 0
  have h : envelopingDerivation D (1 : UniversalEnvelopingAlgebra R L) = 0 := by
    simpa using envelopingDerivation_scalar D (1 : R)
  rw [h, map_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SolvableFaithfulRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful representation nilpotent on the canonical nilradical

The representation is obtained from the proved nilshadow and its finite
truncated enveloping algebra. Real triangularization is a separate step.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H

def solvableTruncatedRepresentation (c : ℕ) :
    L →ₗ⁅ℝ⁆ Module.End ℝ (TruncatedEnvelopingAlgebra ℝ K c) :=
  (truncatedSemidirectRepresentation c (nilshadowWeightAction T H).range.incl).comp
    (nilshadowSemidirectEmbedding T H)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportSymmetries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite group of height labels

The segment support determines a finite spanning body in the dual. A linear
support isometry preserves that body and hence permutes its vertices. This
proves finiteness of the group used to label stationary slopes and profiles.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

variable (D : SupportDatum W I B)

/-- A support isometry preserves the concrete dual support body. -/
theorem supportBody_preserved (A : W ≃L[ℝ] W)
    (hA : ∀ w, D.segmentSupport (A w) = D.segmentSupport w) :
    heightDualAction A '' convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) =
      convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    apply (D.mem_supportBody_iff _).mpr
    intro w
    change φ (A w) ≤ D.segmentSupport w
    rw [← hA w]
    exact (D.mem_supportBody_iff φ).mp hφ (A w)
  · intro φ hφ
    refine ⟨heightDualAction A.symm φ, ?_, ?_⟩
    · apply (D.mem_supportBody_iff _).mpr
      intro w
      change φ (A.symm w) ≤ D.segmentSupport w
      have h := (D.mem_supportBody_iff φ).mp hφ (A.symm w)
      simpa only [← hA (A.symm w), A.apply_symm_apply] using h
    · ext w
      simp only [heightDualAction_apply, A.symm_apply_apply]

/-- There are finitely many possible linear labels. The finite set is
determined by the support data, independently of any quasi-isometry. -/
theorem finite_support_isometries :
    Set.Finite {A : W ≃L[ℝ] W | ∀ w, D.segmentSupport (A w) = D.segmentSupport w} := by
  classical
  let Labels := {A : W ≃L[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  let DualLabels := {A : (W →L[ℝ] ℝ) ≃L[ℝ] (W →L[ℝ] ℝ) //
    A '' convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) =
      convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ))}
  have hfinite : Finite DualLabels :=
    (finite_polytope_symmetries D.supportForms D.supportForms_span).to_subtype
  let f : Labels → DualLabels := fun A =>
    ⟨heightDualAction A.val, supportBody_preserved D A.val A.property⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    ext w
    apply sub_eq_zero.mp
    apply D.supportForms_separate
    intro φ _
    have hφ := congrArg (fun T : DualLabels => T.val φ w) h
    change φ (A.val w) = φ (B.val w) at hφ
    simpa only [map_sub] using sub_eq_zero.mpr hφ
  have : Finite Labels := Finite.of_injective f hinj
  exact Set.finite_coe_iff.mp this

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearSupportSymmetries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic support symmetries

The finite symmetry conclusion does not require a preselected norm or
topology on the finite-dimensional height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

/-- The support norm supplies the topology used to prove finiteness. The
result concerns the original algebraic linear equivalences. -/
theorem finite_linear_support_isometries (D : SupportDatum W I B) :
    Set.Finite {A : W ≃ₗ[ℝ] W | ∀ w, D.segmentSupport (A w) = D.segmentSupport w} := by
  let : Norm W := ⟨D.segmentSupport⟩
  let core : NormedSpace.Core ℝ W := D.normCore
  let : NormedAddCommGroup W := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ W := NormedSpace.ofCore core
  let Labels := {A : W ≃ₗ[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  let ContinuousLabels := {A : W ≃L[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  have : Finite ContinuousLabels := (finite_support_isometries D).to_subtype
  let f : Labels → ContinuousLabels := fun A => ⟨A.val.toContinuousLinearEquiv, A.property⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    ext w
    exact congrArg (fun A : ContinuousLabels => A.val w) h
  have : Finite Labels := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp this

instance instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup (D : SupportDatum W I B) : Finite (linearSupportSymmetryGroup D) :=
  (finite_linear_support_isometries D).to_subtype

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateSymmetries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite template-preserving group from the manuscript

Preserving the support exponent of every compact convex template is stronger
than preserving only its values on segments. This file keeps those groups
distinct and proves the required inclusion and finiteness.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- Every template symmetry is an isometry of the segment norm. -/
theorem templateSymmetry_mem_linearSupportSymmetry
    (D : SupportDatum W I B) (A : templateSymmetryGroup D) :
    A.val ∈ linearSupportSymmetryGroup D := by
  intro w
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hn : (segment ℝ (0 : W) w).Nonempty := ⟨0, left_mem_segment ℝ 0 w⟩
  have him : A.val '' segment ℝ (0 : W) w = segment ℝ (0 : W) (A.val w) := by
    change A.val.toLinearMap.toAffineMap '' segment ℝ (0 : W) w = _
    rw [image_segment]
    simp
  have hh := A.property (segment ℝ (0 : W) w) hc hn (convex_segment 0 w)
  rw [him, D.templateSupport_segment, D.templateSupport_segment] at hh
  exact hh

instance finite_templateSymmetryGroup (D : SupportDatum W I B) :
    Finite (templateSymmetryGroup D) := by
  let f : templateSymmetryGroup D → linearSupportSymmetryGroup D :=
    fun A => ⟨A.val, templateSymmetry_mem_linearSupportSymmetry D A⟩
  apply Finite.of_injective f
  intro A C h
  apply Subtype.ext
  exact congrArg (fun x : linearSupportSymmetryGroup D => x.val) h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UpperCentralLayerMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Equivariant rational maps from the actual upper central series -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

def upperCentralLayerMap (i : ℕ) : ambientUpperCentralSeries F (i + 1) →* CentralLayer F i where
  toFun a := ⟨QuotientGroup.mk' (Subgroup.upperCentralSeries F i)
    (ambientUpperCentralToF F (i + 1) a), by
      change ambientUpperCentralToF F (i + 1) a ∈
        (Subgroup.center _).comap (QuotientGroup.mk' (Subgroup.upperCentralSeries F i))
      rw [← Subgroup.upperCentralSeriesStep_eq_comap_center]
      exact (mem_ambientUpperCentralSeries_iff F (i + 1) _).mp a.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

def rationalUpperCentralMap (i : ℕ) :
    ambientUpperCentralSeries F (i + 1) →* Multiplicative (RationalAbelianSpace (CentralLayer F i)) where
  toFun a := Multiplicative.ofAdd (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a)))
  map_one' := by simp
  map_mul' a b := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AmenableCorrection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting bounded height defects with an invariant mean

This is the averaging step in Proposition `recognition-from-height` of the
manuscript *Quasi-isometric recognition of virtually polycyclic groups*.
The mean is on the actual space of all bounded real functions. Neither the
height function itself nor its corrected homomorphism has to be bounded.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u v

variable {G : Type u} [Group G]

/-- Averaging the bounded increments gives an additive homomorphism. -/
def meanCorrection (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) : ℝ :=
  M (boundedIncrement s D hD h)

theorem meanCorrection_mul (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h k : G) :
    meanCorrection M s D hD (h * k) =
      meanCorrection M s D hD h + meanCorrection M s D hD k := by
  unfold meanCorrection
  rw [boundedIncrement_mul, M.map_add]
  exact congrArg (fun t => t + M (boundedIncrement s D hD k))
    (M.left_invariant k (boundedIncrement s D hD h))

@[simp]
theorem meanCorrection_one (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) :
    meanCorrection M s D hD 1 = 0 := by
  have h := meanCorrection_mul M s D hD (1 : G) 1
  simp only [one_mul] at h
  linarith

/-- The finite-dimensional correction obtained by applying the mean to each coordinate. -/
def vectorMeanCorrection {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h : G) (i : ι) : ℝ :=
  meanCorrection M (fun k => s k i) D (coordinate_defect_le s D hD i) h

@[simp]
theorem vectorMeanCorrection_one {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    vectorMeanCorrection M s D hD 1 = 0 := by
  funext i
  exact meanCorrection_one M (fun k => s k i) D (coordinate_defect_le s D hD i)

theorem vectorMeanCorrection_mul {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h k : G) :
    vectorMeanCorrection M s D hD (h * k) =
      vectorMeanCorrection M s D hD h + vectorMeanCorrection M s D hD k := by
  funext i
  exact meanCorrection_mul M (fun k => s k i) D (coordinate_defect_le s D hD i) h k

/-- Finite-dimensional bounded-defect correction, packaged as a genuine homomorphism. -/
def correctedHom {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    G →* Multiplicative (ι → ℝ) where
  toFun h := Multiplicative.ofAdd (vectorMeanCorrection M s D hD h)
  map_one' := vectorMeanCorrection_one M s D hD
  map_mul' := vectorMeanCorrection_mul M s D hD

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactExtensionModels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally compact models in the compact-extension comparison -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

def compactSemidirectLCModel (S : CompactlyGeneratedLCModel) (K : Type)
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
    [CompactSpace K] [SecondCountableTopology K]
    (α : K →* MulAut S.carrier) (hα : Continuous (fun p : K × S.carrier => α p.1 p.2)) :
    CompactlyGeneratedLCModel := by
  let tg : IsTopologicalGroup (S.carrier ⋊[α] K) := semidirectProductTopologicalGroup α hα
  exact
    { carrier := (S.carrier ⋊[α] K)
      compactlyGenerated := compactlyGenerated_compact_semidirect α S.compactlyGenerated }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactGeneratingBalls
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the word API of `Group.Generators`
(`Mathlib/Geometry/Group/WordProd.lean` and `WordMetric.lean` there). -/

namespace OAI

/-! # Compact bounds for words in a compact symmetric generating set -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {G : Type*} [Group G] (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)

include hsymm in
theorem wordLength_ball_subset_pow (hone : (1 : G) ∈ K) (n : ℕ) :
    {g | (Group.Generators.ofSet hK).wordLength g ≤ n} ⊆ K ^ n := by
  intro g hg
  obtain ⟨l, hl, he⟩ := (Group.Generators.ofSet hK).wordLength_le_iff g |>.mp hg
  rw [← he]
  exact Set.pow_right_monotone hone hl (generator_wordProd_mem_pow K hK hsymm l)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactWordCost
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted costs attached to a compact generating neighborhood

Inside the generating neighborhood use the original metric; outside it use
word length. This preserves the local topology while controlling word length.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

variable (K : Set G) (hK : Subgroup.closure K = ⊤)

omit [IsIsometricSMul G G] in
theorem wordLength_le_cost (g : G) :
    (compactWordLength K hK g : ℝ) ≤ max 1 (compactWordCost K hK g : ℝ) := by
  classical
  by_cases hg : g ∈ K
  · have h : (compactWordLength K hK g : ℝ) ≤ 1 := by
      exact_mod_cast compactWordLength_le_one K hK g hg
    exact h.trans (le_max_left _ _)
  · simp only [compactWordCost, ite_eq_right hg, NNReal.coe_natCast]
    exact le_max_right _ _

variable (hbounded : ∀ x y : G, dist x y ≤ 1)

theorem wordLength_le_weightedNorm_add
    (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K) (g : G) :
    (compactWordLength K hK g : ℝ) ≤
      (4 / δ) * compactWeightedNorm K hK hbounded hsymm g + (4 / δ) + 1 := by
  obtain ⟨l, hl, hcost⟩ := exists_productCost_lt (compactWordCost K hK) g 1 (by norm_num)
  have hbound := seminorm_product_cost_bound
    (metricGroupNorm (G := G)).toGroupSeminorm
    (compactWordGenerators K hK).groupNorm.toGroupSeminorm (compactWordCost K hK) hδ hδ1
    (metric_le_compactWordCost K hK hbounded)
    (fun x hx => by
      change (compactWordLength K hK x : ℝ) ≤ 1
      exact_mod_cast compactWordLength_le_one K hK x (hball x hx))
    (wordLength_le_cost K hK) l
  change (compactWordLength K hK l.prod : ℝ) ≤ _ at hbound
  rw [hl] at hbound
  have hcost' : (productCost (compactWordCost K hK) l : ℝ) <
      compactWeightedNorm K hK hbounded hsymm g + 1 := by exact_mod_cast hcost
  nlinarith [div_pos (show (0 : ℝ) < 4 by norm_num) hδ]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExtensionInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.meanCorrection_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealCoinvariantMean_one _root_.OAI.PolycyclicRecognition.smallCoefficientRealMean_one _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.vectorMeanCorrection_one _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on extensions

Average first on each kernel coset and then on the quotient. All averages
act on the actual bounded real functions used in the height correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

variable {G Q : Type*} [Group G] [Group Q]

/-- An invariant mean descends along a surjective group homomorphism. -/
def imageInvariantMean (φ : G →* Q) (hφ : Function.Surjective φ)
    (M : InvariantMean G) : InvariantMean Q where
  toLinearMap := M.toLinearMap.comp (boundedFunctionPull φ)
  positive f hf := M.positive _ (fun g => hf (φ g))
  normalized := by
    change M (boundedFunctionPull φ 1) = 1
    rw [boundedFunctionPull_one]
    exact M.normalized
  left_invariant q f := by
    obtain ⟨g, rfl⟩ := hφ q
    change M (boundedFunctionPull φ (leftPull (φ g) f)) = M (boundedFunctionPull φ f)
    have he : boundedFunctionPull φ (leftPull (φ g) f) =
        leftPull g (boundedFunctionPull φ f) := by
      apply lp.ext
      funext x
      exact congrArg f (φ.map_mul g x).symm
    rw [he, M.left_invariant]

def kernelSlice (φ : G →* Q) (s : Q → G) (q : Q) :
    BoundedReal G →ₗ[ℝ] BoundedReal φ.ker :=
  boundedFunctionPull (fun n : φ.ker => s q * n)

def kernelAverage (φ : G →* Q) (s : Q → G) (M : InvariantMean φ.ker) :
    BoundedReal G →ₗ[ℝ] BoundedReal Q where
  toFun f := ⟨fun q => M (kernelSlice φ s q f), memℓp_infty ⟨‖f‖, by
    rintro y ⟨q, rfl⟩
    have hb : ‖M (kernelSlice φ s q f)‖ ≤ ‖kernelSlice φ s q f‖ := by
      simpa only [Real.norm_eq_abs] using M.abs_apply_le_norm (kernelSlice φ s q f)
    exact hb.trans (boundedFunctionPull_norm_le _ _)⟩⟩
  map_add' f h := by
    apply lp.ext
    funext q
    exact (congrArg M ((kernelSlice φ s q).map_add f h)).trans (M.map_add _ _)
  map_smul' r f := by
    apply lp.ext
    funext q
    exact (congrArg M ((kernelSlice φ s q).map_smul r f)).trans (M.map_smul _ _)

@[simp]
theorem kernelAverage_one (φ : G →* Q) (s : Q → G) (M : InvariantMean φ.ker) :
    kernelAverage φ s M 1 = 1 := by
  apply lp.ext
  funext q
  change M (boundedFunctionPull _ 1) = 1
  rw [boundedFunctionPull_one]
  exact M.normalized

/-- Changing a representative inserts a kernel translation, which disappears
under the inner mean. -/
theorem kernelAverage_leftPull (φ : G →* Q) (s : Q → G) (hs : ∀ q, φ (s q) = q)
    (M : InvariantMean φ.ker) (g : G) (f : BoundedReal G) :
    kernelAverage φ s M (leftPull g f) = leftPull (φ g) (kernelAverage φ s M f) := by
  apply lp.ext
  funext q
  let c : φ.ker := ⟨(s (φ g * q))⁻¹ * g * s q, by
    change φ ((s (φ g * q))⁻¹ * g * s q) = 1
    simp only [map_mul, map_inv, hs]
    group⟩
  have he : kernelSlice φ s q (leftPull g f) =
      leftPull c (kernelSlice φ s (φ g * q) f) := by
    apply lp.ext
    funext n
    change f (g * (s q * n)) = f (s (φ g * q) * ((c : G) * n))
    dsimp only [c]
    group
  change M (kernelSlice φ s q (leftPull g f)) = M (kernelSlice φ s (φ g * q) f)
  rw [he, M.left_invariant]

def extensionInvariantMean (φ : G →* Q) (s : Q → G) (hs : ∀ q, φ (s q) = q)
    (MN : InvariantMean φ.ker) (MQ : InvariantMean Q) : InvariantMean G where
  toLinearMap := MQ.toLinearMap.comp (kernelAverage φ s MN)
  positive f hf := MQ.positive _ (fun q => MN.positive _ (fun n => hf (s q * n)))
  normalized := by
    change MQ (kernelAverage φ s MN 1) = 1
    rw [kernelAverage_one]
    exact MQ.normalized
  left_invariant g f := by
    change MQ (kernelAverage φ s MN (leftPull g f)) = MQ (kernelAverage φ s MN f)
    rw [kernelAverage_leftPull φ s hs, MQ.left_invariant]

/-- The normalized counting mean on a finite group. -/
def finiteInvariantMean [Finite G] : InvariantMean G := by
  classical
  letI := Fintype.ofFinite G
  refine ⟨finiteMeanState Finset.univ, finiteMeanState_positive _,
    finiteMeanState_one _ Finset.univ_nonempty, ?_⟩
  intro g f
  change realAvg Finset.univ (fun x => f (g * x)) = realAvg Finset.univ f
  unfold realAvg
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HorseshoeCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A projective cover adapted to a short exact coefficient sequence

The middle cover is the product of the two endpoint free covers. Its kernel
will provide an exact sequence of syzygies, without claiming that the
normalized free-cover functor itself is exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

abbrev horseshoeCover (S : ShortComplex (Rep.{0} ℤ G)) : Rep.{0} ℤ G :=
  Rep.of ((normalizedFreeRepresentation S.X₁).ρ.prod (normalizedFreeRepresentation S.X₃).ρ)

def horseshoeFst (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeCover S ⟶ normalizedFreeRepresentation S.X₁ :=
  Rep.ofHom (.fst ℤ _ _)

def horseshoeSnd (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeCover S ⟶ normalizedFreeRepresentation S.X₃ :=
  Rep.ofHom (.snd ℤ _ _)

def horseshoeInl (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₁ ⟶ horseshoeCover S :=
  Rep.ofHom (.inl ℤ _ _)

def horseshoeInr (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₃ ⟶ horseshoeCover S :=
  Rep.ofHom (.inr ℤ _ _)

theorem horseshoe_total (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeFst S ≫ horseshoeInl S + horseshoeSnd S ≫ horseshoeInr S = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (x.1 + 0, 0 + x.2) = x
  simp only [add_zero, zero_add]

instance horseshoeCover_projective (S : ShortComplex (Rep.{0} ℤ G)) :
    Projective (horseshoeCover S) where
  factors f e _ := by
    let l := Projective.factorThru (horseshoeInl S ≫ f) e
    let r := Projective.factorThru (horseshoeInr S ≫ f) e
    refine ⟨horseshoeFst S ≫ l + horseshoeSnd S ≫ r, ?_⟩
    rw [Preadditive.add_comp, Category.assoc, Category.assoc,
      Projective.factorThru_comp, Projective.factorThru_comp,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      horseshoe_total, Category.id_comp]

def horseshoeAugmentation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeCover S ⟶ S.X₂ :=
  horseshoeFst S ≫ normalizedFreeAugmentation S.X₁ ≫ S.f +
    horseshoeSnd S ≫ presentationFreeLift S hS

theorem horseshoeAugmentation_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedFreeRepresentation S.X₁) (y : normalizedFreeRepresentation S.X₃) :
    (horseshoeAugmentation S hS).hom (x, y) =
      S.f.hom ((normalizedFreeAugmentation S.X₁).hom x) + (presentationFreeLift S hS).hom y := rfl

@[reassoc]
theorem horseshoeAugmentation_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeAugmentation S hS ≫ S.g = horseshoeSnd S ≫ normalizedFreeAugmentation S.X₃ := by
  rw [horseshoeAugmentation, Preadditive.add_comp, Category.assoc, Category.assoc,
    S.zero, comp_zero, comp_zero, Category.assoc, presentationFreeLift_g, zero_add]

@[reassoc]
theorem horseshoeInl_augmentation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeInl S ≫ horseshoeAugmentation S hS = normalizedFreeAugmentation S.X₁ ≫ S.f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom ((normalizedFreeAugmentation S.X₁).hom x) +
    (presentationFreeLift S hS).hom 0 = _
  rw [map_zero, add_zero]
  rfl

theorem horseshoeAugmentation_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (horseshoeAugmentation S hS).hom := by
  intro z
  let y := normalizedFreeGenerator S.X₃ (S.g.hom z)
  have hy : S.g.hom ((presentationFreeLift S hS).hom y) = S.g.hom z := by
    have h := ConcreteCategory.congr_hom (presentationFreeLift_g S hS) y
    exact h.trans (normalizedFreeAugmentation_generator _ _)
  have hz : S.g.hom (z - (presentationFreeLift S hS).hom y) = 0 := by
    rw [map_sub, hy, sub_self]
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hz
  refine ⟨(normalizedFreeGenerator S.X₁ a, y), ?_⟩
  rw [horseshoeAugmentation_apply, normalizedFreeAugmentation_generator, ha, sub_add_cancel]

instance horseshoeAugmentation_epi (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Epi (horseshoeAugmentation S hS) :=
  (Rep.epi_iff_surjective _).mpr (horseshoeAugmentation_surjective S hS)

abbrev horseshoeKernel (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) : Rep.{0} ℤ G :=
  kernel (horseshoeAugmentation S hS)

def horseshoeKernelInl (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₁ ⟶ horseshoeKernel S hS :=
  kernel.lift (horseshoeAugmentation S hS)
    (kernel.ι (normalizedFreeAugmentation S.X₁) ≫ horseshoeInl S) (by
      rw [Category.assoc, horseshoeInl_augmentation, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
theorem horseshoeKernelInl_ι (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelInl S hS ≫ kernel.ι (horseshoeAugmentation S hS) =
      kernel.ι (normalizedFreeAugmentation S.X₁) ≫ horseshoeInl S := kernel.lift_ι _ _ _

def horseshoeKernelSnd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernel S hS ⟶ normalizedSyzygy S.X₃ :=
  kernel.lift (normalizedFreeAugmentation S.X₃)
    (kernel.ι (horseshoeAugmentation S hS) ≫ horseshoeSnd S) (by
      rw [Category.assoc, ← horseshoeAugmentation_g S hS, ← Category.assoc,
        kernel.condition, zero_comp])

@[reassoc]
theorem horseshoeKernelSnd_ι (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelSnd S hS ≫ kernel.ι (normalizedFreeAugmentation S.X₃) =
      kernel.ι (horseshoeAugmentation S hS) ≫ horseshoeSnd S := kernel.lift_ι _ _ _

theorem horseshoeKernelInl_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedSyzygy S.X₁) :
    (kernel.ι (horseshoeAugmentation S hS)).hom ((horseshoeKernelInl S hS).hom x) =
      ((kernel.ι (normalizedFreeAugmentation S.X₁)).hom x, 0) :=
  ConcreteCategory.congr_hom (horseshoeKernelInl_ι S hS) x

theorem horseshoeKernelSnd_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : horseshoeKernel S hS) :
    (kernel.ι (normalizedFreeAugmentation S.X₃)).hom ((horseshoeKernelSnd S hS).hom x) =
      ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 :=
  ConcreteCategory.congr_hom (horseshoeKernelSnd_ι S hS) x

theorem horseshoeKernel_condition (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : horseshoeKernel S hS) :
    S.f.hom ((normalizedFreeAugmentation S.X₁).hom
        ((kernel.ι (horseshoeAugmentation S hS)).hom x).1) +
      (presentationFreeLift S hS).hom ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 = 0 :=
  ConcreteCategory.congr_hom (kernel.condition (horseshoeAugmentation S hS)) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairErgodic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ergodic probabilities on compact normalized sections

Second countability of the model group gives a Polish topology on the
compact normalized section. Ergodic decomposition therefore applies to
its invariant probabilities.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] {Λ : ℝ≥0}

instance normalizedPair_polishSpace : PolishSpace (NormalizedPair G Λ) := by
  let : MetricSpace (NormalizedPair G Λ) :=
    TopologicalSpace.metrizableSpaceMetric (NormalizedPair G Λ)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairMeanControl
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control of the actual stationary mean

The common Lipschitz constant of normalized pairs bounds their height
profiles, and hence bounds the homomorphism obtained by integration.
Consequently the actual averaged homomorphism kills every root flow.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory LieAlgebra LieModule
open scoped NNReal Manifold

section Mean

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {Λ K : ℝ≥0}

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

attribute [local instance] stationaryL2Action

/-- The averaged slope of the actual evaluation cocycle. -/
def normalizedPairMeanSlope (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) : G →* Multiplicative W :=
  l2MeanSlope μ (pairHeightL2 μ π hπ) (isCocycle_pairHeightL2 μ π hπ)

end Mean

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SampledSuccessfulVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual successful interval parameters have subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

def sampledSwitchParameters {G : Type*} (f : ℕ → ℝ → G) (m : ℕ)
    (t : Fin (m + m) → ℝ) : SwitchParameters G m :=
  mapSwitchParameters f 0 m (flatSwitchSamples m t)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SegmentSupportTimes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prescribed endpoint times realizing the segment support exponents -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [Fintype B] (D : SupportDatum W I B)

/-- A linear weight on the segment chooses the final time exactly when its
value on the direction is nonnegative. -/
def segmentSupportTime (v : W) (T : ℝ) (i : I) : ℝ :=
  if 0 ≤ D.weight i v then T else 0

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateOffsetCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite family of polar quotients that detects one root offset -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

/-- One ray, and the two-ray cones independent of that ray. This is precisely
the finite family needed for a single neighboring root step. -/
def rootOffsetConeIndex (D : SupportDatum W I B) (j : I) :=
  Option {k : I // LinearIndependent ℝ
    ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]}

instance instFiniteRootOffsetConeIndex (D : SupportDatum W I B) (j : I) : Finite (rootOffsetConeIndex D j) := by
  unfold rootOffsetConeIndex
  infer_instance

instance instNonemptyRootOffsetConeIndex (D : SupportDatum W I B) (j : I) : Nonempty (rootOffsetConeIndex D j) := ⟨none⟩

/-- The source polar cone attached to one member of the finite family. -/
def rootOffsetCone (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0) (j : I) :
    rootOffsetConeIndex D j → ProperCone ℝ (StrongDual ℝ W)
  | none => closedWeightRay (D.weight j).toContinuousLinearMap (by simpa using hne j)
  | some k => closedTwoWeightCone (D.weight j).toContinuousLinearMap
      (D.weight k.val).toContinuousLinearMap k.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartLeftShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact changes of basepoint in nilpotent exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped Manifold

variable {L E G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- The chart change determined by left multiplication by `k⁻¹`. -/
def wordChartLeftShift {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) :
    C((Fin n → ℝ), (Fin n → ℝ)) where
  toFun z := (exponentialCoordinates e chart target).symm
    (k⁻¹ * exponentialCoordinates e chart source z)
  continuous_toFun := (exponentialCoordinates e chart target).symm.continuous.comp
    (continuous_const.mul (exponentialCoordinates e chart source).continuous)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordBallLeftShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact-ball restriction of the actual changed-center chart -/

noncomputable section
namespace PolycyclicRecognition

open Module Metric
open scoped Manifold

variable {L E G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- The genuine group-defined shift, with its range restricted by the
proved chart bound. -/
def wordBallLeftShift {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) (R S : ℝ)
    (hbound : ∀ z : Fin n → ℝ, ‖z‖ ≤ R →
      ‖wordChartLeftShift e chart source target k z‖ ≤ S) :
    C(closedBall (0 : Fin n → ℝ) R, closedBall (0 : Fin n → ℝ) S) := by
  let f : closedBall (0 : Fin n → ℝ) R → closedBall (0 : Fin n → ℝ) S :=
    fun z => ⟨wordChartLeftShift e chart source target k z, by
      rw [mem_closedBall, dist_zero_right]
      exact hbound z (by simpa only [mem_closedBall, dist_zero_right] using z.property)⟩
  exact ⟨f, ((wordChartLeftShift e chart source target k).continuous.comp
    continuous_subtype_val).subtype_mk _⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartScaleTransition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coordinate and height identities between two chart scales -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Finite J]

/-- Enlarging a scale contracts all coordinates with nonnegative weight. -/
theorem norm_basisScaleTransition_le [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 ≤ cost j)
    {r t : ℝ} (hrt : r ≤ t) (z : J → ℝ) :
    ‖basisScaleTransition b cost r t z‖ ≤ ‖z‖ := by
  have hh := norm_scale_exponentialRescaleBasis_le b cost t r 0
    (fun j => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrt) (hcost j))
    ((exponentialRescaleBasis b cost r).equivFun.symm z)
  simpa only [basisScaleTransition, LinearEquiv.trans_apply, Real.exp_zero, one_mul,
    LinearEquiv.apply_symm_apply] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BoundedResolutionTopHomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Top homology represented by the regular-dual cokernel

For a bounded finite projective resolution, only the final differential is
needed. Its regular-dual cokernel represents homology in the top degree.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def boundedResolutionTopHomologyEquiv
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    groupHomology A n ≃ₗ[ℤ]
      (cokernel (regularDualMap (P.complex.d n (n - 1))) ⟶ A) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hz : (P.complex.coinvariantsTensorObj A).d (n + 1) n = 0 := by
    change F.map (P.complex.d (n + 1) n) = 0
    rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, F.map_zero]
  let e := (groupHomologyIso A n P).toLinearEquiv.toAddEquiv.trans
    ((topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n hz).toAddEquiv.trans
      (regularKernelCokernelEquiv (P.complex.d n (n - 1)) A
        (hfin n) (hfin (n - 1))).toAddEquiv)
  exact { e with map_smul' := fun r x => map_intCast_smul e ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteCohomologyConnecting
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting maps for the completed coefficient theory

The kernel map of a projective cover and the syzygy dimension equivalence
give connecting maps for every short exact coefficient sequence. Naturality
holds because different choices of projective lift have the same stable map.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def shiftedCompleteBoundary (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShiftedCompletedCohomology p S.X₃ →ₗ[ℤ] ShiftedCompletedCohomology (p + 1) S.X₁ :=
  (shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS)).comp
    (shiftedSyzygyAddEquiv p S.X₃).symm.toAddMonoidHom.toIntLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HorseshoeSyzygySequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedFreeRepresentation_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_integral_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exactness of the kernel sequence of the endpoint free covers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem horseshoeKernel_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelInl S hS ≫ horseshoeKernelSnd S hS = 0 := by
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation S.X₃))).mp
  rw [Category.assoc, horseshoeKernelSnd_ι, ← Category.assoc, horseshoeKernelInl_ι]
  have h : horseshoeInl S ≫ horseshoeSnd S = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  rw [Category.assoc, h, comp_zero, zero_comp]

def horseshoeSyzygySequence (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (horseshoeKernelInl S hS) (horseshoeKernelSnd S hS) (horseshoeKernel_zero S hS)

theorem horseshoeKernelInl_injective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Injective (horseshoeKernelInl S hS).hom := by
  intro x y hxy
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₁))).mp inferInstance
  have h := congrArg (fun z => (kernel.ι (horseshoeAugmentation S hS)).hom z) hxy
  rw [horseshoeKernelInl_apply, horseshoeKernelInl_apply] at h
  exact congrArg Prod.fst h

theorem horseshoeSyzygySequence_exact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (horseshoeSyzygySequence S hS).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  change horseshoeKernel S hS at x
  change (horseshoeKernelSnd S hS).hom x = 0 at hx
  have hsnd : ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 = 0 := by
    rw [← horseshoeKernelSnd_apply, hx, map_zero]
  have hfst : (normalizedFreeAugmentation S.X₁).hom
      ((kernel.ι (horseshoeAugmentation S hS)).hom x).1 = 0 := by
    apply (Rep.mono_iff_injective S.f).mp hS.mono_f
    have h := horseshoeKernel_condition S hS x
    rw [hsnd, map_zero, add_zero] at h
    simpa only [map_zero] using h
  obtain ⟨y, hy⟩ := rep_kernel_element (normalizedFreeAugmentation S.X₁) _ hfst
  refine ⟨y, ?_⟩
  change (horseshoeKernelInl S hS).hom y = x
  apply (Rep.mono_iff_injective (kernel.ι (horseshoeAugmentation S hS))).mp inferInstance
  rw [horseshoeKernelInl_apply, hy]
  exact Prod.ext rfl hsnd.symm

theorem horseshoeKernelSnd_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (horseshoeKernelSnd S hS).hom := by
  intro y
  let c := (kernel.ι (normalizedFreeAugmentation S.X₃)).hom y
  have hc : (normalizedFreeAugmentation S.X₃).hom c = 0 :=
    ConcreteCategory.congr_hom (kernel.condition (normalizedFreeAugmentation S.X₃)) y
  have hl : S.g.hom ((presentationFreeLift S hS).hom c) = 0 := by
    exact (ConcreteCategory.congr_hom (presentationFreeLift_g S hS) c).trans hc
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact
    (- (presentationFreeLift S hS).hom c) (by rw [map_neg, hl, neg_zero])
  let u : horseshoeCover S := (normalizedFreeGenerator S.X₁ a, c)
  have hu : (horseshoeAugmentation S hS).hom u = 0 := by
    rw [horseshoeAugmentation_apply, normalizedFreeAugmentation_generator, ha, neg_add_cancel]
  obtain ⟨x, hx⟩ := rep_kernel_element (horseshoeAugmentation S hS) u hu
  refine ⟨x, ?_⟩
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₃))).mp inferInstance
  rw [horseshoeKernelSnd_apply, hx]

theorem horseshoeSyzygySequence_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (horseshoeSyzygySequence S hS).ShortExact where
  exact := horseshoeSyzygySequence_exact S hS
  mono_f := (Rep.mono_iff_injective _).mpr (horseshoeKernelInl_injective S hS)
  epi_g := (Rep.epi_iff_surjective _).mpr (horseshoeKernelSnd_surjective S hS)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_HorseshoeProjectiveTowers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three compatible projective towers resolving a short exact sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def horseshoeStage (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ℕ → {T : ShortComplex (Rep.{0} ℤ G) // T.ShortExact}
  | 0 => ⟨S, hS⟩
  | n + 1 =>
    let t := horseshoeStage S hS n
    ⟨horseshoeSyzygySequence t.1 t.2, horseshoeSyzygySequence_shortExact t.1 t.2⟩

def horseshoeLeftTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₁
  projectiveObj n := normalizedFreeRepresentation (horseshoeStage S hS n).1.X₁
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation (horseshoeStage S hS n).1.X₁)
  π n := normalizedFreeAugmentation (horseshoeStage S hS n).1.X₁
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def horseshoeMiddleTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₂
  projectiveObj n := horseshoeCover (horseshoeStage S hS n).1
  projective _n := inferInstance
  ι n := kernel.ι (horseshoeAugmentation (horseshoeStage S hS n).1 (horseshoeStage S hS n).2)
  π n := horseshoeAugmentation (horseshoeStage S hS n).1 (horseshoeStage S hS n).2
  zero _n := kernel.condition _
  shortExact n := {
    exact := ShortComplex.exact_kernel _
    mono_f := by
      change Mono (kernel.ι (horseshoeAugmentation
        (horseshoeStage S hS n).1 (horseshoeStage S hS n).2))
      infer_instance
    epi_g := inferInstance }

def horseshoeRightTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₃
  projectiveObj n := normalizedFreeRepresentation (horseshoeStage S hS n).1.X₃
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation (horseshoeStage S hS n).1.X₃)
  π n := normalizedFreeAugmentation (horseshoeStage S hS n).1.X₃
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def horseshoeTowerInl (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower.Map (horseshoeLeftTower S hS) (horseshoeMiddleTower S hS) where
  app n := (horseshoeStage S hS n).1.f
  cover n := horseshoeInl (horseshoeStage S hS n).1
  comm_left _n := horseshoeKernelInl_ι _ _
  comm_right _n := horseshoeInl_augmentation _ _

def horseshoeTowerSnd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower.Map (horseshoeMiddleTower S hS) (horseshoeRightTower S hS) where
  app n := (horseshoeStage S hS n).1.g
  cover n := horseshoeSnd (horseshoeStage S hS n).1
  comm_left _n := horseshoeKernelSnd_ι _ _
  comm_right _n := (horseshoeAugmentation_g _ _).symm

theorem horseshoeTower_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    (horseshoeTowerInl S hS).app n ≫ (horseshoeTowerSnd S hS).app n = 0 :=
  (horseshoeStage S hS n).1.zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PresentationRotation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotating a short exact sequence using a projective cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Prod.instModule
variable {G : Type} [Group G]

abbrev rotationMiddle (S : ShortComplex (Rep.{0} ℤ G)) : Rep.{0} ℤ G :=
  Rep.of (S.X₁.ρ.prod (normalizedFreeRepresentation S.X₃).ρ)

def rotationFst (S : ShortComplex (Rep.{0} ℤ G)) : rotationMiddle S ⟶ S.X₁ :=
  Rep.ofHom (.fst ℤ _ _)

def rotationSnd (S : ShortComplex (Rep.{0} ℤ G)) :
    rotationMiddle S ⟶ normalizedFreeRepresentation S.X₃ :=
  Rep.ofHom (.snd ℤ _ _)

def rotationInl (S : ShortComplex (Rep.{0} ℤ G)) : S.X₁ ⟶ rotationMiddle S :=
  Rep.ofHom (.inl ℤ _ _)

def rotationInr (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₃ ⟶ rotationMiddle S :=
  Rep.ofHom (.inr ℤ _ _)

def rotationProjection (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationMiddle S ⟶ S.X₂ :=
  rotationFst S ≫ S.f + rotationSnd S ≫ presentationFreeLift S hS

def rotationInclusion (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₃ ⟶ rotationMiddle S :=
  Rep.ofHom ((presentationKernelMap S hS).hom.prod
    (-(kernel.ι (normalizedFreeAugmentation S.X₃))).hom)

theorem rotationProjection_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : S.X₁) (y : normalizedFreeRepresentation S.X₃) :
    (rotationProjection S hS).hom (x, y) = S.f.hom x + (presentationFreeLift S hS).hom y := rfl

theorem rotationInclusion_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedSyzygy S.X₃) :
    (rotationInclusion S hS).hom x =
      ((presentationKernelMap S hS).hom x, -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) := rfl

theorem rotation_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationProjection S hS = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom ((presentationKernelMap S hS).hom x) +
    (presentationFreeLift S hS).hom (-(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) = 0
  have h := ConcreteCategory.congr_hom (presentationKernelMap_f S hS) x
  change S.f.hom ((presentationKernelMap S hS).hom x) =
    (presentationFreeLift S hS).hom ((kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) at h
  rw [map_neg, h, add_neg_cancel]

def presentationRotation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (rotationInclusion S hS) (rotationProjection S hS) (rotation_zero S hS)

theorem rotationProjection_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationProjection S hS ≫ S.g = rotationSnd S ≫ normalizedFreeAugmentation S.X₃ := by
  rw [rotationProjection, Preadditive.add_comp, Category.assoc, S.zero, comp_zero,
    Category.assoc, presentationFreeLift_g, zero_add]

theorem rotationInclusion_injective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Injective (rotationInclusion S hS).hom := by
  intro x y hxy
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₃))).mp inferInstance
  have h := congrArg Prod.snd hxy
  change -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x =
    -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom y at h
  exact neg_injective h

theorem rotationProjection_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (rotationProjection S hS).hom := by
  intro z
  let y := normalizedFreeGenerator S.X₃ (S.g.hom z)
  have hy : S.g.hom ((presentationFreeLift S hS).hom y) = S.g.hom z :=
    (ConcreteCategory.congr_hom (presentationFreeLift_g S hS) y).trans
      (normalizedFreeAugmentation_generator _ _)
  have hz : S.g.hom (z - (presentationFreeLift S hS).hom y) = 0 := by
    rw [map_sub, hy, sub_self]
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hz
  refine ⟨(a, y), ?_⟩
  rw [rotationProjection_apply, ha, sub_add_cancel]

theorem presentationRotation_exact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (presentationRotation S hS).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro z hz
  change rotationMiddle S at z
  change (rotationProjection S hS).hom z = 0 at hz
  have hc : (normalizedFreeAugmentation S.X₃).hom z.2 = 0 := by
    have h := ConcreteCategory.congr_hom (rotationProjection_g S hS) z
    change S.g.hom ((rotationProjection S hS).hom z) =
      (normalizedFreeAugmentation S.X₃).hom z.2 at h
    rw [hz, map_zero] at h
    exact h.symm
  obtain ⟨c, hc'⟩ := rep_kernel_element (normalizedFreeAugmentation S.X₃) z.2 hc
  have ha : z.1 = -(presentationKernelMap S hS).hom c := by
    apply (Rep.mono_iff_injective S.f).mp hS.mono_f
    have h := ConcreteCategory.congr_hom (presentationKernelMap_f S hS) c
    change S.f.hom ((presentationKernelMap S hS).hom c) =
      (presentationFreeLift S hS).hom ((kernel.ι (normalizedFreeAugmentation S.X₃)).hom c) at h
    change S.f.hom z.1 + (presentationFreeLift S hS).hom z.2 = 0 at hz
    rw [map_neg, h, hc']
    exact eq_neg_of_add_eq_zero_left hz
  refine ⟨-c, ?_⟩
  change (rotationInclusion S hS).hom (-c) = z
  rw [rotationInclusion_apply, map_neg, map_neg, neg_neg, hc']
  exact Prod.ext ha.symm rfl

theorem presentationRotation_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (presentationRotation S hS).ShortExact where
  exact := presentationRotation_exact S hS
  mono_f := (Rep.mono_iff_injective _).mpr (rotationInclusion_injective S hS)
  epi_g := (Rep.epi_iff_surjective _).mpr (rotationProjection_surjective S hS)

@[reassoc]
theorem rotationInclusion_fst (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationFst S = presentationKernelMap S hS := rfl

@[reassoc]
theorem rotationInclusion_snd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationSnd S = -(kernel.ι (normalizedFreeAugmentation S.X₃)) := rfl

@[reassoc]
theorem rotationInl_fst (S : ShortComplex (Rep.{0} ℤ G)) :
    rotationInl S ≫ rotationFst S = 𝟙 S.X₁ := rfl

@[reassoc]
theorem rotationInl_projection (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInl S ≫ rotationProjection S hS = S.f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom x + (presentationFreeLift S hS).hom 0 = _
  rw [map_zero, add_zero]
  rfl

def rotationToNormalized (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationRotation S hS ⟶ normalizedSyzygySequence S.X₃ where
  τ₁ := -𝟙 (normalizedSyzygy S.X₃)
  τ₂ := rotationSnd S
  τ₃ := S.g
  comm₁₂ := by
    change (-𝟙 _) ≫ kernel.ι _ = rotationInclusion S hS ≫ rotationSnd S
    rw [Preadditive.neg_comp, Category.id_comp, rotationInclusion_snd]
  comm₂₃ := (rotationProjection_g S hS).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompleteVanishingExactFunctor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional resolutions after an exact coefficient functor

Only the images of countable free covers must have vanishing completion.
The terminal projective is handled by its actual retract of a free cover.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G Q : Type} [Group G] [Group Q]

instance normalizedFreeRepresentation_countable [Countable Q]
    (A : Rep.{0} ℤ Q) [Countable A] : Countable (normalizedFreeRepresentation A) := by
  change Countable ({a : A // a ≠ 0} →₀ ℤ[Q])
  -- our `MonoidAlgebra` is a structure around `Q →₀ ℤ`, with no `Countable` instance
  have : Countable ℤ[Q] := MonoidAlgebra.coeffEquiv.injective.countable
  infer_instance

instance normalizedSyzygy_countable [Countable Q]
    (A : Rep.{0} ℤ Q) [Countable A] : Countable (normalizedSyzygy A) :=
  Function.Injective.countable (f := (kernel.ι (normalizedFreeAugmentation A)).hom)
    ((Rep.mono_iff_injective _).mp inferInstance)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CountableSumVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable sums of vanishing coefficients under FP-infinity -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
attribute [local instance 2300] Submodule.module
variable {G : Type} [Group G]

def sumPrefixGenerator (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (i : Fin n) :
    A i ⟶ sumPrefixRepresentation A n := by
  classical
  let f := integralRepresentationSumInclusion A i.val
  exact Rep.ofHom ⟨{
    toFun x := ⟨f.hom x, by
      intro j hj
      exact integralRepresentationSumInclusion_ne A i.val j (by omega) x⟩
    map_add' x y := by apply Subtype.ext; exact map_add f.hom x y
    map_smul' r x := by apply Subtype.ext; exact f.hom.toLinearMap.map_smul r x }, fun g => by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact Rep.hom_comm_apply f g x⟩

def sumPrefixFromFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    integralRepresentationSum (fun i : Fin n => A i) ⟶ sumPrefixRepresentation A n :=
  integralRepresentationSumDesc _ _ (sumPrefixGenerator A n)

def sumPrefixToFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ⟶ integralRepresentationSum (fun i : Fin n => A i) :=
  Rep.ofHom ⟨{
    toFun x := DFinsupp.comapDomain Fin.val Fin.val_injective x.val
    map_add' x y := DFinsupp.comapDomain_add Fin.val Fin.val_injective x.val y.val
    map_smul' r x := DFinsupp.comapDomain_smul Fin.val Fin.val_injective r x.val }, fun g => by
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro i
      rfl⟩

theorem sumPrefixToFinite_injective (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    Function.Injective (sumPrefixToFinite A n).hom := by
  intro x y h
  apply Subtype.ext
  apply DFinsupp.ext
  intro i
  by_cases hi : i < n
  · exact congrArg (fun z => z ⟨i, hi⟩) h
  · exact (x.property i (by omega)).trans (y.property i (by omega)).symm

theorem sumPrefixGenerator_toFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (i : Fin n) :
    sumPrefixGenerator A n i ≫ sumPrefixToFinite A n =
      integralRepresentationSumInclusion (fun j : Fin n => A j) i := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change DFinsupp.comapDomain Fin.val Fin.val_injective
    ((integralRepresentationSumInclusion A i.val).hom x) =
      (integralRepresentationSumInclusion (fun j : Fin n => A j) i).hom x
  rw [integralRepresentationSumInclusion_apply, integralRepresentationSumInclusion_apply]
  exact DFinsupp.comapDomain_single (β := fun j => (A j).V) Fin.val Fin.val_injective i x

theorem sumPrefixFromFinite_toFinite (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixFromFinite A n ≫ sumPrefixToFinite A n =
      𝟙 (integralRepresentationSum (fun i : Fin n => A i)) := by
  apply integralRepresentationSum_hom_ext
  intro i
  change integralRepresentationSumInclusion (fun i : Fin n => A i) i ≫
    (integralRepresentationSumDesc _ _ (sumPrefixGenerator A n) ≫ sumPrefixToFinite A n) = _
  rw [← Category.assoc, integralRepresentationSumInclusion_desc,
    sumPrefixGenerator_toFinite, Category.comp_id]

def sumPrefixFiniteIso (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ≅ integralRepresentationSum (fun i : Fin n => A i) := by
  let : Mono (sumPrefixToFinite A n) :=
    (Rep.mono_iff_injective _).mpr (sumPrefixToFinite_injective A n)
  exact {
    hom := sumPrefixToFinite A n
    inv := sumPrefixFromFinite A n
    inv_hom_id := sumPrefixFromFinite_toFinite A n
    hom_inv_id := by
      apply (cancel_mono (sumPrefixToFinite A n)).mp
      rw [Category.assoc, sumPrefixFromFinite_toFinite, Category.comp_id, Category.id_comp] }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalQuotientCompleteVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional quotients propagate induced-kernel vanishing

The quotient resolution is inflated and tensored with the coefficient.
Its countable free terms are actual sums of the induced kernel coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

def quotientTensorRegularIso :
    (quotientTensorFunctor N A).obj (Rep.leftRegular ℤ (G ⧸ N)) ≅
      Rep.ind N.subtype (Rep.res N.subtype A) :=
  (β_ A (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)))) ≪≫
    (normalInductionTensorIso N A).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_RegularDualCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.finiteResolution_single_supported _root_.OAI.PolycyclicRecognition.finiteTruncationAugmentation_quasiIso _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.rationalCoefficientInclusion_apply _root_.OAI.PolycyclicRecognition.regularDualFreeEquiv_apply _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The underlying module of the top regular-dual cokernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularDualCokernelCohomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hbound : IsZero (P.complex.X (n + 1))) :
    (forget₂ (Rep ℤ G) (ModuleCat ℤ)).obj
        (cokernel (regularDualMap (P.complex.d n (n - 1)))) ≅
      groupCohomology (Rep.leftRegular ℤ G) n := by
  classical
  let C := P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ G)
  let F := forget₂ (Rep ℤ G) (ModuleCat ℤ)
  have hz : C.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro q
    change P.complex.X n ⟶ Rep.leftRegular ℤ G at q
    change P.complex.d (n + 1) n ≫ q = 0
    rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, zero_comp]
  have hd : C.d (n - 1) n = F.map (regularDualMap (P.complex.d n (n - 1))) := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro q
    rfl
  let e : C.homology n ≅ cokernel (C.d (n - 1) n) :=
    (C.isoHomologyι n (n + 1) (CochainComplex.next ℕ n) hz).trans
      ((C.opcyclesIsoSc' (n - 1) n (n + 1) (by cases n <;> simp) (CochainComplex.next ℕ n)).trans
        (C.sc' (n - 1) n (n + 1)).opcyclesIsoCokernel)
  exact (PreservesCokernel.iso F (regularDualMap (P.complex.d n (n - 1)))).trans
    ((cokernelIsoOfEq hd).symm.trans
      (e.symm.trans (groupCohomologyIso (Rep.leftRegular ℤ G) n P).symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_TopHomologyNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_projective _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient naturality of top-dimensional duality

Use one fixed resolution comparison for all coefficients. This records the
naturality needed to turn a coefficient trace into a top-homology trace.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def naturalTopHomologyEquiv [DecidableEq G]
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    groupHomology A n ≃ₗ[ℤ]
      (cokernel (regularDualMap (P.complex.d n (n - 1))) ⟶ A) := by
  let e := (coefficientNaturalHomologyIso P A n).toLinearEquiv.toAddEquiv.trans
    ((topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n
      (tensor_top_d_zero P n hbound A)).toAddEquiv.trans
        (regularKernelCokernelEquiv (P.complex.d n (n - 1)) A
          (hfin n) (hfin (n - 1))).toAddEquiv)
  exact { e with map_smul' := fun r x => map_intCast_smul e ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRealShadow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real shadow Lie algebra

Removing only the imaginary semisimple Cartan action gives a genuine Lie
algebra on the original vector space. Its bracket is obtained from a closed
graph in the derivation semidirect sum, so the Jacobi identity is inherited.
-/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- Only multiplication changes: the real vector space is unchanged. -/
def cartanRealShadowEquiv : L ≃ₗ[ℝ] CartanRealShadow T H where
  toFun x := ⟨⟨x,-T.weightImaginaryAction H x⟩,rfl⟩
  invFun p := p.val.left
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -T.weightImaginaryAction H (x+y) =
        -T.weightImaginaryAction H x + -T.weightImaginaryAction H y
      rw [map_add,neg_add]
  map_smul' r x := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -T.weightImaginaryAction H (r • x) = r • -T.weightImaginaryAction H x
      rw [map_smul,smul_neg]

set_option maxHeartbeats 1000000 in
instance : FiniteDimensional ℝ (CartanRealShadow T H) :=
  (cartanRealShadowEquiv T H).finiteDimensional

set_option maxHeartbeats 1000000 in
/-- Exact bracket after removing the imaginary semisimple action. -/
theorem cartanRealShadow_bracket (x y : L) :
    (cartanRealShadowEquiv T H).symm ⁅cartanRealShadowEquiv T H x,
      cartanRealShadowEquiv T H y⁆ =
      ⁅x,y⁆ - T.weightImaginaryAction H x y + T.weightImaginaryAction H y x := by
  change ⁅x,y⁆ + (-T.weightImaginaryAction H x) y - (-T.weightImaginaryAction H y) x = _
  simp only [LieDerivation.neg_apply]
  abel

set_option maxHeartbeats 1000000 in
/-- The weight quotient of the modified bracket remains abelian. -/
theorem cartanRealShadow_bracket_weight (x y : L) :
    T.weightMap ((cartanRealShadowEquiv T H).symm
      ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆) = 0 := by
  rw [cartanRealShadow_bracket,map_add,map_sub,T.weightMap_lie]
  change 0 - T.weightMap (realImaginaryOperator L H _ y) +
    T.weightMap (realImaginaryOperator L H _ x) = 0
  rw [T.weightMap_realImaginaryOperator H,T.weightMap_realImaginaryOperator H]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRealShadowSolvable
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real shadow retains its nilpotent kernel and is solvable -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The same weight kernel, now inside the modified Lie algebra. -/
def realShadowKernel : LieIdeal ℝ (CartanRealShadow T H) where
  __ := (T.weightMap.comp (cartanRealShadowEquiv T H).symm.toLinearMap).ker
  lie_mem := by
    intro p q _
    change T.weightMap ((cartanRealShadowEquiv T H).symm ⁅p,q⁆) = 0
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective q
    exact cartanRealShadow_bracket_weight T H x y

set_option maxHeartbeats 1000000 in
/-- On the nilpotent ideal the modified and original brackets agree. -/
def realShadowKernelEquiv : T.kernelIdeal ≃ₗ⁅ℝ⁆ realShadowKernel T H where
  toFun x := ⟨cartanRealShadowEquiv T H x,by
    change T.weightMap ((cartanRealShadowEquiv T H).symm (cartanRealShadowEquiv T H x)) = 0
    simpa only [LinearEquiv.symm_apply_apply] using (T.mem_kernelIdeal (x : L)).mp x.property⟩
  invFun p := ⟨(cartanRealShadowEquiv T H).symm p.val,p.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).symm_apply_apply x
  right_inv p := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).apply_symm_apply p.val
  map_add' x y := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (cartanRealShadowEquiv T H).map_smul r x
  map_lie' {x y} := by
    apply Subtype.ext
    apply (cartanRealShadowEquiv T H).symm.injective
    change (cartanRealShadowEquiv T H).symm (cartanRealShadowEquiv T H ⁅(x : L),(y : L)⁆) =
      (cartanRealShadowEquiv T H).symm ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆
    rw [LinearEquiv.symm_apply_apply,cartanRealShadow_bracket,
      T.weightImaginaryAction_kernel H x x.property,T.weightImaginaryAction_kernel H y y.property]
    simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanScaleTransition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact scale transport of the actual Cartan profiles on a fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℝ L]

set_option maxHeartbeats 1000000 in
/-- The same group point in the two word charts, restricted to a fixed
coordinate ball. Larger physical scales contract this ball. -/
def wordBallScaleTransition
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (R : ℝ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) :
    C(Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R,
      Metric.closedBall (0 : Fin (finrank ℝ L) → ℝ) R) :=
  closedBallLinearSelf
    (basisScaleTransition (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ))
      (Real.log r) (Real.log t)).toContinuousLinearEquiv.toContinuousLinearMap
    (norm_basisScaleTransition_le _ _ (fun _j => Nat.cast_nonneg _)
      (Real.log_le_log hr hrt)) R

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanVisitPath
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The specified Cartan visit path

This definition retains the actual outward-switch-return construction,
so later sampling does not depend on an arbitrary choice of a path.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
def cartanSupportVisitPath (w₀ w₁ : W) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r b : ℝ) :
    Path (n * Exp h₀) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let v := (supportLegDirection T H eW w₀ w₁ : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  exact supportVisitPath (fun t => Exp (t • v))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i))
    (by simp [hExp.map_zero]) n (Exp h₀) r b

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InvariantGraphLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic solvable model on an invariant graph

The graph uses the original vector-space chart. Its operations are analytic,
and its dimension is the dimension of the nilpotent group alone.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance] semidirectProductTopology
variable {L V : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (φ : Multiplicative V →* MulAut L) (τ : L →* Multiplicative V)
  (hinv : ∀ v x, τ (φ v x) = τ x)
  (hφ : ContDiff ℝ ⊤ (fun p : V × L => φ (Multiplicative.ofAdd p.1) p.2))
  (hτ : ContDiff ℝ ⊤ (fun x => (τ x).toAdd))

def invariantGraphEquiv : L ≃ rotationalTwist φ τ hinv where
  toFun x := ⟨⟨x, (τ x)⁻¹⟩, rfl⟩
  invFun x := x.val.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.property.symm

@[instance_reducible]
def invariantGraphGroup : Group L := (invariantGraphEquiv φ τ hinv).group

include hφ hτ in
omit [Group.IsSolvable L] [FiniteDimensional ℝ V] in
theorem invariantGraphLieGroup :
    letI := invariantGraphGroup φ τ hinv
    LieGroup (𝓘(ℝ, L)) ⊤ L := by
  have hm : ContMDiff ((𝓘(ℝ, L)).prod (𝓘(ℝ, L))) (𝓘(ℝ, L)) ⊤
      (fun p : L × L => P.group.mul p.1 (φ ((τ p.1)⁻¹) p.2)) := by
    have hs : ContDiff ℝ ⊤ (fun p : L × L =>
        φ (Multiplicative.ofAdd (-(τ p.1).toAdd)) p.2) :=
      hφ.comp (((hτ.comp contDiff_fst).neg).prodMk contDiff_snd)
    exact contMDiff_fst.mul (hs.comp_contMDiff (contMDiff_fst.prodMk_space contMDiff_snd))
  have hi : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ⊤
      (fun x : L => φ (τ x) (P.group.inv x)) := by
    have hs : ContDiff ℝ ⊤ (fun x : L =>
        φ (Multiplicative.ofAdd (τ x).toAdd) (P.group.inv x)) :=
      hφ.comp (hτ.prodMk (contMDiff_id.inv.contDiff))
    exact hs.contMDiff
  have hig (x : L) : (invariantGraphGroup φ τ hinv).inv x = φ (τ x) (P.group.inv x) := by
    change φ (((τ x)⁻¹)⁻¹) (P.group.inv x) = _
    rw [inv_inv]
  let := invariantGraphGroup φ τ hinv
  refine { toIsManifold := inferInstance, contMDiff_mul := hm, contMDiff_inv := ?_ }
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact hig x

def invariantGraphMulEquiv :
    let T := rotationalTwist φ τ hinv
    letI := invariantGraphGroup φ τ hinv
    L ≃* T := by
  let T := rotationalTwist φ τ hinv
  let e := invariantGraphEquiv φ τ hinv
  letI := invariantGraphGroup φ τ hinv
  refine { e with map_mul' := ?_ }
  intro x y
  change e (e.symm (e x * e y)) = e x * e y
  exact e.apply_symm_apply _

include hφ hτ in
def invariantGraphLieModel : SimplyConnectedSolvableLieModel := by
  let T := rotationalTwist φ τ hinv
  have hsolv : Group.IsSolvable T := by
    let : Group.IsSolvable (L ⋊[φ] Multiplicative V) := semidirect_solvable φ
    infer_instance
  let e1 := invariantGraphMulEquiv φ τ hinv
  have hLie := invariantGraphLieGroup φ τ hinv hφ hτ
  let g := invariantGraphGroup φ τ hinv
  letI : Group L := g
  letI : Mul L := g.toMul
  letI : One L := g.toOne
  letI : Monoid L := g.toMonoid
  letI : MulOneClass L := g.toMulOneClass
  letI : LieGroup (𝓘(ℝ, L)) ⊤ L := hLie
  let e : L ≃* T := e1
  let := hsolv
  letI : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact { modelSpace := L, carrier := L }

def invariantGraphModelEquiv : (invariantGraphLieModel φ τ hinv hφ hτ).carrier ≃*
    rotationalTwist φ τ hinv :=
  invariantGraphMulEquiv φ τ hinv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TangentRotationRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact rotations on the concrete model space of a Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

/-- This version uses the original model-space norm and scalar structures. -/
def tangentTorusUnitAction :
    realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* (E →L[ℝ] E)ˣ where
  toFun z :=
    let e : E ≃ₗ[ℝ] E := (realTorusAutomorphism (GroupLieAlgebra (𝓘(ℝ,E)) G) H z).toLinearEquiv
    e.toContinuousLinearEquiv.toUnit
  map_one' := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_one (GroupLieAlgebra (𝓘(ℝ,E)) G) H x
  map_mul' z w := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro x
    exact realTorusOperator_mul (GroupLieAlgebra (𝓘(ℝ,E)) G) H z w x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealPhaseDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real infinitesimal phase on the group model space -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold TensorProduct

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

local instance instNormedAddCommGroupTensorProductRealComplexGroupLieAlgebraModelWithCornersSelf_solutions : NormedAddCommGroup (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance instNormedSpaceComplexTensorProductRealGroupLieAlgebraModelWithCornersSelf_solutions : NormedSpace ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  ComplexCartan.rotationNormedSpace
local instance instNormedSpaceRealTensorProductComplexGroupLieAlgebraModelWithCornersSelf_solutions : NormedSpace ℝ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealPhaseExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact Cartan rotations as exponentials of their imaginary derivations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

/-- The imaginary derivation with the original model-space norm. -/
def tangentImaginaryOperator (h : H) : E →L[ℝ] E :=
  (show E →ₗ[ℝ] E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h).toContinuousLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealShadowSplit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real triangularizability of the modified Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def realShadowAdjoint (x : L) : Module.End ℝ L :=
  (cartanRealShadowEquiv T H).symm.toLinearMap.comp
    ((ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x)).comp
      (cartanRealShadowEquiv T H).toLinearMap)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multivariate polynomial multiplication in the derivation extension -/

noncomputable section
namespace PolycyclicRecognition
variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

def semidirectCoordinateLinear : (L × ℝ) →ₗ[ℝ] ((Fin n ⊕ Unit) → ℝ) where
  toFun p i := semidirectCoordinate b i p
  map_add' p q := by
    funext i
    cases i with
    | inl i => exact congrFun (map_add b.equivFun p.1 q.1) i
    | inr i => rfl
  map_smul' r p := by
    funext i
    cases i with
    | inl i => exact congrFun (map_smul b.equivFun r p.1) i
    | inr i => rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomiality and linear coordinate readout for the semidirect representation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m d : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def semidirectMatrixReadout :
    letI := derivationSemidirectGroup D hD
    ((Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b)) →
      Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (L × ℝ) := by
  let := derivationSemidirectGroup D hD
  intro B
  exact (semidirectCoordinateLinear b).leftInverse.comp
    (coordinateMatrixReadout (semidirectCoordinate b) B)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ShadowExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear coordinates for the two real-shadow exponential factors -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)

def shadowRepresentationParameter : L →ₗ[ℝ] A :=
  j.toLinearMap.comp (cartanRealShadowEquiv T H).toLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularExponentialKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive triangular exponentials and their kernel

A faithful triangular Lie representation exponentiates into the positive
triangular group. Nilradical exponentials are unipotent, and a real upper
triangular matrix with exponential equal to the identity is zero.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def positiveTriangularExp (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular) :
    positiveTriangular n :=
  ⟨algebraExpUnit A, matrix_exp_upperTriangular A hA,
    fun i => by
      change 0 < NormedSpace.exp A i i
      rw [matrix_exp_diagonal A hA i]
      exact Real.exp_pos _⟩

@[simp] theorem positiveTriangularExp_matrix (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) :
    PositiveTriangular.matrix (positiveTriangularExp A hA) = NormedSpace.exp A := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UnitsLieAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tangent Lie algebra of algebra units

Differentiating the inclusion identifies the tangent Lie algebra with the
commutator algebra. This permits the proved nilpotent integration theorem
to target matrix units directly.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def unitsLieHom : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ →ₗ⁅ℝ⁆ A :=
  unitsHomLieDifferential (MonoidHom.id Aˣ) Units.contMDiff_val

theorem unitsLieHom_apply (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) : unitsLieHom A x = x := by
  change (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) (Units.val : Aˣ → A) 1) x = x
  have he : (Units.val : Aˣ → A) = extChartAt (𝓘(ℝ, A)) (1 : Aˣ) := rfl
  rw [he, mfderiv_extChartAt_self]
  rfl

def unitsLieEquiv : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ ≃ₗ⁅ℝ⁆ A :=
  LieEquiv.ofBijective (unitsLieHom A)
    ⟨fun x y h => (unitsLieHom_apply A x).symm.trans (h.trans (unitsLieHom_apply A y)),
      fun x => ⟨x, unitsLieHom_apply A x⟩⟩

@[simp] theorem unitsLieEquiv_apply (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) :
    unitsLieEquiv A x = x := unitsLieHom_apply A x

@[simp] theorem unitsLieEquiv_symm_apply (x : A) : (unitsLieEquiv A).symm x = x := by
  have h := (unitsLieEquiv A).apply_symm_apply x
  exact (unitsLieEquiv_apply A ((unitsLieEquiv A).symm x)).symm.trans h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedChainMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A proper chain metric from a compact generating neighborhood -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)
  (hbounded : ∀ x y : G, dist x y ≤ 1)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K)

local notation "N" => compactWeightedNorm K hK hbounded hsymm

include hball in
theorem weightedDistance_le_near {x y : G} (hxy : dist x y ≤ δ) :
    N (x⁻¹ * y) ≤ dist x y := by
  have hmem : x⁻¹ * y ∈ K := hball _ (by simpa only [dist_one_groupDifference] using hxy)
  have h := weightedWordNorm_le (compactWordCost K hK) (x⁻¹ * y)
  rw [compactWordCost_mem K hK _ hmem] at h
  have hreal : N (x⁻¹ * y) ≤ dist 1 (x⁻¹ * y) := by exact_mod_cast h
  simpa only [dist_one_groupDifference] using hreal

include hδ hball in
theorem weightedDistance_topology (s : Set G) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, N (x⁻¹ * y) < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hsub⟩ := hs x hx
    refine ⟨ε, hε, fun y hy => hsub ?_⟩
    simpa only [mem_ball, dist_comm] using (metric_le_weightedDistance K hK hsymm hbounded x y).trans_lt hy
  · intro hs x hx
    obtain ⟨ε, hε, hsub⟩ := hs x hx
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro y hy
    have hxy : dist x y < min δ ε := by simpa only [mem_ball, dist_comm] using hy
    exact hsub y ((weightedDistance_le_near K hK hsymm hbounded δ hball
      (lt_of_lt_of_le hxy (min_le_left _ _)).le).trans_lt
        (lt_of_lt_of_le hxy (min_le_right _ _)))

@[instance_reducible]
def weightedGroupMetric : MetricSpace G :=
  MetricSpace.ofDistTopology (fun x y => N (x⁻¹ * y))
    (by intro x; simp)
    (by intro x y; simpa only [mul_inv_rev, inv_inv] using (map_inv_eq_map (N) (x⁻¹ * y)).symm)
    (by
      intro x y z
      simpa only [mul_assoc, mul_inv_cancel_left] using map_mul_le_add (N) (x⁻¹ * y) (y⁻¹ * z))
    (weightedDistance_topology K hK hsymm hbounded δ hδ hball)
    (by intro x y h; exact inv_mul_eq_one.mp ((N).eq_one_of_map_eq_zero' _ h))

theorem weightedGroupMetric_isometric :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    IsIsometricSMul G G := by
  let m₀ : MetricSpace G := inferInstance
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  refine ⟨fun g => Isometry.of_dist_eq ?_⟩
  intro x y
  change @compactWeightedNorm G _ m₀ _ K hK hbounded hsymm ((g * x)⁻¹ * (g * y)) =
    @compactWeightedNorm G _ m₀ _ K hK hbounded hsymm (x⁻¹ * y)
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

include hδ hδ1 hball in
theorem weighted_ball_subset_compact_power (x : G) (R : ℝ) :
    {y | N (x⁻¹ * y) ≤ R} ⊆
      (fun g : G => x * g) '' (K ^ ⌈(4 / δ) * R + (4 / δ) + 1⌉₊) := by
  intro y hy
  have hb := wordLength_le_weightedNorm_add K hK hbounded hsymm hδ hδ1 hball (x⁻¹ * y)
  have hlen : compactWordLength K hK (x⁻¹ * y) ≤ ⌈(4 / δ) * R + (4 / δ) + 1⌉₊ := by
    have hreal := (hb.trans (by gcongr; exact hy)).trans (Nat.le_ceil ((4 / δ) * R + (4 / δ) + 1))
    exact_mod_cast hreal
  have hone : (1 : G) ∈ K := hball 1 (by simpa using hδ.le)
  exact ⟨x⁻¹ * y, wordLength_ball_subset_pow K hK hsymm hone _ hlen, by simp⟩

include hδ1 in
theorem weightedGroupMetric_proper [IsTopologicalGroup G] (hcompact : IsCompact K) :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    ProperSpace G := by
  let n₀ : GroupNorm G := N
  have hcontain (x : G) (R : ℝ) :=
    weighted_ball_subset_compact_power K hK hsymm hbounded δ hδ hδ1 hball x R
  have hcompactPow (n : ℕ) := isCompact_set_pow K hcompact n
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  constructor
  intro x R
  apply IsCompact.of_isClosed_subset
    ((hcompactPow ⌈(4 / δ) * R + (4 / δ) + 1⌉₊).image
      (continuous_const.mul continuous_id)) isClosed_closedBall
  intro y hy
  apply hcontain x R
  change n₀ (y⁻¹ * x) ≤ R at hy
  have he : n₀ (x⁻¹ * y) = n₀ (y⁻¹ * x) := by
    simpa only [mul_inv_rev, inv_inv] using map_inv_eq_map n₀ (y⁻¹ * x)
  exact he.trans_le hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedMetricChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit bounded-step chains for the weighted metric -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped NNReal Pointwise

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)
  (hbounded : ∀ x y : G, dist x y ≤ 1)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K)

def weightedMetricChains :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    LinearMetricChains G := by
  let n₀ := compactWeightedNorm K hK hbounded hsymm
  let P := compactWordGenerators K hK
  have hshort (g : G) (hg : g ∈ K) : n₀ g ≤ 1 := by
    have h := weightedWordNorm_le (compactWordCost K hK) g
    rw [compactWordCost_mem K hK g hg] at h
    have hreal : n₀ g ≤ dist 1 g := by exact_mod_cast h
    exact hreal.trans (hbounded 1 g)
  have hword (g : G) : (P.wordLength g : ℝ) ≤ (4 / δ) * n₀ g + (4 / δ) + 1 :=
    wordLength_le_weightedNorm_add K hK hbounded hsymm hδ hδ1 hball g
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  refine {
    step := 1
    step_pos := by norm_num
    slope := 4 / δ
    slope_nonneg := div_nonneg (by norm_num) hδ.le
    error := (4 / δ) + 1
    error_nonneg := by positivity
    chain := ?_ }
  intro x y
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l.length, fun i => x * P.wordProd (l.take i), by simp, by simp [he], ?_, ?_⟩
  · change (l.length : ℝ) ≤ (4 / δ) * n₀ (x⁻¹ * y) + ((4 / δ) + 1)
    have hh : l.length = P.wordLength (x⁻¹ * y) := by rw [← he, hl.eq]
    rw [hh]
    simpa only [add_assoc] using hword (x⁻¹ * y)
  · intro i hi
    change n₀ ((x * P.wordProd (l.take i))⁻¹ * (x * P.wordProd (l.take (i + 1)))) ≤ 1
    rw [← List.take_concat_get' l i hi, P.wordProd_append]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    apply hshort
    simpa only [P, compactWordGenerators, List.length_singleton, pow_one] using
      generator_wordProd_mem_pow K hK hsymm [l[i]]

def weightedProperChainMetric [IsTopologicalGroup G] (hcompact : IsCompact K) :
    ProperChainMetric G where
  metric := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  topology_eq := rfl
  proper := weightedGroupMetric_proper K hK hsymm hbounded δ hδ hδ1 hball hcompact
  leftInvariant := weightedGroupMetric_isometric K hK hsymm hbounded δ hδ hball
  chains := weightedMetricChains K hK hsymm hbounded δ hδ hδ1 hball

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_LatticeWordExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending lattice automorphisms through ordered polynomial coordinates

The extension is constructed by replacing each integral generator power by
the corresponding real one-parameter subgroup. Polynomial identities prove
both multiplicativity and the inverse identities.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
variable {L H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group H] {d : ℕ}
  (b : Basis (Fin d) ℝ L) (p : L ≃ L) (e : H →* L) (X : Fin d → H)

def latticeWordMap (a : H →* H) : L → L :=
  fun x => orderedRealWord b (fun i => e (a (X i))) (p.symm x)

theorem latticeWordMap_polynomial (hq : IsPolynomialInBasis b b p.symm) (a : H →* H) :
    IsPolynomialInBasis b b (latticeWordMap b p e X a) :=
  (orderedRealWord_polynomial b _).comp hq

theorem latticeWordMap_on_lattice
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : H →* H) (x : H) :
    latticeWordMap b p e X a (e x) = e (a x) := by
  obtain ⟨z, rfl⟩ := hX x
  rw [← hparam z]
  change orderedRealWord b (fun i => e (a (X i)))
    (p.symm (p (b.equivFun.symm (fun i => (z i : ℝ))))) = _
  rw [p.symm_apply_apply, orderedRealWord_integer]
  exact orderedWord_map (e.comp a) X z

def latticeWordAut (hp : IsPolynomialInBasis b b p) (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) : MulAut L := by
  let f := latticeWordMap b p e X a.toMonoidHom
  let g := latticeWordMap b p e X a.symm.toMonoidHom
  have hf := latticeWordMap_polynomial b p e X hq a.toMonoidHom
  have hg := latticeWordMap_polynomial b p e X hq a.symm.toMonoidHom
  have hF (x : H) : f (e x) = e (a x) :=
    latticeWordMap_on_lattice b p e X hparam hX a.toMonoidHom x
  have hG (x : H) : g (e x) = e (a.symm x) :=
    latticeWordMap_on_lattice b p e X hparam hX a.symm.toMonoidHom x
  refine polynomialGroupEquivFromParameter b hf hg hp p.surjective ?_ ?_ ?_
  · intro z w
    rw [hparam z, hparam w]
    calc
      f (e (orderedWord X z) * e (orderedWord X w)) =
          e (a (orderedWord X z * orderedWord X w)) := by rw [← map_mul, hF]
      _ = e (a (orderedWord X z)) * e (a (orderedWord X w)) := by rw [map_mul, map_mul]
      _ = f (e (orderedWord X z)) * f (e (orderedWord X w)) := by rw [hF, hF]
  · intro z
    change g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
      p (b.equivFun.symm (fun i => (z i : ℝ)))
    rw [hparam z, hF, hG, a.symm_apply_apply]
  · intro z
    change f (g (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
      p (b.equivFun.symm (fun i => (z i : ℝ)))
    rw [hparam z, hG, hF, a.apply_symm_apply]

theorem latticeWordAut_on_lattice (hp : IsPolynomialInBasis b b p)
    (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) (x : H) :
    latticeWordAut b p e X hp hq hparam hX a (e x) = e (a x) :=
  latticeWordMap_on_lattice b p e X hparam hX a.toMonoidHom x

end PolycyclicRecognition

end

end OAI
end


